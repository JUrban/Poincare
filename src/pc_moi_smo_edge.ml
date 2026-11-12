needs "src/pc_moi_smo_cf.ml";;
needs "src/pc_moi_smo_base.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* pc_moi_smo_edge (route M): the edge charts (angular rescaling about an   *)
(* edge) and the smooth atlas on the polyhedron minus its vertices.  Main   *)
(* theorems: MOI_SMO_EDGE (C4), MOI_SMO_PUNCTURED_FROM_PARTS (the glue      *)
(* MOI_SMO_PUNCTURED_TERM) and MOI_SMO_PUNCTURED (C5).                      *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* 0. Points of real^3 written as (complex number, height), rotations about *)
(* the third axis, the angular rescaling in this form, axis isometries.     *)
(* ------------------------------------------------------------------------- *)

let moi_sed_v3 = new_definition
 `moi_sed_v3 (z:complex) (h:real) = vector[Re z; Im z; h]:real^3`;;

let moi_sed_pt = new_definition
 `moi_sed_pt = moi_sed_v3 (Cx(sqrt(&3) / &2)) (&1 / &2)`;;

let moi_sed_qt = new_definition
 `moi_sed_qt = moi_sed_v3 (Cx(sqrt(&3) / &2) * cexp(ii * Cx moi_smo_dihedral))
                          (&1 / &2)`;;

let moi_sed_slit = new_definition
 `moi_sed_slit = {y:real^3 | ~(y$2 = &0 /\ &0 <= y$1)}`;;

let moi_sed_ax = new_definition
 `moi_sed_ax (b:real) (eps:bool) (y:real^3) =
    moi_sed_v3 (cexp(ii * Cx b) *
                (if eps then complex(y$1,y$2) else cnj(complex(y$1,y$2))))
               (y$3)`;;

let moi_sed_flip = new_definition
 `moi_sed_flip (y:real^3) = vector[y$1; y$2; &1 - y$3]:real^3`;;

let MOI_SED_V3_COMPONENTS = prove
 (`!z h. (moi_sed_v3 z h)$1 = Re z /\ (moi_sed_v3 z h)$2 = Im z /\
         (moi_sed_v3 z h)$3 = h`,
  REWRITE_TAC[moi_sed_v3; VECTOR_3]);;

let MOI_SED_V3_EQ = prove
 (`!z h z' h'. moi_sed_v3 z h = moi_sed_v3 z' h' <=> z = z' /\ h = h'`,
  REWRITE_TAC[moi_sed_v3; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
              COMPLEX_EQ] THEN
  MESON_TAC[]);;

let MOI_SED_V3_CZ = prove
 (`!z h. complex((moi_sed_v3 z h)$1,(moi_sed_v3 z h)$2) = z`,
  REWRITE_TAC[MOI_SED_V3_COMPONENTS; COMPLEX]);;

let MOI_SED_V3_EXPAND = prove
 (`!y:real^3. y = moi_sed_v3 (complex(y$1,y$2)) (y$3)`,
  REWRITE_TAC[moi_sed_v3; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; RE; IM]);;

let MOI_SED_V3_ADD = prove
 (`!z h z' h'. moi_sed_v3 z h + moi_sed_v3 z' h' = moi_sed_v3 (z + z') (h + h')`,
  REWRITE_TAC[moi_sed_v3; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
              VECTOR_ADD_COMPONENT; RE_ADD; IM_ADD]);;

let MOI_SED_V3_CMUL = prove
 (`!c z h. c % moi_sed_v3 z h = moi_sed_v3 (Cx c * z) (c * h)`,
  REWRITE_TAC[moi_sed_v3; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
              VECTOR_MUL_COMPONENT; RE_MUL_CX; IM_MUL_CX]);;

let MOI_SED_V3_SUB = prove
 (`!z h z' h'. moi_sed_v3 z h - moi_sed_v3 z' h' = moi_sed_v3 (z - z') (h - h')`,
  REWRITE_TAC[moi_sed_v3; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
              VECTOR_SUB_COMPONENT; RE_SUB; IM_SUB]);;

let MOI_SED_V3_ZERO = prove
 (`vec 0:real^3 = moi_sed_v3 (Cx(&0)) (&0) /\
   basis 3:real^3 = moi_sed_v3 (Cx(&0)) (&1)`,
  SIMP_TAC[moi_sed_v3; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
           VEC_COMPONENT; BASIS_COMPONENT; RE_CX; IM_CX; ARITH]);;

let MOI_SED_ROTZ_V3 = prove
 (`!a z h. moi_smo_rotz a (moi_sed_v3 z h) =
           moi_sed_v3 (cexp(ii * Cx a) * z) h`,
  REWRITE_TAC[moi_smo_rotz; moi_sed_v3; CART_EQ; DIMINDEX_3; FORALL_3;
              VECTOR_3; RE_MUL_CX; IM_MUL_CX; complex_mul; RE; IM;
              RE_CEXP; IM_CEXP; RE_MUL_II; IM_MUL_II; RE_CX; IM_CX] THEN
  REWRITE_TAC[REAL_NEG_0; REAL_EXP_0; REAL_MUL_LID] THEN REAL_ARITH_TAC);;

let MOI_SED_TWIST_V3 = prove
 (`!k z h. moi_smo_twist k (moi_sed_v3 z h) =
           moi_sed_v3 (Cx(norm z) * cexp(ii * Cx(k * Arg z))) h`,
  REWRITE_TAC[moi_smo_twist; MOI_SED_V3_CZ] THEN
  REWRITE_TAC[moi_sed_v3; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
              RE_MUL_CX; IM_MUL_CX; RE_CEXP; IM_CEXP; RE_MUL_II; IM_MUL_II;
              RE_CX; IM_CX; REAL_NEG_0; REAL_EXP_0; REAL_MUL_LID]);;

let MOI_SED_NORM_POLAR = prove
 (`!r th. &0 <= r ==> norm(Cx r * cexp(ii * Cx th)) = r`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; NORM_CEXP; COMPLEX_NORM_CX; RE_MUL_II;
              IM_CX; REAL_NEG_0; REAL_EXP_0; REAL_MUL_RID] THEN
  ASM_REAL_ARITH_TAC);;

let MOI_SED_TWIST_POLAR = prove
 (`!k r th h. &0 <= r /\ &0 <= th /\ th < &2 * pi
              ==> moi_smo_twist k (moi_sed_v3 (Cx r * cexp(ii * Cx th)) h) =
                  moi_sed_v3 (Cx r * cexp(ii * Cx(k * th))) h`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MOI_SED_TWIST_V3; MOI_SED_V3_EQ] THEN
  ASM_SIMP_TAC[MOI_SED_NORM_POLAR] THEN
  ASM_CASES_TAC `r = &0` THENL
   [ASM_REWRITE_TAC[COMPLEX_MUL_LZERO]; ALL_TAC] THEN
  SUBGOAL_THEN `Arg(Cx r * cexp(ii * Cx th)) = th` (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC ARG_UNIQUE THEN EXISTS_TAC `r:real` THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let MOI_SED_AX_V3 = prove
 (`!b eps z h. moi_sed_ax b eps (moi_sed_v3 z h) =
               moi_sed_v3 (cexp(ii * Cx b) * (if eps then z else cnj z)) h`,
  REWRITE_TAC[moi_sed_ax; MOI_SED_V3_CZ; MOI_SED_V3_COMPONENTS]);;

let MOI_SED_FLIP_V3 = prove
 (`!z h. moi_sed_flip (moi_sed_v3 z h) = moi_sed_v3 z (&1 - h)`,
  REWRITE_TAC[moi_sed_flip; moi_sed_v3; CART_EQ; DIMINDEX_3; FORALL_3;
              VECTOR_3]);;

let MOI_SED_ROTZ_LINEAR = prove
 (`!a. linear(moi_smo_rotz a)`,
  REWRITE_TAC[linear; moi_smo_rotz; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
              VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  REAL_ARITH_TAC);;

let MOI_SED_COMPLEX_LIN = prove
 (`!u v w z c. complex(u + w,v + z) = complex(u,v) + complex(w,z) /\
               complex(c * u,c * v) = Cx c * complex(u,v)`,
  REWRITE_TAC[COMPLEX_EQ; RE; IM; RE_ADD; IM_ADD; RE_MUL_CX; IM_MUL_CX]);;

let MOI_SED_AX_LINEAR = prove
 (`!b eps. linear(moi_sed_ax b eps)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[linear; moi_sed_ax; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
              MOI_SED_V3_ADD; MOI_SED_V3_CMUL; MOI_SED_V3_EQ;
              MOI_SED_COMPLEX_LIN] THEN
  BOOL_CASES_TAC `eps:bool` THEN REWRITE_TAC[CNJ_ADD; CNJ_MUL; CNJ_CX] THEN
  REPEAT GEN_TAC THEN CONV_TAC COMPLEX_RING);;

let MOI_SED_FLIP_AFFINE = prove
 (`?l y. linear l /\ !x. moi_sed_flip x = l x + y`,
  EXISTS_TAC `\x:real^3. vector[x$1; x$2; --(x$3)]:real^3` THEN
  EXISTS_TAC `basis 3:real^3` THEN
  SIMP_TAC[linear; moi_sed_flip; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
           VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT;
           ARITH] THEN
  REAL_ARITH_TAC);;

let MOI_SED_ROTZ_ROTZ = prove
 (`!a b y. moi_smo_rotz a (moi_smo_rotz b y) = moi_smo_rotz (a + b) y`,
  REWRITE_TAC[moi_smo_rotz; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
              COS_ADD; SIN_ADD] THEN
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THEN CONV_TAC REAL_RING);;

let MOI_SED_ROTZ_0 = prove
 (`!y. moi_smo_rotz (&0) y = y`,
  REWRITE_TAC[moi_smo_rotz; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
              COS_0; SIN_0] THEN
  REAL_ARITH_TAC);;

let MOI_SED_ROTZ_CMUL = prove
 (`!a t y. moi_smo_rotz a (t % y) = t % moi_smo_rotz a y`,
  MESON_TAC[MOI_SED_ROTZ_LINEAR; LINEAR_CMUL]);;

(* ------------------------------------------------------------------------- *)
(* 1. The dihedral angle, angular sectors and the standard tetrahedron with *)
(* vertices 0, basis 3, moi_sed_pt (angle 0) and moi_sed_qt (angle alpha).  *)
(* ------------------------------------------------------------------------- *)

let MOI_SED_ALPHA = prove
 (`cos moi_smo_dihedral = &1 / &3 /\ &0 < moi_smo_dihedral /\
   moi_smo_dihedral < pi / &2 /\ pi / &3 < moi_smo_dihedral /\
   &0 < sin moi_smo_dihedral /\ sin moi_smo_dihedral pow 2 = &8 / &9`,
  MP_TAC MOI_SMO_DIHEDRAL_COS THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC PI_POS THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < sin moi_smo_dihedral` ASSUME_TAC THENL
   [MATCH_MP_TAC SIN_POS_PI THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`moi_smo_dihedral`; `pi / &3`] COS_MONO_LT_EQ) THEN
    ASM_REWRITE_TAC[COS_PI3] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REAL_ARITH_TAC;
    MP_TAC(SPEC `moi_smo_dihedral` SIN_CIRCLE) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC]);;

let MOI_SED_RE_IM_ARG = prove
 (`!z. Re z = norm z * cos(Arg z) /\ Im z = norm z * sin(Arg z)`,
  GEN_TAC THEN
  GEN_REWRITE_TAC (BINOP_CONV o LAND_CONV o RAND_CONV)
    [last(CONJUNCTS(SPEC `z:complex` ARG))] THEN
  REWRITE_TAC[RE_MUL_CX; IM_MUL_CX; RE_CEXP; IM_CEXP; RE_MUL_II; IM_MUL_II;
              RE_CX; IM_CX; REAL_NEG_0; REAL_EXP_0; REAL_MUL_LID]);;

let MOI_SED_SECTOR_GEN = prove
 (`!al a b. &0 < al /\ al < pi /\ &0 <= a /\ &0 <= b /\ ~(a = &0 /\ b = &0)
            ==> ~(Cx a + Cx b * cexp(ii * Cx al) = Cx(&0)) /\
                Arg(Cx a + Cx b * cexp(ii * Cx al)) <= al /\
                (Arg(Cx a + Cx b * cexp(ii * Cx al)) = &0 ==> b = &0) /\
                (Arg(Cx a + Cx b * cexp(ii * Cx al)) = al ==> a = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `z = Cx a + Cx b * cexp(ii * Cx al)` THEN
  SUBGOAL_THEN `Re z = a + b * cos al /\ Im z = b * sin al`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN
    REWRITE_TAC[RE_ADD; IM_ADD; RE_CX; IM_CX; RE_MUL_CX; IM_MUL_CX; RE_CEXP;
                IM_CEXP; RE_MUL_II; IM_MUL_II; REAL_NEG_0; REAL_EXP_0;
                REAL_MUL_LID] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sin al` ASSUME_TAC THENL
   [MATCH_MP_TAC SIN_POS_PI THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(z = Cx(&0))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `Im z = b * sin al` THEN UNDISCH_TAC `Re z = a + b * cos al` THEN
    ASM_REWRITE_TAC[RE_CX; IM_CX] THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `b = &0` SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SYM) THEN REWRITE_TAC[REAL_ENTIRE] THEN
      ASM_MESON_TAC[REAL_LT_IMP_NZ];
      ALL_TAC] THEN
    ASM_MESON_TAC[REAL_MUL_LZERO; REAL_ADD_RID];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `z:complex` MOI_SED_RE_IM_ARG) THEN
  MP_TAC(SPEC `z:complex` ARG) THEN
  MP_TAC(SPEC `z:complex` ARG_LE_PI) THEN
  SUBGOAL_THEN `&0 < norm(z:complex)` MP_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_NORM_NZ]; ALL_TAC] THEN
  ABBREV_TAC `th = Arg z` THEN ABBREV_TAC `r = norm(z:complex)` THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `r * sin(al - th) = a * sin al` ASSUME_TAC THENL
   [REWRITE_TAC[SIN_SUB] THEN
    UNDISCH_TAC `Re z = r * cos th` THEN UNDISCH_TAC `Im z = r * sin th` THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `th <= pi` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LE_MUL; REAL_LT_IMP_LE]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < sin(th - al)` ASSUME_TAC THENL
     [MATCH_MP_TAC SIN_POS_PI THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `sin(al - th) = --sin(th - al)` SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM SIN_NEG] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= a * sin al` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[REAL_MUL_RNEG; REAL_ARITH `&0 <= --x <=> x <= &0`] THEN
    REWRITE_TAC[REAL_NOT_LE] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN
    UNDISCH_TAC `Im z = b * sin al` THEN ASM_REWRITE_TAC[SIN_0] THEN
    REWRITE_TAC[REAL_MUL_RZERO] THEN
    ASM_MESON_TAC[REAL_ENTIRE; REAL_LT_IMP_NZ];
    DISCH_TAC THEN
    UNDISCH_TAC `r * sin(al - th) = a * sin al` THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; SIN_0; REAL_MUL_RZERO] THEN
    ASM_MESON_TAC[REAL_ENTIRE; REAL_LT_IMP_NZ]]);;

let MOI_SED_IN_HULL4 = prove
 (`!a b c d x:real^N.
     x IN convex hull {a,b,c,d} <=>
     ?u1 u2 u3 u4. &0 <= u1 /\ &0 <= u2 /\ &0 <= u3 /\ &0 <= u4 /\
                   u1 + u2 + u3 + u4 = &1 /\
                   x = u1 % a + u2 % b + u3 % c + u4 % d`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[CONVEX_HULL_FINITE; FINITE_INSERT; FINITE_RULES] THEN
  SIMP_TAC[CONVEX_HULL_FINITE_STEP; FINITE_INSERT; FINITE_RULES] THEN
  REWRITE_TAC[REAL_ARITH `x - y = z:real <=> x = y + z`;
              VECTOR_ARITH `x - y = z:real^N <=> x = y + z`] THEN
  REWRITE_TAC[VECTOR_ADD_RID; REAL_ADD_RID] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_SED_IN_HULL3 = prove
 (`!a b c x:real^N.
     x IN convex hull {a,b,c} <=>
     ?u1 u2 u3. &0 <= u1 /\ &0 <= u2 /\ &0 <= u3 /\ u1 + u2 + u3 = &1 /\
                x = u1 % a + u2 % b + u3 % c`,
  REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_SED_V3_DOT = prove
 (`!z h z' h'. moi_sed_v3 z h dot moi_sed_v3 z' h' =
               Re z * Re z' + Im z * Im z' + h * h'`,
  REWRITE_TAC[moi_sed_v3; DOT_3; VECTOR_3]);;

let MOI_SED_SQRT3 = prove
 (`sqrt(&3) pow 2 = &3 /\ &0 < sqrt(&3)`,
  SIMP_TAC[SQRT_POW_2; REAL_POS; SQRT_POS_LT; REAL_ARITH `&0 < &3`]);;

let MOI_SED_PT_COMPONENTS = prove
 (`moi_sed_pt$1 = sqrt(&3) / &2 /\ moi_sed_pt$2 = &0 /\ moi_sed_pt$3 = &1 / &2`,
  REWRITE_TAC[moi_sed_pt; MOI_SED_V3_COMPONENTS; RE_CX; IM_CX]);;

let MOI_SED_QT_COMPONENTS = prove
 (`moi_sed_qt$1 = sqrt(&3) / &2 * cos moi_smo_dihedral /\
   moi_sed_qt$2 = sqrt(&3) / &2 * sin moi_smo_dihedral /\
   moi_sed_qt$3 = &1 / &2`,
  REWRITE_TAC[moi_sed_qt; MOI_SED_V3_COMPONENTS; RE_MUL_CX; IM_MUL_CX;
              RE_CEXP; IM_CEXP; RE_MUL_II; IM_MUL_II; RE_CX; IM_CX;
              REAL_NEG_0; REAL_EXP_0; REAL_MUL_LID]);;

let MOI_SED_STD_REG = prove
 (`moi_sba_reg (vec 0) (basis 3) moi_sed_pt moi_sed_qt`,
  REWRITE_TAC[moi_sba_reg; MOI_SBA_DIST1] THEN
  SIMP_TAC[DOT_3; VECTOR_SUB_COMPONENT; VEC_COMPONENT; BASIS_COMPONENT;
           DIMINDEX_3; ARITH; MOI_SED_PT_COMPONENTS; MOI_SED_QT_COMPONENTS] THEN
  REPEAT CONJ_TAC THEN
  MP_TAC(CONJUNCT1 MOI_SED_SQRT3) THEN
  MP_TAC(SPEC `moi_smo_dihedral` SIN_CIRCLE) THEN
  MP_TAC(CONJUNCT1 MOI_SED_ALPHA) THEN
  CONV_TAC REAL_RING);;

let MOI_SED_STD_COMB = prove
 (`!u1 u2 u3 u4.
     u1 % vec 0 + u2 % basis 3 + u3 % moi_sed_pt + u4 % moi_sed_qt =
     moi_sed_v3 (Cx(sqrt(&3) / &2) *
                 (Cx u3 + Cx u4 * cexp(ii * Cx moi_smo_dihedral)))
                (u2 + (u3 + u4) / &2)`,
  REWRITE_TAC[MOI_SED_V3_ZERO; moi_sed_pt; moi_sed_qt; MOI_SED_V3_CMUL;
              MOI_SED_V3_ADD; MOI_SED_V3_EQ] THEN
  REPEAT GEN_TAC THEN CONJ_TAC THENL
   [CONV_TAC COMPLEX_RING; REAL_ARITH_TAC]);;

let MOI_SED_REGMAP_STD = prove
 (`!a b p q:real^N.
     ~(a = b) /\ ~(a = p) /\ ~(a = q) /\ ~(b = p) /\ ~(b = q) /\ ~(p = q) /\
     ~affine_dependent {a,b,p,q}
     ==> ?A:real^N->real^3.
            moi_smo_regmap (convex hull {a,b,p,q}) A /\
            A a = vec 0 /\ A b = basis 3 /\ A p = moi_sed_pt /\
            A q = moi_sed_qt`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`{a,b,p,q}:real^N->bool`;
    `\x:real^N. if x = a then vec 0 else if x = b then basis 3
                else if x = p then moi_sed_pt else moi_sed_qt:real^3`]
   MOI_REAL_AFFINE_EXTEND_POINTS) THEN
  ASM_REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^N->real^3` (X_CHOOSE_THEN `y:real^3`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `\x:real^N. (l:real^N->real^3) x + y` THEN
  ASM_SIMP_TAC[MOI_SBA_REGMAP_4] THEN
  REWRITE_TAC[MOI_SED_STD_REG] THEN
  MAP_EVERY EXISTS_TAC [`l:real^N->real^3`; `y:real^3`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_SED_SQ_EQ = prove
 (`!x y. &0 <= x /\ &0 <= y /\ x pow 2 = y pow 2 ==> x = y`,
  MESON_TAC[REAL_POW_EQ; ARITH_RULE `~(2 = 0)`]);;

let MOI_SED_CLASSIFY_P = prove
 (`!y:real^3. dist(y,vec 0) = &1 /\ dist(y,basis 3) = &1 /\
              y$2 = &0 /\ &0 < y$1
              ==> y = moi_sed_pt`,
  GEN_TAC THEN REWRITE_TAC[MOI_SBA_DIST1] THEN
  SIMP_TAC[DOT_3; VECTOR_SUB_COMPONENT; VEC_COMPONENT; BASIS_COMPONENT;
           DIMINDEX_3; ARITH; CART_EQ; FORALL_3; MOI_SED_PT_COMPONENTS;
           REAL_SUB_RZERO] THEN
  ABBREV_TAC `y1 = (y:real^3)$1` THEN ABBREV_TAC `y2 = (y:real^3)$2` THEN
  ABBREV_TAC `y3 = (y:real^3)$3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `y3 = &1 / &2` ASSUME_TAC THENL
   [REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_eq o concl))) THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_SED_SQ_EQ THEN
  MP_TAC MOI_SED_SQRT3 THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `sqrt(&3) pow 2 = &3` THEN
  UNDISCH_TAC `y1 * y1 + y2 * y2 + y3 * y3 = &1` THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING);;

(* Push every real equation among the assumptions into the goal.          *)

let MOI_SED_REQS_TAC : tactic =
  EVERY_ASSUM (fun th -> let c = concl th in
                         if is_eq c && type_of(lhand c) = `:real`
                         then MP_TAC th else ALL_TAC);;

let MOI_SED_CLASSIFY_Q = prove
 (`!y:real^3. dist(y,vec 0) = &1 /\ dist(y,basis 3) = &1 /\
              dist(y,moi_sed_pt) = &1 /\ &0 <= y$2
              ==> y = moi_sed_qt`,
  GEN_TAC THEN REWRITE_TAC[MOI_SBA_DIST1] THEN
  SIMP_TAC[DOT_3; VECTOR_SUB_COMPONENT; VEC_COMPONENT; BASIS_COMPONENT;
           DIMINDEX_3; ARITH; CART_EQ; FORALL_3; MOI_SED_PT_COMPONENTS;
           MOI_SED_QT_COMPONENTS; REAL_SUB_RZERO] THEN
  STRIP_TAC THEN
  MP_TAC MOI_SED_SQRT3 THEN MP_TAC MOI_SED_ALPHA THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:real^3)$3 = &1 / &2` ASSUME_TAC THENL
   [MOI_SED_REQS_TAC THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3)$1 = sqrt(&3) / &2 * cos moi_smo_dihedral`
  ASSUME_TAC THENL
   [MOI_SED_REQS_TAC THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_SED_SQ_EQ THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    MOI_SED_REQS_TAC THEN CONV_TAC REAL_RING]);;

(* ------------------------------------------------------------------------- *)
(* 2. Calculus of the angular rescaling: smoothness off the closed ray of   *)
(* angle 0 (the slit), continuity on the closed upper half-space, inverse.  *)
(* ------------------------------------------------------------------------- *)

let MOI_SED_RSM_CONST = prove
 (`!s c. smooth_map_on s (lift o (\y:real^M. c))`,
  REWRITE_TAC[o_DEF; SMOOTH_MAP_ON_CONST]);;

let MOI_SED_RSM_COORD = prove
 (`!s i. open s ==> smooth_map_on s (lift o (\y:real^M. y$i))`,
  REWRITE_TAC[o_DEF; SMOOTH_MAP_ON_LIFT_COORDINATE]);;

let MOI_SED_RSM_ADD = prove
 (`!s f g. open s /\ smooth_map_on s (lift o f) /\ smooth_map_on s (lift o g)
           ==> smooth_map_on s (lift o (\y:real^M. f y + g y))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `lift o (f:real^M->real)`;
                 `lift o (g:real^M->real)`] SMOOTH_MAP_ON_LIFT_ADD) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[o_DEF; LIFT_DROP]);;

let MOI_SED_RSM_SUB = prove
 (`!s f g. open s /\ smooth_map_on s (lift o f) /\ smooth_map_on s (lift o g)
           ==> smooth_map_on s (lift o (\y:real^M. f y - g y))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `lift o (f:real^M->real)`;
                 `lift o (g:real^M->real)`] SMOOTH_MAP_ON_LIFT_SUB) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[o_DEF; LIFT_DROP]);;

let MOI_SED_RSM_MUL = prove
 (`!s f g. open s /\ smooth_map_on s (lift o f) /\ smooth_map_on s (lift o g)
           ==> smooth_map_on s (lift o (\y:real^M. f y * g y))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `lift o (f:real^M->real)`;
                 `lift o (g:real^M->real)`] SMOOTH_MAP_ON_LIFT_MUL) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[o_DEF; LIFT_DROP]);;

let MOI_SED_RSM_DIV = prove
 (`!s f g. open s /\ smooth_map_on s (lift o f) /\ smooth_map_on s (lift o g) /\
           (!y. y IN s ==> ~(g y = &0))
           ==> smooth_map_on s (lift o (\y:real^M. f y / g y))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `lift o (f:real^M->real)`;
                 `lift o (g:real^M->real)`] SMOOTH_MAP_ON_LIFT_DIV) THEN
  ASM_SIMP_TAC[o_THM; LIFT_DROP] THEN REWRITE_TAC[o_DEF; LIFT_DROP]);;

let MOI_SED_RSM_POW = prove
 (`!s f n. open s /\ smooth_map_on s (lift o f)
           ==> smooth_map_on s (lift o (\y:real^M. f y pow n))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `lift o (f:real^M->real)`; `n:num`]
    SMOOTH_MAP_ON_LIFT_POW) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[o_DEF; LIFT_DROP]);;

let MOI_SED_RSM_SQRT = prove
 (`!s f. open s /\ smooth_map_on s (lift o f) /\ (!y. y IN s ==> &0 < f y)
         ==> smooth_map_on s (lift o (\y:real^M. sqrt(f y)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `lift o (f:real^M->real)`]
    SMOOTH_MAP_ON_LIFT_SQRT) THEN
  ASM_SIMP_TAC[o_THM; LIFT_DROP] THEN REWRITE_TAC[o_DEF; LIFT_DROP]);;

let MOI_SED_RSM_COS = prove
 (`!s f. open s /\ smooth_map_on s (lift o f)
         ==> smooth_map_on s (lift o (\y:real^M. cos(f y)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `lift o (f:real^M->real)`]
    SMOOTH_MAP_ON_LIFT_COS) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[o_DEF; LIFT_DROP]);;

let MOI_SED_RSM_SIN = prove
 (`!s f. open s /\ smooth_map_on s (lift o f)
         ==> smooth_map_on s (lift o (\y:real^M. sin(f y)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `lift o (f:real^M->real)`]
    SMOOTH_MAP_ON_LIFT_SIN) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[o_DEF; LIFT_DROP]);;

let MOI_SED_SMOOTH_ATN_1D = prove
 (`smooth_map_on (:real^1) (lift o atn o drop)`,
  MATCH_MP_TAC SMOOTH_MAP_ON_REAL_DERIVATIVE_1D THEN
  EXISTS_TAC `\x. inv(&1 + x pow 2)` THEN
  REWRITE_TAC[OPEN_UNIV; IN_UNIV; HAS_REAL_DERIVATIVE_ATN] THEN
  MP_TAC(ISPECL [`(:real^1)`; `\x:real^1. lift(&1 + drop x pow 2)`]
    SMOOTH_MAP_ON_LIFT_INV) THEN
  REWRITE_TAC[OPEN_UNIV; IN_UNIV; LIFT_DROP] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`(:real^1)`; `\x:real^1. lift(&1)`;
                     `\x:real^1. lift(drop x pow 2)`] SMOOTH_MAP_ON_LIFT_ADD) THEN
      REWRITE_TAC[OPEN_UNIV; LIFT_DROP; SMOOTH_MAP_ON_CONST] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      MP_TAC(ISPECL [`(:real^1)`; `\x:real^1. x`; `2`]
        SMOOTH_MAP_ON_LIFT_POW) THEN
      REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID];
      GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> ~(&1 + x = &0)`) THEN
      REWRITE_TAC[REAL_LE_POW_2]];
    REWRITE_TAC[o_DEF]]);;

let MOI_SED_RSM_ATN = prove
 (`!s f. open s /\ smooth_map_on s (lift o f)
         ==> smooth_map_on s (lift o (\y:real^M. atn(f y)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `(:real^1)`; `lift o (f:real^M->real)`;
                 `atn`] SMOOTH_MAP_ON_LIFT_COMPOSE_1D) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV; MOI_SED_SMOOTH_ATN_1D] THEN
  REWRITE_TAC[o_DEF; LIFT_DROP]);;

let MOI_SED_RSM_VEC3 = prove
 (`!s f1 f2 f3.
     open s /\ smooth_map_on s (lift o f1) /\ smooth_map_on s (lift o f2) /\
     smooth_map_on s (lift o f3)
     ==> smooth_map_on s (\y:real^M. vector[f1 y; f2 y; f3 y]:real^3)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC I
    [MATCH_MP (ISPEC `s:real^M->bool` SMOOTH_MAP_ON_COMPONENTWISE) th]) THEN
  REWRITE_TAC[DIMINDEX_3; ARITH_RULE `1 <= k /\ k <= 3 <=> k = 1 \/ k = 2 \/ k = 3`] THEN
  GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_3] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[o_DEF]) THEN ASM_REWRITE_TAC[]);;

let MOI_SED_OPEN_SLIT = prove
 (`open moi_sed_slit`,
  SUBGOAL_THEN
   `moi_sed_slit = (:real^3) DIFF
      ({y:real^3 | y$2 <= &0} INTER {y | y$2 >= &0} INTER {y | y$1 >= &0})`
  SUBST1_TAC THENL
   [REWRITE_TAC[moi_sed_slit; EXTENSION; IN_DIFF; IN_UNIV; IN_INTER;
                IN_ELIM_THM] THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC OPEN_DIFF THEN REWRITE_TAC[OPEN_UNIV] THEN
    REPEAT(MATCH_MP_TAC CLOSED_INTER THEN CONJ_TAC) THEN
    REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_LE; CLOSED_HALFSPACE_COMPONENT_GE]]);;

let MOI_SED_SLIT_POS = prove
 (`!y:real^3. y IN moi_sed_slit
              ==> &0 < y$1 pow 2 + y$2 pow 2 /\
                  y$1 < sqrt(y$1 pow 2 + y$2 pow 2)`,
  GEN_TAC THEN REWRITE_TAC[moi_sed_slit; IN_ELIM_THM] THEN DISCH_TAC THEN
  ASM_CASES_TAC `(y:real^3)$1 < &0` THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 < a /\ &0 <= b ==> &0 < a + b`) THEN
      REWRITE_TAC[REAL_LE_POW_2; REAL_LT_POW_2] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `a < &0 /\ &0 <= b ==> a < b`) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SQRT_POS_LE THEN
      MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_LE_POW_2]];
    SUBGOAL_THEN `&0 < (y:real^3)$2 pow 2` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_LT_POW_2] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 < b ==> &0 < a + b`) THEN
      ASM_REWRITE_TAC[REAL_LE_POW_2];
      MATCH_MP_TAC REAL_LT_RSQRT THEN ASM_REAL_ARITH_TAC]]);;

let MOI_SED_ARG_SLIT = prove
 (`!z. ~(real z /\ &0 <= Re z)
       ==> Arg z = pi - &2 * atn(Im z / (norm z - Re z))`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(z = Cx(&0))` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN FIRST_X_ASSUM MP_TAC THEN
    REWRITE_TAC[REAL_CX; RE_CX; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(Arg z = &0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ARG_EQ_0]; ALL_TAC] THEN
  MP_TAC(SPEC `z:complex` ARG) THEN MP_TAC(SPEC `z:complex` MOI_SED_RE_IM_ARG) THEN
  SUBGOAL_THEN `&0 < norm(z:complex)` MP_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_NORM_NZ]; ALL_TAC] THEN
  ABBREV_TAC `th = Arg z` THEN ABBREV_TAC `r = norm(z:complex)` THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < sin(th / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SIN_POS_PI THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(r * sin th) / (r - r * cos th) = tan(pi / &2 - th / &2)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `th = &2 * (th / &2)` (fun t -> GEN_REWRITE_TAC
      (LAND_CONV o ONCE_DEPTH_CONV) [t]) THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SIN_DOUBLE; COS_DOUBLE_SIN; tan; SIN_SUB; COS_SUB; SIN_PI2;
                COS_PI2] THEN
    ABBREV_TAC `x = th / &2` THEN
    UNDISCH_TAC `&0 < sin x` THEN UNDISCH_TAC `&0 < r` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `atn(tan(pi / &2 - th / &2)) = pi / &2 - th / &2` SUBST1_TAC THENL
   [MATCH_MP_TAC TAN_ATN THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

(* Decompose a goal smooth_map_on s (lift o (\y. ...)) into elementary     *)
(* pieces; leaves the openness and positivity side conditions.              *)

let MOI_SED_RSM_TAC : tactic =
  REPEAT(FIRST [MATCH_ACCEPT_TAC MOI_SED_RSM_CONST;
                MATCH_MP_TAC MOI_SED_RSM_COORD;
                MATCH_MP_TAC MOI_SED_RSM_ADD; MATCH_MP_TAC MOI_SED_RSM_SUB;
                MATCH_MP_TAC MOI_SED_RSM_MUL; MATCH_MP_TAC MOI_SED_RSM_DIV;
                MATCH_MP_TAC MOI_SED_RSM_POW; MATCH_MP_TAC MOI_SED_RSM_SQRT;
                MATCH_MP_TAC MOI_SED_RSM_COS; MATCH_MP_TAC MOI_SED_RSM_SIN;
                MATCH_MP_TAC MOI_SED_RSM_ATN; CONJ_TAC]);;

let MOI_SED_TW_FORMULA = prove
 (`!k y. y IN moi_sed_slit
         ==> moi_smo_twist k y =
             vector[sqrt(y$1 pow 2 + y$2 pow 2) *
                    cos(k * (pi - &2 * atn(y$2 /
                        (sqrt(y$1 pow 2 + y$2 pow 2) - y$1))));
                    sqrt(y$1 pow 2 + y$2 pow 2) *
                    sin(k * (pi - &2 * atn(y$2 /
                        (sqrt(y$1 pow 2 + y$2 pow 2) - y$1))));
                    y$3]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_sed_slit; IN_ELIM_THM] THEN DISCH_TAC THEN
  REWRITE_TAC[moi_smo_twist] THEN
  SUBGOAL_THEN `Arg(complex((y:real^3)$1,y$2)) =
                pi - &2 * atn(y$2 / (sqrt(y$1 pow 2 + y$2 pow 2) - y$1))`
  SUBST1_TAC THENL
   [MP_TAC(SPEC `complex((y:real^3)$1,y$2)` MOI_SED_ARG_SLIT) THEN
    REWRITE_TAC[real; RE; IM; complex_norm] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    REWRITE_TAC[complex_norm; RE; IM]]);;

let MOI_SED_SMOOTH_TWIST = prove
 (`!k. smooth_map_on moi_sed_slit (moi_smo_twist k)`,
  GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC
   `\y:real^3. vector[sqrt(y$1 pow 2 + y$2 pow 2) *
                      cos(k * (pi - &2 * atn(y$2 /
                          (sqrt(y$1 pow 2 + y$2 pow 2) - y$1))));
                      sqrt(y$1 pow 2 + y$2 pow 2) *
                      sin(k * (pi - &2 * atn(y$2 /
                          (sqrt(y$1 pow 2 + y$2 pow 2) - y$1))));
                      y$3]:real^3` THEN
  REWRITE_TAC[MOI_SED_OPEN_SLIT] THEN CONJ_TAC THENL
   [SIMP_TAC[MOI_SED_TW_FORMULA]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_SED_RSM_VEC3 THEN REWRITE_TAC[MOI_SED_OPEN_SLIT] THEN
  MOI_SED_RSM_TAC THEN REWRITE_TAC[MOI_SED_OPEN_SLIT] THEN
  SIMP_TAC[MOI_SED_SLIT_POS; REAL_ARITH `x < y ==> ~(y - x = &0)`]);;

let MOI_SED_POLAR = prove
 (`!y:real^3. y = moi_sed_v3 (Cx(norm(complex(y$1,y$2))) *
                              cexp(ii * Cx(Arg(complex(y$1,y$2))))) (y$3)`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [MOI_SED_V3_EXPAND] THEN
  REWRITE_TAC[MOI_SED_V3_EQ] THEN MATCH_ACCEPT_TAC(last(CONJUNCTS(SPEC_ALL ARG))));;

let MOI_SED_ROTZ_POLAR = prove
 (`!a r th h. moi_smo_rotz a (moi_sed_v3 (Cx r * cexp(ii * Cx th)) h) =
              moi_sed_v3 (Cx r * cexp(ii * Cx(th + a))) h`,
  REWRITE_TAC[MOI_SED_ROTZ_V3; MOI_SED_V3_EQ; CX_ADD; COMPLEX_ADD_LDISTRIB;
              CEXP_ADD] THEN
  REPEAT GEN_TAC THEN CONV_TAC COMPLEX_RING);;

let MOI_SED_IN_SLIT_POLAR = prove
 (`!r th h. &0 < r /\ &0 < th /\ th < &2 * pi
            ==> moi_sed_v3 (Cx r * cexp(ii * Cx th)) h IN moi_sed_slit`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[moi_sed_slit; IN_ELIM_THM; MOI_SED_V3_COMPONENTS] THEN
  SUBGOAL_THEN `Arg(Cx r * cexp(ii * Cx th)) = th` MP_TAC THENL
   [MATCH_MP_TAC ARG_UNIQUE THEN EXISTS_TAC `r:real` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `Im(Cx r * cexp(ii * Cx th)) = &0 /\
                 &0 <= Re(Cx r * cexp(ii * Cx th))` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `Arg(Cx r * cexp(ii * Cx th)) = &0` (fun t -> REWRITE_TAC[t]) THENL
   [ASM_REWRITE_TAC[ARG_EQ_0; real]; ASM_REAL_ARITH_TAC]);;

let MOI_SED_TWIST_AXIS_DIST = prove
 (`!k y y0:real^3. y0$1 = &0 /\ y0$2 = &0
                   ==> dist(moi_smo_twist k y,moi_smo_twist k y0) = dist(y,y0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[dist; vector_norm] THEN AP_TERM_TAC THEN
  ASM_REWRITE_TAC[moi_smo_twist; DOT_3; VECTOR_SUB_COMPONENT; VECTOR_3] THEN
  SUBGOAL_THEN `complex(&0,&0) = Cx(&0)` SUBST1_TAC THENL
   [REWRITE_TAC[COMPLEX_EQ; RE; IM; RE_CX; IM_CX]; ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_0; REAL_MUL_LZERO; REAL_SUB_RZERO] THEN
  MP_TAC(INST [`complex((y:real^3)$1,y$2)`,`z:complex`] COMPLEX_SQNORM) THEN
  REWRITE_TAC[RE; IM] THEN
  MP_TAC(SPEC `k * Arg(complex((y:real^3)$1,y$2))` SIN_CIRCLE) THEN
  CONV_TAC REAL_RING);;

let MOI_SED_TWIST_CONT_SA = prove
 (`!k. moi_smo_twist k continuous_on
       (moi_sed_slit UNION {y:real^3 | y$1 = &0 /\ y$2 = &0})`,
  GEN_TAC THEN REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  X_GEN_TAC `y0:real^3` THEN REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN
  STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_WITHIN THENL
   [MP_TAC(ISPECL [`moi_smo_twist k`; `moi_sed_slit`]
      CONTINUOUS_ON_EQ_CONTINUOUS_AT) THEN
    REWRITE_TAC[MOI_SED_OPEN_SLIT] THEN
    MP_TAC(ISPECL [`moi_sed_slit`; `moi_smo_twist k`]
      SMOOTH_MAP_ON_CONTINUOUS_ON) THEN
    REWRITE_TAC[MOI_SED_SMOOTH_TWIST] THEN ASM_MESON_TAC[];
    REWRITE_TAC[continuous_at] THEN ASM_SIMP_TAC[MOI_SED_TWIST_AXIS_DIST] THEN
    MESON_TAC[]]);;

let MOI_SED_TWIST_ROT = prove
 (`!k y:real^3. &0 <= y$2
                ==> moi_smo_twist k y =
                    moi_smo_rotz (--(k * pi / &2))
                      (moi_smo_twist k (moi_smo_rotz (pi / &2) y))`,
  REPEAT STRIP_TAC THEN SUBST1_TAC(SPEC `y:real^3` MOI_SED_POLAR) THEN
  ABBREV_TAC `r = norm(complex((y:real^3)$1,y$2))` THEN
  ABBREV_TAC `th = Arg(complex((y:real^3)$1,y$2))` THEN
  SUBGOAL_THEN `&0 <= r /\ &0 <= th /\ th <= pi` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["r"; "th"] THEN REWRITE_TAC[NORM_POS_LE; ARG] THEN
    REWRITE_TAC[ARG_LE_PI; IM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC PI_POS THEN DISCH_TAC THEN
  ASM_SIMP_TAC[MOI_SED_ROTZ_POLAR; MOI_SED_TWIST_POLAR;
               REAL_ARITH `&0 < pi /\ th <= pi ==> th < &2 * pi`;
               REAL_ARITH `&0 < pi /\ &0 <= th /\ th <= pi
                           ==> &0 <= th + pi / &2 /\ th + pi / &2 < &2 * pi`] THEN
  REWRITE_TAC[MOI_SED_V3_EQ] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

let MOI_SED_TWIST_CONT_UHS = prove
 (`!k. moi_smo_twist k continuous_on {y:real^3 | &0 <= y$2}`,
  GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC `moi_smo_rotz (--(k * pi / &2)) o moi_smo_twist k o
              moi_smo_rotz (pi / &2)` THEN
  CONJ_TAC THENL
   [SIMP_TAC[IN_ELIM_THM; o_THM; GSYM MOI_SED_TWIST_ROT]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  SIMP_TAC[LINEAR_CONTINUOUS_ON; MOI_SED_ROTZ_LINEAR] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  SIMP_TAC[LINEAR_CONTINUOUS_ON; MOI_SED_ROTZ_LINEAR] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `moi_sed_slit UNION {y:real^3 | y$1 = &0 /\ y$2 = &0}` THEN
  REWRITE_TAC[MOI_SED_TWIST_CONT_SA] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_UNION; moi_sed_slit;
              moi_smo_rotz; VECTOR_3; COS_PI2; SIN_PI2] THEN
  REAL_ARITH_TAC);;

let MOI_SED_TWIST_INV = prove
 (`!k y:real^3. &0 < k /\ k < &2 /\ &0 <= y$2
                ==> moi_smo_twist (inv k) (moi_smo_twist k y) = y`,
  REPEAT STRIP_TAC THEN SUBST1_TAC(SPEC `y:real^3` MOI_SED_POLAR) THEN
  ABBREV_TAC `r = norm(complex((y:real^3)$1,y$2))` THEN
  ABBREV_TAC `th = Arg(complex((y:real^3)$1,y$2))` THEN
  SUBGOAL_THEN `&0 <= r /\ &0 <= th /\ th <= pi` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["r"; "th"] THEN REWRITE_TAC[NORM_POS_LE; ARG] THEN
    REWRITE_TAC[ARG_LE_PI; IM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC PI_POS THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= k * th /\ k * th < &2 * pi` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    TRANS_TAC REAL_LET_TRANS `k * pi` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_SED_TWIST_POLAR; REAL_ARITH `&0 < pi /\ th <= pi ==> th < &2 * pi`] THEN
  ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_MUL_LID]);;

let MOI_SED_TWIST_SLIT = prove
 (`!k y:real^3. &0 < k /\ k < &2 /\ &0 < y$2
                ==> moi_smo_twist k y IN moi_sed_slit`,
  REPEAT STRIP_TAC THEN SUBST1_TAC(SPEC `y:real^3` MOI_SED_POLAR) THEN
  ABBREV_TAC `r = norm(complex((y:real^3)$1,y$2))` THEN
  ABBREV_TAC `th = Arg(complex((y:real^3)$1,y$2))` THEN
  SUBGOAL_THEN `&0 < r /\ &0 < th /\ th < pi` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["r"; "th"] THEN
    REWRITE_TAC[ARG_LT_PI; IM; COMPLEX_NORM_NZ] THEN
    ASM_REWRITE_TAC[COMPLEX_EQ; RE; IM; RE_CX; IM_CX] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC PI_POS THEN DISCH_TAC THEN
  ASM_SIMP_TAC[MOI_SED_TWIST_POLAR; REAL_LT_IMP_LE;
               REAL_ARITH `&0 < pi /\ th < pi ==> th < &2 * pi`] THEN
  MATCH_MP_TAC MOI_SED_IN_SLIT_POLAR THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  TRANS_TAC REAL_LTE_TRANS `&2 * th` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 3. The cycle of tetrahedra around an edge e = convex hull {a,b}: the     *)
(* triangle S i INTER S (SUC i) = convex hull {a,b,q i}, the tetrahedron    *)
(* S i = convex hull {a,b,q (i + n - 1),q i}, periodicity, and the          *)
(* canonical regular maps a |-> 0, b |-> basis 3, q (i + n - 1) |-> pt,     *)
(* q i |-> qt.                                                              *)
(* ------------------------------------------------------------------------- *)

let moi_sed_cyc = new_definition
 `moi_sed_cyc (c:(real^N->bool)->bool) (e:real^N->bool) (n:num)
              (S:num->real^N->bool) <=>
    3 <= n /\ (!i. S(i + n) = S i) /\
    (!i j. i < n /\ j < n /\ S i = S j ==> i = j) /\
    (!i. S i IN c /\ aff_dim(S i) = &3 /\ e SUBSET S i /\
         aff_dim(S i INTER S(SUC i)) = &2) /\
    (!tet. tet IN c /\ aff_dim tet = &3 /\ e SUBSET tet ==> ?i. i < n /\ tet = S i)`;;

let moi_sed_setup = new_definition
 `moi_sed_setup (c:(real^N->bool)->bool) (e:real^N->bool) (a:real^N) (b:real^N)
                (n:num) (S:num->real^N->bool) <=>
    FINITE c /\ combinatorial_manifold 3 c /\ e IN c /\ aff_dim e = &1 /\
    ~(a = b) /\ e = convex hull {a,b} /\ moi_sed_cyc c e n S`;;

let moi_sed_vx = new_definition
 `moi_sed_vx (a:real^N) (b:real^N) (S:num->real^N->bool) (i:num) =
    @w. ~(w = a) /\ ~(w = b) /\ ~affine_dependent {a,b,w} /\
        S i INTER S (SUC i) = convex hull {a,b,w}`;;

let MOI_SED_CYC_EXISTS = prove
 (`!c e:real^N->bool.
     FINITE c /\ combinatorial_manifold 3 c /\ e IN c /\ aff_dim e = &1
     ==> ?n S. moi_sed_cyc c e n S`,
  REWRITE_TAC[moi_sed_cyc] THEN MESON_TAC[MOI_SCF_CF_EDGE]);;

let MOI_SED_SETUP_FACTS = prove
 (`!c e a b n (S:num->real^N->bool).
     moi_sed_setup c e a b n S
     ==> lf_simplicial_complex c /\ simplicial_complex c /\
         (!s. s IN c ==> aff_dim s <= &3) /\ {a} IN c /\ {b} IN c /\
         3 <= n /\ a IN e /\ b IN e /\ a extreme_point_of e /\
         b extreme_point_of e /\ convex hull {a,b} IN c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_sed_setup; moi_sed_cyc] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^N) extreme_point_of e /\ b extreme_point_of e`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; EXTREME_POINT_OF_SEGMENT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_SCF_CM_FACTS];
    ASM_MESON_TAC[MOI_SBA_DIM_LE3];
    ASM_MESON_TAC[MOI_SBA_VERTEX_IN];
    ASM_MESON_TAC[MOI_SBA_VERTEX_IN];
    ASM_MESON_TAC[extreme_point_of];
    ASM_MESON_TAC[extreme_point_of];
    ASM_MESON_TAC[]]);;

let MOI_SED_SETUP_CYC = prove
 (`!c e a b n (S:num->real^N->bool).
     moi_sed_setup c e a b n S ==> moi_sed_cyc c e n S`,
  SIMP_TAC[moi_sed_setup]);;

(* Discharge a moi_sed_setup antecedent: keep it, add its facts.          *)

let MOI_SED_SETUP_TAC : tactic =
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
                       STRIP_ASSUME_TAC(MATCH_MP MOI_SED_SETUP_FACTS th) THEN
                       STRIP_ASSUME_TAC(REWRITE_RULE[moi_sed_setup; moi_sed_cyc] th));;

let MOI_SED_S_PERIODIC = prove
 (`!c e n (S:num->real^N->bool).
     moi_sed_cyc c e n S ==> !m i. S(i + m * n) = S i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_sed_cyc] THEN STRIP_TAC THEN
  INDUCT_TAC THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
  ASM_REWRITE_TAC[ADD_ASSOC]);;

let MOI_SED_S_MOD = prove
 (`!c e n (S:num->real^N->bool).
     moi_sed_cyc c e n S ==> !i. S i = S(i MOD n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_sed_cyc; ARITH_RULE `3 <= n ==> ~(n = 0)`]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
    [CONJUNCT1(SPEC `i:num` (MATCH_MP DIVISION th))]) THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_MESON_TAC[MOI_SED_S_PERIODIC]);;

let MOI_SED_S_EQ = prove
 (`!c e n (S:num->real^N->bool).
     moi_sed_cyc c e n S ==> !i j. S i = S j <=> i MOD n = j MOD n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_sed_cyc; ARITH_RULE `3 <= n ==> ~(n = 0)`]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[MATCH_MP MOI_SED_S_MOD th]) THEN
  EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o el 2 o CONJUNCTS o GEN_REWRITE_RULE I [moi_sed_cyc]) THEN
  ASM_REWRITE_TAC[MOD_LT_EQ]);;

let MOI_SED_MOD_NE = prove
 (`!n i d. 0 < d /\ d < n ==> ~((i + d) MOD n = i MOD n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `n divides d` MP_TAC THENL
   [MATCH_MP_TAC(NUMBER_RULE `!n i d. (i + d == i) (mod n) ==> n divides d`) THEN
    EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[CONG];
    DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC]);;

let MOI_SED_S_DISTINCT = prove
 (`!c e n (S:num->real^N->bool).
     moi_sed_cyc c e n S
     ==> !i. ~(S(SUC i) = S i) /\ ~(S(i + n - 1) = S i) /\
             ~(S(i + n - 1) = S(SUC i))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MOI_SED_S_EQ th]) THEN
  SUBGOAL_THEN `3 <= n` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_sed_cyc]; ALL_TAC] THEN
  GEN_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[ADD1] THEN MATCH_MP_TAC MOI_SED_MOD_NE THEN ASM_ARITH_TAC;
    MATCH_MP_TAC MOI_SED_MOD_NE THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `i + n - 1 = SUC i + (n - 2)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MOI_SED_MOD_NE THEN ASM_ARITH_TAC]);;

let MOI_SED_TRI = prove
 (`!c e a b n (S:num->real^N->bool).
     moi_sed_setup c e a b n S
     ==> !i. (S i INTER S(SUC i)) IN c /\ aff_dim(S i INTER S(SUC i)) = &2 /\
             e SUBSET S i INTER S(SUC i) /\
             (S i INTER S(SUC i)) face_of S i /\
             (S i INTER S(SUC i)) face_of S(SUC i)`,
  REPEAT GEN_TAC THEN MOI_SED_SETUP_TAC THEN GEN_TAC THEN
  SUBGOAL_THEN `(S i INTER S(SUC i)) face_of (S:num->real^N->bool) i /\
                (S i INTER S(SUC i)) face_of S(SUC i)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `lf_simplicial_complex(c:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN
    DISCH_THEN(MATCH_MP_TAC o el 2 o CONJUNCTS) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[SUBSET_INTER] THEN
  UNDISCH_TAC `lf_simplicial_complex(c:(real^N->bool)->bool)` THEN
  REWRITE_TAC[lf_simplicial_complex] THEN
  DISCH_THEN(MATCH_MP_TAC o el 1 o CONJUNCTS) THEN
  EXISTS_TAC `(S:num->real^N->bool) i` THEN ASM_REWRITE_TAC[]);;

let MOI_SED_VX = prove
 (`!c e a b n (S:num->real^N->bool).
     moi_sed_setup c e a b n S
     ==> !i. ~(moi_sed_vx a b S i = a) /\ ~(moi_sed_vx a b S i = b) /\
             ~affine_dependent {a,b,moi_sed_vx a b S i} /\
             S i INTER S(SUC i) = convex hull {a,b,moi_sed_vx a b S i}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SED_SETUP_FACTS) THEN
  FIRST_ASSUM(MP_TAC o SPEC `i:num` o MATCH_MP MOI_SED_TRI) THEN STRIP_TAC THEN
  REWRITE_TAC[moi_sed_vx] THEN CONV_TAC SELECT_CONV THEN
  MATCH_MP_TAC MOI_SCF_TRIANGLE_ON_EDGE THEN
  EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[moi_sed_setup]);;

let MOI_SED_VX_PERIODIC = prove
 (`!c e n a b (S:num->real^N->bool).
     moi_sed_cyc c e n S ==> !i. moi_sed_vx a b S (i + n) = moi_sed_vx a b S i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_sed_vx] THEN
  SUBGOAL_THEN `(S:num->real^N->bool)(i + n) = S i /\
                S(SUC(i + n)) = S(SUC i)`
  (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[ARITH_RULE `SUC(i + n) = SUC i + n`] THEN
  ASM_MESON_TAC[moi_sed_cyc]);;

let MOI_SED_TET = prove
 (`!c e a b n (S:num->real^N->bool).
     moi_sed_setup c e a b n S
     ==> !i. ~(moi_sed_vx a b S (i + n - 1) = a) /\
             ~(moi_sed_vx a b S (i + n - 1) = b) /\
             ~(moi_sed_vx a b S i = a) /\ ~(moi_sed_vx a b S i = b) /\
             ~(moi_sed_vx a b S (i + n - 1) = moi_sed_vx a b S i) /\
             ~affine_dependent {a,b,moi_sed_vx a b S (i + n - 1),
                                moi_sed_vx a b S i} /\
             S i = convex hull {a,b,moi_sed_vx a b S (i + n - 1),
                                moi_sed_vx a b S i}`,
  REPEAT GEN_TAC THEN MOI_SED_SETUP_TAC THEN GEN_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SED_VX) THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `i:num`) THEN
  FIRST_ASSUM(MP_TAC o SPEC `i + n - 1`) THEN
  ABBREV_TAC `q' = moi_sed_vx a b (S:num->real^N->bool) (i + n - 1)` THEN
  ABBREV_TAC `q = moi_sed_vx a b (S:num->real^N->bool) i` THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `SUC(i + n - 1) = i + n` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(S:num->real^N->bool)(i + n - 1) INTER S i = convex hull {a,b,q'}`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&3 simplex (S:num->real^N->bool) i` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SBA_LF_SIMPLEX]; ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {a,b,q} face_of (S:num->real^N->bool) i /\
                convex hull {a,b,q'} face_of S i`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[lf_simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `(q':real^N) extreme_point_of (S:num->real^N->bool) i`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`convex hull {a:real^N,b,q'}`; `(S:num->real^N->bool) i`;
                   `q':real^N`] EXTREME_POINT_OF_FACE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT; IN_INSERT] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(S:num->real^N->bool) i`; `a:real^N`; `b:real^N`; `q:real^N`]
    MOI_SBA_TET_OVER_TRI) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `q' IN {a:real^N,b,q,p}` MP_TAC THENL
   [UNDISCH_TAC `(q':real^N) extreme_point_of (S:num->real^N->bool) i` THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT];
    ALL_TAC] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THENL
   [SUBGOAL_THEN `F` CONTR_TAC THEN
    MATCH_MP_TAC MOI_SBA_TRI_NOT_THREE THEN
    MAP_EVERY EXISTS_TAC
     [`c:(real^N->bool)->bool`; `convex hull {a:real^N,b,q}`;
      `(S:num->real^N->bool)(i + n - 1)`; `(S:num->real^N->bool) i`;
      `(S:num->real^N->bool)(SUC i)`] THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o MATCH_MP MOI_SED_TRI) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SED_S_DISTINCT o
      MATCH_MP MOI_SED_SETUP_CYC) THEN
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
    UNDISCH_TAC `(S:num->real^N->bool)(i + n - 1) INTER S i = convex hull {a,b,q'}` THEN
    UNDISCH_TAC `(S:num->real^N->bool) i INTER S(SUC i) = convex hull {a,b,q}` THEN
    UNDISCH_TAC `(q':real^N) = q` THEN DISCH_THEN SUBST1_TAC THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `!j. (S:num->real^N->bool) j IN c /\ aff_dim(S j) = &3`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN ASM_MESON_TAC[INTER_SUBSET];
    UNDISCH_TAC `(q':real^N) = p` THEN DISCH_THEN SUBST_ALL_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `~affine_dependent {a:real^N,b,q,p}` THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_TERM_TAC THEN SET_TAC[];
      AP_TERM_TAC THEN SET_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* 4. The triangles around e, the canonical regular maps, the formulas      *)
(* moi_sed_ff (rotation by k i alpha of the rescaled canonical chart of     *)
(* S i) and their polar form, agreement on common faces.                    *)
(* ------------------------------------------------------------------------- *)

let MOI_SED_TRI_CASES = prove
 (`!c e a b n (S:num->real^N->bool) t.
     moi_sed_setup c e a b n S /\ t IN c /\ aff_dim t = &2 /\ e SUBSET t
     ==> ?i. t = S i INTER S(SUC i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN MOI_SED_SETUP_TAC THEN
  REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`] MOI_SBA_TRI_IN_TET) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `tet:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?j. tet = (S:num->real^N->bool) j` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `a:real^N`; `b:real^N`; `t:real^N->bool`]
    MOI_SCF_TRIANGLE_ON_EDGE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o SPEC `j:num` o MATCH_MP MOI_SED_TET) THEN
  ABBREV_TAC `q' = moi_sed_vx a b (S:num->real^N->bool) (j + n - 1)` THEN
  ABBREV_TAC `q = moi_sed_vx a b (S:num->real^N->bool) j` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^N) extreme_point_of S(j:num)` MP_TAC THENL
   [MP_TAC(ISPECL [`t:real^N->bool`; `(S:num->real^N->bool) j`; `x:real^N`]
      EXTREME_POINT_OF_FACE) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC MOI_SBA_LF_SUBSET_FACE THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `p ==> (p <=> q /\ r) ==> q`) THEN
    UNDISCH_TAC `t = convex hull {a:real^N,b,x}` THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT; IN_INSERT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THENL
   [EXISTS_TAC `j + n - 1` THEN
    FIRST_ASSUM(MP_TAC o SPEC `j + n - 1` o MATCH_MP MOI_SED_VX) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    EXISTS_TAC `j:num` THEN
    FIRST_ASSUM(MP_TAC o SPEC `j:num` o MATCH_MP MOI_SED_VX) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;

let moi_sed_a0 = new_definition
 `moi_sed_a0 (a:real^N) (b:real^N) (n:num) (S:num->real^N->bool) (i:num) =
    @A:real^N->real^3. moi_smo_regmap (S i) A /\ A a = vec 0 /\ A b = basis 3 /\
       A (moi_sed_vx a b S (i + n - 1)) = moi_sed_pt /\
       A (moi_sed_vx a b S i) = moi_sed_qt`;;

let MOI_SED_A0 = prove
 (`!c e a b n (S:num->real^N->bool).
     moi_sed_setup c e a b n S
     ==> !i. moi_smo_regmap (S i) (moi_sed_a0 a b n S i) /\
             moi_sed_a0 a b n S i a = vec 0 /\
             moi_sed_a0 a b n S i b = basis 3 /\
             moi_sed_a0 a b n S i (moi_sed_vx a b S (i + n - 1)) = moi_sed_pt /\
             moi_sed_a0 a b n S i (moi_sed_vx a b S i) = moi_sed_qt`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  REWRITE_TAC[moi_sed_a0] THEN CONV_TAC SELECT_CONV THEN
  FIRST_ASSUM(MP_TAC o SPEC `i:num` o MATCH_MP MOI_SED_TET) THEN
  STRIP_TAC THEN ONCE_ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_SED_REGMAP_STD THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[moi_sed_setup]);;

let MOI_SED_A0_AFFINE = prove
 (`!c e a b n (S:num->real^N->bool).
     moi_sed_setup c e a b n S
     ==> !i. ?l y. linear l /\ !x. moi_sed_a0 a b n S i x = l x + y`,
  MESON_TAC[MOI_SED_A0; MOI_SBA_REGMAP_AFFINE]);;

let MOI_SED_A0_PERIODIC = prove
 (`!c e n a b (S:num->real^N->bool).
     moi_sed_cyc c e n S
     ==> !i. moi_sed_a0 a b n S (i + n) = moi_sed_a0 a b n S i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_sed_a0] THEN
  SUBGOAL_THEN `3 <= n` ASSUME_TAC THENL [ASM_MESON_TAC[moi_sed_cyc]; ALL_TAC] THEN
  SUBGOAL_THEN `(i + n) + n - 1 = (i + n - 1) + n` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MOI_SED_VX_PERIODIC th]) THEN
  SUBGOAL_THEN `(S:num->real^N->bool)(i + n) = S i` (fun th -> REWRITE_TAC[th]) THEN
  ASM_MESON_TAC[moi_sed_cyc]);;

let moi_sed_ff = new_definition
 `moi_sed_ff (c:(real^N->bool)->bool) (e:real^N->bool) (a:real^N) (b:real^N)
             (n:num) (S:num->real^N->bool) (i:num) (x:real^N) =
    moi_smo_rotz (moi_smo_edge_factor c e * &i * moi_smo_dihedral)
      (moi_smo_twist (moi_smo_edge_factor c e) (moi_sed_a0 a b n S i x))`;;

let moi_sed_kap = new_definition
 `moi_sed_kap (c:(real^N->bool)->bool) (e:real^N->bool) (a:real^N) (b:real^N)
              (n:num) (S:num->real^N->bool) (x:real^N) =
    moi_sed_ff c e a b n S (@i. x IN S i) x`;;

let MOI_SED_CARD = prove
 (`!c e a b n (S:num->real^N->bool).
     moi_sed_setup c e a b n S
     ==> CARD {tet | tet IN c /\ aff_dim tet = &3 /\ e SUBSET tet} = n`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MOI_SED_SETUP_CYC) THEN
  REWRITE_TAC[moi_sed_cyc] THEN STRIP_TAC THEN
  SUBGOAL_THEN `{tet | tet IN c /\ aff_dim tet = &3 /\ e SUBSET tet} =
                IMAGE (S:num->real^N->bool) {i | i < n}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN
    X_GEN_TAC `tet:real^N->bool` THEN EQ_TAC THENL
     [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `tet:real^N->bool`) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) CARD_IMAGE_INJ o lhand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; CARD_NUMSEG_LT; IN_ELIM_THM] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let MOI_SED_K = prove
 (`!c e a b n (S:num->real^N->bool).
     moi_sed_setup c e a b n S
     ==> moi_smo_edge_factor c e = &2 * pi / (&n * moi_smo_dihedral) /\
         &0 < moi_smo_edge_factor c e /\ moi_smo_edge_factor c e < &2 /\
         moi_smo_edge_factor c e * moi_smo_dihedral = &2 * pi / &n`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_SED_CARD) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SED_SETUP_FACTS) THEN
  ASM_REWRITE_TAC[moi_smo_edge_factor] THEN
  MP_TAC MOI_SED_ALPHA THEN STRIP_TAC THEN MP_TAC PI_POS THEN DISCH_TAC THEN
  SUBGOAL_THEN `&3 <= &n` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &n * moi_smo_dihedral` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `pi < &n * moi_smo_dihedral` ASSUME_TAC THENL
   [TRANS_TAC REAL_LTE_TRANS `&3 * moi_smo_dihedral` THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC(REAL_ARITH `x < &1 ==> &2 * x < &2`) THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `&0 < moi_smo_dihedral` THEN UNDISCH_TAC `&3 <= &n` THEN
    CONV_TAC REAL_FIELD]);;

let MOI_SED_ROTZ_2PI = prove
 (`!a y. moi_smo_rotz (a + &2 * pi) y = moi_smo_rotz a y`,
  REWRITE_TAC[moi_smo_rotz; SIN_PERIODIC; COS_PERIODIC]);;

let MOI_SED_FF_AT = prove
 (`!c e a b n (S:num->real^N->bool) i u1 u2 u3 u4 r th.
     moi_sed_setup c e a b n S /\
     &0 <= u1 /\ &0 <= u2 /\ &0 <= u3 /\ &0 <= u4 /\ u1 + u2 + u3 + u4 = &1 /\
     &0 <= r /\ &0 <= th /\ th < &2 * pi /\
     Cx(sqrt(&3) / &2) * (Cx u3 + Cx u4 * cexp(ii * Cx moi_smo_dihedral)) =
     Cx r * cexp(ii * Cx th)
     ==> moi_sed_ff c e a b n S i
           (u1 % a + u2 % b + u3 % moi_sed_vx a b S (i + n - 1) +
            u4 % moi_sed_vx a b S i) =
         moi_sed_v3 (Cx r * cexp(ii * Cx(moi_smo_edge_factor c e * th +
                                         moi_smo_edge_factor c e * &i *
                                         moi_smo_dihedral)))
                    (u2 + (u3 + u4) / &2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_sed_ff] THEN
  FIRST_ASSUM(MP_TAC o SPEC `i:num` o MATCH_MP MOI_SED_A0) THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `i:num` o MATCH_MP MOI_SED_A0_AFFINE) THEN DISCH_TAC THEN
  W(MP_TAC o PART_MATCH (lhs o rand) MOI_SBA_AFF_EVAL4 o
    rand o rand o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[MOI_SED_STD_COMB] THEN
  ASM_SIMP_TAC[MOI_SED_TWIST_POLAR; MOI_SED_ROTZ_POLAR]);;

let MOI_SED_FF_ON_E = prove
 (`!c e a b n (S:num->real^N->bool) i u1 u2.
     moi_sed_setup c e a b n S /\ &0 <= u1 /\ &0 <= u2 /\ u1 + u2 = &1
     ==> moi_sed_ff c e a b n S i (u1 % a + u2 % b) = moi_sed_v3 (Cx(&0)) u2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                 `b:real^N`; `n:num`; `S:num->real^N->bool`; `i:num`;
                 `u1:real`; `u2:real`; `&0`; `&0`; `&0`; `&0`] MOI_SED_FF_AT) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; REAL_ADD_RID; COMPLEX_MUL_LZERO; COMPLEX_ADD_LID;
                  COMPLEX_MUL_RZERO; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
  MP_TAC PI_POS THEN SIMP_TAC[REAL_ARITH `&0 < pi ==> &0 < &2 * pi`] THEN
  DISCH_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID]);;

let MOI_SED_FF_ON_NEXT = prove
 (`!c e a b n (S:num->real^N->bool) i u1 u2 u4.
     moi_sed_setup c e a b n S /\ &0 <= u1 /\ &0 <= u2 /\ &0 <= u4 /\
     u1 + u2 + u4 = &1
     ==> moi_sed_ff c e a b n S i (u1 % a + u2 % b + u4 % moi_sed_vx a b S i) =
         moi_sed_v3 (Cx(sqrt(&3) / &2 * u4) *
                     cexp(ii * Cx(moi_smo_edge_factor c e * moi_smo_dihedral +
                                  moi_smo_edge_factor c e * &i *
                                  moi_smo_dihedral)))
                    (u2 + u4 / &2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC MOI_SED_ALPHA THEN MP_TAC MOI_SED_SQRT3 THEN MP_TAC PI_POS THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                 `b:real^N`; `n:num`; `S:num->real^N->bool`; `i:num`;
                 `u1:real`; `u2:real`; `&0`; `u4:real`;
                 `sqrt(&3) / &2 * u4`; `moi_smo_dihedral`] MOI_SED_FF_AT) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; REAL_ADD_LID; VECTOR_MUL_LZERO; VECTOR_ADD_LID] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST [ASM_REAL_ARITH_TAC;
           MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
           REWRITE_TAC[CX_MUL; COMPLEX_ADD_LID] THEN CONV_TAC COMPLEX_RING];
    REWRITE_TAC[VECTOR_ADD_ASSOC] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_ADD_LID]]);;

let MOI_SED_FF_ON_PREV = prove
 (`!c e a b n (S:num->real^N->bool) i u1 u2 u3.
     moi_sed_setup c e a b n S /\ &0 <= u1 /\ &0 <= u2 /\ &0 <= u3 /\
     u1 + u2 + u3 = &1
     ==> moi_sed_ff c e a b n S i
           (u1 % a + u2 % b + u3 % moi_sed_vx a b S (i + n - 1)) =
         moi_sed_v3 (Cx(sqrt(&3) / &2 * u3) *
                     cexp(ii * Cx(moi_smo_edge_factor c e * &i *
                                  moi_smo_dihedral)))
                    (u2 + u3 / &2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC MOI_SED_SQRT3 THEN MP_TAC PI_POS THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                 `b:real^N`; `n:num`; `S:num->real^N->bool`; `i:num`;
                 `u1:real`; `u2:real`; `u3:real`; `&0`;
                 `sqrt(&3) / &2 * u3`; `&0`] MOI_SED_FF_AT) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; REAL_ADD_RID; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST [ASM_REAL_ARITH_TAC;
           MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
           REWRITE_TAC[CX_MUL; COMPLEX_MUL_LZERO; COMPLEX_ADD_RID;
                       COMPLEX_MUL_RZERO; CEXP_0; COMPLEX_MUL_RID]];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID]]);;

let MOI_SED_FF_ADJ = prove
 (`!c e a b n (S:num->real^N->bool).
     moi_sed_setup c e a b n S
     ==> !i x. x IN convex hull {a,b,moi_sed_vx a b S i}
               ==> moi_sed_ff c e a b n S i x = moi_sed_ff c e a b n S (SUC i) x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[MOI_SED_IN_HULL3] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real` (X_CHOOSE_THEN `u2:real`
    (X_CHOOSE_THEN `u4:real` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_SED_SETUP_CYC) THEN
  SUBGOAL_THEN `moi_sed_vx a b (S:num->real^N->bool) i =
                moi_sed_vx a b S (SUC i + n - 1)` ASSUME_TAC THENL
   [SUBGOAL_THEN `SUC i + n - 1 = i + n` SUBST1_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SED_SETUP_FACTS) THEN ARITH_TAC;
      ASM_MESON_TAC[MOI_SED_VX_PERIODIC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                 `b:real^N`; `n:num`; `S:num->real^N->bool`; `i:num`;
                 `u1:real`; `u2:real`; `u4:real`] MOI_SED_FF_ON_NEXT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (is_eq o concl)) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                 `b:real^N`; `n:num`; `S:num->real^N->bool`; `SUC i`;
                 `u1:real`; `u2:real`; `u4:real`] MOI_SED_FF_ON_PREV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MOI_SED_V3_EQ; GSYM REAL_OF_NUM_SUC] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REAL_ARITH_TAC);;

let MOI_SED_FF_PERIODIC = prove
 (`!c e a b n (S:num->real^N->bool).
     moi_sed_setup c e a b n S
     ==> !i. moi_sed_ff c e a b n S (i + n) = moi_sed_ff c e a b n S i`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_SED_SETUP_CYC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SED_K) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SED_SETUP_FACTS) THEN
  REWRITE_TAC[FUN_EQ_THM; moi_sed_ff] THEN GEN_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MOI_SED_A0_PERIODIC th]) THEN
  SUBGOAL_THEN `moi_smo_edge_factor (c:(real^N->bool)->bool) e * &(i + n) *
                moi_smo_dihedral =
                moi_smo_edge_factor c e * &i * moi_smo_dihedral + &2 * pi`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    MATCH_MP_TAC(REAL_RING `k * al = &2 * pi / m /\ m * (pi / m) = pi
                            ==> k * (i + m) * al = k * i * al + &2 * pi`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_DIV_LMUL THEN
    REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC;
    REWRITE_TAC[MOI_SED_ROTZ_2PI]]);;

let MOI_SED_FF_MOD = prove
 (`!c e a b n (S:num->real^N->bool).
     moi_sed_setup c e a b n S
     ==> !i. moi_sed_ff c e a b n S i = moi_sed_ff c e a b n S (i MOD n)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!m i. moi_sed_ff c e a b n (S:num->real^N->bool) (i + m * n) =
                      moi_sed_ff c e a b n S i`
  ASSUME_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
    ASM_SIMP_TAC[ADD_ASSOC; MOI_SED_FF_PERIODIC];
    ALL_TAC] THEN
  GEN_TAC THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SED_SETUP_FACTS) THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
    [CONJUNCT1(SPEC `i:num` (MATCH_MP DIVISION th))]) THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[]);;

let MOI_SED_FF_EQ_S = prove
 (`!c e a b n (S:num->real^N->bool).
     moi_sed_setup c e a b n S
     ==> !i j. S i = S j
               ==> moi_sed_ff c e a b n S i = moi_sed_ff c e a b n S j`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MOI_SED_S_EQ
    (MATCH_MP MOI_SED_SETUP_CYC th)]) THEN
  FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[MATCH_MP MOI_SED_FF_MOD th]) THEN
  SIMP_TAC[]);;

let MOI_SED_TRI_TETS = prove
 (`!c e a b n (S:num->real^N->bool) tet i.
     moi_sed_setup c e a b n S /\ tet IN c /\ aff_dim tet = &3 /\
     convex hull {a,b,moi_sed_vx a b S i} SUBSET tet
     ==> tet = S i \/ tet = S(SUC i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(S:num->real^N->bool) i INTER S(SUC i) =
                convex hull {a,b,moi_sed_vx a b S i}` (SUBST_ALL_TAC o SYM) THENL
   [ASM_MESON_TAC[MOI_SED_VX]; ALL_TAC] THEN
  SUBGOAL_THEN `((S:num->real^N->bool) i INTER S(SUC i)) IN c /\
                aff_dim(S i INTER S(SUC i)) = &2` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SED_TRI]; ALL_TAC] THEN
  SUBGOAL_THEN `(S:num->real^N->bool) i IN c /\ aff_dim(S i) = &3 /\
                S(SUC i) IN c /\ aff_dim(S(SUC i)) = &3 /\ ~(S(SUC i) = S i)`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_sed_cyc] o
      MATCH_MP MOI_SED_SETUP_CYC) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MOI_SED_S_DISTINCT; MOI_SED_SETUP_CYC];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p /\ ~q ==> F) ==> p \/ q`) THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_SBA_TRI_NOT_THREE THEN
  MAP_EVERY EXISTS_TAC
   [`c:(real^N->bool)->bool`; `(S:num->real^N->bool) i INTER S(SUC i)`;
    `(S:num->real^N->bool) i`; `(S:num->real^N->bool)(SUC i)`;
    `tet:real^N->bool`] THEN
  ASM_REWRITE_TAC[INTER_SUBSET] THEN
  REPEAT CONJ_TAC THEN ASM_MESON_TAC[moi_sed_setup]);;

let MOI_SED_FF_CONSIST = prove
 (`!c e a b n (S:num->real^N->bool).
     moi_sed_setup c e a b n S
     ==> !i j x. x IN S i /\ x IN S j
                 ==> moi_sed_ff c e a b n S i x = moi_sed_ff c e a b n S j x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `(S:num->real^N->bool) i = S j` THENL
   [ASM_MESON_TAC[MOI_SED_FF_EQ_S]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SED_SETUP_FACTS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_SED_SETUP_CYC) THEN
  SUBGOAL_THEN `!k. (S:num->real^N->bool) k IN c` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_sed_cyc]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `i:num` o MATCH_MP MOI_SED_TET) THEN
  FIRST_ASSUM(MP_TAC o SPEC `j:num` o MATCH_MP MOI_SED_TET) THEN
  ABBREV_TAC `qj' = moi_sed_vx a b (S:num->real^N->bool) (j + n - 1)` THEN
  ABBREV_TAC `qj = moi_sed_vx a b (S:num->real^N->bool) j` THEN
  ABBREV_TAC `qi' = moi_sed_vx a b (S:num->real^N->bool) (i + n - 1)` THEN
  ABBREV_TAC `qi = moi_sed_vx a b (S:num->real^N->bool) i` THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:real^N) IN convex hull ({a,b,qi',qi} INTER {a,b,qj',qj})`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `convex hull {a:real^N,b,qi',qi} INTER convex hull {a,b,qj',qj} =
                  convex hull ({a,b,qi',qi} INTER {a,b,qj',qj})`
    (SUBST1_TAC o SYM) THENL
     [MATCH_MP_TAC MOI_REAL_SIMPLICIAL_COMPLEX_INTER_HULL THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[];
      ASM_MESON_TAC[IN_INTER]];
    ALL_TAC] THEN
  ASM_CASES_TAC `(qi:real^N) IN {a,b,qj',qj}` THENL
   [SUBGOAL_THEN `(S:num->real^N->bool) j = S(SUC i)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                     `b:real^N`; `n:num`; `S:num->real^N->bool`;
                     `(S:num->real^N->bool) j`; `i:num`] MOI_SED_TRI_TETS) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [CONJ_TAC THENL [ASM_MESON_TAC[moi_sed_cyc]; ALL_TAC] THEN
        UNDISCH_TAC `(S:num->real^N->bool) j = convex hull {a,b,qj',qj}` THEN
        DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC HULL_MONO THEN
        UNDISCH_TAC `(qi:real^N) IN {a,b,qj',qj}` THEN SET_TAC[];
        ASM_MESON_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^N) IN convex hull {a,b,qi}` ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPEC `i:num` o MATCH_MP MOI_SED_VX) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_MESON_TAC[IN_INTER];
      ALL_TAC] THEN
    TRANS_TAC EQ_TRANS `moi_sed_ff c e a b n (S:num->real^N->bool) (SUC i) x` THEN
    CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPECL [`i:num`; `x:real^N`] o MATCH_MP MOI_SED_FF_ADJ) THEN
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[MOI_SED_FF_EQ_S]];
    ALL_TAC] THEN
  ASM_CASES_TAC `(qi':real^N) IN {a,b,qj',qj}` THENL
   [SUBGOAL_THEN `(S:num->real^N->bool) j = S(i + n - 1)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                     `b:real^N`; `n:num`; `S:num->real^N->bool`;
                     `(S:num->real^N->bool) j`; `i + n - 1`] MOI_SED_TRI_TETS) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [CONJ_TAC THENL [ASM_MESON_TAC[moi_sed_cyc]; ALL_TAC] THEN
        UNDISCH_TAC `(S:num->real^N->bool) j = convex hull {a,b,qj',qj}` THEN
        DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC HULL_MONO THEN
        UNDISCH_TAC `(qi':real^N) IN {a,b,qj',qj}` THEN SET_TAC[];
        SUBGOAL_THEN `SUC(i + n - 1) = i + n` SUBST1_TAC THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_MESON_TAC[moi_sed_cyc]];
      ALL_TAC] THEN
    SUBGOAL_THEN `SUC(i + n - 1) = i + n` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(S:num->real^N->bool)(SUC(i + n - 1)) = S i` ASSUME_TAC THENL
     [ASM_MESON_TAC[moi_sed_cyc]; ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^N) IN convex hull {a,b,qi'}` ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPEC `i + n - 1` o MATCH_MP MOI_SED_VX) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_MESON_TAC[IN_INTER];
      ALL_TAC] THEN
    TRANS_TAC EQ_TRANS
      `moi_sed_ff c e a b n (S:num->real^N->bool) (SUC(i + n - 1)) x` THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_SED_FF_EQ_S];
      FIRST_ASSUM(MP_TAC o SPECL [`i + n - 1`; `x:real^N`] o
        MATCH_MP MOI_SED_FF_ADJ) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_MESON_TAC[MOI_SED_FF_EQ_S]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN convex hull {a,b}` MP_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN convex hull ({a,b,qi',qi} INTER {a,b,qj',qj})` THEN
    MATCH_MP_TAC(SET_RULE `(s:real^N->bool) SUBSET t ==> (x:real^N) IN s ==> x IN t`) THEN
    MATCH_MP_TAC HULL_MONO THEN
    UNDISCH_TAC `~((qi:real^N) IN {a,b,qj',qj})` THEN
    UNDISCH_TAC `~((qi':real^N) IN {a,b,qj',qj})` THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CONVEX_HULL_2; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` (X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[MOI_SED_FF_ON_E]);;

let MOI_SED_KAP_FF = prove
 (`!c e a b n (S:num->real^N->bool).
     moi_sed_setup c e a b n S
     ==> !i x. x IN S i
               ==> moi_sed_kap c e a b n S x = moi_sed_ff c e a b n S i x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_sed_kap] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP MOI_SED_FF_CONSIST) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC SELECT_CONV THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 5. Injectivity of the canonical edge chart on the closed star of e, its  *)
(* membership in the edge atlas and in the star atlas at a (C4, part 1).    *)
(* ------------------------------------------------------------------------- *)

let MOI_SED_POLAR_EQ = prove
 (`!r t1 t2. &0 < r /\ Cx r * cexp(ii * Cx t1) = Cx r * cexp(ii * Cx t2)
             ==> ?m. integer m /\ t1 = t2 + &2 * m * pi`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `Cx r * cexp(ii * Cx t1) = Cx r * cexp(ii * Cx t2)` THEN
  ASM_SIMP_TAC[COMPLEX_EQ_MUL_LCANCEL; CX_INJ; REAL_LT_IMP_NZ; CEXP_EQ] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `m:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `Im`) THEN
  REWRITE_TAC[IM_ADD; IM_MUL_II; RE_CX] THEN REAL_ARITH_TAC);;

let MOI_SED_ANGLE_CASES = prove
 (`!n i j fx fy m.
     3 <= n /\ i < n /\ j < n /\ &0 <= fx /\ fx <= &1 /\ &0 <= fy /\ fy <= &1 /\
     integer m /\ fx + &i = fy + &j + m * &n
     ==> (i = j /\ fx = fy) \/
         ((j = i + 1 \/ (i = n - 1 /\ j = 0)) /\ fx = &1 /\ fy = &0) \/
         ((i = j + 1 \/ (j = n - 1 /\ i = 0)) /\ fx = &0 /\ fy = &1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&3 <= &n /\ &i + &1 <= &n /\ &j + &1 <= &n` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `m = &0 \/ m = &1 \/ m = -- &1` ASSUME_TAC THENL
   [UNDISCH_TAC `integer m` THEN REWRITE_TAC[integer] THEN
    DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
    SUBGOAL_THEN `abs(m) * &n < &2 * &n` MP_TAC THENL
     [REWRITE_TAC[GSYM REAL_ABS_NUM; GSYM REAL_ABS_MUL] THEN
      SUBGOAL_THEN `abs(&n) = &n` SUBST1_TAC THENL
       [REWRITE_TAC[REAL_ABS_NUM]; ALL_TAC] THEN
      SUBGOAL_THEN `m * &n = (fx - fy) + (&i - &j)` SUBST1_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPEC `i:num` REAL_POS) THEN MP_TAC(SPEC `j:num` REAL_POS) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_RMUL_EQ] THEN
    REWRITE_TAC[REAL_OF_NUM_LT; ARITH_RULE `k < 2 <=> k = 0 \/ k = 1`] THEN
    STRIP_TAC THEN UNDISCH_TAC `abs m = &k` THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THENL
   [SUBGOAL_THEN `&j = &i \/ &j = &i + &1 \/ &i = &j + &1` MP_TAC THENL
     [SUBGOAL_THEN `abs(&i - &j) < &2` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISJ_CASES_TAC(ARITH_RULE `i:num <= j \/ j < i`) THENL
       [UNDISCH_TAC `i:num <= j` THEN
        REWRITE_TAC[LE_EXISTS] THEN DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
        REWRITE_TAC[REAL_ARITH `abs(i - (i + d)) = abs d`; REAL_ABS_NUM] THEN
        REWRITE_TAC[REAL_OF_NUM_LT; ARITH_RULE `d < 2 <=> d = 0 \/ d = 1`] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        UNDISCH_TAC `j:num < i` THEN
        REWRITE_TAC[LT_EXISTS] THEN DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_SUC] THEN
        REWRITE_TAC[REAL_ARITH `abs((j + d + &1) - j) = abs(d + &1)`] THEN
        SIMP_TAC[REAL_ARITH `&0 <= d ==> abs(d + &1) = d + &1`; REAL_POS] THEN
        REWRITE_TAC[REAL_ARITH `d + &1 < &2 <=> d < &1`; REAL_OF_NUM_LT] THEN
        REWRITE_TAC[ARITH_RULE `d < 1 <=> d = 0`] THEN DISCH_THEN SUBST1_TAC THEN
        REAL_ARITH_TAC];
      REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THENL
       [DISJ1_TAC THEN UNDISCH_TAC `fx + &i = fy + &j + &0 * &n` THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        DISJ2_TAC THEN DISJ1_TAC THEN
        UNDISCH_TAC `fx + &i = fy + &j + &0 * &n` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN ASM_REAL_ARITH_TAC;
        DISJ2_TAC THEN DISJ2_TAC THEN
        UNDISCH_TAC `fx + &i = fy + &j + &0 * &n` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN ASM_REAL_ARITH_TAC]];
    DISJ2_TAC THEN DISJ1_TAC THEN
    SUBGOAL_THEN `&i = &n - &1 /\ &j = &0 /\ fx = &1 /\ fy = &0` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&n - &1 = &(n - 1)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[REAL_OF_NUM_SUB; ARITH_RULE `3 <= n ==> 1 <= n`]; ALL_TAC] THEN
    SIMP_TAC[REAL_OF_NUM_EQ];
    DISJ2_TAC THEN DISJ2_TAC THEN
    SUBGOAL_THEN `&j = &n - &1 /\ &i = &0 /\ fx = &0 /\ fy = &1` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&n - &1 = &(n - 1)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[REAL_OF_NUM_SUB; ARITH_RULE `3 <= n ==> 1 <= n`]; ALL_TAC] THEN
    SIMP_TAC[REAL_OF_NUM_EQ]]);;

let MOI_SED_Z_ZERO = prove
 (`!u3 u4. &0 <= u3 /\ &0 <= u4 /\
           Cx u3 + Cx u4 * cexp(ii * Cx moi_smo_dihedral) = Cx(&0)
           ==> u3 = &0 /\ u4 = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(SPECL [`moi_smo_dihedral`; `u3:real`; `u4:real`] MOI_SED_SECTOR_GEN) THEN
  ASM_REWRITE_TAC[] THEN MP_TAC MOI_SED_ALPHA THEN MP_TAC PI_POS THEN
  REAL_ARITH_TAC);;

let MOI_SED_Z_EQ = prove
 (`!u3 u4 w3 w4.
     Cx u3 + Cx u4 * cexp(ii * Cx moi_smo_dihedral) =
     Cx w3 + Cx w4 * cexp(ii * Cx moi_smo_dihedral)
     ==> u3 = w3 /\ u4 = w4`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MP_TAC(AP_TERM `Re` th) THEN MP_TAC(AP_TERM `Im` th)) THEN
  REWRITE_TAC[RE_ADD; IM_ADD; RE_CX; IM_CX; RE_MUL_CX; IM_MUL_CX; RE_CEXP;
              IM_CEXP; RE_MUL_II; IM_MUL_II; REAL_NEG_0; REAL_EXP_0;
              REAL_MUL_LID; REAL_ADD_LID] THEN
  MP_TAC MOI_SED_ALPHA THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_EQ_MUL_RCANCEL] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let MOI_SED_FF_BARY = prove
 (`!c e a b n (S:num->real^N->bool) i x.
     moi_sed_setup c e a b n S /\ x IN S i
     ==> ?u1 u2 u3 u4.
           moi_sed_ff c e a b n S i x =
           moi_sed_v3
            (Cx(sqrt(&3) / &2 *
                norm(Cx u3 + Cx u4 * cexp(ii * Cx moi_smo_dihedral))) *
             cexp(ii * Cx(moi_smo_edge_factor c e *
                          Arg(Cx u3 + Cx u4 * cexp(ii * Cx moi_smo_dihedral)) +
                          moi_smo_edge_factor c e * &i * moi_smo_dihedral)))
            (u2 + (u3 + u4) / &2) /\
           x = u1 % a + u2 % b + u3 % moi_sed_vx a b S (i + n - 1) +
               u4 % moi_sed_vx a b S i /\
           &0 <= u1 /\ &0 <= u2 /\ &0 <= u3 /\ &0 <= u4 /\
           u1 + u2 + u3 + u4 = &1 /\
           Arg(Cx u3 + Cx u4 * cexp(ii * Cx moi_smo_dihedral)) <=
           moi_smo_dihedral`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `i:num` o MATCH_MP MOI_SED_TET) THEN STRIP_TAC THEN
  UNDISCH_TAC `(x:real^N) IN S(i:num)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MOI_SED_IN_HULL4] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u1:real` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u2:real` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u3:real` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u4:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `z = Cx u3 + Cx u4 * cexp(ii * Cx moi_smo_dihedral)` THEN
  MP_TAC MOI_SED_SQRT3 THEN MP_TAC MOI_SED_ALPHA THEN MP_TAC PI_POS THEN
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC MOI_SED_FF_AT THEN ASM_REWRITE_TAC[ARG] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [last(CONJUNCTS(SPEC `z:complex` ARG))] THEN
      REWRITE_TAC[CX_MUL] THEN CONV_TAC COMPLEX_RING];
    ASM_CASES_TAC `z = Cx(&0)` THENL
     [ASM_REWRITE_TAC[ARG_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`moi_smo_dihedral`; `u3:real`; `u4:real`] MOI_SED_SECTOR_GEN) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
      UNDISCH_TAC `~(z = Cx(&0))` THEN EXPAND_TAC "z" THEN
      REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_ADD_LID];
      SIMP_TAC[]]]);;

let MOI_SED_FF_INJ = prove
 (`!c e a b n (S:num->real^N->bool) i j x y.
     moi_sed_setup c e a b n S /\ i < n /\ j < n /\ x IN S i /\ y IN S j /\
     moi_sed_ff c e a b n S i x = moi_sed_ff c e a b n S j y
     ==> x = y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o CONJUNCT2 o MATCH_MP MOI_SED_K) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SED_SETUP_FACTS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_SED_SETUP_CYC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                 `b:real^N`; `n:num`; `S:num->real^N->bool`; `i:num`; `x:real^N`]
    MOI_SED_FF_BARY) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real` (X_CHOOSE_THEN `u2:real`
   (X_CHOOSE_THEN `u3:real` (X_CHOOSE_THEN `u4:real`
    (CONJUNCTS_THEN2 (LABEL_TAC "fx") STRIP_ASSUME_TAC))))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                 `b:real^N`; `n:num`; `S:num->real^N->bool`; `j:num`; `y:real^N`]
    MOI_SED_FF_BARY) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:real` (X_CHOOSE_THEN `w2:real`
   (X_CHOOSE_THEN `w3:real` (X_CHOOSE_THEN `w4:real`
    (CONJUNCTS_THEN2 (LABEL_TAC "fy") STRIP_ASSUME_TAC))))) THEN
  UNDISCH_TAC `moi_sed_ff c e a b n S i x =
               moi_sed_ff c e a b n (S:num->real^N->bool) j y` THEN
  USE_THEN "fx" (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [th]) THEN
  USE_THEN "fy" (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
  REWRITE_TAC[MOI_SED_V3_EQ] THEN STRIP_TAC THEN
  REMOVE_THEN "fx" (K ALL_TAC) THEN REMOVE_THEN "fy" (K ALL_TAC) THEN
  ABBREV_TAC `zx = Cx u3 + Cx u4 * cexp(ii * Cx moi_smo_dihedral)` THEN
  ABBREV_TAC `zy = Cx w3 + Cx w4 * cexp(ii * Cx moi_smo_dihedral)` THEN
  ABBREV_TAC `k = moi_smo_edge_factor (c:(real^N->bool)->bool) e` THEN
  MP_TAC MOI_SED_SQRT3 THEN MP_TAC MOI_SED_ALPHA THEN MP_TAC PI_POS THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `norm(zx:complex) = norm(zy:complex)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `norm:complex->real` o check
      (fun th -> is_eq(concl th) && type_of(lhs(concl th)) = `:complex` &&
                 not(is_var(lhs(concl th))) && not(is_var(rhs(concl th))))) THEN
    SIMP_TAC[MOI_SED_NORM_POLAR; REAL_LE_MUL; NORM_POS_LE;
             REAL_ARITH `&0 < s ==> &0 <= s / &2`] THEN
    ASM_SIMP_TAC[MOI_SED_NORM_POLAR; REAL_LE_MUL; NORM_POS_LE;
                 REAL_ARITH `&0 < s ==> &0 <= s / &2`] THEN
    ASM_SIMP_TAC[REAL_EQ_MUL_LCANCEL; REAL_ARITH `&0 < s ==> ~(s / &2 = &0)`];
    ALL_TAC] THEN
  ASM_CASES_TAC `norm(zx:complex) = &0` THENL
   [SUBGOAL_THEN `u3 = &0 /\ u4 = &0` STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_SED_Z_ZERO THEN ASM_REWRITE_TAC[GSYM COMPLEX_NORM_ZERO] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `w3 = &0 /\ w4 = &0` STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_SED_Z_ZERO THEN ASM_REWRITE_TAC[GSYM COMPLEX_NORM_ZERO] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    SUBGOAL_THEN `(u2:real) = w2 /\ (u1:real) = w1` (fun th -> REWRITE_TAC[th]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?m. integer m /\
                    k * Arg zx + k * &i * moi_smo_dihedral =
                    (k * Arg zy + k * &j * moi_smo_dihedral) + &2 * m * pi`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SED_POLAR_EQ THEN
    EXISTS_TAC `sqrt(&3) / &2 * norm(zx:complex)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN
      MP_TAC(ISPEC `zx:complex` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC;
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `Arg zx / moi_smo_dihedral + &i =
                Arg zy / moi_smo_dihedral + &j + m * &n` ASSUME_TAC THENL
   [SUBGOAL_THEN `~(moi_smo_dihedral = &0) /\ ~(pi = &0) /\ ~(&n = &0)`
    MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `k * moi_smo_dihedral = &2 * pi / &n` THEN
    UNDISCH_TAC `k * Arg zx + k * &i * moi_smo_dihedral =
                 (k * Arg zy + k * &j * moi_smo_dihedral) + &2 * m * pi` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `i:num`; `j:num`; `Arg zx / moi_smo_dihedral`;
                `Arg zy / moi_smo_dihedral`; `m:real`] MOI_SED_ANGLE_CASES) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV; ARG; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ;
                 REAL_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(zx = Cx(&0)) /\ ~(zy = Cx(&0))` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPLEX_NORM_ZERO]; ALL_TAC] THEN
  SIMP_TAC[REAL_FIELD `&0 < al ==> (x / al = &1 <=> x = al)`;
           REAL_FIELD `&0 < al ==> (x / al = &0 <=> x = &0)`;
           ASSUME `&0 < moi_smo_dihedral`] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THENL
   [(* same tetrahedron *)
    SUBGOAL_THEN `Arg zx = Arg zy` ASSUME_TAC THENL
     [UNDISCH_TAC `Arg zx / moi_smo_dihedral = Arg zy / moi_smo_dihedral` THEN
      UNDISCH_TAC `&0 < moi_smo_dihedral` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    SUBGOAL_THEN `(zx:complex) = zy` MP_TAC THENL
     [ONCE_REWRITE_TAC[last(CONJUNCTS(SPEC `zx:complex` ARG))] THEN
      ONCE_REWRITE_TAC[last(CONJUNCTS(SPEC `zy:complex` ARG))] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["zx"; "zy"] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MOI_SED_Z_EQ) THEN
    UNDISCH_TAC `i:num = j` THEN DISCH_THEN SUBST_ALL_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(u2:real) = w2 /\ (u1:real) = w1` (fun th -> REWRITE_TAC[th]) THEN
    ASM_REAL_ARITH_TAC;
    (* x on the next face of S i, y on the previous face of S j *)
    MP_TAC(SPECL [`moi_smo_dihedral`; `u3:real`; `u4:real`] MOI_SED_SECTOR_GEN) THEN
    MP_TAC(SPECL [`moi_smo_dihedral`; `w3:real`; `w4:real`] MOI_SED_SECTOR_GEN) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
      UNDISCH_TAC `~(zy = Cx(&0))` THEN EXPAND_TAC "zy" THEN
      REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_ADD_LID];
      STRIP_TAC] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
      UNDISCH_TAC `~(zx = Cx(&0))` THEN EXPAND_TAC "zx" THEN
      REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_ADD_LID];
      STRIP_TAC] THEN
    SUBGOAL_THEN `u3 = &0 /\ w4 = &0` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `norm(zx:complex) = u4 /\ norm(zy:complex) = w3`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["zx"; "zy"] THEN
      REWRITE_TAC[ASSUME `u3 = &0`; ASSUME `w4 = &0`] THEN
      REWRITE_TAC[COMPLEX_ADD_LID; COMPLEX_MUL_LZERO; COMPLEX_ADD_RID] THEN
      SIMP_TAC[MOI_SED_NORM_POLAR; ASSUME `&0 <= u4`; COMPLEX_NORM_CX] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `moi_sed_vx a b (S:num->real^N->bool) (j + n - 1) =
                  moi_sed_vx a b S i` ASSUME_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (is_disj o concl)) THEN
      ASM_REWRITE_TAC[] THENL
       [SUBGOAL_THEN `(i + 1) + n - 1 = i + n` SUBST1_TAC THENL
         [ASM_ARITH_TAC; ASM_MESON_TAC[MOI_SED_VX_PERIODIC]];
        AP_TERM_TAC THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID; VECTOR_ADD_RID] THEN
    SUBGOAL_THEN `(u4:real) = w3 /\ (u2:real) = w2 /\ (u1:real) = w1` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    (* x on the previous face of S i, y on the next face of S j *)
    MP_TAC(SPECL [`moi_smo_dihedral`; `u3:real`; `u4:real`] MOI_SED_SECTOR_GEN) THEN
    MP_TAC(SPECL [`moi_smo_dihedral`; `w3:real`; `w4:real`] MOI_SED_SECTOR_GEN) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
      UNDISCH_TAC `~(zy = Cx(&0))` THEN EXPAND_TAC "zy" THEN
      REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_ADD_LID];
      STRIP_TAC] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
      UNDISCH_TAC `~(zx = Cx(&0))` THEN EXPAND_TAC "zx" THEN
      REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_ADD_LID];
      STRIP_TAC] THEN
    SUBGOAL_THEN `u4 = &0 /\ w3 = &0` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `norm(zx:complex) = u3 /\ norm(zy:complex) = w4`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["zx"; "zy"] THEN
      REWRITE_TAC[ASSUME `u4 = &0`; ASSUME `w3 = &0`] THEN
      REWRITE_TAC[COMPLEX_ADD_LID; COMPLEX_MUL_LZERO; COMPLEX_ADD_RID] THEN
      SIMP_TAC[MOI_SED_NORM_POLAR; ASSUME `&0 <= w4`; COMPLEX_NORM_CX] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `moi_sed_vx a b (S:num->real^N->bool) (i + n - 1) =
                  moi_sed_vx a b S j` ASSUME_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (is_disj o concl)) THEN
      ASM_REWRITE_TAC[] THENL
       [SUBGOAL_THEN `(j + 1) + n - 1 = j + n` SUBST1_TAC THENL
         [ASM_ARITH_TAC; ASM_MESON_TAC[MOI_SED_VX_PERIODIC]];
        AP_TERM_TAC THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID; VECTOR_ADD_RID] THEN
    SUBGOAL_THEN `(u3:real) = w4 /\ (u2:real) = w2 /\ (u1:real) = w1` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC]);;

(* Membership in the edge atlas, unpacked.                                  *)

let moi_sed_echart = new_definition
 `moi_sed_echart (c:(real^N->bool)->bool) (e:real^N->bool) (a:real^N) (b:real^N)
                 (kappa:real^N->real^3) <=>
    (!x y. x IN moi_smo_open_star c e /\ y IN moi_smo_open_star c e /\
           kappa x = kappa y ==> x = y) /\
    ~(a = b) /\ e = segment[a,b] /\
    !tet. tet IN c /\ aff_dim tet = &3 /\ e SUBSET tet
          ==> ?A th. moi_smo_regmap tet A /\ A a = vec 0 /\ A b = basis 3 /\
                     (!p. p extreme_point_of tet /\ ~(p = a) /\ ~(p = b)
                          ==> &0 <= (A p)$2) /\
                     (?p. p extreme_point_of tet /\ ~(p = a) /\ ~(p = b) /\
                          (A p)$2 = &0 /\ &0 < (A p)$1) /\
                     !x. x IN tet INTER moi_smo_open_star c e
                         ==> kappa x =
                             moi_smo_rotz (moi_smo_edge_factor c e * th)
                               (moi_smo_twist (moi_smo_edge_factor c e) (A x))`;;

let MOI_SED_EDGE_ATLAS_IN = prove
 (`!c U (kappa:real^N->real^3).
     (U,kappa) IN moi_smo_edge_atlas c <=>
     ?e a b. e IN c /\ aff_dim e = &1 /\ U = moi_smo_open_star c e /\
             moi_sed_echart c e a b kappa`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_smo_edge_atlas; IN_ELIM_THM; PAIR_EQ] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` (X_CHOOSE_THEN `k':real^N->real^3`
      (CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC)))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `a:real^N`
        (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC))))) THEN
    MAP_EVERY EXISTS_TAC [`e:real^N->bool`; `a:real^N`; `b:real^N`] THEN
    ASM_REWRITE_TAC[moi_sed_echart];
    DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` (X_CHOOSE_THEN `a:real^N`
      (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`e:real^N->bool`; `kappa:real^N->real^3`] THEN
    UNDISCH_TAC `moi_sed_echart c e a b (kappa:real^N->real^3)` THEN
    REWRITE_TAC[moi_sed_echart] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY REFL_TAC THEN
    MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

let MOI_SED_KAP_INJ = prove
 (`!c e a b n (S:num->real^N->bool) i j x y.
     moi_sed_setup c e a b n S /\ x IN S i /\ y IN S j /\
     moi_sed_kap c e a b n S x = moi_sed_kap c e a b n S y
     ==> x = y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_SED_SETUP_CYC) THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SED_SETUP_FACTS) THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_SED_FF_INJ THEN
  MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                        `b:real^N`; `n:num`; `S:num->real^N->bool`;
                        `i MOD n`; `j MOD n`] THEN
  ASM_REWRITE_TAC[MOD_LT_EQ] THEN
  SUBGOAL_THEN `(x:real^N) IN S(i MOD n) /\ (y:real^N) IN S(j MOD n)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SED_S_MOD]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[MOI_SED_KAP_FF]);;

let MOI_SED_OPEN_STAR_IN = prove
 (`!c e a b n (S:num->real^N->bool) x.
     moi_sed_setup c e a b n S /\ x IN moi_smo_open_star c e
     ==> ?i. i < n /\ x IN S i /\
             ?s. s IN c /\ e face_of s /\ x IN relative_interior s /\ s SUBSET S i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN MOI_SED_SETUP_TAC THEN
  REWRITE_TAC[moi_smo_open_star; IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `~(s:real^N->bool = {})` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_EMPTY; NOT_IN_EMPTY]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_SCF_CF_PURE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `tet:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?i. i < n /\ tet = (S:num->real^N->bool) i` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET_TRANS];
    ALL_TAC] THEN
  EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `(s:real^N->bool) SUBSET tet` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `s:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN ASM SET_TAC[];
    EXISTS_TAC `s:real^N->bool` THEN ASM_MESON_TAC[]]);;

let MOI_SED_KAP_ECHART = prove
 (`!c e a b n (S:num->real^N->bool).
     moi_sed_setup c e a b n S
     ==> moi_sed_echart c e a b (moi_sed_kap c e a b n S)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[moi_sed_echart] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                   `b:real^N`; `n:num`; `S:num->real^N->bool`; `x:real^N`]
      MOI_SED_OPEN_STAR_IN) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                   `b:real^N`; `n:num`; `S:num->real^N->bool`; `y:real^N`]
      MOI_SED_OPEN_STAR_IN) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC MOI_SED_KAP_INJ THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                          `b:real^N`; `n:num`; `S:num->real^N->bool`;
                          `i:num`; `j:num`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[moi_sed_setup]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN ASM_MESON_TAC[moi_sed_setup];
    ALL_TAC] THEN
  X_GEN_TAC `tet:real^N->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `?i. tet = (S:num->real^N->bool) i` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o last o CONJUNCTS o GEN_REWRITE_RULE I [moi_sed_cyc] o
      MATCH_MP MOI_SED_SETUP_CYC) THEN
    DISCH_THEN(MP_TAC o SPEC `tet:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  EXISTS_TAC `moi_sed_a0 a b n (S:num->real^N->bool) i` THEN
  EXISTS_TAC `&i * moi_smo_dihedral` THEN
  FIRST_ASSUM(MP_TAC o SPEC `i:num` o MATCH_MP MOI_SED_A0) THEN
  FIRST_ASSUM(MP_TAC o SPEC `i:num` o MATCH_MP MOI_SED_TET) THEN
  ABBREV_TAC `q' = moi_sed_vx a b (S:num->real^N->bool) (i + n - 1)` THEN
  ABBREV_TAC `q = moi_sed_vx a b (S:num->real^N->bool) i` THEN
  ABBREV_TAC `A = moi_sed_a0 a b n (S:num->real^N->bool) i` THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC MOI_SED_ALPHA THEN MP_TAC MOI_SED_SQRT3 THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `p:real^N` THEN
    ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[MOI_SED_PT_COMPONENTS; MOI_SED_QT_COMPONENTS; REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    EXISTS_TAC `q':real^N` THEN
    ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    REWRITE_TAC[IN_INSERT; MOI_SED_PT_COMPONENTS] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                   `b:real^N`; `n:num`; `S:num->real^N->bool`]
      MOI_SED_KAP_FF) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`i:num`; `x:real^N`]) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[moi_sed_ff]]);;

let MOI_SED_KAP_STAR = prove
 (`!c e a b n (S:num->real^N->bool).
     moi_sed_setup c e a b n S
     ==> (moi_smo_open_star c e,moi_sed_kap c e a b n S) IN
         moi_smo_star_atlas c a`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[MOI_SBA_STAR_ATLAS_IN; IN_UNION] THEN CONJ_TAC THENL
   [DISJ2_TAC THEN DISJ2_TAC THEN REWRITE_TAC[MOI_SED_EDGE_ATLAS_IN] THEN
    MAP_EVERY EXISTS_TAC [`e:real^N->bool`; `a:real^N`; `b:real^N`] THEN
    ASM_SIMP_TAC[MOI_SED_KAP_ECHART] THEN ASM_MESON_TAC[moi_sed_setup];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `t:real`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                 `b:real^N`; `n:num`; `S:num->real^N->bool`; `x:real^N`]
    MOI_SED_OPEN_STAR_IN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `s:real^N->bool`
      STRIP_ASSUME_TAC)))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SED_SETUP_FACTS) THEN
  SUBGOAL_THEN `(a:real^N) IN s` ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[moi_smo_open_star; IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `relative_interior s:real^N->bool` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_SBA_SHRINK THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MOI_SBA_LF_CONVEX];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^N) IN S(i:num) /\ a + t % (x - a) IN S i` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `convex((S:num->real^N->bool) i)` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_SBA_LF_CONVEX; moi_sed_setup; moi_sed_cyc]; ALL_TAC] THEN
    SUBGOAL_THEN `(a:real^N) IN S(i:num)` ASSUME_TAC THENL
     [ASM SET_TAC[]; ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[VECTOR_ARITH `a + t % (x - a):real^N = (&1 - t) % a + t % x`] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[CONVEX_ALT]) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                 `b:real^N`; `n:num`; `S:num->real^N->bool`] MOI_SED_KAP_FF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[moi_sed_ff] THEN
  FIRST_ASSUM(MP_TAC o SPEC `i:num` o MATCH_MP MOI_SED_A0) THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `i:num` o MATCH_MP MOI_SED_A0_AFFINE) THEN DISCH_TAC THEN
  ASM_SIMP_TAC[MOI_SBA_AFFINE_HOMOG; MOI_SMO_TWIST_HOMOG; MOI_SED_ROTZ_CMUL]);;

let MOI_SED_EDGE_PART1 = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold 3 c
     ==> !e v. e IN c /\ aff_dim e = &1 /\ v extreme_point_of e
               ==> ?kappa. (moi_smo_open_star c e,kappa) IN moi_smo_edge_atlas c /\
                           (moi_smo_open_star c e,kappa) IN moi_smo_star_atlas c v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_SCF_EDGE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MOI_SCF_CM_FACTS]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `q:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `?w:real^N. ~(v = w) /\ e = convex hull {v,w}` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(v:real^N) extreme_point_of e` THEN
    ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; EXTREME_POINT_OF_SEGMENT] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [EXISTS_TAC `q:real^N` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `p:real^N` THEN ASM_REWRITE_TAC[SEGMENT_SYM]];
    ALL_TAC] THEN
  UNDISCH_TAC `e = convex hull {p:real^N,q}` THEN DISCH_THEN(K ALL_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_SED_CYC_EXISTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_TAC `S:num->real^N->bool`)) THEN
  SUBGOAL_THEN `moi_sed_setup c e (v:real^N) w n S` ASSUME_TAC THENL
   [REWRITE_TAC[moi_sed_setup] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `moi_sed_kap c e (v:real^N) w n S` THEN CONJ_TAC THENL
   [REWRITE_TAC[MOI_SED_EDGE_ATLAS_IN] THEN
    MAP_EVERY EXISTS_TAC [`e:real^N->bool`; `v:real^N`; `w:real^N`] THEN
    ASM_SIMP_TAC[MOI_SED_KAP_ECHART];
    ASM_SIMP_TAC[MOI_SED_KAP_STAR]]);;

(* ------------------------------------------------------------------------- *)
(* 6. Every edge chart is continuous on the open star of its edge, hence    *)
(* (invariance of domain) a homeomorphism onto an open set (C4, part 2).    *)
(* ------------------------------------------------------------------------- *)

let MOI_SED_TET_UHS = prove
 (`!c tet a b (A:real^N->real^3).
     lf_simplicial_complex c /\ tet IN c /\ moi_smo_regmap tet A /\
     A a = vec 0 /\ A b = basis 3 /\
     (!p. p extreme_point_of tet /\ ~(p = a) /\ ~(p = b) ==> &0 <= (A p)$2)
     ==> !x. x IN tet ==> &0 <= (A x)$2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `tet SUBSET {x:real^N | &0 <= ((A:real^N->real^3) x)$2}` MP_TAC THENL
   [ALL_TAC; REWRITE_TAC[SUBSET; IN_ELIM_THM]] THEN
  SUBGOAL_THEN `tet = convex hull {x:real^N | x extreme_point_of tet}`
  (fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THENL
   [MATCH_MP_TAC KREIN_MILMAN_MINKOWSKI THEN
    ASM_MESON_TAC[MOI_SBA_LF_CONVEX; MOI_SBA_LF_SIMPLEX; SIMPLEX_IMP_COMPACT];
    ALL_TAC] THEN
  MATCH_MP_TAC HULL_MINIMAL THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
    ASM_CASES_TAC `p:real^N = a` THENL
     [ASM_REWRITE_TAC[VEC_COMPONENT; REAL_LE_REFL]; ALL_TAC] THEN
    ASM_CASES_TAC `p:real^N = b` THENL
     [ASM_SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH; REAL_LE_REFL]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SBA_REGMAP_AFFINE) THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^N->real^3` (X_CHOOSE_THEN `y:real^3`
    STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `{x:real^N | &0 <= ((l:real^N->real^3) x + y)$2} =
                {x | l x IN {z:real^3 | z$2 >= --(y$2)}}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; VECTOR_ADD_COMPONENT] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC CONVEX_LINEAR_PREIMAGE THEN
    ASM_REWRITE_TAC[CONVEX_HALFSPACE_COMPONENT_GE]]);;

let MOI_SED_ECHART_CONT = prove
 (`!c e a b (kappa:real^N->real^3).
     FINITE c /\ combinatorial_manifold 3 c /\ e IN c /\ aff_dim e = &1 /\
     moi_sed_echart c e a b kappa
     ==> kappa continuous_on moi_smo_open_star c e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  UNDISCH_TAC `moi_sed_echart c e a b (kappa:real^N->real^3)` THEN
  REWRITE_TAC[moi_sed_echart] THEN STRIP_TAC THEN
  UNDISCH_TAC `e = segment[a:real^N,b]` THEN DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[GSYM CONTINUOUS_MAP_EUCLIDEAN] THEN
  MATCH_MP_TAC(INST_TYPE [`:real^N->bool`,`:K`] PASTING_LEMMA_CLOSED) THEN
  MAP_EVERY EXISTS_TAC
   [`(\tet:real^N->bool. kappa:real^N->real^3)`;
    `(\tet:real^N->bool. moi_smo_open_star c e INTER tet)`;
    `{tet:real^N->bool | tet IN c /\ aff_dim tet = &3 /\ e SUBSET tet}`] THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; IN_ELIM_THM] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    X_GEN_TAC `tet:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tet:real^N->bool`]
      MOI_SBA_LF_CONVEX) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY; CONTINUOUS_MAP_EUCLIDEAN] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `tet:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `A:real^N->real^3` (X_CHOOSE_THEN `th:real`
      STRIP_ASSUME_TAC)) THEN
    MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
    EXISTS_TAC `moi_smo_rotz (moi_smo_edge_factor c (e:real^N->bool) * th) o
                moi_smo_twist (moi_smo_edge_factor c e) o (A:real^N->real^3)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[o_THM] THEN GEN_TAC THEN DISCH_TAC THEN
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `tet:real^N->bool` THEN
    CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; MOI_SED_ROTZ_LINEAR] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_SBA_AFFINE_CONTINUOUS_ON THEN
      MATCH_MP_TAC MOI_SBA_REGMAP_AFFINE THEN EXISTS_TAC `tet:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `{y:real^3 | &0 <= y$2}` THEN
    REWRITE_TAC[MOI_SED_TWIST_CONT_UHS] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    MATCH_MP_TAC MOI_SED_TET_UHS THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `a:real^N`; `b:real^N`] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o REWRITE_RULE[moi_smo_open_star; IN_UNIONS; IN_ELIM_THM]) THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    UNDISCH_TAC `r = relative_interior(s:real^N->bool)` THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    SUBGOAL_THEN `~(s:real^N->bool = {})` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `(x:real^N) IN relative_interior s` THEN
      ASM_REWRITE_TAC[RELATIVE_INTERIOR_EMPTY; NOT_IN_EMPTY];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_SCF_CF_PURE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `tet:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `tet:real^N->bool` THEN ASM_REWRITE_TAC[IN_INTER] THEN
    SUBGOAL_THEN `(e:real^N->bool) SUBSET s /\ relative_interior s SUBSET s`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[FACE_OF_IMP_SUBSET; RELATIVE_INTERIOR_SUBSET]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(s:real^N->bool) SUBSET tet` THEN
    UNDISCH_TAC `relative_interior s SUBSET (s:real^N->bool)` THEN
    UNDISCH_TAC `(x:real^N) IN relative_interior s` THEN SET_TAC[]]);;

let MOI_SED_EDGE_PART2 = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold 3 c
     ==> !U kappa. (U,kappa) IN moi_smo_edge_atlas c
                   ==> open_in (subtopology euclidean (UNIONS c)) U /\
                       open (IMAGE kappa U) /\
                       homeomorphic_map (subtopology euclidean U,
                                         subtopology euclidean (IMAGE kappa U))
                                        kappa`,
  GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[MOI_SED_EDGE_ATLAS_IN] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` (X_CHOOSE_THEN `a:real^N`
    (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (UNIONS c))
                        (moi_smo_open_star c (e:real^N->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SBA_OPEN_STAR_OPEN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `{a:real^N} IN c /\ {a} SUBSET e` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_sed_echart c e a b (kappa:real^N->real^3)` THEN
    REWRITE_TAC[moi_sed_echart] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(a:real^N) extreme_point_of e` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[EXTREME_POINT_OF_SEGMENT]; ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_SBA_VERTEX_IN];
      REWRITE_TAC[SING_SUBSET] THEN ASM_MESON_TAC[extreme_point_of]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `a:real^N`;
                 `moi_smo_open_star c (e:real^N->bool)`; `kappa:real^N->real^3`]
    MOI_SBA_IOD_FWD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_SBA_OPEN_STAR_MONO THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_SED_ECHART_CONT THEN
      MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`] THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[moi_sed_echart]];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `h':real^3->real^N`)) THEN
  ASM_REWRITE_TAC[HOMEOMORPHIC_MAP_MAPS; HOMEOMORPHIC_MAPS_EUCLIDEAN_SUBTOPOLOGY] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 7. Normal form: every edge chart of e (orientation a,b) is an axis       *)
(* isometry moi_sed_ax composed with the canonical chart moi_sed_kap.       *)
(* ------------------------------------------------------------------------- *)

let MOI_SED_AX_EQ = prove
 (`!b1 b2 eps y. cexp(ii * Cx b1) = cexp(ii * Cx b2)
                 ==> moi_sed_ax b1 eps y = moi_sed_ax b2 eps y`,
  SIMP_TAC[moi_sed_ax]);;

let MOI_SED_AX_ROTZ = prove
 (`!a y. moi_smo_rotz a y = moi_sed_ax a T y`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [MOI_SED_V3_EXPAND] THEN
  REWRITE_TAC[MOI_SED_ROTZ_V3; moi_sed_ax]);;

let MOI_SED_CEXP_INV = prove
 (`!b. cexp(ii * Cx b) * cexp(ii * Cx(--b)) = Cx(&1) /\
       cnj(cexp(ii * Cx b)) = cexp(ii * Cx(--b))`,
  GEN_TAC THEN REWRITE_TAC[GSYM CEXP_ADD; CX_NEG; CNJ_CEXP; CNJ_MUL; CNJ_II;
                           CNJ_CX] THEN
  REWRITE_TAC[COMPLEX_RING `ii * Cx b + ii * --Cx b = Cx(&0)`; CEXP_0] THEN
  AP_TERM_TAC THEN CONV_TAC COMPLEX_RING);;

let MOI_SED_AX_INV = prove
 (`!b eps. ?b'. !y. moi_sed_ax b' eps (moi_sed_ax b eps y) = y`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `eps:bool` THENL
   [EXISTS_TAC `--b`; EXISTS_TAC `b:real`] THEN
  GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [MOI_SED_V3_EXPAND] THEN
  REWRITE_TAC[moi_sed_ax; MOI_SED_V3_CZ; MOI_SED_V3_COMPONENTS; MOI_SED_V3_EQ;
              COMPLEX] THEN
  REWRITE_TAC[CNJ_MUL; CNJ_CNJ; MOI_SED_CEXP_INV] THEN
  MP_TAC(SPEC `b:real` MOI_SED_CEXP_INV) THEN REWRITE_TAC[REAL_NEG_NEG] THEN
  CONV_TAC COMPLEX_RING);;

let MOI_SED_AX_AFFINE = prove
 (`!b eps. ?l y. linear l /\ !x. moi_sed_ax b eps x = l x + y`,
  REPEAT GEN_TAC THEN MAP_EVERY EXISTS_TAC [`moi_sed_ax b eps`; `vec 0:real^3`] THEN
  REWRITE_TAC[MOI_SED_AX_LINEAR; VECTOR_ADD_RID]);;

let MOI_SED_AX_COMP = prove
 (`!a b c y. moi_smo_rotz a (moi_sed_ax b F (moi_smo_rotz c y)) =
             moi_sed_ax (a + b - c) F y`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV)
    [MOI_SED_V3_EXPAND] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [MOI_SED_V3_EXPAND] THEN
  REWRITE_TAC[MOI_SED_ROTZ_V3; moi_sed_ax; MOI_SED_V3_CZ; MOI_SED_V3_COMPONENTS;
              MOI_SED_V3_EQ; COMPLEX] THEN
  REWRITE_TAC[CNJ_MUL; CNJ_CEXP; CNJ_II; CNJ_CX] THEN
  REWRITE_TAC[CX_ADD; CX_SUB; COMPLEX_ADD_LDISTRIB; COMPLEX_SUB_LDISTRIB;
              CEXP_ADD; CEXP_SUB] THEN
  REWRITE_TAC[COMPLEX_RING `--ii * Cx c = --(ii * Cx c)`; CEXP_NEG] THEN
  SUBGOAL_THEN `~(cexp(ii * Cx c) = Cx(&0))` MP_TAC THENL
   [REWRITE_TAC[CEXP_NZ]; CONV_TAC COMPLEX_FIELD]);;

let MOI_SED_AX_COMP2 = prove
 (`!a c y. moi_smo_rotz a (moi_smo_rotz c y) = moi_sed_ax (a + c) T y`,
  REWRITE_TAC[MOI_SED_ROTZ_ROTZ; MOI_SED_AX_ROTZ]);;

let MOI_SED_AX_F_POLAR = prove
 (`!b r t h. moi_sed_ax b F (moi_sed_v3 (Cx r * cexp(ii * Cx t)) h) =
             moi_sed_v3 (Cx r * cexp(ii * Cx(b - t))) h`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[MOI_SED_AX_V3; MOI_SED_V3_EQ; CNJ_MUL; CNJ_CX; CNJ_CEXP; CNJ_II;
              CX_SUB; COMPLEX_SUB_LDISTRIB; CEXP_SUB] THEN
  REWRITE_TAC[COMPLEX_RING `--ii * Cx t = --(ii * Cx t)`; CEXP_NEG] THEN
  SUBGOAL_THEN `~(cexp(ii * Cx t) = Cx(&0))` MP_TAC THENL
   [REWRITE_TAC[CEXP_NZ]; CONV_TAC COMPLEX_FIELD]);;

let MOI_SED_TWIST_SW = prove
 (`!k r th h. &0 <= r /\ &0 <= th /\ th <= moi_smo_dihedral
              ==> moi_smo_twist k
                    (moi_sed_ax moi_smo_dihedral F
                       (moi_sed_v3 (Cx r * cexp(ii * Cx th)) h)) =
                  moi_sed_ax (k * moi_smo_dihedral) F
                    (moi_smo_twist k (moi_sed_v3 (Cx r * cexp(ii * Cx th)) h))`,
  REPEAT STRIP_TAC THEN MP_TAC MOI_SED_ALPHA THEN MP_TAC PI_POS THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `th < &2 * pi /\ &0 <= moi_smo_dihedral - th /\
                moi_smo_dihedral - th < &2 * pi` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_SED_AX_F_POLAR; MOI_SED_TWIST_POLAR] THEN
  REWRITE_TAC[MOI_SED_AX_F_POLAR; MOI_SED_V3_EQ; REAL_SUB_LDISTRIB]);;

let MOI_SED_A0_POLAR = prove
 (`!c e a b n (S:num->real^N->bool) i x.
     moi_sed_setup c e a b n S /\ x IN S i
     ==> ?r t h. &0 <= r /\ &0 <= t /\ t <= moi_smo_dihedral /\
                 moi_sed_a0 a b n S i x = moi_sed_v3 (Cx r * cexp(ii * Cx t)) h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `i:num` o MATCH_MP MOI_SED_TET) THEN STRIP_TAC THEN
  UNDISCH_TAC `(x:real^N) IN S(i:num)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MOI_SED_IN_HULL4] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real` (X_CHOOSE_THEN `u2:real`
   (X_CHOOSE_THEN `u3:real` (X_CHOOSE_THEN `u4:real` STRIP_ASSUME_TAC)))) THEN
  FIRST_ASSUM(MP_TAC o SPEC `i:num` o MATCH_MP MOI_SED_A0) THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `i:num` o MATCH_MP MOI_SED_A0_AFFINE) THEN DISCH_TAC THEN
  ASM_SIMP_TAC[MOI_SBA_AFF_EVAL4; MOI_SED_STD_COMB] THEN
  ABBREV_TAC `z = Cx u3 + Cx u4 * cexp(ii * Cx moi_smo_dihedral)` THEN
  EXISTS_TAC `sqrt(&3) / &2 * norm(z:complex)` THEN
  EXISTS_TAC `Arg z` THEN EXISTS_TAC `u2 + (u3 + u4) / &2` THEN
  MP_TAC MOI_SED_SQRT3 THEN MP_TAC MOI_SED_ALPHA THEN MP_TAC PI_POS THEN
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[ARG];
    ASM_CASES_TAC `z = Cx(&0)` THENL
     [ASM_REWRITE_TAC[ARG_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`moi_smo_dihedral`; `u3:real`; `u4:real`] MOI_SED_SECTOR_GEN) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
      UNDISCH_TAC `~(z = Cx(&0))` THEN EXPAND_TAC "z" THEN
      REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_ADD_LID];
      SIMP_TAC[]];
    REWRITE_TAC[MOI_SED_V3_EQ] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [last(CONJUNCTS(SPEC `z:complex` ARG))] THEN
    REWRITE_TAC[CX_MUL] THEN CONV_TAC COMPLEX_RING]);;

let MOI_SED_KAP_FORM = prove
 (`!c e a b n (S:num->real^N->bool) i x.
     moi_sed_setup c e a b n S /\ x IN S i
     ==> moi_smo_twist (moi_smo_edge_factor c e) (moi_sed_a0 a b n S i x) =
         moi_smo_rotz (--(moi_smo_edge_factor c e * &i * moi_smo_dihedral))
           (moi_sed_kap c e a b n S x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                 `b:real^N`; `n:num`; `S:num->real^N->bool`] MOI_SED_KAP_FF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`i:num`; `x:real^N`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[moi_sed_ff; MOI_SED_ROTZ_ROTZ; REAL_ADD_LINV; MOI_SED_ROTZ_0]);;

let MOI_SED_SW_VALUES = prove
 (`moi_sed_ax moi_smo_dihedral F (vec 0) = vec 0 /\
   moi_sed_ax moi_smo_dihedral F (basis 3) = basis 3 /\
   moi_sed_ax moi_smo_dihedral F moi_sed_pt = moi_sed_qt /\
   moi_sed_ax moi_smo_dihedral F moi_sed_qt = moi_sed_pt`,
  REPEAT CONJ_TAC THENL
   [MESON_TAC[MOI_SED_AX_LINEAR; LINEAR_0];
    REWRITE_TAC[MOI_SED_V3_ZERO; MOI_SED_AX_V3; CNJ_CX; COMPLEX_MUL_RZERO];
    SUBGOAL_THEN `moi_sed_pt = moi_sed_v3 (Cx(sqrt(&3) / &2) * cexp(ii * Cx(&0)))
                                          (&1 / &2)` SUBST1_TAC THENL
     [REWRITE_TAC[moi_sed_pt; COMPLEX_MUL_RZERO; CEXP_0; COMPLEX_MUL_RID];
      REWRITE_TAC[MOI_SED_AX_F_POLAR; REAL_SUB_RZERO; moi_sed_qt]];
    REWRITE_TAC[moi_sed_qt; MOI_SED_AX_F_POLAR; REAL_SUB_REFL; moi_sed_pt;
                COMPLEX_MUL_RZERO; CEXP_0; COMPLEX_MUL_RID]]);;

let MOI_SED_REG_VALUES = prove
 (`!tet a b q' q (A:real^N->real^3).
     ~(a = b) /\ ~(a = q') /\ ~(a = q) /\ ~(b = q') /\ ~(b = q) /\ ~(q' = q) /\
     ~affine_dependent {a,b,q',q} /\ tet = convex hull {a,b,q',q} /\
     moi_smo_regmap tet A /\ A a = vec 0 /\ A b = basis 3 /\
     (!p. p extreme_point_of tet /\ ~(p = a) /\ ~(p = b)
          ==> &0 <= (A p)$2) /\
     (?p. p extreme_point_of tet /\ ~(p = a) /\ ~(p = b) /\
          (A p)$2 = &0 /\ &0 < (A p)$1)
     ==> (A q' = moi_sed_pt /\ A q = moi_sed_qt) \/
         (A q' = moi_sed_qt /\ A q = moi_sed_pt)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPLICATE_TAC 7 DISCH_TAC THEN
  DISCH_THEN SUBST1_TAC THEN REPLICATE_TAC 3 DISCH_TAC THEN
  DISCH_THEN(LABEL_TAC "nonneg") THEN DISCH_THEN(LABEL_TAC "special") THEN
  SUBGOAL_THEN `!p:real^N. p extreme_point_of convex hull {a,b,q',q} <=>
                           p = a \/ p = b \/ p = q' \/ p = q`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u v. (u = a \/ u = b \/ u = q' \/ u = q) /\
                      (v = a \/ v = b \/ v = q' \/ v = q) /\ ~(u = v)
                      ==> dist((A:real^N->real^3) u,A v) = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_smo_regmap (convex hull {a,b,q',q}) (A:real^N->real^3)` THEN
    ASM_REWRITE_TAC[moi_smo_regmap] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= ((A:real^N->real^3) q)$2 /\ &0 <= (A q')$2`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "nonneg" MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "special" MP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N` (CONJUNCTS_THEN2 ASSUME_TAC
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `p:real^N = q' \/ p = q` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THENL
   [DISJ1_TAC THEN
    SUBGOAL_THEN `(A:real^N->real^3) q' = moi_sed_pt` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_SED_CLASSIFY_P THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_SED_CLASSIFY_Q THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    DISJ2_TAC THEN
    SUBGOAL_THEN `(A:real^N->real^3) q = moi_sed_pt` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_SED_CLASSIFY_P THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_SED_CLASSIFY_Q THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

let MOI_SED_NF_TET = prove
 (`!c e a b n (S:num->real^N->bool) (kappa:real^N->real^3).
     moi_sed_setup c e a b n S /\ moi_sed_echart c e a b kappa
     ==> !i. ?beta eps.
               !x. x IN S i /\ x IN moi_smo_open_star c e
                   ==> kappa x = moi_sed_ax beta eps (moi_sed_kap c e a b n S x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  SUBGOAL_THEN `(S:num->real^N->bool) i IN c /\ aff_dim(S i) = &3 /\ e SUBSET S i`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
      REWRITE_RULE[moi_sed_cyc] o MATCH_MP MOI_SED_SETUP_CYC) THEN SIMP_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_sed_echart c e a b (kappa:real^N->real^3)` THEN
  REWRITE_TAC[moi_sed_echart] THEN
  DISCH_THEN(MP_TAC o SPEC `(S:num->real^N->bool) i` o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real^N->real^3` (X_CHOOSE_THEN `th:real`
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "nonneg")
     (CONJUNCTS_THEN2 (LABEL_TAC "special") (LABEL_TAC "formula")))))))) THEN
  FIRST_ASSUM(MP_TAC o SPEC `i:num` o MATCH_MP MOI_SED_TET) THEN
  FIRST_ASSUM(MP_TAC o SPEC `i:num` o MATCH_MP MOI_SED_A0) THEN
  FIRST_ASSUM(ASSUME_TAC o SPEC `i:num` o MATCH_MP MOI_SED_A0_AFFINE) THEN
  ABBREV_TAC `q' = moi_sed_vx a b (S:num->real^N->bool) (i + n - 1)` THEN
  ABBREV_TAC `q = moi_sed_vx a b (S:num->real^N->bool) i` THEN
  ABBREV_TAC `A0 = moi_sed_a0 a b n (S:num->real^N->bool) i` THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?l y. linear l /\ !x. (A:real^N->real^3) x = l x + y`
  ASSUME_TAC THENL [ASM_MESON_TAC[MOI_SBA_REGMAP_AFFINE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(S:num->real^N->bool) i`; `a:real^N`; `b:real^N`; `q':real^N`;
                 `q:real^N`; `A:real^N->real^3`] MOI_SED_REG_VALUES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[moi_sed_setup]; ALL_TAC] THEN
  ABBREV_TAC `k = moi_smo_edge_factor c (e:real^N->bool)` THEN
  DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
   [SUBGOAL_THEN `!x. x IN S(i:num) ==> (A:real^N->real^3) x = A0 x`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SBA_AFF_EQ_HULL4 THEN
      MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`; `q':real^N`; `q:real^N`] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `k * th + --(k * &i * moi_smo_dihedral)` THEN EXISTS_TAC `T` THEN
    X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    USE_THEN "formula" (MP_TAC o SPEC `x:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[IN_INTER]; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                   `b:real^N`; `n:num`; `S:num->real^N->bool`; `i:num`; `x:real^N`]
      MOI_SED_KAP_FORM) THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[MOI_SED_AX_COMP2];
    SUBGOAL_THEN `!x. x IN S(i:num)
                      ==> (A:real^N->real^3) x = moi_sed_ax moi_smo_dihedral F (A0 x)`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `?l y. linear l /\
                          !x. moi_sed_ax moi_smo_dihedral F ((A0:real^N->real^3) x) =
                              l x + y` ASSUME_TAC THENL
       [MATCH_MP_TAC MOI_SBA_AFFINE_COMPOSE THEN
        ASM_REWRITE_TAC[MOI_SED_AX_AFFINE];
        ALL_TAC] THEN
      SUBGOAL_THEN `(x:real^N) IN convex hull {a,b,q',q}` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`A:real^N->real^3`;
                     `moi_sed_ax moi_smo_dihedral F o (A0:real^N->real^3)`;
                     `a:real^N`; `b:real^N`; `q':real^N`; `q:real^N`; `x:real^N`]
        MOI_SBA_AFF_EQ_HULL4) THEN
      REWRITE_TAC[o_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[MOI_SED_SW_VALUES];
      ALL_TAC] THEN
    EXISTS_TAC `k * th + k * moi_smo_dihedral - --(k * &i * moi_smo_dihedral)` THEN
    EXISTS_TAC `F` THEN
    X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    USE_THEN "formula" (MP_TAC o SPEC `x:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[IN_INTER]; DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                   `b:real^N`; `n:num`; `S:num->real^N->bool`; `i:num`; `x:real^N`]
      MOI_SED_A0_POLAR) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `t:real`
      (X_CHOOSE_THEN `h:real` STRIP_ASSUME_TAC))) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                   `b:real^N`; `n:num`; `S:num->real^N->bool`; `i:num`; `x:real^N`]
      MOI_SED_KAP_FORM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[MOI_SED_TWIST_SW] THEN
    REWRITE_TAC[MOI_SED_AX_COMP]]);;

let MOI_SED_HALF_ANGLE = prove
 (`!al. Cx(&1 / &4) + Cx(&1 / &4) * cexp(ii * Cx al) =
        Cx(cos(al / &2) / &2) * cexp(ii * Cx(al / &2))`,
  GEN_TAC THEN REWRITE_TAC[COMPLEX_EQ] THEN
  REWRITE_TAC[RE_ADD; IM_ADD; RE_CX; IM_CX; RE_MUL_CX; IM_MUL_CX; RE_CEXP;
              IM_CEXP; RE_MUL_II; IM_MUL_II; REAL_NEG_0; REAL_EXP_0;
              REAL_MUL_LID] THEN
  SUBGOAL_THEN `al = &2 * (al / &2)` (fun th -> GEN_REWRITE_TAC
    (BINOP_CONV o LAND_CONV o ONCE_DEPTH_CONV) [th]) THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[COS_DOUBLE_COS; SIN_DOUBLE] THEN CONV_TAC REAL_RING);;

let MOI_SED_RELINT_IN_STAR = prove
 (`!c e s x:real^N.
     lf_simplicial_complex c /\ s IN c /\ e IN c /\ e SUBSET s /\
     x IN relative_interior s
     ==> x IN moi_smo_open_star c e`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_smo_open_star; IN_UNIONS; IN_ELIM_THM] THEN
  EXISTS_TAC `relative_interior s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_SBA_LF_SUBSET_FACE THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
  ASM_REWRITE_TAC[]);;

let MOI_SED_CENTROIDS = prove
 (`!c e a b n (S:num->real^N->bool) i.
     moi_sed_setup c e a b n S
     ==> ?x0 c1 c2 r0 rho h0.
           &0 < r0 /\ &0 < rho /\
           x0 IN S i /\ x0 IN S(SUC i) /\ x0 IN moi_smo_open_star c e /\
           c1 IN S i /\ c1 IN moi_smo_open_star c e /\
           c2 IN S(SUC i) /\ c2 IN moi_smo_open_star c e /\ ~(c1 = c2) /\
           moi_sed_kap c e a b n S x0 =
           moi_sed_v3 (Cx r0 * cexp(ii * Cx(moi_smo_edge_factor c e * moi_smo_dihedral +
                                            moi_smo_edge_factor c e * &i *
                                            moi_smo_dihedral))) h0 /\
           moi_sed_kap c e a b n S c1 =
           moi_sed_v3 (Cx rho * cexp(ii * Cx(moi_smo_edge_factor c e *
                                             moi_smo_dihedral / &2 +
                                             moi_smo_edge_factor c e * &i *
                                             moi_smo_dihedral))) (&1 / &2) /\
           moi_sed_kap c e a b n S c2 =
           moi_sed_v3 (Cx rho * cexp(ii * Cx(moi_smo_edge_factor c e *
                                             moi_smo_dihedral / &2 +
                                             moi_smo_edge_factor c e * &(SUC i) *
                                             moi_smo_dihedral))) (&1 / &2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SED_SETUP_FACTS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_SED_SETUP_CYC) THEN
  SUBGOAL_THEN `moi_sed_vx a b (S:num->real^N->bool) (SUC i + n - 1) =
                moi_sed_vx a b S i` ASSUME_TAC THENL
   [SUBGOAL_THEN `SUC i + n - 1 = i + n` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ASM_MESON_TAC[MOI_SED_VX_PERIODIC]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `SUC i` o MATCH_MP MOI_SED_TET) THEN
  FIRST_ASSUM(MP_TAC o SPEC `i:num` o MATCH_MP MOI_SED_TET) THEN
  FIRST_ASSUM(MP_TAC o SPEC `i:num` o MATCH_MP MOI_SED_VX) THEN
  FIRST_ASSUM(MP_TAC o SPEC `i:num` o MATCH_MP MOI_SED_TRI) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `q' = moi_sed_vx a b (S:num->real^N->bool) (i + n - 1)` THEN
  ABBREV_TAC `q = moi_sed_vx a b (S:num->real^N->bool) i` THEN
  ABBREV_TAC `q'' = moi_sed_vx a b (S:num->real^N->bool) (SUC i)` THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    try lhs(concl th) = `(S:num->real^N->bool) i INTER S(SUC i)`
    with Failure _ -> false)) THEN
  SUBGOAL_THEN `!j. (S:num->real^N->bool) j IN c /\ e SUBSET S j` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_sed_cyc]; ALL_TAC] THEN
  MP_TAC MOI_SED_SQRT3 THEN MP_TAC MOI_SED_ALPHA THEN MP_TAC PI_POS THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(a:real^N = q) /\ ~(b:real^N = q) /\ ~(a:real^N = q') /\
                ~(b:real^N = q') /\ ~(a:real^N = q'') /\ ~(b:real^N = q'') /\
                ~(a:real^N = b) /\ (e:real^N->bool) IN c`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[moi_sed_setup]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < cos(moi_smo_dihedral / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC COS_POS_PI2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!s x:real^N. x IN relative_interior s ==> x IN s` ASSUME_TAC THENL
   [MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(inv(&4) % a + inv(&4) % b + inv(&4) % q' + inv(&4) % (q:real^N)) IN
    relative_interior(S(i:num)) /\
    (inv(&4) % a + inv(&4) % b + inv(&4) % q + inv(&4) % (q'':real^N)) IN
    relative_interior(S(SUC i)) /\
    (inv(&3) % a + inv(&3) % b + inv(&3) % (q:real^N)) IN
    relative_interior(convex hull {a,b,q})`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[MOI_SBA_RELINT_4; MOI_SBA_RELINT_3] THEN
    REPEAT CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`inv(&4)`; `inv(&4)`; `inv(&4)`; `inv(&4)`];
      MAP_EVERY EXISTS_TAC [`inv(&4)`; `inv(&4)`; `inv(&4)`; `inv(&4)`];
      MAP_EVERY EXISTS_TAC [`inv(&3)`; `inv(&3)`; `inv(&3)`]] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `(inv(&3) % a + inv(&3) % b + inv(&3) % (q:real^N)) IN S(i:num) /\
                (inv(&3) % a + inv(&3) % b + inv(&3) % (q:real^N)) IN S(SUC i)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MOI_SED_IN_HULL4] THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`inv(&3)`; `inv(&3)`; `&0`; `inv(&3)`];
      MAP_EVERY EXISTS_TAC [`inv(&3)`; `inv(&3)`; `inv(&3)`; `&0`]] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `x0 = inv(&3) % a + inv(&3) % b + inv(&3) % (q:real^N)` THEN
  ABBREV_TAC `c1 = inv(&4) % a + inv(&4) % b + inv(&4) % q' + inv(&4) % (q:real^N)` THEN
  ABBREV_TAC `c2 = inv(&4) % a + inv(&4) % b + inv(&4) % q + inv(&4) % (q'':real^N)` THEN
  SUBGOAL_THEN `(c1:real^N) IN S(i:num) /\ (c2:real^N) IN S(SUC i)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y j. y IN S j ==> moi_sed_kap c e a b n S (y:real^N) =
                                   moi_sed_ff c e a b n S j y` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MOI_SED_KAP_FF th]); ALL_TAC] THEN
  SUBGOAL_THEN `moi_sed_kap c e a b n S (x0:real^N) = moi_sed_ff c e a b n S i x0 /\
                moi_sed_kap c e a b n S (c1:real^N) = moi_sed_ff c e a b n S i c1 /\
                moi_sed_kap c e a b n S (c2:real^N) =
                moi_sed_ff c e a b n S (SUC i) c2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `x0:real^N` THEN EXISTS_TAC `c1:real^N` THEN EXISTS_TAC `c2:real^N` THEN
  EXISTS_TAC `sqrt(&3) / &2 * inv(&3)` THEN
  EXISTS_TAC `sqrt(&3) / &2 * cos(moi_smo_dihedral / &2) / &2` THEN
  EXISTS_TAC `inv(&3) + inv(&3) / &2` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_SED_RELINT_IN_STAR THEN
    EXISTS_TAC `convex hull {a:real^N,b,q}` THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_SED_RELINT_IN_STAR THEN
    EXISTS_TAC `(S:num->real^N->bool) i` THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_SED_RELINT_IN_STAR THEN
    EXISTS_TAC `(S:num->real^N->bool) (SUC i)` THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `(S:num->real^N->bool) i`;
                   `(S:num->real^N->bool) (SUC i)`] MOI_SBA_RELINT_EQ) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o MATCH_MP MOI_SED_S_DISTINCT) THEN
    REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "x0" THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                   `b:real^N`; `n:num`; `S:num->real^N->bool`; `i:num`;
                   `inv(&3)`; `inv(&3)`; `inv(&3)`] MOI_SED_FF_ON_NEXT) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV; SIMP_TAC[]];
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "c1" THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                   `b:real^N`; `n:num`; `S:num->real^N->bool`; `i:num`;
                   `inv(&4)`; `inv(&4)`; `inv(&4)`; `inv(&4)`;
                   `sqrt(&3) / &2 * cos(moi_smo_dihedral / &2) / &2`;
                   `moi_smo_dihedral / &2`] MOI_SED_FF_AT) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
        MP_TAC(SPEC `moi_smo_dihedral` MOI_SED_HALF_ANGLE) THEN
        REWRITE_TAC[REAL_ARITH `inv(&4) = &1 / &4`; CX_MUL] THEN
        CONV_TAC COMPLEX_RING];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MOI_SED_V3_EQ] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV];
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "c2" THEN
    UNDISCH_TAC `moi_sed_vx a b (S:num->real^N->bool) (SUC i + n - 1) = q` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                   `b:real^N`; `n:num`; `S:num->real^N->bool`; `SUC i`;
                   `inv(&4)`; `inv(&4)`; `inv(&4)`; `inv(&4)`;
                   `sqrt(&3) / &2 * cos(moi_smo_dihedral / &2) / &2`;
                   `moi_smo_dihedral / &2`] MOI_SED_FF_AT) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
        MP_TAC(SPEC `moi_smo_dihedral` MOI_SED_HALF_ANGLE) THEN
        REWRITE_TAC[REAL_ARITH `inv(&4) = &1 / &4`; CX_MUL] THEN
        CONV_TAC COMPLEX_RING];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MOI_SED_V3_EQ] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV]]);;

let MOI_SED_CNJ_POLAR = prove
 (`!r t. cnj(Cx r * cexp(ii * Cx t)) = Cx r * inv(cexp(ii * Cx t))`,
  REWRITE_TAC[CNJ_MUL; CNJ_CX; CNJ_CEXP; CNJ_II] THEN
  REWRITE_TAC[COMPLEX_RING `--ii * Cx t = --(ii * Cx t)`; CEXP_NEG]);;

let MOI_SED_CEXP_II_ADD = prove
 (`!x y. cexp(ii * Cx(x + y)) = cexp(ii * Cx x) * cexp(ii * Cx y) /\
         cexp(ii * Cx(x - y)) = cexp(ii * Cx x) / cexp(ii * Cx y)`,
  REWRITE_TAC[CX_ADD; CX_SUB; COMPLEX_ADD_LDISTRIB; COMPLEX_SUB_LDISTRIB;
              CEXP_ADD; CEXP_SUB]);;

let MOI_SED_NF_STEP = prove
 (`!c e a b n (S:num->real^N->bool) (kappa:real^N->real^3) i b1 e1 b2 e2.
     moi_sed_setup c e a b n S /\ moi_sed_echart c e a b kappa /\
     (!x. x IN S i /\ x IN moi_smo_open_star c e
          ==> kappa x = moi_sed_ax b1 e1 (moi_sed_kap c e a b n S x)) /\
     (!x. x IN S(SUC i) /\ x IN moi_smo_open_star c e
          ==> kappa x = moi_sed_ax b2 e2 (moi_sed_kap c e a b n S x))
     ==> e1 = e2 /\ cexp(ii * Cx b1) = cexp(ii * Cx b2)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "h1") (LABEL_TAC "h2")))) THEN
  SUBGOAL_THEN `!x y. x IN moi_smo_open_star c e /\ y IN moi_smo_open_star c e /\
                      (kappa:real^N->real^3) x = kappa y ==> x = y`
  ASSUME_TAC THENL [ASM_MESON_TAC[moi_sed_echart]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                 `b:real^N`; `n:num`; `S:num->real^N->bool`; `i:num`]
    MOI_SED_CENTROIDS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:real^N` (X_CHOOSE_THEN `c1:real^N`
   (X_CHOOSE_THEN `c2:real^N` (X_CHOOSE_THEN `r0:real`
    (X_CHOOSE_THEN `rho:real` (X_CHOOSE_THEN `h0:real` STRIP_ASSUME_TAC)))))) THEN
  ABBREV_TAC `k = moi_smo_edge_factor c (e:real^N->bool)` THEN
  ABBREV_TAC `T0 = k * moi_smo_dihedral + k * &i * moi_smo_dihedral` THEN
  ABBREV_TAC `d = k * moi_smo_dihedral / &2` THEN
  SUBGOAL_THEN `d + k * &i * moi_smo_dihedral = T0 - d /\
                d + k * &(SUC i) * moi_smo_dihedral = T0 + d`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [MAP_EVERY EXPAND_TAC ["T0"; "d"] THEN REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_sed_ax b1 e1 (moi_sed_kap c e a b n S (x0:real^N)) =
                moi_sed_ax b2 e2 (moi_sed_kap c e a b n S x0)` MP_TAC THENL
   [USE_THEN "h1" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th
      (CONJ (ASSUME `(x0:real^N) IN S(i:num)`)
            (ASSUME `(x0:real^N) IN moi_smo_open_star c e`)))]) THEN
    USE_THEN "h2" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th
      (CONJ (ASSUME `(x0:real^N) IN S(SUC i)`)
            (ASSUME `(x0:real^N) IN moi_smo_open_star c e`)))]);
    ALL_TAC] THEN
  ASM_REWRITE_TAC[MOI_SED_AX_V3; MOI_SED_V3_EQ] THEN
  SUBGOAL_THEN `~(Cx r0 * cexp(ii * Cx T0) = Cx(&0)) /\ ~(Cx rho = Cx(&0)) /\
                ~(cexp(ii * Cx T0) = Cx(&0)) /\ ~(cexp(ii * Cx d) = Cx(&0)) /\
                ~(Cx r0 = Cx(&0))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[COMPLEX_ENTIRE; CEXP_NZ; CX_INJ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_sed_ax b1 e1 (moi_sed_kap c e a b n S (c1:real^N)) =
                moi_sed_ax b2 e2 (moi_sed_kap c e a b n S c2) ==> F` MP_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(c1:real^N) = c2` (fun th -> ASM_MESON_TAC[th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "h1" (fun th -> REWRITE_TAC[MATCH_MP th
      (CONJ (ASSUME `(c1:real^N) IN S(i:num)`)
            (ASSUME `(c1:real^N) IN moi_smo_open_star c e`))]) THEN
    USE_THEN "h2" (fun th -> REWRITE_TAC[MATCH_MP th
      (CONJ (ASSUME `(c2:real^N) IN S(SUC i)`)
            (ASSUME `(c2:real^N) IN moi_smo_open_star c e`))]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[MOI_SED_AX_V3; MOI_SED_V3_EQ] THEN
  BOOL_CASES_TAC `e1:bool` THEN BOOL_CASES_TAC `e2:bool` THEN
  REWRITE_TAC[MOI_SED_CNJ_POLAR; MOI_SED_CEXP_II_ADD] THENL
   [DISCH_THEN(K ALL_TAC) THEN
    UNDISCH_TAC `~(Cx r0 * cexp(ii * Cx T0) = Cx(&0))` THEN
    CONV_TAC COMPLEX_FIELD;
    MATCH_MP_TAC(TAUT `(q ==> p) ==> ~p ==> ~q`) THEN
    UNDISCH_TAC `~(Cx r0 = Cx(&0))` THEN UNDISCH_TAC `~(Cx rho = Cx(&0))` THEN
    UNDISCH_TAC `~(cexp(ii * Cx T0) = Cx(&0))` THEN
    UNDISCH_TAC `~(cexp(ii * Cx d) = Cx(&0))` THEN
    CONV_TAC COMPLEX_FIELD;
    MATCH_MP_TAC(TAUT `(q ==> p) ==> ~p ==> ~q`) THEN
    UNDISCH_TAC `~(Cx r0 = Cx(&0))` THEN UNDISCH_TAC `~(Cx rho = Cx(&0))` THEN
    UNDISCH_TAC `~(cexp(ii * Cx T0) = Cx(&0))` THEN
    UNDISCH_TAC `~(cexp(ii * Cx d) = Cx(&0))` THEN
    CONV_TAC COMPLEX_FIELD;
    DISCH_THEN(K ALL_TAC) THEN
    UNDISCH_TAC `~(Cx r0 = Cx(&0))` THEN
    UNDISCH_TAC `~(cexp(ii * Cx T0) = Cx(&0))` THEN
    CONV_TAC COMPLEX_FIELD]);;

let MOI_SED_NF = prove
 (`!c e a b n (S:num->real^N->bool) (kappa:real^N->real^3).
     moi_sed_setup c e a b n S /\ moi_sed_echart c e a b kappa
     ==> ?beta eps. !x. x IN moi_smo_open_star c e
                        ==> kappa x = moi_sed_ax beta eps (moi_sed_kap c e a b n S x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                 `b:real^N`; `n:num`; `S:num->real^N->bool`; `kappa:real^N->real^3`]
    MOI_SED_NF_TET) THEN
  ASM_REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:num->real` (X_CHOOSE_TAC `E:num->bool`)) THEN
  SUBGOAL_THEN `!i. (E:num->bool) i = E 0 /\
                    cexp(ii * Cx((B:num->real) i)) = cexp(ii * Cx(B 0))`
  ASSUME_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                   `b:real^N`; `n:num`; `S:num->real^N->bool`; `kappa:real^N->real^3`;
                   `i:num`; `(B:num->real) i`; `(E:num->bool) i`;
                   `(B:num->real) (SUC i)`; `(E:num->bool) (SUC i)`]
      MOI_SED_NF_STEP) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`(B:num->real) 0`; `(E:num->bool) 0`] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                 `b:real^N`; `n:num`; `S:num->real^N->bool`; `x:real^N`]
    MOI_SED_OPEN_STAR_IN) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  TRANS_TAC EQ_TRANS
    `moi_sed_ax ((B:num->real) i) ((E:num->bool) i)
       (moi_sed_kap c e a b n (S:num->real^N->bool) (x:real^N))` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> t = `moi_sed_ax`)) (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (is_forall o concl) o
    check (fun th -> can (find_term (fun t -> t = `(E:num->bool) 0`)) (concl th))) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_SED_AX_EQ THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 8. Reversing the orientation of the edge composes the canonical chart    *)
(* with the flip x3 |-> 1 - x3; hence any two edge charts of the same edge  *)
(* differ by an affine map of real^3.                                        *)
(* ------------------------------------------------------------------------- *)

let MOI_SED_FLIP_TWIST = prove
 (`!k y. moi_smo_twist k (moi_sed_flip y) = moi_sed_flip (moi_smo_twist k y)`,
  REWRITE_TAC[moi_smo_twist; moi_sed_flip; CART_EQ; DIMINDEX_3; FORALL_3;
              VECTOR_3]);;

let MOI_SED_FLIP_ROTZ = prove
 (`!a y. moi_smo_rotz a (moi_sed_flip y) = moi_sed_flip (moi_smo_rotz a y)`,
  REWRITE_TAC[moi_smo_rotz; moi_sed_flip; CART_EQ; DIMINDEX_3; FORALL_3;
              VECTOR_3]);;

let MOI_SED_FLIP_VALUES = prove
 (`moi_sed_flip (vec 0) = basis 3 /\ moi_sed_flip (basis 3) = vec 0 /\
   moi_sed_flip moi_sed_pt = moi_sed_pt /\ moi_sed_flip moi_sed_qt = moi_sed_qt`,
  REWRITE_TAC[MOI_SED_V3_ZERO; moi_sed_pt; moi_sed_qt; MOI_SED_FLIP_V3] THEN
  REWRITE_TAC[MOI_SED_V3_EQ] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let MOI_SED_SETUP_SWAP = prove
 (`!c e a b n (S:num->real^N->bool).
     moi_sed_setup c e a b n S ==> moi_sed_setup c e b a n S`,
  REWRITE_TAC[moi_sed_setup] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[INSERT_AC]);;

let MOI_SED_VX_SWAP = prove
 (`!a b (S:num->real^N->bool) i. moi_sed_vx b a S i = moi_sed_vx a b S i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_sed_vx] THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `w:real^N` THEN
  REWRITE_TAC[SET_RULE `{b:real^N,a,w} = {a,b,w}`] THEN MESON_TAC[]);;

let MOI_SED_A0_SWAP = prove
 (`!c e a b n (S:num->real^N->bool) i x.
     moi_sed_setup c e a b n S /\ x IN S i
     ==> moi_sed_a0 b a n S i x = moi_sed_flip (moi_sed_a0 a b n S i x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `i:num` o MATCH_MP MOI_SED_TET) THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_SED_SETUP_SWAP) THEN
  SUBGOAL_THEN `(x:real^N) IN convex hull {a,b,moi_sed_vx a b S (i + n - 1),
                                          moi_sed_vx a b S i}` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN S(i:num)` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASSUME_TAC(SPEC `i:num` (MATCH_MP MOI_SED_A0_AFFINE (ASSUME
    `moi_sed_setup c e b a n (S:num->real^N->bool)`))) THEN
  ASSUME_TAC(SPEC `i:num` (MATCH_MP MOI_SED_A0_AFFINE (ASSUME
    `moi_sed_setup c e a b n (S:num->real^N->bool)`))) THEN
  MP_TAC(SPEC `i:num` (MATCH_MP MOI_SED_A0 (ASSUME
    `moi_sed_setup c e b a n (S:num->real^N->bool)`))) THEN
  MP_TAC(SPEC `i:num` (MATCH_MP MOI_SED_A0 (ASSUME
    `moi_sed_setup c e a b n (S:num->real^N->bool)`))) THEN
  REWRITE_TAC[MOI_SED_VX_SWAP] THEN
  ABBREV_TAC `A1 = moi_sed_a0 a b n (S:num->real^N->bool) i` THEN
  ABBREV_TAC `A2 = moi_sed_a0 b a n (S:num->real^N->bool) i` THEN
  ABBREV_TAC `q' = moi_sed_vx a b (S:num->real^N->bool) (i + n - 1)` THEN
  ABBREV_TAC `q = moi_sed_vx a b (S:num->real^N->bool) i` THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?l y. linear l /\ !x. moi_sed_flip ((A1:real^N->real^3) x) = l x + y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SBA_AFFINE_COMPOSE THEN ASM_REWRITE_TAC[MOI_SED_FLIP_AFFINE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`A2:real^N->real^3`; `moi_sed_flip o (A1:real^N->real^3)`;
                 `a:real^N`; `b:real^N`; `q':real^N`; `q:real^N`; `x:real^N`]
    MOI_SBA_AFF_EQ_HULL4) THEN
  REWRITE_TAC[o_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[MOI_SED_FLIP_VALUES]);;

let MOI_SED_KAP_SWAP = prove
 (`!c e a b n (S:num->real^N->bool) x.
     moi_sed_setup c e a b n S /\ x IN moi_smo_open_star c e
     ==> moi_sed_kap c e b a n S x = moi_sed_flip (moi_sed_kap c e a b n S x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_SED_SETUP_SWAP) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                 `b:real^N`; `n:num`; `S:num->real^N->bool`; `x:real^N`]
    MOI_SED_OPEN_STAR_IN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`i:num`; `x:real^N`] (MATCH_MP MOI_SED_KAP_FF (ASSUME
    `moi_sed_setup c e b a n (S:num->real^N->bool)`))) THEN
  MP_TAC(SPECL [`i:num`; `x:real^N`] (MATCH_MP MOI_SED_KAP_FF (ASSUME
    `moi_sed_setup c e a b n (S:num->real^N->bool)`))) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[moi_sed_ff] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                 `b:real^N`; `n:num`; `S:num->real^N->bool`; `i:num`; `x:real^N`]
    MOI_SED_A0_SWAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MOI_SED_FLIP_TWIST; MOI_SED_FLIP_ROTZ]);;

let MOI_SED_SEGMENT_ENDS = prove
 (`!a b a' b':real^N.
     ~(a' = b') /\ segment[a,b] = segment[a',b']
     ==> (a' = a /\ b' = b) \/ (a' = b /\ b' = a)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(a':real^N) extreme_point_of segment[a,b] /\
                (b':real^N) extreme_point_of segment[a,b]` MP_TAC THENL
   [REWRITE_TAC[ASSUME `segment[a:real^N,b] = segment[a',b']`] THEN
    REWRITE_TAC[EXTREME_POINT_OF_SEGMENT];
    ALL_TAC] THEN
  REWRITE_TAC[EXTREME_POINT_OF_SEGMENT] THEN
  SUBGOAL_THEN `(a:real^N) extreme_point_of segment[a',b']` MP_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[EXTREME_POINT_OF_SEGMENT];
    ALL_TAC] THEN
  REWRITE_TAC[EXTREME_POINT_OF_SEGMENT] THEN ASM_MESON_TAC[]);;

let MOI_SED_SAME_EDGE = prove
 (`!c e a b a' b' (kappa:real^N->real^3) phi.
     FINITE c /\ combinatorial_manifold 3 c /\ e IN c /\ aff_dim e = &1 /\
     moi_sed_echart c e a b kappa /\ moi_sed_echart c e a' b' phi
     ==> ?L. (?l y. linear l /\ !z. L z = l z + y) /\
             !x. x IN moi_smo_open_star c e ==> phi x = L(kappa x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_SED_CYC_EXISTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_TAC `S:num->real^N->bool`)) THEN
  SUBGOAL_THEN `~(a':real^N = b') /\ segment[a:real^N,b] = segment[a',b']`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_sed_echart]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_sed_setup c e (a:real^N) b n S` ASSUME_TAC THENL
   [REWRITE_TAC[moi_sed_setup] THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SEGMENT_CONVEX_HULL; moi_sed_echart];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                 `b:real^N`; `n:num`; `S:num->real^N->bool`; `kappa:real^N->real^3`]
    MOI_SED_NF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `beta:real` (X_CHOOSE_THEN `eps:bool`
    (LABEL_TAC "nk"))) THEN
  MP_TAC(ISPECL [`beta:real`; `eps:bool`] MOI_SED_AX_INV) THEN
  DISCH_THEN(X_CHOOSE_THEN `beta0:real` (LABEL_TAC "inv")) THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `a':real^N`; `b':real^N`]
    MOI_SED_SEGMENT_ENDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `segment[a:real^N,b] = segment[a',b']` THEN DISCH_THEN(K ALL_TAC) THEN
  DISCH_THEN(DISJ_CASES_THEN (CONJUNCTS_THEN SUBST_ALL_TAC)) THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                   `b:real^N`; `n:num`; `S:num->real^N->bool`; `phi:real^N->real^3`]
      MOI_SED_NF) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `beta':real` (X_CHOOSE_THEN `eps':bool`
      ASSUME_TAC)) THEN
    EXISTS_TAC `\z. moi_sed_ax beta' eps' (moi_sed_ax beta0 eps z)` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`moi_sed_ax beta0 eps`; `moi_sed_ax beta' eps'`]
        MOI_SBA_AFFINE_COMPOSE) THEN
      REWRITE_TAC[MOI_SED_AX_AFFINE];
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN ASM_SIMP_TAC[]];
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_SED_SETUP_SWAP) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `b:real^N`;
                   `a:real^N`; `n:num`; `S:num->real^N->bool`; `phi:real^N->real^3`]
      MOI_SED_NF) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `beta':real` (X_CHOOSE_THEN `eps':bool`
      ASSUME_TAC)) THEN
    EXISTS_TAC `\z. moi_sed_ax beta' eps' (moi_sed_flip (moi_sed_ax beta0 eps z))` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`moi_sed_ax beta0 eps`; `moi_sed_flip`]
        MOI_SBA_AFFINE_COMPOSE) THEN
      REWRITE_TAC[MOI_SED_AX_AFFINE; MOI_SED_FLIP_AFFINE] THEN
      DISCH_THEN(MP_TAC o CONJ (ISPECL [`beta':real`; `eps':bool`] MOI_SED_AX_AFFINE)) THEN
      DISCH_THEN(MP_TAC o MATCH_MP MOI_SBA_AFFINE_COMPOSE o ONCE_REWRITE_RULE[CONJ_SYM]) THEN
      REWRITE_TAC[];
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                     `b:real^N`; `n:num`; `S:num->real^N->bool`; `x:real^N`]
        MOI_SED_KAP_SWAP) THEN
      ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_TAC THEN ASM_SIMP_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* 9. Near the triangle S i INTER S (SUC i) the canonical chart is the       *)
(* rescaling of an unfolding of the two tetrahedra (S i in the wedge         *)
(* [0,alpha], S (SUC i) rotated into [alpha,2 alpha]).                       *)
(* ------------------------------------------------------------------------- *)

let moi_sed_unf = new_definition
 `moi_sed_unf (a:real^N) (b:real^N) (n:num) (S:num->real^N->bool) (i:num) (x:real^N) =
    if x IN S i then moi_sed_a0 a b n S i x
    else moi_smo_rotz moi_smo_dihedral (moi_sed_a0 a b n S (SUC i) x)`;;

let MOI_SED_ROTZ_VALUES = prove
 (`!t. moi_smo_rotz t (vec 0) = vec 0 /\ moi_smo_rotz t (basis 3) = basis 3 /\
       moi_smo_rotz moi_smo_dihedral moi_sed_pt = moi_sed_qt`,
  GEN_TAC THEN REPEAT CONJ_TAC THENL
   [MESON_TAC[MOI_SED_ROTZ_LINEAR; LINEAR_0];
    REWRITE_TAC[MOI_SED_V3_ZERO; MOI_SED_ROTZ_V3; COMPLEX_MUL_RZERO];
    REWRITE_TAC[moi_sed_pt; moi_sed_qt; MOI_SED_ROTZ_V3; MOI_SED_V3_EQ] THEN
    CONV_TAC COMPLEX_RING]);;

let MOI_SED_ROTZ_REGMAP = prove
 (`!tet (A:real^N->real^3) t.
     moi_smo_regmap tet A ==> moi_smo_regmap tet (\x. moi_smo_rotz t (A x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_smo_regmap] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`A:real^N->real^3`; `moi_smo_rotz t`] MOI_SBA_AFFINE_COMPOSE) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[];
      MAP_EVERY EXISTS_TAC [`moi_smo_rotz t`; `vec 0:real^3`] THEN
      REWRITE_TAC[MOI_SED_ROTZ_LINEAR; VECTOR_ADD_RID]];
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[dist; GSYM(MATCH_MP LINEAR_SUB (SPEC `t:real` MOI_SED_ROTZ_LINEAR));
                MOI_SMO_TWIST_NORM] THEN
    REWRITE_TAC[GSYM dist] THEN ASM_MESON_TAC[]]);;

let MOI_SED_TWIST_ROT_AL = prove
 (`!k r t h. &0 <= r /\ &0 <= t /\ t <= moi_smo_dihedral
             ==> moi_smo_twist k
                   (moi_smo_rotz moi_smo_dihedral
                     (moi_sed_v3 (Cx r * cexp(ii * Cx t)) h)) =
                 moi_smo_rotz (k * moi_smo_dihedral)
                   (moi_smo_twist k (moi_sed_v3 (Cx r * cexp(ii * Cx t)) h))`,
  REPEAT STRIP_TAC THEN MP_TAC MOI_SED_ALPHA THEN MP_TAC PI_POS THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `t < &2 * pi /\ &0 <= t + moi_smo_dihedral /\
                t + moi_smo_dihedral < &2 * pi` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_SED_ROTZ_POLAR; MOI_SED_TWIST_POLAR] THEN
  REWRITE_TAC[MOI_SED_ROTZ_POLAR; MOI_SED_V3_EQ] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REAL_ARITH_TAC);;

let MOI_SED_OT_CASES = prove
 (`!c e a b n (S:num->real^N->bool) i x.
     moi_sed_setup c e a b n S /\
     x IN moi_smo_open_star c (S i INTER S(SUC i))
     ==> x IN relative_interior(convex hull {a,b,moi_sed_vx a b S i}) \/
         x IN relative_interior(S i) \/
         (x IN relative_interior(S(SUC i)) /\ ~(x IN S i))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN MOI_SED_SETUP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `i:num` o MATCH_MP MOI_SED_TRI) THEN
  FIRST_ASSUM(MP_TAC o SPEC `i:num` o MATCH_MP MOI_SED_VX) THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `(S:num->real^N->bool) i INTER S(SUC i)`]
    MOI_SBA_OPEN_STAR_TRI) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THENL
   [DISJ1_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                 `b:real^N`; `n:num`; `S:num->real^N->bool`; `tet:real^N->bool`;
                 `i:num`] MOI_SED_TRI_TETS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THENL
   [DISJ2_TAC THEN DISJ1_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISJ2_TAC THEN DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `(S:num->real^N->bool) (SUC i)`;
                 `(S:num->real^N->bool) i`] MOI_SBA_RELINT_DISJ_EQDIM) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o SPEC `i:num` o MATCH_MP MOI_SED_S_DISTINCT o
    MATCH_MP MOI_SED_SETUP_CYC) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_SED_A0_NEXT = prove
 (`!c e a b n (S:num->real^N->bool) i x.
     moi_sed_setup c e a b n S /\ x IN S i /\ x IN S(SUC i)
     ==> moi_sed_a0 a b n S i x =
         moi_smo_rotz moi_smo_dihedral (moi_sed_a0 a b n S (SUC i) x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_SED_SETUP_CYC) THEN
  SUBGOAL_THEN `moi_sed_vx a b (S:num->real^N->bool) (SUC i + n - 1) =
                moi_sed_vx a b S i` ASSUME_TAC THENL
   [SUBGOAL_THEN `SUC i + n - 1 = i + n` SUBST1_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SED_SETUP_FACTS) THEN ARITH_TAC;
      ASM_MESON_TAC[MOI_SED_VX_PERIODIC]];
    ALL_TAC] THEN
  ASSUME_TAC(SPEC `i:num` (MATCH_MP MOI_SED_A0_AFFINE (ASSUME
    `moi_sed_setup c e a b n (S:num->real^N->bool)`))) THEN
  ASSUME_TAC(SPEC `SUC i` (MATCH_MP MOI_SED_A0_AFFINE (ASSUME
    `moi_sed_setup c e a b n (S:num->real^N->bool)`))) THEN
  MP_TAC(SPEC `i:num` (MATCH_MP MOI_SED_A0 (ASSUME
    `moi_sed_setup c e a b n (S:num->real^N->bool)`))) THEN
  MP_TAC(SPEC `SUC i` (MATCH_MP MOI_SED_A0 (ASSUME
    `moi_sed_setup c e a b n (S:num->real^N->bool)`))) THEN
  MP_TAC(SPEC `i:num` (MATCH_MP MOI_SED_VX (ASSUME
    `moi_sed_setup c e a b n (S:num->real^N->bool)`))) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `q = moi_sed_vx a b (S:num->real^N->bool) i` THEN
  ABBREV_TAC `A1 = moi_sed_a0 a b n (S:num->real^N->bool) i` THEN
  ABBREV_TAC `A2 = moi_sed_a0 a b n (S:num->real^N->bool) (SUC i)` THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?l y. linear l /\
                      !x. moi_smo_rotz moi_smo_dihedral ((A2:real^N->real^3) x) =
                          l x + y` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SBA_AFFINE_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`moi_smo_rotz moi_smo_dihedral`; `vec 0:real^3`] THEN
    REWRITE_TAC[MOI_SED_ROTZ_LINEAR; VECTOR_ADD_RID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`A1:real^N->real^3`;
                 `moi_smo_rotz moi_smo_dihedral o (A2:real^N->real^3)`;
                 `a:real^N`; `b:real^N`; `q:real^N`; `q:real^N`; `x:real^N`]
    MOI_SBA_AFF_EQ_HULL4) THEN
  REWRITE_TAC[o_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[MOI_SED_ROTZ_VALUES] THEN
  REWRITE_TAC[SET_RULE `{a:real^N,b,q,q} = {a,b,q}`] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    try lhs(concl th) = `(S:num->real^N->bool) i INTER S(SUC i)`
    with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[IN_INTER]);;

let MOI_SED_KAP_UNF = prove
 (`!c e a b n (S:num->real^N->bool) i x.
     moi_sed_setup c e a b n S /\
     x IN moi_smo_open_star c (S i INTER S(SUC i))
     ==> moi_sed_kap c e a b n S x =
         moi_smo_rotz (moi_smo_edge_factor c e * &i * moi_smo_dihedral)
           (moi_smo_twist (moi_smo_edge_factor c e) (moi_sed_unf a b n S i x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                 `b:real^N`; `n:num`; `S:num->real^N->bool`; `i:num`; `x:real^N`]
    MOI_SED_OT_CASES) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!s:real^N->bool. relative_interior s SUBSET s` ASSUME_TAC THENL
   [REWRITE_TAC[RELATIVE_INTERIOR_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {a,b,moi_sed_vx a b S i} SUBSET (S:num->real^N->bool) i`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `i:num` o MATCH_MP MOI_SED_VX) THEN
    STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(x:real^N) IN S(i:num)` THEN ASM_REWRITE_TAC[moi_sed_unf] THENL
   [DISCH_TAC THEN
    MP_TAC(SPECL [`i:num`; `x:real^N`] (MATCH_MP MOI_SED_KAP_FF (ASSUME
      `moi_sed_setup c e a b n (S:num->real^N->bool)`))) THEN
    ASM_REWRITE_TAC[moi_sed_ff];
    STRIP_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^N) IN S(SUC i)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(SPECL [`SUC i`; `x:real^N`] (MATCH_MP MOI_SED_KAP_FF (ASSUME
      `moi_sed_setup c e a b n (S:num->real^N->bool)`))) THEN
    ASM_REWRITE_TAC[moi_sed_ff] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                   `b:real^N`; `n:num`; `S:num->real^N->bool`; `SUC i`; `x:real^N`]
      MOI_SED_A0_POLAR) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `t:real`
      (X_CHOOSE_THEN `h:real` STRIP_ASSUME_TAC))) THEN
    ASM_SIMP_TAC[MOI_SED_TWIST_ROT_AL; MOI_SED_ROTZ_ROTZ] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
    REAL_ARITH_TAC]);;

let MOI_SED_STD_COMB_COMPONENTS = prove
 (`!u1 u2 u3 u4.
     (u1 % vec 0 + u2 % basis 3 + u3 % moi_sed_pt + u4 % moi_sed_qt:real^3)$1 =
     u3 * sqrt(&3) / &2 + u4 * sqrt(&3) / &2 * cos moi_smo_dihedral /\
     (u1 % vec 0 + u2 % basis 3 + u3 % moi_sed_pt + u4 % moi_sed_qt:real^3)$2 =
     u4 * sqrt(&3) / &2 * sin moi_smo_dihedral`,
  SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT;
           BASIS_COMPONENT; DIMINDEX_3; ARITH; MOI_SED_PT_COMPONENTS;
           MOI_SED_QT_COMPONENTS] THEN
  REAL_ARITH_TAC);;

let MOI_SED_UNF_POS = prove
 (`!c e a b n (S:num->real^N->bool) i x.
     moi_sed_setup c e a b n S /\
     x IN moi_smo_open_star c (S i INTER S(SUC i))
     ==> &0 < (moi_sed_unf a b n S i x)$2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                 `b:real^N`; `n:num`; `S:num->real^N->bool`; `i:num`; `x:real^N`]
    MOI_SED_OT_CASES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "cases") THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_SED_SETUP_CYC) THEN
  SUBGOAL_THEN `moi_sed_vx a b (S:num->real^N->bool) (SUC i + n - 1) =
                moi_sed_vx a b S i` ASSUME_TAC THENL
   [SUBGOAL_THEN `SUC i + n - 1 = i + n` SUBST1_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SED_SETUP_FACTS) THEN ARITH_TAC;
      ASM_MESON_TAC[MOI_SED_VX_PERIODIC]];
    ALL_TAC] THEN
  ASSUME_TAC(SPEC `i:num` (MATCH_MP MOI_SED_A0_AFFINE (ASSUME
    `moi_sed_setup c e a b n (S:num->real^N->bool)`))) THEN
  ASSUME_TAC(SPEC `SUC i` (MATCH_MP MOI_SED_A0_AFFINE (ASSUME
    `moi_sed_setup c e a b n (S:num->real^N->bool)`))) THEN
  MP_TAC(SPEC `i:num` (MATCH_MP MOI_SED_A0 (ASSUME
    `moi_sed_setup c e a b n (S:num->real^N->bool)`))) THEN
  MP_TAC(SPEC `SUC i` (MATCH_MP MOI_SED_A0 (ASSUME
    `moi_sed_setup c e a b n (S:num->real^N->bool)`))) THEN
  MP_TAC(SPEC `i:num` (MATCH_MP MOI_SED_TET (ASSUME
    `moi_sed_setup c e a b n (S:num->real^N->bool)`))) THEN
  MP_TAC(SPEC `SUC i` (MATCH_MP MOI_SED_TET (ASSUME
    `moi_sed_setup c e a b n (S:num->real^N->bool)`))) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `q' = moi_sed_vx a b (S:num->real^N->bool) (i + n - 1)` THEN
  ABBREV_TAC `q = moi_sed_vx a b (S:num->real^N->bool) i` THEN
  ABBREV_TAC `q'' = moi_sed_vx a b (S:num->real^N->bool) (SUC i)` THEN
  ABBREV_TAC `A1 = moi_sed_a0 a b n (S:num->real^N->bool) i` THEN
  ABBREV_TAC `A2 = moi_sed_a0 a b n (S:num->real^N->bool) (SUC i)` THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(a:real^N = b)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_sed_setup]; ALL_TAC] THEN
  SUBGOAL_THEN `~affine_dependent {a:real^N,b,q}` ASSUME_TAC THENL
   [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN
    EXISTS_TAC `{a:real^N,b,q',q}` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC MOI_SED_SQRT3 THEN MP_TAC MOI_SED_ALPHA THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!u4. &0 < u4 ==> &0 < u4 * sqrt(&3) / &2 * sin moi_smo_dihedral`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "cases" MP_TAC THEN
  STRIP_TAC THENL
   [SUBGOAL_THEN `(x:real^N) IN S(i:num)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `convex hull {a:real^N,b,q} SUBSET convex hull {a,b,q',q}`
      MP_TAC THENL [MATCH_MP_TAC HULL_MONO THEN SET_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPEC `convex hull {a:real^N,b,q}` RELATIVE_INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(x:real^N) IN relative_interior (convex hull {a,b,q})` THEN
      SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[moi_sed_unf] THEN
    UNDISCH_TAC `(x:real^N) IN relative_interior (convex hull {a,b,q})` THEN
    ASM_SIMP_TAC[MOI_SBA_RELINT_3] THEN
    DISCH_THEN(X_CHOOSE_THEN `u1:real` (X_CHOOSE_THEN `u2:real`
      (X_CHOOSE_THEN `u4:real` STRIP_ASSUME_TAC))) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `u1 % a + u2 % b + u4 % (q:real^N) =
                  u1 % a + u2 % b + &0 % q' + u4 % q` SUBST1_TAC THENL
     [VECTOR_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`A1:real^N->real^3`; `u1:real`; `u2:real`; `&0`; `u4:real`;
                   `a:real^N`; `b:real^N`; `q':real^N`; `q:real^N`]
      MOI_SBA_AFF_EVAL4) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[MOI_SED_STD_COMB_COMPONENTS] THEN
    ASM_SIMP_TAC[];
    SUBGOAL_THEN `(x:real^N) IN S(i:num)` ASSUME_TAC THENL
     [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
    ASM_REWRITE_TAC[moi_sed_unf] THEN
    UNDISCH_TAC `(x:real^N) IN relative_interior(S(i:num))` THEN
    ASM_SIMP_TAC[MOI_SBA_RELINT_4] THEN
    DISCH_THEN(X_CHOOSE_THEN `u1:real` (X_CHOOSE_THEN `u2:real`
      (X_CHOOSE_THEN `u3:real` (X_CHOOSE_THEN `u4:real` STRIP_ASSUME_TAC)))) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`A1:real^N->real^3`; `u1:real`; `u2:real`; `u3:real`; `u4:real`;
                   `a:real^N`; `b:real^N`; `q':real^N`; `q:real^N`]
      MOI_SBA_AFF_EVAL4) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[MOI_SED_STD_COMB_COMPONENTS] THEN
    ASM_SIMP_TAC[];
    ASM_REWRITE_TAC[moi_sed_unf] THEN
    UNDISCH_TAC `(x:real^N) IN relative_interior(S(SUC i))` THEN
    ASM_SIMP_TAC[MOI_SBA_RELINT_4] THEN
    DISCH_THEN(X_CHOOSE_THEN `w1:real` (X_CHOOSE_THEN `w2:real`
      (X_CHOOSE_THEN `w3:real` (X_CHOOSE_THEN `w4:real` STRIP_ASSUME_TAC)))) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`A2:real^N->real^3`; `w1:real`; `w2:real`; `w3:real`; `w4:real`;
                   `a:real^N`; `b:real^N`; `q:real^N`; `q'':real^N`]
      MOI_SBA_AFF_EVAL4) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[moi_smo_rotz; VECTOR_3; MOI_SED_STD_COMB_COMPONENTS] THEN
    REWRITE_TAC[REAL_RING
     `sin al * (w3 * s / &2 + w4 * s / &2 * co) + co * w4 * s / &2 * sin al =
      (s / &2 * sin al) * (w3 + &2 * w4 * co)`] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]]);;

let MOI_SED_UNF_UNF = prove
 (`!c e a b n (S:num->real^N->bool) i.
     moi_sed_setup c e a b n S
     ==> moi_sba_unf c (S i INTER S(SUC i)) (moi_sed_unf a b n S i)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_sba_unf] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SED_SETUP_FACTS) THEN
  FIRST_ASSUM(MP_TAC o SPEC `i:num` o MATCH_MP MOI_SED_TRI) THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_smo_open_star c ((S:num->real^N->bool) i INTER S(SUC i)) SUBSET
                moi_smo_open_star c e` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SBA_OPEN_STAR_MONO THEN ASM_MESON_TAC[moi_sed_setup];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                   `b:real^N`; `n:num`; `S:num->real^N->bool`; `i:num`; `x:real^N`]
      MOI_SED_KAP_UNF) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                   `b:real^N`; `n:num`; `S:num->real^N->bool`; `i:num`; `y:real^N`]
      MOI_SED_KAP_UNF) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                   `b:real^N`; `n:num`; `S:num->real^N->bool`; `x:real^N`]
      MOI_SED_OPEN_STAR_IN) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                   `b:real^N`; `n:num`; `S:num->real^N->bool`; `y:real^N`]
      MOI_SED_OPEN_STAR_IN) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC MOI_SED_KAP_INJ THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                          `b:real^N`; `n:num`; `S:num->real^N->bool`;
                          `k:num`; `j:num`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `tet:real^N->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                 `b:real^N`; `n:num`; `S:num->real^N->bool`; `tet:real^N->bool`;
                 `i:num`] MOI_SED_TRI_TETS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o MATCH_MP MOI_SED_VX) THEN
    STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THENL
   [EXISTS_TAC `moi_sed_a0 a b n (S:num->real^N->bool) i` THEN
    MP_TAC(SPEC `i:num` (MATCH_MP MOI_SED_A0 (ASSUME
      `moi_sed_setup c e a b n (S:num->real^N->bool)`))) THEN
    SIMP_TAC[IN_INTER; moi_sed_unf];
    EXISTS_TAC `\x. moi_smo_rotz moi_smo_dihedral
                      (moi_sed_a0 a b n (S:num->real^N->bool) (SUC i) x)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_SED_ROTZ_REGMAP THEN REWRITE_TAC[ETA_AX] THEN
      MP_TAC(SPEC `SUC i` (MATCH_MP MOI_SED_A0 (ASSUME
        `moi_sed_setup c e a b n (S:num->real^N->bool)`))) THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    REWRITE_TAC[moi_sed_unf] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_SED_A0_NEXT THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `e:real^N->bool`] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 10. Local factorizations: on the interior of a tetrahedron every chart   *)
(* is a smooth map G applied to a regular map, with a smooth local inverse   *)
(* H; on the open star of a triangle it is G applied to an unfolding.        *)
(* Transitions between two such charts are smooth.                          *)
(* ------------------------------------------------------------------------- *)

let moi_sed_ftet = new_definition
 `moi_sed_ftet (phi:real^N->real^3) (tet:real^N->bool) <=>
    ?A G H OG OH. moi_smo_regmap tet A /\ open OG /\ open OH /\
                  IMAGE A (relative_interior tet) SUBSET OG /\
                  IMAGE phi (relative_interior tet) SUBSET OH /\
                  smooth_map_on OG G /\ smooth_map_on OH H /\
                  !x. x IN relative_interior tet ==> G(A x) = phi x /\ H(phi x) = A x`;;

let moi_sed_ftri = new_definition
 `moi_sed_ftri (c:(real^N->bool)->bool) (phi:real^N->real^3) (t:real^N->bool) <=>
    ?u G H OG OH. moi_sba_unf c t u /\ open OG /\ open OH /\
                  IMAGE u (moi_smo_open_star c t) SUBSET OG /\
                  IMAGE phi (moi_smo_open_star c t) SUBSET OH /\
                  smooth_map_on OG G /\ smooth_map_on OH H /\
                  !x. x IN moi_smo_open_star c t ==> G(u x) = phi x /\ H(phi x) = u x`;;

let MOI_SED_SMOOTH_COMP2 = prove
 (`!s t (f:real^M->real^N) (g:real^N->real^P).
     open s /\ open t /\ smooth_map_on s f /\ smooth_map_on t g
     ==> open {x | x IN s /\ f x IN t} /\
         smooth_map_on {x | x IN s /\ f x IN t} (g o f)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open {x | x IN s /\ (f:real^M->real^N) x IN t}` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `t:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `s:real^M->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

let MOI_SED_REGMAP_LEFT_INV = prove
 (`!c tet (A:real^N->real^3).
     lf_simplicial_complex c /\ tet IN c /\ aff_dim tet = &3 /\ moi_smo_regmap tet A
     ==> ?B:real^3->real^N. (?l y. linear l /\ !x. B x = l x + y) /\
                            !x. x IN tet ==> B(A x) = x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&3 simplex (tet:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SBA_LF_SIMPLEX]; ALL_TAC] THEN
  SUBGOAL_THEN `~(tet:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `aff_dim(tet:real^N->bool) = &3` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tet:real^N->bool`] MOI_SBA_EXTREME_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`tet:real^N->bool`; `v:real^N`] MOI_SBA_TET_VERTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q2:real^N` (X_CHOOSE_THEN `q3:real^N`
    (X_CHOOSE_THEN `q4:real^N` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`v:real^N`; `q2:real^N`; `q3:real^N`; `q4:real^N`;
                 `A:real^N->real^3`] MOI_SBA_REGMAP_INV) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `B:real^3->real^N` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(ISPEC `{v:real^N,q2,q3,q4}` CONVEX_HULL_SUBSET_AFFINE_HULL) THEN
  ASM SET_TAC[]);;

let MOI_SED_TRANS_TET = prove
 (`!c tet (phi:real^N->real^3) psi.
     lf_simplicial_complex c /\ tet IN c /\ aff_dim tet = &3 /\
     moi_sed_ftet phi tet /\ moi_sed_ftet psi tet
     ==> ?g O. open O /\ IMAGE phi (relative_interior tet) SUBSET O /\
               smooth_map_on O g /\
               !x. x IN relative_interior tet ==> g(phi x) = psi x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_sed_ftet] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `A1:real^N->real^3` (X_CHOOSE_THEN `G1:real^3->real^3`
     (X_CHOOSE_THEN `H1:real^3->real^3` (X_CHOOSE_THEN `OG1:real^3->bool`
      (X_CHOOSE_THEN `OH1:real^3->bool` STRIP_ASSUME_TAC)))))
    (X_CHOOSE_THEN `A2:real^N->real^3` (X_CHOOSE_THEN `G2:real^3->real^3`
     (X_CHOOSE_THEN `H2:real^3->real^3` (X_CHOOSE_THEN `OG2:real^3->bool`
      (X_CHOOSE_THEN `OH2:real^3->bool` STRIP_ASSUME_TAC))))))))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tet:real^N->bool`; `A1:real^N->real^3`]
    MOI_SED_REGMAP_LEFT_INV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real^3->real^N` (CONJUNCTS_THEN2 ASSUME_TAC
    ASSUME_TAC)) THEN
  SUBGOAL_THEN `?l y. linear l /\ !x. (A2:real^N->real^3) ((B:real^3->real^N) x) =
                                      l x + y` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SBA_AFFINE_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MOI_SBA_REGMAP_AFFINE];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on OH1 ((\z. (A2:real^N->real^3) ((B:real^3->real^N) z)) o
                                   (H1:real^3->real^3))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^3)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
    MATCH_MP_TAC MOI_SBA_AFFINE_SMOOTH THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`OH1:real^3->bool`; `OG2:real^3->bool`;
                 `(\z. (A2:real^N->real^3) ((B:real^3->real^N) z)) o (H1:real^3->real^3)`;
                 `G2:real^3->real^3`] MOI_SED_SMOOTH_COMP2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `(G2:real^3->real^3) o (\z. (A2:real^N->real^3) ((B:real^3->real^N) z)) o
              (H1:real^3->real^3)` THEN
  EXISTS_TAC `{y | y IN OH1 /\ ((\z. (A2:real^N->real^3) ((B:real^3->real^N) z)) o
                                (H1:real^3->real^3)) y IN OG2}` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!x. x IN relative_interior tet ==> x IN (tet:real^N->bool)`
  ASSUME_TAC THENL [MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; o_THM] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ASM_SIMP_TAC[] THEN ASM SET_TAC[]];
    REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[]]);;

let MOI_SED_TRANS_TRI = prove
 (`!c t (phi:real^N->real^3) psi.
     FINITE c /\ combinatorial_manifold 3 c /\ t IN c /\ aff_dim t = &2 /\
     moi_sed_ftri c phi t /\ moi_sed_ftri c psi t
     ==> ?g O. open O /\ IMAGE phi (moi_smo_open_star c t) SUBSET O /\
               smooth_map_on O g /\
               !x. x IN moi_smo_open_star c t ==> g(phi x) = psi x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_sed_ftri] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `u1:real^N->real^3` (X_CHOOSE_THEN `G1:real^3->real^3`
     (X_CHOOSE_THEN `H1:real^3->real^3` (X_CHOOSE_THEN `OG1:real^3->bool`
      (X_CHOOSE_THEN `OH1:real^3->bool` STRIP_ASSUME_TAC)))))
    (X_CHOOSE_THEN `u2:real^N->real^3` (X_CHOOSE_THEN `G2:real^3->real^3`
     (X_CHOOSE_THEN `H2:real^3->real^3` (X_CHOOSE_THEN `OG2:real^3->bool`
      (X_CHOOSE_THEN `OH2:real^3->bool` STRIP_ASSUME_TAC)))))))))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`; `u1:real^N->real^3`;
                 `u2:real^N->real^3`] MOI_SBA_TRANS_SAME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g0:real^3->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `open(IMAGE (u1:real^N->real^3) (moi_smo_open_star c t))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`;
                   `moi_smo_open_star c (t:real^N->bool)`; `u1:real^N->real^3`]
      MOI_SBA_CHART_OK_UNF) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`OH1:real^3->bool`;
                 `IMAGE (u1:real^N->real^3) (moi_smo_open_star c t)`;
                 `H1:real^3->real^3`; `g0:real^3->real^3`] MOI_SED_SMOOTH_COMP2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `O1 = {y | y IN OH1 /\
                        (H1:real^3->real^3) y IN IMAGE (u1:real^N->real^3)
                                                   (moi_smo_open_star c t)}` THEN
  MP_TAC(ISPECL [`O1:real^3->bool`; `OG2:real^3->bool`;
                 `(g0:real^3->real^3) o (H1:real^3->real^3)`;
                 `G2:real^3->real^3`] MOI_SED_SMOOTH_COMP2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `(G2:real^3->real^3) o (g0:real^3->real^3) o (H1:real^3->real^3)` THEN
  EXISTS_TAC `{y | y IN O1 /\ ((g0:real^3->real^3) o (H1:real^3->real^3)) y IN OG2}` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [EXPAND_TAC "O1" THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; o_THM] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]];
    REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 11. The factorizations hold for the charts of all three families.        *)
(* ------------------------------------------------------------------------- *)

let MOI_SED_SMOOTH_ID = prove
 (`!s. smooth_map_on s (\y:real^3. y)`,
  REWRITE_TAC[SMOOTH_MAP_ON_ID]);;

let MOI_SED_FTET_BASE = prove
 (`!c U (phi:real^N->real^3) tet.
     FINITE c /\ combinatorial_manifold 3 c /\
     (U,phi) IN moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c /\
     tet IN c /\ aff_dim tet = &3 /\ ~(U INTER relative_interior tet = {})
     ==> relative_interior tet SUBSET U /\ moi_sed_ftet phi tet`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SBA_CHART_ON_TET) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `A:real^N->real^3` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[moi_sed_ftet] THEN
  MAP_EVERY EXISTS_TAC [`A:real^N->real^3`; `\y:real^3. y`; `\y:real^3. y`;
                        `(:real^3)`; `(:real^3)`] THEN
  ASM_SIMP_TAC[OPEN_UNIV; SUBSET_UNIV; SMOOTH_MAP_ON_ID]);;

let MOI_SED_FTRI_BASE = prove
 (`!c U (phi:real^N->real^3) t.
     FINITE c /\ combinatorial_manifold 3 c /\
     (U,phi) IN moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c /\
     t IN c /\ aff_dim t = &2 /\ ~(U INTER relative_interior t = {})
     ==> moi_smo_open_star c t SUBSET U /\ moi_sed_ftri c phi t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool) /\
                simplicial_complex c /\ (!s. s IN c ==> aff_dim s <= &3)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold; MOI_SCF_CM_FACTS; MOI_SBA_DIM_LE3];
    ALL_TAC] THEN
  UNDISCH_TAC `(U,phi) IN moi_smo_tet_atlas c UNION
               moi_smo_unfold_atlas (c:(real^N->bool)->bool)` THEN
  REWRITE_TAC[IN_UNION; MOI_SBA_TET_ATLAS_IN2; MOI_SBA_UNFOLD_ATLAS_IN] THEN
  STRIP_TAC THENL
   [UNDISCH_TAC `~(U INTER relative_interior t:real^N->bool = {})` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tet:real^N->bool`; `t:real^N->bool`]
      MOI_SBA_RELINT_EQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `aff_dim(t:real^N->bool) = &3` THEN ASM_REWRITE_TAC[] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `t':real^N->bool = t` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `~(U INTER relative_interior t:real^N->bool = {})` THEN
    ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(x:real^N) IN moi_smo_open_star c t'` THEN
    REWRITE_TAC[moi_smo_open_star; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    UNDISCH_TAC `r = relative_interior(s:real^N->bool)` THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`; `t:real^N->bool`]
      MOI_SBA_RELINT_EQ) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST_ALL_TAC] THEN
    MATCH_MP_TAC MOI_SCF_SUBSET_DIM_EQ THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[FACE_OF_IMP_SUBSET];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[SUBSET_REFL; moi_sed_ftri] THEN
  MAP_EVERY EXISTS_TAC [`phi:real^N->real^3`; `\y:real^3. y`; `\y:real^3. y`;
                        `(:real^3)`; `(:real^3)`] THEN
  ASM_SIMP_TAC[OPEN_UNIV; SUBSET_UNIV; SMOOTH_MAP_ON_ID]);;

let MOI_SED_ECHART_SETUP = prove
 (`!c e a b (kappa:real^N->real^3).
     FINITE c /\ combinatorial_manifold 3 c /\ e IN c /\ aff_dim e = &1 /\
     moi_sed_echart c e a b kappa
     ==> ?n S. moi_sed_setup c e a b n S`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_SED_CYC_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `S:num->real^N->bool` THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[moi_sed_setup] THEN
  ASM_MESON_TAC[moi_sed_echart; SEGMENT_CONVEX_HULL]);;

let MOI_SED_SMOOTH_RT = prove
 (`!a k. smooth_map_on moi_sed_slit (moi_smo_rotz a o moi_smo_twist k)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
  REWRITE_TAC[MOI_SED_OPEN_SLIT; MOI_SED_ROTZ_LINEAR; MOI_SED_SMOOTH_TWIST]);;

let MOI_SED_SMOOTH_INV = prove
 (`!(L:real^3->real^3) k.
     linear L
     ==> open {y | y IN (:real^3) /\ L y IN moi_sed_slit} /\
         smooth_map_on {y | y IN (:real^3) /\ L y IN moi_sed_slit}
                       (moi_smo_twist k o L)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC MOI_SED_SMOOTH_COMP2 THEN
  REWRITE_TAC[OPEN_UNIV; MOI_SED_OPEN_SLIT; MOI_SED_SMOOTH_TWIST] THEN
  MATCH_MP_TAC MOI_SBA_AFFINE_SMOOTH THEN
  MAP_EVERY EXISTS_TAC [`L:real^3->real^3`; `vec 0:real^3`] THEN
  ASM_REWRITE_TAC[VECTOR_ADD_RID]);;

let MOI_SED_UHS_SLIT = prove
 (`!y:real^3. &0 < y$2 ==> y IN moi_sed_slit`,
  REWRITE_TAC[moi_sed_slit; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

let MOI_SED_ECHART_TET = prove
 (`!c e a b n (S:num->real^N->bool) (kappa:real^N->real^3) j.
     moi_sed_setup c e a b n S /\ moi_sed_echart c e a b kappa
     ==> ?A th. moi_smo_regmap (S j) A /\
                (?l y. linear l /\ !x. A x = l x + y) /\
                (!x. x IN relative_interior(S j) ==> &0 < (A x)$2) /\
                (!x. x IN S j ==> &0 <= (A x)$2) /\
                !x. x IN S j INTER moi_smo_open_star c e
                    ==> kappa x =
                        moi_smo_rotz (moi_smo_edge_factor c e * th)
                          (moi_smo_twist (moi_smo_edge_factor c e) (A x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SED_SETUP_FACTS) THEN
  SUBGOAL_THEN `(S:num->real^N->bool) j IN c /\ aff_dim(S j) = &3 /\ e SUBSET S j`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
      REWRITE_RULE[moi_sed_cyc] o MATCH_MP MOI_SED_SETUP_CYC) THEN SIMP_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_sed_echart c e a b (kappa:real^N->real^3)` THEN
  REWRITE_TAC[moi_sed_echart] THEN
  DISCH_THEN(MP_TAC o SPEC `(S:num->real^N->bool) j` o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real^N->real^3` (X_CHOOSE_THEN `th:real`
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "nonneg")
     (CONJUNCTS_THEN2 (LABEL_TAC "special") (LABEL_TAC "formula")))))))) THEN
  MAP_EVERY EXISTS_TAC [`A:real^N->real^3`; `th:real`] THEN
  SUBGOAL_THEN `?l y. linear l /\ !x. (A:real^N->real^3) x = l x + y`
  ASSUME_TAC THENL [ASM_MESON_TAC[MOI_SBA_REGMAP_AFFINE]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC;
    MATCH_MP_TAC MOI_SED_TET_UHS THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `a:real^N`; `b:real^N`] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "nonneg" ACCEPT_TAC;
    USE_THEN "formula" ACCEPT_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `j:num` o MATCH_MP MOI_SED_TET) THEN
  ABBREV_TAC `q' = moi_sed_vx a b (S:num->real^N->bool) (j + n - 1)` THEN
  ABBREV_TAC `q = moi_sed_vx a b (S:num->real^N->bool) j` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`(S:num->real^N->bool) j`; `a:real^N`; `b:real^N`; `q':real^N`;
                 `q:real^N`; `A:real^N->real^3`] MOI_SED_REG_VALUES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[moi_sed_setup]; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "vals") THEN
  MP_TAC MOI_SED_SQRT3 THEN MP_TAC MOI_SED_ALPHA THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(a:real^N = b)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_sed_setup]; ALL_TAC] THEN
  X_GEN_TAC `x:real^N` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[MOI_SBA_RELINT_4] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real` (X_CHOOSE_THEN `u2:real`
    (X_CHOOSE_THEN `u3:real` (X_CHOOSE_THEN `u4:real` STRIP_ASSUME_TAC)))) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`A:real^N->real^3`; `u1:real`; `u2:real`; `u3:real`; `u4:real`;
                 `a:real^N`; `b:real^N`; `q':real^N`; `q:real^N`]
    MOI_SBA_AFF_EVAL4) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REMOVE_THEN "vals" (DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[MOI_SED_STD_COMB_COMPONENTS];
    ONCE_REWRITE_TAC[VECTOR_ARITH
     `u1 % vec 0 + u2 % b3 + u3 % qt + u4 % pt:real^3 =
      u1 % vec 0 + u2 % b3 + u4 % pt + u3 % qt`] THEN
    REWRITE_TAC[MOI_SED_STD_COMB_COMPONENTS]] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC);;

let MOI_SED_ROTZ_NEG = prove
 (`!a y. moi_smo_rotz (--a) (moi_smo_rotz a y) = y`,
  REWRITE_TAC[MOI_SED_ROTZ_ROTZ; REAL_ADD_LINV; MOI_SED_ROTZ_0]);;

let MOI_SED_FTET_EDGE = prove
 (`!c e a b (kappa:real^N->real^3) tet.
     FINITE c /\ combinatorial_manifold 3 c /\ e IN c /\ aff_dim e = &1 /\
     moi_sed_echart c e a b kappa /\ tet IN c /\ aff_dim tet = &3 /\ e SUBSET tet
     ==> moi_sed_ftet kappa tet`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`; `b:real^N`;
                 `kappa:real^N->real^3`] MOI_SED_ECHART_SETUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_TAC `S:num->real^N->bool`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o CONJUNCT2 o MATCH_MP MOI_SED_K) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SED_SETUP_FACTS) THEN
  SUBGOAL_THEN `?j. tet = (S:num->real^N->bool) j` (X_CHOOSE_THEN `j:num`
    SUBST_ALL_TAC) THENL
   [FIRST_ASSUM(MP_TAC o last o CONJUNCTS o GEN_REWRITE_RULE I [moi_sed_cyc] o
      MATCH_MP MOI_SED_SETUP_CYC) THEN
    DISCH_THEN(MP_TAC o SPEC `tet:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                 `b:real^N`; `n:num`; `S:num->real^N->bool`; `kappa:real^N->real^3`;
                 `j:num`] MOI_SED_ECHART_TET) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real^N->real^3` (X_CHOOSE_THEN `th:real`
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "pos") (CONJUNCTS_THEN2 (LABEL_TAC "nn")
      (LABEL_TAC "formula"))))))) THEN
  ABBREV_TAC `k = moi_smo_edge_factor c (e:real^N->bool)` THEN
  SUBGOAL_THEN `!x:real^N. x IN relative_interior(S(j:num))
                           ==> x IN S j /\ x IN moi_smo_open_star c e`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
      MATCH_MP_TAC MOI_SED_RELINT_IN_STAR THEN
      EXISTS_TAC `(S:num->real^N->bool) j` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_smo_rotz (--(k * th))`; `inv k`] MOI_SED_SMOOTH_INV) THEN
  REWRITE_TAC[MOI_SED_ROTZ_LINEAR] THEN STRIP_TAC THEN
  REWRITE_TAC[moi_sed_ftet] THEN
  MAP_EVERY EXISTS_TAC
   [`A:real^N->real^3`; `moi_smo_rotz (k * th) o moi_smo_twist k`;
    `moi_smo_twist (inv k) o moi_smo_rotz (--(k * th))`; `moi_sed_slit`;
    `{y | y IN (:real^3) /\ moi_smo_rotz (--(k * th)) y IN moi_sed_slit}`] THEN
  ASM_REWRITE_TAC[MOI_SED_OPEN_SLIT; MOI_SED_SMOOTH_RT] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_UNIV; o_THM] THEN
  SUBGOAL_THEN `!x:real^N. x IN relative_interior(S(j:num))
                           ==> kappa x = moi_smo_rotz (k * th)
                                           (moi_smo_twist k (A x))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "formula" MATCH_MP_TAC THEN
    ASM_SIMP_TAC[IN_INTER];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_SED_UHS_SLIT THEN
    USE_THEN "pos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN ASM_SIMP_TAC[MOI_SED_ROTZ_NEG] THEN
    MATCH_MP_TAC MOI_SED_TWIST_SLIT THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "pos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN ASM_SIMP_TAC[MOI_SED_ROTZ_NEG] THEN
    MATCH_MP_TAC MOI_SED_TWIST_INV THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "nn" MATCH_MP_TAC THEN ASM_SIMP_TAC[]]);;

let MOI_SED_FTRI_EDGE = prove
 (`!c e a b (kappa:real^N->real^3) t.
     FINITE c /\ combinatorial_manifold 3 c /\ e IN c /\ aff_dim e = &1 /\
     moi_sed_echart c e a b kappa /\ t IN c /\ aff_dim t = &2 /\ e SUBSET t
     ==> moi_sed_ftri c kappa t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`; `b:real^N`;
                 `kappa:real^N->real^3`] MOI_SED_ECHART_SETUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_TAC `S:num->real^N->bool`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o CONJUNCT2 o MATCH_MP MOI_SED_K) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SED_SETUP_FACTS) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                 `b:real^N`; `n:num`; `S:num->real^N->bool`; `kappa:real^N->real^3`]
    MOI_SED_NF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `beta:real` (X_CHOOSE_THEN `eps:bool`
    (LABEL_TAC "nf"))) THEN
  MP_TAC(ISPECL [`beta:real`; `eps:bool`] MOI_SED_AX_INV) THEN
  DISCH_THEN(X_CHOOSE_THEN `beta0:real` (LABEL_TAC "inv")) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                 `b:real^N`; `n:num`; `S:num->real^N->bool`; `t:real^N->bool`]
    MOI_SED_TRI_CASES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` SUBST_ALL_TAC) THEN
  SUBGOAL_THEN `moi_smo_open_star c ((S:num->real^N->bool) i INTER S(SUC i))
                SUBSET moi_smo_open_star c e` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SBA_OPEN_STAR_MONO THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_sba_unf c ((S:num->real^N->bool) i INTER S(SUC i)) (moi_sed_unf a b n S i) /\
    !x. x IN moi_smo_open_star c ((S:num->real^N->bool) i INTER S(SUC i))
        ==> moi_sed_kap c e a b n S x =
            moi_smo_rotz (moi_smo_edge_factor c e * &i * moi_smo_dihedral)
              (moi_smo_twist (moi_smo_edge_factor c e) (moi_sed_unf a b n S i x)) /\
            &0 < (moi_sed_unf a b n S i x)$2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MOI_SED_UNF_UNF THEN EXISTS_TAC `e:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_SED_KAP_UNF THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC MOI_SED_UNF_POS THEN
        MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `e:real^N->bool`] THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  ABBREV_TAC `k = moi_smo_edge_factor c (e:real^N->bool)` THEN
  ABBREV_TAC `u = moi_sed_unf a b n (S:num->real^N->bool) i` THEN
  MP_TAC(ISPECL [`moi_smo_rotz (--(k * &i * moi_smo_dihedral)) o
                  moi_sed_ax beta0 eps`; `inv k`] MOI_SED_SMOOTH_INV) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC LINEAR_COMPOSE THEN
    REWRITE_TAC[MOI_SED_ROTZ_LINEAR; MOI_SED_AX_LINEAR];
    STRIP_TAC] THEN
  REWRITE_TAC[moi_sed_ftri] THEN
  MAP_EVERY EXISTS_TAC
   [`u:real^N->real^3`;
    `moi_sed_ax beta eps o (moi_smo_rotz (k * &i * moi_smo_dihedral) o
                            moi_smo_twist k)`;
    `moi_smo_twist (inv k) o (moi_smo_rotz (--(k * &i * moi_smo_dihedral)) o
                              moi_sed_ax beta0 eps)`;
    `moi_sed_slit`;
    `{y | y IN (:real^3) /\
          (moi_smo_rotz (--(k * &i * moi_smo_dihedral)) o moi_sed_ax beta0 eps) y IN
          moi_sed_slit}`] THEN
  SUBGOAL_THEN `smooth_map_on moi_sed_slit
                 (moi_sed_ax beta eps o (moi_smo_rotz (k * &i * moi_smo_dihedral) o
                                         moi_smo_twist k))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
    REWRITE_TAC[MOI_SED_OPEN_SLIT; MOI_SED_AX_LINEAR; MOI_SED_SMOOTH_RT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[MOI_SED_OPEN_SLIT] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_UNIV; o_THM] THEN
  SUBGOAL_THEN
   `!x:real^N. x IN moi_smo_open_star c (S i INTER S(SUC i))
               ==> kappa x = moi_sed_ax beta eps (moi_smo_rotz (k * &i * moi_smo_dihedral)
                                                    (moi_smo_twist k (u x)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "nf" (fun th -> W(fun (asl,w) ->
      MP_TAC(SPEC `x:real^N` th))) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_SED_UHS_SLIT THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[MOI_SED_ROTZ_NEG] THEN USE_THEN "inv" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[MOI_SED_ROTZ_NEG] THEN
    MATCH_MP_TAC MOI_SED_TWIST_SLIT THEN ASM_SIMP_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[];
      ASM_SIMP_TAC[] THEN USE_THEN "inv" (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[MOI_SED_ROTZ_NEG] THEN
      MATCH_MP_TAC MOI_SED_TWIST_INV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]]]);;

(* ------------------------------------------------------------------------- *)
(* 12. Factorizations for all three families, chart properties, and the     *)
(* local-to-global principle for smooth transition maps.                     *)
(* ------------------------------------------------------------------------- *)

let MOI_SED_STAR_MEETS = prove
 (`!c r s x:real^N.
     lf_simplicial_complex c /\ s IN c /\
     x IN moi_smo_open_star c r /\ x IN relative_interior s
     ==> r face_of s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_smo_open_star; IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (X_CHOOSE_THEN `w:real^N->bool` (CONJUNCTS_THEN2
     (X_CHOOSE_THEN `s':real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) ASSUME_TAC))) THEN
  UNDISCH_TAC `w = relative_interior(s':real^N->bool)` THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  SUBGOAL_THEN `s':real^N->bool = s` (fun th -> ASM_MESON_TAC[th]) THEN
  MATCH_MP_TAC MOI_SBA_RELINT_EQ THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
  ASM SET_TAC[]);;

let MOI_SED_FTET_ALL = prove
 (`!c U (phi:real^N->real^3) tet.
     FINITE c /\ combinatorial_manifold 3 c /\
     (U,phi) IN moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c UNION
                moi_smo_edge_atlas c /\
     tet IN c /\ aff_dim tet = &3 /\ ~(U INTER relative_interior tet = {})
     ==> relative_interior tet SUBSET U /\ moi_sed_ftet phi tet`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM UNION_ASSOC] THEN
  ONCE_REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
   [MATCH_MP_TAC MOI_SED_FTET_BASE THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  UNDISCH_TAC `(U,phi) IN moi_smo_edge_atlas (c:(real^N->bool)->bool)` THEN
  REWRITE_TAC[MOI_SED_EDGE_ATLAS_IN] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` (X_CHOOSE_THEN `a:real^N`
    (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `(e:real^N->bool) face_of tet` ASSUME_TAC THENL
   [UNDISCH_TAC `~(moi_smo_open_star c e INTER relative_interior tet:real^N->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC MOI_SED_STAR_MEETS THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `x:real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; moi_smo_open_star; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    EXISTS_TAC `relative_interior tet:real^N->bool` THEN ASM_MESON_TAC[];
    MATCH_MP_TAC MOI_SED_FTET_EDGE THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `e:real^N->bool`; `a:real^N`;
                          `b:real^N`] THEN
    ASM_MESON_TAC[FACE_OF_IMP_SUBSET]]);;

let MOI_SED_FTRI_ALL = prove
 (`!c U (phi:real^N->real^3) t.
     FINITE c /\ combinatorial_manifold 3 c /\
     (U,phi) IN moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c UNION
                moi_smo_edge_atlas c /\
     t IN c /\ aff_dim t = &2 /\ ~(U INTER relative_interior t = {})
     ==> moi_smo_open_star c t SUBSET U /\ moi_sed_ftri c phi t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM UNION_ASSOC] THEN
  ONCE_REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
   [MATCH_MP_TAC MOI_SED_FTRI_BASE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  UNDISCH_TAC `(U,phi) IN moi_smo_edge_atlas (c:(real^N->bool)->bool)` THEN
  REWRITE_TAC[MOI_SED_EDGE_ATLAS_IN] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` (X_CHOOSE_THEN `a:real^N`
    (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `(e:real^N->bool) face_of t` ASSUME_TAC THENL
   [UNDISCH_TAC `~(moi_smo_open_star c e INTER relative_interior t:real^N->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC MOI_SED_STAR_MEETS THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `x:real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_SBA_OPEN_STAR_MONO THEN ASM_MESON_TAC[FACE_OF_IMP_SUBSET];
    MATCH_MP_TAC MOI_SED_FTRI_EDGE THEN
    MAP_EVERY EXISTS_TAC [`e:real^N->bool`; `a:real^N`; `b:real^N`] THEN
    ASM_MESON_TAC[FACE_OF_IMP_SUBSET]]);;

let moi_sed_chartp = new_definition
 `moi_sed_chartp (c:(real^N->bool)->bool) U (phi:real^N->real^3) <=>
    open_in (subtopology euclidean (UNIONS c)) U /\ phi continuous_on U /\
    (!x y. x IN U /\ y IN U /\ phi x = phi y ==> x = y) /\
    ?v. {v} IN c /\ U SUBSET moi_smo_open_star c {v}`;;

let MOI_SED_CHARTP_ALL = prove
 (`!c U (phi:real^N->real^3).
     FINITE c /\ combinatorial_manifold 3 c /\
     (U,phi) IN moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c UNION
                moi_smo_edge_atlas c
     ==> moi_sed_chartp c U phi`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool) /\
                (!s. s IN c ==> aff_dim s <= &3)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold; MOI_SBA_DIM_LE3]; ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN c /\ ~(s = {})
                ==> ?v. {v} IN c /\ moi_smo_open_star c s SUBSET
                                    moi_smo_open_star c {v}` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`]
      MOI_SBA_EXTREME_EXISTS) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real^N` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_SBA_OPEN_STAR_MONO THEN
    ASM_REWRITE_TAC[SING_SUBSET];
    ALL_TAC] THEN
  UNDISCH_TAC `(U,phi) IN moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c UNION
               moi_smo_edge_atlas (c:(real^N->bool)->bool)` THEN
  REWRITE_TAC[IN_UNION; MOI_SBA_TET_ATLAS_IN2; MOI_SBA_UNFOLD_ATLAS_IN;
              MOI_SED_EDGE_ATLAS_IN] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[moi_sed_chartp] THENL
   [SUBGOAL_THEN `moi_smo_open_star c (tet:real^N->bool) = relative_interior tet`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_SBA_OPEN_STAR_TET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC MOI_SBA_OPEN_STAR_OPEN THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_SBA_AFFINE_CONTINUOUS_ON THEN
      MATCH_MP_TAC MOI_SBA_REGMAP_AFFINE THEN EXISTS_TAC `tet:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tet:real^N->bool`;
                     `phi:real^N->real^3`] MOI_SED_REGMAP_LEFT_INV) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `B:real^3->real^N` (CONJUNCTS_THEN2 ASSUME_TAC
        (LABEL_TAC "inv"))) THEN
      MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(x:real^N) IN tet /\ (y:real^N) IN tet` STRIP_ASSUME_TAC THENL
       [MP_TAC(ISPEC `tet:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
        UNDISCH_TAC `(x:real^N) IN relative_interior tet` THEN
        UNDISCH_TAC `(y:real^N) IN relative_interior tet` THEN SET_TAC[];
        ALL_TAC] THEN
      REMOVE_THEN "inv" (fun th ->
        MP_TAC(MATCH_MP th (ASSUME `(x:real^N) IN tet`)) THEN
        MP_TAC(MATCH_MP th (ASSUME `(y:real^N) IN tet`))) THEN
      UNDISCH_TAC `(phi:real^N->real^3) x = phi y` THEN MESON_TAC[];
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN UNDISCH_TAC `aff_dim(tet:real^N->bool) = &3` THEN
      ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC];
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_SBA_OPEN_STAR_OPEN THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_SBA_UNF_CONTINUOUS THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `moi_sba_unf c t (phi:real^N->real^3)` THEN
      REWRITE_TAC[moi_sba_unf] THEN DISCH_THEN(ACCEPT_TAC o CONJUNCT1);
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN UNDISCH_TAC `aff_dim(t:real^N->bool) = &2` THEN
      ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC];
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_SBA_OPEN_STAR_OPEN THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_SED_ECHART_CONT THEN
      MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`] THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `moi_sed_echart c e a b (phi:real^N->real^3)` THEN
      REWRITE_TAC[moi_sed_echart] THEN DISCH_THEN(ACCEPT_TAC o CONJUNCT1);
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN UNDISCH_TAC `aff_dim(e:real^N->bool) = &1` THEN
      ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* 13. Every chart of the three families lives on an open star; local      *)
(* smooth transitions near every point; the local-to-global principle; C4  *)
(* part 3 and the edge statement MOI_SMO_EDGE.                              *)
(* ------------------------------------------------------------------------- *)

let MOI_SED_ALL3_STAR = prove
 (`!c U (phi:real^N->real^3).
     FINITE c /\ combinatorial_manifold 3 c /\
     (U,phi) IN moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c UNION
                moi_smo_edge_atlas c
     ==> ?r. r IN c /\ &1 <= aff_dim r /\ U = moi_smo_open_star c r /\
             (aff_dim r = &1 ==> ?a b. moi_sed_echart c r a b phi)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool) /\
                (!s. s IN c ==> aff_dim s <= &3)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold; MOI_SBA_DIM_LE3]; ALL_TAC] THEN
  UNDISCH_TAC `(U,phi) IN moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c UNION
               moi_smo_edge_atlas (c:(real^N->bool)->bool)` THEN
  REWRITE_TAC[IN_UNION; MOI_SBA_TET_ATLAS_IN2; MOI_SBA_UNFOLD_ATLAS_IN;
              MOI_SED_EDGE_ATLAS_IN] THEN
  STRIP_TAC THENL
   [EXISTS_TAC `tet:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC INT_REDUCE_CONV THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_SBA_OPEN_STAR_TET THEN
    ASM_REWRITE_TAC[];
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC INT_REDUCE_CONV;
    EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC INT_REDUCE_CONV THEN ASM_MESON_TAC[]]);;

let MOI_SED_LOCAL_TRANS = prove
 (`!c U1 (phi1:real^N->real^3) U2 phi2.
     FINITE c /\ combinatorial_manifold 3 c /\
     (U1,phi1) IN moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c UNION
                  moi_smo_edge_atlas c /\
     (U2,phi2) IN moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c UNION
                  moi_smo_edge_atlas c
     ==> !x. x IN U1 INTER U2
             ==> ?W g O. open_in (subtopology euclidean (UNIONS c)) W /\ x IN W /\
                         W SUBSET U1 INTER U2 /\ open O /\
                         IMAGE phi1 W SUBSET O /\ smooth_map_on O g /\
                         !z. z IN W ==> g(phi1 z) = phi2 z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool) /\
                simplicial_complex c /\
                (!s. s IN c ==> aff_dim s <= &3)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold; MOI_SBA_DIM_LE3; MOI_SCF_CM_FACTS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `U1:real^N->bool`;
                 `phi1:real^N->real^3`] MOI_SED_ALL3_STAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `U2:real^N->bool`;
                 `phi2:real^N->real^3`] MOI_SED_ALL3_STAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?s:real^N->bool. s IN c /\ x IN relative_interior s`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SBA_CARRIER THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `r1:real^N->bool`]
      MOI_SBA_STAR_SUBSET_UNIONS) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(r1:real^N->bool) face_of s /\ (r2:real^N->bool) face_of s`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_SED_STAR_MEETS THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `x:real^N`] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(r1:real^N->bool) <= aff_dim(s:real^N->bool) /\
                aff_dim(r2:real^N->bool) <= aff_dim s` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[AFF_DIM_SUBSET; FACE_OF_IMP_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(s:real^N->bool) = &3 \/ aff_dim s = &2 \/ aff_dim s = &1`
  MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `U1:real^N->bool`;
                   `phi1:real^N->real^3`; `s:real^N->bool`] MOI_SED_FTET_ALL) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `U2:real^N->bool`;
                   `phi2:real^N->real^3`; `s:real^N->bool`] MOI_SED_FTET_ALL) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`;
                   `phi1:real^N->real^3`; `phi2:real^N->real^3`]
      MOI_SED_TRANS_TET) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^3->real^3` (X_CHOOSE_THEN `O:real^3->bool`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`relative_interior s:real^N->bool`; `g:real^3->real^3`;
                          `O:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `relative_interior s = moi_smo_open_star c (s:real^N->bool)`
      SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_SBA_OPEN_STAR_TET THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC MOI_SBA_OPEN_STAR_OPEN THEN ASM_REWRITE_TAC[]];
      ASM SET_TAC[]];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `U1:real^N->bool`;
                   `phi1:real^N->real^3`; `s:real^N->bool`] MOI_SED_FTRI_ALL) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `U2:real^N->bool`;
                   `phi2:real^N->real^3`; `s:real^N->bool`] MOI_SED_FTRI_ALL) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`;
                   `phi1:real^N->real^3`; `phi2:real^N->real^3`]
      MOI_SED_TRANS_TRI) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^3->real^3` (X_CHOOSE_THEN `O:real^3->bool`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`moi_smo_open_star c s:real^N->bool`; `g:real^3->real^3`;
                          `O:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_SBA_OPEN_STAR_OPEN THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`]
        MOI_SBA_RELINT_IN_STAR) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ASM SET_TAC[]];
    SUBGOAL_THEN `(r1:real^N->bool) = s /\ (r2:real^N->bool) = s`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC MOI_SCF_SUBSET_DIM_EQ THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET; INT_LE_ANTISYM];
      ALL_TAC] THEN
    UNDISCH_TAC `(r1:real^N->bool) = s` THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `(r2:real^N->bool) = s` THEN DISCH_THEN SUBST_ALL_TAC THEN
    SUBGOAL_THEN `(?a b. moi_sed_echart c s a b (phi1:real^N->real^3)) /\
                  (?a b. moi_sed_echart c s a b (phi2:real^N->real^3))`
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `a:real^N` (X_CHOOSE_TAC `b:real^N`))
                     (X_CHOOSE_THEN `a':real^N` (X_CHOOSE_TAC `b':real^N`)))
    THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`; `a:real^N`;
                   `b:real^N`; `a':real^N`; `b':real^N`; `phi1:real^N->real^3`;
                   `phi2:real^N->real^3`] MOI_SED_SAME_EDGE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `L:real^3->real^3` (CONJUNCTS_THEN2 ASSUME_TAC
      ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`moi_smo_open_star c s:real^N->bool`; `L:real^3->real^3`;
                          `(:real^3)`] THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; INTER_IDEMPOT; SUBSET_REFL] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_SBA_OPEN_STAR_OPEN THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `(x:real^N) IN U1 INTER U2` THEN ASM_REWRITE_TAC[IN_INTER] THEN
      SIMP_TAC[];
      MATCH_MP_TAC MOI_SBA_AFFINE_SMOOTH THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]]]);;

let MOI_SED_LTG = prove
 (`!c (U:real^N->bool) (phi:real^N->real^3) V (psi:real^N->real^3).
     FINITE c /\ combinatorial_manifold 3 c /\ moi_sed_chartp c U phi /\
     open_in (subtopology euclidean (UNIONS c)) V /\
     (!x. x IN U INTER V
          ==> ?W g O. open_in (subtopology euclidean (UNIONS c)) W /\ x IN W /\
                      W SUBSET U INTER V /\ open O /\ IMAGE phi W SUBSET O /\
                      smooth_map_on O g /\ !z. z IN W ==> g(phi z) = psi z)
     ==> ?g. smooth_map_on (IMAGE phi (U INTER V)) g /\
             !x. x IN U INTER V ==> g(phi x) = psi x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_sed_chartp] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (LABEL_TAC "loc"))))) THEN
  SUBGOAL_THEN `!W. open_in (subtopology euclidean (UNIONS c)) W /\ W SUBSET U
                    ==> open (IMAGE (phi:real^N->real^3) W)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `W:real^N->bool`;
                   `phi:real^N->real^3`] MOI_SBA_IOD_FWD) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM SET_TAC[];
        ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
        ASM SET_TAC[]];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN U INTER V
                    ==> (@z:real^N. z IN U INTER V /\
                                    (phi:real^N->real^3) z = phi x) = x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN
    X_GEN_TAC `y:real^N` THEN EQ_TAC THENL
     [STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        try (let v,_ = dest_forall(concl th) in type_of v = `:real^N`) &&
            can (find_term (fun t -> t = `(phi:real^N->real^3)`)) (concl th)
        with Failure _ -> false)) THEN
      ASM SET_TAC[];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `\y:real^3. (psi:real^N->real^3)
                 (@z:real^N. z IN U INTER V /\ (phi:real^N->real^3) z = y)` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
  SUBGOAL_THEN `open(IMAGE (phi:real^N->real^3) (U INTER V))` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[]; SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[smooth_map_on] THEN X_GEN_TAC `m:num` THEN
  ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_LOCAL_OPEN] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  USE_THEN "loc" (fun th -> MP_TAC(MATCH_MP th
    (ASSUME `(x:real^N) IN U INTER V`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `W:real^N->bool` (X_CHOOSE_THEN `g:real^3->real^3`
    (X_CHOOSE_THEN `O:real^3->bool` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `IMAGE (phi:real^N->real^3) W` THEN REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ASM SET_TAC[];
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (IMAGE (phi:real^N->real^3) W)
                 (\y. (psi:real^N->real^3) (@z. z IN U INTER V /\ phi z = y))`
  MP_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN EXISTS_TAC `g:real^3->real^3` THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(z:real^N) IN U INTER V` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `O:real^3->bool` THEN
      ASM_REWRITE_TAC[]];
    SIMP_TAC[smooth_map_on]]);;

let MOI_SED_EDGE_PART3 = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold 3 c
     ==> !U kappa V phi.
           (U,kappa) IN moi_smo_edge_atlas c /\
           (V,phi) IN moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c UNION
                      moi_smo_edge_atlas c
           ==> (?g. smooth_map_on (IMAGE kappa (U INTER V)) g /\
                    !x. x IN U INTER V ==> g(kappa x) = phi x) /\
               (?g. smooth_map_on (IMAGE phi (U INTER V)) g /\
                    !x. x IN U INTER V ==> g(phi x) = kappa x)`,
  GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(U,kappa) IN moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c UNION
                moi_smo_edge_atlas (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_UNION]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_sed_chartp c U (kappa:real^N->real^3) /\
                moi_sed_chartp c V (phi:real^N->real^3)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_SED_CHARTP_ALL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_SED_LTG THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[moi_sed_chartp];
      MATCH_MP_TAC MOI_SED_LOCAL_TRANS THEN ASM_REWRITE_TAC[]];
    ONCE_REWRITE_TAC[INTER_COMM] THEN
    MATCH_MP_TAC MOI_SED_LTG THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[moi_sed_chartp];
      MATCH_MP_TAC MOI_SED_LOCAL_TRANS THEN ASM_REWRITE_TAC[]]]);;

let MOI_SMO_EDGE = prove
 (`!u:N->bool. MOI_SMO_EDGE_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[MOI_SMO_EDGE_STATEMENT] THEN
  X_GEN_TAC `c:(real^N->bool)->bool` THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_SED_EDGE_PART1 THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_SED_EDGE_PART2 THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_SED_EDGE_PART3 THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 14. The punctured atlas (C5): the three families form a smooth atlas on  *)
(* the polyhedron minus its vertices.                                        *)
(* ------------------------------------------------------------------------- *)

let MOI_SED_SK1_OPEN = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ lf_simplicial_complex c
     ==> open_in (subtopology euclidean (UNIONS c))
                 (UNIONS c DIFF UNIONS {e | e IN c /\ aff_dim e <= &1})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `UNIONS c DIFF UNIONS {e | e IN c /\ aff_dim e <= &1} =
                UNIONS c INTER ((:real^N) DIFF UNIONS {e | e IN c /\ aff_dim e <= &1})`
  SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN REWRITE_TAC[GSYM closed] THEN
  MATCH_MP_TAC CLOSED_UNIONS THEN
  ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM] THEN
  ASM_MESON_TAC[MOI_SBA_LF_CONVEX]);;

let MOI_SED_VERTS_SK1 = prove
 (`!c:(real^N->bool)->bool.
     {v | {v} IN c} SUBSET UNIONS {e | e IN c /\ aff_dim e <= &1}`,
  GEN_TAC THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNIONS] THEN
  X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN EXISTS_TAC `{v:real^N}` THEN
  ASM_REWRITE_TAC[AFF_DIM_SING; IN_SING] THEN INT_ARITH_TAC);;

let MOI_SED_EDGE_STAR_NOVERT = prove
 (`!c e:real^N->bool.
     lf_simplicial_complex c /\ e IN c /\ aff_dim e = &1
     ==> moi_smo_open_star c e SUBSET (UNIONS c DIFF {v | {v} IN c})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; IN_DIFF; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_SBA_STAR_SUBSET_UNIONS; SUBSET]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `{x:real^N}`;
                 `x:real^N`] MOI_SED_STAR_MEETS) THEN
  ASM_REWRITE_TAC[RELATIVE_INTERIOR_SING; IN_SING] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`e:real^N->bool`; `{x:real^N}`] AFF_DIM_SUBSET) THEN
  ASM_SIMP_TAC[FACE_OF_IMP_SUBSET; AFF_DIM_SING] THEN INT_ARITH_TAC);;

let MOI_SED_PUNCT_COVER = prove
 (`!c x:real^N.
     FINITE c /\ combinatorial_manifold 3 c /\ MOI_SMO_EDGE_STATEMENT (u:N->bool) /\
     x IN UNIONS c /\ ~(x IN {v | {v} IN c}) /\
     x IN UNIONS {e | e IN c /\ aff_dim e <= &1}
     ==> ?U phi. (U,phi) IN moi_smo_edge_atlas c /\ x IN U`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `x:real^N`] MOI_SBA_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(x:real^N) IN UNIONS {e | e IN c /\ aff_dim e <= &1}` THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`; `e:real^N->bool`]
    MOI_SBA_RELINT_MEETS) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `aff_dim(s:real^N->bool) = &1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^N->bool`; `e:real^N->bool`] AFF_DIM_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(aff_dim(s:real^N->bool) = -- &1) /\ ~(aff_dim s = &0)`
    MP_TAC THENL
     [REWRITE_TAC[AFF_DIM_EQ_MINUS1; AFF_DIM_EQ_0] THEN CONJ_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN
        UNDISCH_TAC `(x:real^N) IN relative_interior {}` THEN
        REWRITE_TAC[RELATIVE_INTERIOR_EMPTY; NOT_IN_EMPTY];
        DISCH_THEN(X_CHOOSE_THEN `w:real^N` SUBST_ALL_TAC) THEN
        UNDISCH_TAC `(x:real^N) IN relative_interior {w}` THEN
        REWRITE_TAC[RELATIVE_INTERIOR_SING; IN_SING] THEN DISCH_THEN SUBST_ALL_TAC THEN
        UNDISCH_TAC `~((w:real^N) IN {v | {v} IN c})` THEN
        ASM_REWRITE_TAC[IN_ELIM_THM]];
      MP_TAC(ISPEC `s:real^N->bool` AFF_DIM_GE) THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `?v:real^N. v extreme_point_of s` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`]
      MOI_SBA_EXTREME_EXISTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `(x:real^N) IN relative_interior {}` THEN
      REWRITE_TAC[RELATIVE_INTERIOR_EMPTY; NOT_IN_EMPTY];
      MESON_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `MOI_SMO_EDGE_STATEMENT (u:N->bool)` THEN
  REWRITE_TAC[MOI_SMO_EDGE_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `c:(real^N->bool)->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`s:real^N->bool`; `v:real^N`] o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `kappa:real^N->real^3` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`moi_smo_open_star c (s:real^N->bool)`;
                        `kappa:real^N->real^3`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`]
    MOI_SBA_RELINT_IN_STAR) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;
let MOI_SED_IN_ALL3 = prove
 (`!c (p:(real^N->bool)#(real^N->real^3)).
     p IN moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c UNION moi_smo_edge_atlas c <=>
     p IN moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c \/ p IN moi_smo_edge_atlas c`,
  REWRITE_TAC[IN_UNION; DISJ_ASSOC]);;

let MOI_SED_Q_SUBSET_P = prove
 (`!c:(real^N->bool)->bool.
     UNIONS c DIFF UNIONS {e | e IN c /\ aff_dim e <= &1} SUBSET
     UNIONS c DIFF {v | {v} IN c}`,
  GEN_TAC THEN MATCH_MP_TAC(SET_RULE
   `(A:real^N->bool) SUBSET B ==> (X:real^N->bool) DIFF B SUBSET X DIFF A`) THEN
  REWRITE_TAC[MOI_SED_VERTS_SK1]);;

let MOI_SED_PUNCT_CHART = prove
 (`!c U (phi:real^N->real^3).
     FINITE c /\ combinatorial_manifold 3 c /\
     MOI_SMO_BASE_STATEMENT (u:N->bool) /\ MOI_SMO_EDGE_STATEMENT (u:N->bool) /\
     (U,phi) IN moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c UNION
                moi_smo_edge_atlas c
     ==> open_in (subtopology euclidean (UNIONS c DIFF {v | {v} IN c})) U /\
         open (IMAGE phi U) /\
         homeomorphic_map
           (subtopology (subtopology euclidean (UNIONS c DIFF {v | {v} IN c})) U,
            subtopology euclidean (IMAGE phi U)) phi`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOI_SED_IN_ALL3] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THENL
   [UNDISCH_TAC `MOI_SMO_BASE_STATEMENT (u:N->bool)` THEN
    REWRITE_TAC[MOI_SMO_BASE_STATEMENT; smooth_manifold_atlas] THEN
    DISCH_THEN(MP_TAC o SPEC `c:(real^N->bool)->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`U:real^N->bool`; `phi:real^N->real^3`] o
               CONJUNCT1 o CONJUNCT1) THEN
    ASM_REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    SUBGOAL_THEN `(U:real^N->bool) SUBSET
                  UNIONS c DIFF UNIONS {e | e IN c /\ aff_dim e <= &1}` ASSUME_TAC THENL
     [FIRST_ASSUM(ACCEPT_TAC o MATCH_MP OPEN_IN_IMP_SUBSET); ALL_TAC] THEN
    MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_SED_Q_SUBSET_P) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(UNIONS c DIFF UNIONS {e | e IN c /\ aff_dim e <= &1}) INTER U = U /\
                  (UNIONS c DIFF {v | {v} IN c}) INTER U = (U:real^N->bool)`
    (fun th -> REWRITE_TAC[th]) THENL
     [MAP_EVERY UNDISCH_TAC
       [`(U:real^N->bool) SUBSET UNIONS c DIFF UNIONS {e | e IN c /\ aff_dim e <= &1}`;
        `UNIONS c DIFF UNIONS {e | e IN c /\ aff_dim e <= &1} SUBSET
         UNIONS c DIFF {v:real^N | {v} IN c}`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN EXISTS_TAC `UNIONS c:real^N->bool` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_TRANS THEN
      EXISTS_TAC `UNIONS c DIFF UNIONS {e | e IN c /\ aff_dim e <= &1}:real^N->bool` THEN
      ASM_SIMP_TAC[MOI_SED_SK1_OPEN];
      MAP_EVERY UNDISCH_TAC
       [`(U:real^N->bool) SUBSET UNIONS c DIFF UNIONS {e | e IN c /\ aff_dim e <= &1}`;
        `UNIONS c DIFF UNIONS {e | e IN c /\ aff_dim e <= &1} SUBSET
         UNIONS c DIFF {v:real^N | {v} IN c}`] THEN
      SET_TAC[];
      SET_TAC[]];
    UNDISCH_TAC `MOI_SMO_EDGE_STATEMENT (u:N->bool)` THEN
    REWRITE_TAC[MOI_SMO_EDGE_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPEC `c:(real^N->bool)->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`U:real^N->bool`; `phi:real^N->real^3`] o
               CONJUNCT1 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    SUBGOAL_THEN `(U:real^N->bool) SUBSET UNIONS c DIFF {v | {v} IN c}`
    ASSUME_TAC THENL
     [UNDISCH_TAC `(U,phi) IN moi_smo_edge_atlas (c:(real^N->bool)->bool)` THEN
      REWRITE_TAC[MOI_SED_EDGE_ATLAS_IN] THEN
      DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` (X_CHOOSE_THEN `a:real^N`
        (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC))) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_SED_EDGE_STAR_NOVERT THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(UNIONS c DIFF {v | {v} IN c}) INTER U = (U:real^N->bool)`
    (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `(U:real^N->bool) SUBSET UNIONS c DIFF {v | {v} IN c}` THEN
      SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN EXISTS_TAC `UNIONS c:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

let MOI_SED_PUNCT_COVER2 = prove
 (`!c x:real^N.
     FINITE c /\ combinatorial_manifold 3 c /\
     MOI_SMO_BASE_STATEMENT (u:N->bool) /\ MOI_SMO_EDGE_STATEMENT (u:N->bool) /\
     x IN UNIONS c DIFF {v | {v} IN c}
     ==> ?U phi. (U,phi) IN moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c UNION
                            moi_smo_edge_atlas c /\ x IN U`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
  REWRITE_TAC[MOI_SED_IN_ALL3] THEN
  ASM_CASES_TAC `(x:real^N) IN UNIONS {e | e IN c /\ aff_dim e <= &1}` THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `x:real^N`] MOI_SED_PUNCT_COVER) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    UNDISCH_TAC `MOI_SMO_BASE_STATEMENT (u:N->bool)` THEN
    REWRITE_TAC[MOI_SMO_BASE_STATEMENT; smooth_manifold_atlas] THEN
    DISCH_THEN(MP_TAC o SPEC `c:(real^N->bool)->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N` o CONJUNCT1 o CONJUNCT2 o CONJUNCT1) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; IN_DIFF] THEN MESON_TAC[]]);;

let MOI_SED_PUNCT_TRANS = prove
 (`!c U (phi:real^N->real^3) V psi.
     FINITE c /\ combinatorial_manifold 3 c /\
     MOI_SMO_BASE_STATEMENT (u:N->bool) /\ MOI_SMO_EDGE_STATEMENT (u:N->bool) /\
     (U,phi) IN moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c UNION
                moi_smo_edge_atlas c /\
     (V,psi) IN moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c UNION
                moi_smo_edge_atlas c
     ==> ?g. smooth_map_on (IMAGE phi (U INTER V)) g /\
             !x. x IN U INTER V ==> g(phi x) = psi x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `(U,phi) IN moi_smo_edge_atlas (c:(real^N->bool)->bool)` THENL
   [UNDISCH_TAC `MOI_SMO_EDGE_STATEMENT (u:N->bool)` THEN
    REWRITE_TAC[MOI_SMO_EDGE_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPEC `c:(real^N->bool)->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`U:real^N->bool`; `phi:real^N->real^3`;
                               `V:real^N->bool`; `psi:real^N->real^3`] o
               CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o CONJUNCT1);
    ALL_TAC] THEN
  ASM_CASES_TAC `(V,psi) IN moi_smo_edge_atlas (c:(real^N->bool)->bool)` THENL
   [UNDISCH_TAC `MOI_SMO_EDGE_STATEMENT (u:N->bool)` THEN
    REWRITE_TAC[MOI_SMO_EDGE_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPEC `c:(real^N->bool)->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`V:real^N->bool`; `psi:real^N->real^3`;
                               `U:real^N->bool`; `phi:real^N->real^3`] o
               CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    REWRITE_TAC[INTER_COMM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(U,phi) IN moi_smo_tet_atlas c UNION moi_smo_unfold_atlas (c:(real^N->bool)->bool) /\
    (V,psi) IN moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(U,phi) IN moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c UNION
                  moi_smo_edge_atlas (c:(real^N->bool)->bool)`;
      `(V,psi) IN moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c UNION
                  moi_smo_edge_atlas (c:(real^N->bool)->bool)`;
      `~((U,phi) IN moi_smo_edge_atlas (c:(real^N->bool)->bool))`;
      `~((V,psi) IN moi_smo_edge_atlas (c:(real^N->bool)->bool))`] THEN
    REWRITE_TAC[MOI_SED_IN_ALL3] THEN MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `MOI_SMO_BASE_STATEMENT (u:N->bool)` THEN
  REWRITE_TAC[MOI_SMO_BASE_STATEMENT; smooth_manifold_atlas] THEN
  DISCH_THEN(MP_TAC o SPEC `c:(real^N->bool)->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`U:real^N->bool`; `phi:real^N->real^3`;
                             `V:real^N->bool`; `psi:real^N->real^3`] o
             CONJUNCT2 o CONJUNCT2 o CONJUNCT1) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let MOI_SMO_PUNCTURED_FROM_PARTS = prove
 (`!u:N->bool. MOI_SMO_CF_STATEMENT u /\ MOI_SMO_BASE_STATEMENT u /\
               MOI_SMO_EDGE_STATEMENT u ==> MOI_SMO_PUNCTURED_STATEMENT u`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[MOI_SMO_PUNCTURED_STATEMENT] THEN
  X_GEN_TAC `c:(real^N->bool)->bool` THEN STRIP_TAC THEN
  REWRITE_TAC[smooth_manifold_atlas; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`U:real^N->bool`; `phi:real^N->real^3`] THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_SED_PUNCT_CHART THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_SED_PUNCT_COVER2 THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`U:real^N->bool`; `phi:real^N->real^3`;
                         `V:real^N->bool`; `psi:real^N->real^3`] THEN
    STRIP_TAC THEN MATCH_MP_TAC MOI_SED_PUNCT_TRANS THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]]);;

let MOI_SMO_PUNCTURED = prove
 (`!u:N->bool. MOI_SMO_PUNCTURED_STATEMENT u`,
  GEN_TAC THEN MATCH_MP_TAC MOI_SMO_PUNCTURED_FROM_PARTS THEN
  REWRITE_TAC[MOI_SMO_CF; MOI_SMO_BASE; MOI_SMO_EDGE]);;


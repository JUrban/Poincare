(* ========================================================================= *)
(* pc_lrg_constcurv: the curvature tensor of a metric field with constant    *)
(* sectional curvature k at a point,                                         *)
(*   lriemann G y u v w = k((v.Gw)u - (u.Gw)v)   (APX_CONST_CURV_RIEMANN),   *)
(* by the standard polarization argument from the algebraic symmetries of    *)
(* pc_lrg.  Used for N7 of the neck layer (pc_apx_neck); kept in a small     *)
(* file so that the geodesics layer can derive MFD_SECTIONAL_CONST_RIEMANN   *)
(* without loading the Appendix files.                                       *)
(* ========================================================================= *)

needs "src/pc_lrg_stab.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Positivity of the denominator of lsectional off collinear pairs, and      *)
(* APX_CONST_CURV_RIEMANN.                                                   *)
(* ------------------------------------------------------------------------- *)

let APX_SECT_DEN_POS = prove
 (`!s (G:real^N->real^N^N) y u v.
        metric_field s G /\ y IN s /\ ~collinear {vec 0,u,v}
        ==> &0 < (u dot (G y ** u)) * (v dot (G y ** v)) - (u dot (G y ** v)) pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `M:real^N^N` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP LRG_FRAME_DOT th)]) THEN
  REWRITE_TAC[GSYM NORM_POW_2] THEN
  SUBGOAL_THEN `~collinear {vec 0,(M:real^N^N) ** u,M ** v}` MP_TAC THENL
   [SUBGOAL_THEN
     `{vec 0,(M:real^N^N) ** u,M ** v} = IMAGE (\z. M ** z) {vec 0,u,v}`
    SUBST1_TAC THENL
     [REWRITE_TAC[IMAGE_CLAUSES; MATRIX_VECTOR_MUL_RZERO]; ALL_TAC] THEN
    MP_TAC(ISPECL [`\z:real^N. (M:real^N^N) ** z`; `{vec 0:real^N,u,v}`]
                  COLLINEAR_LINEAR_IMAGE_EQ) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN
      REWRITE_TAC[GSYM MATRIX_LEFT_INVERTIBLE_INJECTIVE] THEN
      ASM_MESON_TAC[INVERTIBLE_LEFT_INVERSE];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SPEC_TAC(`(M:real^N^N) ** v`,`b:real^N`) THEN
  SPEC_TAC(`(M:real^N^N) ** u`,`a:real^N`) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM NORM_CAUCHY_SCHWARZ_EQUAL] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`] NORM_CAUCHY_SCHWARZ_ABS) THEN DISCH_TAC THEN
  SUBGOAL_THEN `abs((a:real^N) dot b) pow 2 < (norm a * norm b) pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[REAL_ABS_POS; ARITH] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_POW2_ABS; REAL_POW_MUL] THEN REAL_ARITH_TAC]);;

(* Constant sectional curvature k at y determines the curvature tensor. *)

let APX_CONST_CURV_RIEMANN = prove
 (`!s (G:real^N->real^N^N) y k.
        metric_field s G /\ y IN s /\
        (!u v. ~collinear {vec 0,u,v} ==> lsectional G y u v = k)
        ==> !u v w. lriemann G y u v w =
                    k % ((v dot (G y ** w)) % u - (u dot (G y ** w)) % v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
                LRIEMANN_TRILINEAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> let a,b = CONJ_PAIR th in let b,c = CONJ_PAIR b in
    ASSUME_TAC(GEN_ALL(MATCH_MP LINEAR_ADD (SPEC_ALL a))) THEN
    ASSUME_TAC(GEN_ALL(MATCH_MP LINEAR_ADD (SPEC_ALL b))) THEN
    ASSUME_TAC(GEN_ALL(MATCH_MP LINEAR_ADD (SPEC_ALL c))) THEN
    ASSUME_TAC(GEN_ALL(MATCH_MP LINEAR_CMUL (SPEC_ALL a))) THEN
    ASSUME_TAC(GEN_ALL(MATCH_MP LINEAR_CMUL (SPEC_ALL b)))) THEN
  RULE_ASSUM_TAC BETA_RULE THEN
  SUBGOAL_THEN `!a b. a dot ((G:real^N->real^N^N) y ** b) = b dot (G y ** a)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC LRG_METRIC_SYM THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `TQ = \a b c d:real^N.
          c dot ((G:real^N->real^N^N) y ** lriemann G y a b d) -
          k * ((a dot (G y ** c)) * (b dot (G y ** d)) -
               (a dot (G y ** d)) * (b dot (G y ** c)))` THEN
  SUBGOAL_THEN
   `(!a1 a2 b c d. (TQ:real^N->real^N->real^N->real^N->real) (a1 + a2) b c d =
                   TQ a1 b c d + TQ a2 b c d) /\
    (!a b1 b2 c d. (TQ:real^N->real^N->real^N->real^N->real) a (b1 + b2) c d =
                   TQ a b1 c d + TQ a b2 c d) /\
    (!a b c1 c2 d. (TQ:real^N->real^N->real^N->real^N->real) a b (c1 + c2) d =
                   TQ a b c1 d + TQ a b c2 d) /\
    (!a b c d1 d2. (TQ:real^N->real^N->real^N->real^N->real) a b c (d1 + d2) =
                   TQ a b c d1 + TQ a b c d2)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "TQ" THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; DOT_LADD; DOT_RADD] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!a b c d. (TQ:real^N->real^N->real^N->real^N->real) b a c d = --(TQ a b c d)) /\
    (!a b c d. (TQ:real^N->real^N->real^N->real^N->real) c d a b = TQ a b c d) /\
    (!a b c z. (TQ:real^N->real^N->real^N->real^N->real) a b z c + TQ b c z a +
               TQ c a z b = &0)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "TQ" THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
     [MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                     `a:real^N`; `b:real^N`; `d:real^N`; `c:real^N`] LRG_RM_ANTI1) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
      MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                     `a:real^N`; `b:real^N`; `d:real^N`; `c:real^N`]
                    LRIEMANN_PAIR_SYM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      MP_TAC(SPECL [`c:real^N`; `a:real^N`] (ASSUME `!a b. a dot ((G:real^N->real^N^N) y ** b) = b dot (G y ** a)`)) THEN
      MP_TAC(SPECL [`d:real^N`; `b:real^N`] (ASSUME `!a b. a dot ((G:real^N->real^N^N) y ** b) = b dot (G y ** a)`)) THEN
      MP_TAC(SPECL [`c:real^N`; `b:real^N`] (ASSUME `!a b. a dot ((G:real^N->real^N^N) y ** b) = b dot (G y ** a)`)) THEN
      MP_TAC(SPECL [`d:real^N`; `a:real^N`] (ASSUME `!a b. a dot ((G:real^N->real^N^N) y ** b) = b dot (G y ** a)`)) THEN
      CONV_TAC REAL_RING;
      MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                     `a:real^N`; `b:real^N`; `c:real^N`; `z:real^N`] LRG_RM_BIANCHI) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`a:real^N`; `z:real^N`] (ASSUME
        `!a b. a dot ((G:real^N->real^N^N) y ** b) = b dot (G y ** a)`)) THEN
      MP_TAC(SPECL [`b:real^N`; `z:real^N`] (ASSUME
        `!a b. a dot ((G:real^N->real^N^N) y ** b) = b dot (G y ** a)`)) THEN
      MP_TAC(SPECL [`c:real^N`; `z:real^N`] (ASSUME
        `!a b. a dot ((G:real^N->real^N^N) y ** b) = b dot (G y ** a)`)) THEN
      MP_TAC(SPECL [`a:real^N`; `b:real^N`] (ASSUME
        `!a b. a dot ((G:real^N->real^N^N) y ** b) = b dot (G y ** a)`)) THEN
      MP_TAC(SPECL [`b:real^N`; `c:real^N`] (ASSUME
        `!a b. a dot ((G:real^N->real^N^N) y ** b) = b dot (G y ** a)`)) THEN
      MP_TAC(SPECL [`c:real^N`; `a:real^N`] (ASSUME
        `!a b. a dot ((G:real^N->real^N^N) y ** b) = b dot (G y ** a)`)) THEN
      CONV_TAC REAL_RING];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u v. (TQ:real^N->real^N->real^N->real^N->real) u v u v = &0`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "TQ" THEN BETA_TAC THEN
    ASM_CASES_TAC `collinear {vec 0:real^N,u,v}` THENL
     [UNDISCH_TAC `collinear {vec 0:real^N,u,v}` THEN
      REWRITE_TAC[COLLINEAR_LEMMA_ALT] THEN
      DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `c:real` SUBST1_TAC)) THENL
       [REWRITE_TAC[DOT_LZERO; DOT_RZERO; MATRIX_VECTOR_MUL_RZERO] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `lriemann (G:real^N->real^N^N) y u (c % u) (c % u) = vec 0`
      SUBST1_TAC THENL
       [MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                       `u:real^N`; `c % u:real^N`; `c % u:real^N`] LRIEMANN_ANTISYM) THEN
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `lriemann (G:real^N->real^N^N) y (c % u) u (c % u) =
                      c % lriemann G y u u (c % u) /\
                      lriemann (G:real^N->real^N^N) y u (c % u) (c % u) =
                      c % lriemann G y u u (c % u)`
        (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                       `u:real^N`; `u:real^N`; `c % u:real^N`] LRIEMANN_ANTISYM) THEN
        ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; MATRIX_VECTOR_MUL_RMUL;
                  DOT_LMUL; DOT_RMUL] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N`; `v:real^N`] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lsectional"))
          (concl th))) THEN
    ASM_REWRITE_TAC[lsectional] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `u:real^N`;
                   `v:real^N`] APX_SECT_DEN_POS) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`v:real^N`; `u:real^N`] (ASSUME `!a b. a dot ((G:real^N->real^N^N) y ** b) = b dot (G y ** a)`)) THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_POW_2] THEN
    SPEC_TAC(`u dot ((G:real^N->real^N^N) y ** lriemann G y u v v)`,`n:real`) THEN
    SPEC_TAC(`(u dot ((G:real^N->real^N^N) y ** u)) * (v dot (G y ** v)) -
              (u dot (G y ** v)) * (u dot (G y ** v))`,`dd:real`) THEN
    REPEAT GEN_TAC THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `!u v w. (TQ:real^N->real^N->real^N->real^N->real) u v w v = &0` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(SPECL [`u + w:real^N`; `v:real^N`]
      (ASSUME `!u v. (TQ:real^N->real^N->real^N->real^N->real) u v u v = &0`)) THEN
    REWRITE_TAC[ASSUME `!a1 a2 b c d. (TQ:real^N->real^N->real^N->real^N->real) (a1 + a2) b c d = TQ a1 b c d + TQ a2 b c d`;
                ASSUME `!a b c1 c2 d. (TQ:real^N->real^N->real^N->real^N->real) a b (c1 + c2) d = TQ a b c1 d + TQ a b c2 d`;
                ASSUME `!u v. (TQ:real^N->real^N->real^N->real^N->real) u v u v = &0`] THEN
    MP_TAC(SPECL [`u:real^N`; `v:real^N`; `w:real^N`; `v:real^N`]
      (ASSUME `!a b c d. (TQ:real^N->real^N->real^N->real^N->real) c d a b = TQ a b c d`)) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!u v w z. (TQ:real^N->real^N->real^N->real^N->real) u v w z = --(TQ u z w v)` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(SPECL [`u:real^N`; `v + z:real^N`; `w:real^N`]
      (ASSUME `!u v w. (TQ:real^N->real^N->real^N->real^N->real) u v w v = &0`)) THEN
    REWRITE_TAC[ASSUME `!a b1 b2 c d. (TQ:real^N->real^N->real^N->real^N->real) a (b1 + b2) c d = TQ a b1 c d + TQ a b2 c d`;
                ASSUME `!a b c d1 d2. (TQ:real^N->real^N->real^N->real^N->real) a b c (d1 + d2) = TQ a b c d1 + TQ a b c d2`;
                ASSUME `!u v w. (TQ:real^N->real^N->real^N->real^N->real) u v w v = &0`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!a b c d. (TQ:real^N->real^N->real^N->real^N->real) a b c d = &0` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(SPECL [`a:real^N`; `b:real^N`; `d:real^N`; `c:real^N`]
      (ASSUME `!a b c z. (TQ:real^N->real^N->real^N->real^N->real) a b z c + TQ b c z a + TQ c a z b = &0`)) THEN
    MP_TAC(SPECL [`b:real^N`; `d:real^N`; `c:real^N`; `a:real^N`]
      (ASSUME `!u v w z. (TQ:real^N->real^N->real^N->real^N->real) u v w z = --(TQ u z w v)`)) THEN
    MP_TAC(SPECL [`a:real^N`; `d:real^N`; `c:real^N`; `b:real^N`]
      (ASSUME `!u v w z. (TQ:real^N->real^N->real^N->real^N->real) u v w z = --(TQ u z w v)`)) THEN
    MP_TAC(SPECL [`a:real^N`; `b:real^N`; `c:real^N`; `d:real^N`]
      (ASSUME `!a b c d. (TQ:real^N->real^N->real^N->real^N->real) b a c d = --(TQ a b c d)`)) THEN
    MP_TAC(SPECL [`a:real^N`; `d:real^N`; `c:real^N`; `b:real^N`]
      (ASSUME `!a b c d. (TQ:real^N->real^N->real^N->real^N->real) b a c d = --(TQ a b c d)`)) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  ABBREV_TAC `D = lriemann (G:real^N->real^N^N) y u v w -
                  k % ((v dot (G y ** w)) % u - (u dot (G y ** w)) % v)` THEN
  SUBGOAL_THEN `!c. c dot ((G:real^N->real^N^N) y ** D) = &0` ASSUME_TAC THENL
   [X_GEN_TAC `c:real^N` THEN EXPAND_TAC "D" THEN
    MP_TAC(SPECL [`u:real^N`; `v:real^N`; `c:real^N`; `w:real^N`]
      (ASSUME `!a b c d. (TQ:real^N->real^N->real^N->real^N->real) a b c d = &0`)) THEN
    EXPAND_TAC "TQ" THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB; MATRIX_VECTOR_MUL_RMUL; DOT_RSUB;
                DOT_RMUL] THEN
    MP_TAC(SPECL [`c:real^N`; `u:real^N`] (ASSUME
      `!a b. a dot ((G:real^N->real^N^N) y ** b) = b dot (G y ** a)`)) THEN
    MP_TAC(SPECL [`c:real^N`; `v:real^N`] (ASSUME
      `!a b. a dot ((G:real^N->real^N^N) y ** b) = b dot (G y ** a)`)) THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  UNDISCH_TAC `metric_field s (G:real^N->real^N^N)` THEN
  REWRITE_TAC[metric_field] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^N` o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `D:real^N` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[REAL_LT_REFL]);;


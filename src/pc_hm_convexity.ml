(* ========================================================================= *)
(* Unit pc_hm_convexity: the chain statement CM_CHAIN_HM_CONVEXITY_STATEMENT *)
(* of pc_cm_stmts, the convexity of the G-energy at small-energy harmonic    *)
(* maps (Colding-Minicozzi 2008, Thm 3.1, in the G form).  Of the hypotheses *)
(* of the chain statement only WAN_HARDY_BALL and CM_EPS_REG are used        *)
(* (WAN_W12_C1 is the theorem of pc_wan_weak; WAN_CHAIN_W12 and              *)
(* WAN_W120_CONT are not needed).  Headline: CM_CHAIN_HM_CONVEXITY, at the   *)
(* end of the file.  Route: no Coulomb gauge; the weak Euler-Lagrange        *)
(* equation of v from cm_harmonic, the normal part of u - v is quadratic,    *)
(* interior gradient bounds from CM_EPS_REG on the balls ball(x, dist to     *)
(* boundary) and the Hardy inequality on balls absorb the bad terms.         *)
(* ========================================================================= *)

needs "src/pc_cm_stmts.ml";;
needs "src/pc_cm_target.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Pointwise linear algebra.  The energy density difference minus the        *)
(* Euler-Lagrange density is bounded below by a positive multiple of |Y|^2   *)
(* up to an error |w|^2 |X|^2, where X is a tangent vector (a partial of v), *)
(* Y a partial of w = u - v.                                                 *)
(* ========================================================================= *)

let HMC_SYM_DOT = prove
 (`!(A:real^N^N) x y. transp A = A ==> x dot (A ** y) = y dot (A ** x)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM DOT_MATRIX_TRANSP_LMUL] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[DOT_SYM]);;

let HMC_AMGM = prove
 (`!a b lam. &0 < lam ==> &2 * a * b <= lam / &2 * b pow 2 + &2 / lam * a pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lam / &2 * b pow 2 + &2 / lam * a pow 2 =
                &2 * a * b + &2 / lam * (a - lam / &2 * b) pow 2` MP_TAC THENL
   [UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> x = z + y ==> z <= x`) THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC);;

(* An orthogonal projection does not increase norms.                        *)

let HMC_PROJ_NORM = prove
 (`!(P:real^N^N) x. transp P = P /\ P ** P = P ==> norm(P ** x) <= norm x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `norm((P:real^N^N) ** x) pow 2 = (P ** x) dot x` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_POW_2] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM DOT_MATRIX_TRANSP_LMUL] THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC];
    ALL_TAC] THEN
  ASM_CASES_TAC `(P:real^N^N) ** x = vec 0` THENL
   [ASM_REWRITE_TAC[NORM_0; NORM_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm((P:real^N^N) ** x)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `norm((P:real^N^N) ** x) * norm(P ** x) <= norm(P ** x) * norm x`
  MP_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_2] THEN ASM_REWRITE_TAC[NORM_CAUCHY_SCHWARZ];
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ]]);;

(* The main pointwise inequality.  P: the tangent projection at v(x); Gu, Gv: *)
(* G at u(x), v(x); DJ, DG: the derivatives of the projection field and of G *)
(* at v(x); X: a partial of v (tangent); Y: the same partial of w; w: u - v. *)

let HMC_DENSITY_ALG = prove
 (`!(P:real^K^K) (Gu:real^K^K) Gv (DJ:real^K->real^K^K) (DG:real^K->real^K^K)
    (X:real^K) Y w lam Lam1 CJ CG C2 C3 C4.
     &0 < lam /\ &0 <= Lam1 /\ &0 <= CJ /\ &0 <= CG /\ &0 <= C2 /\ &0 <= C3 /\
     &0 <= C4 /\
     transp P = P /\ P ** P = P /\ transp Gu = Gu /\ transp Gv = Gv /\
     (!xi. lam * norm xi pow 2 <= xi dot (Gu ** xi)) /\
     (!xi. norm(Gv ** xi) <= Lam1 * norm xi) /\
     (!a b. P ** a = a /\ P ** b = b ==> P ** (DJ a ** b) = vec 0) /\
     (!a b. norm(DJ a ** b) <= CJ * norm a * norm b) /\
     (!a b. DJ(a + b) = DJ a + DJ b) /\
     (!a xi. norm(DG a ** xi) <= CG * norm a * norm xi) /\
     (!a b. DG(a + b) = DG a + DG b) /\
     (!xi. norm((Gu - Gv - DG w) ** xi) <= C2 * norm w pow 2 * norm xi) /\
     (!xi. norm((Gu - Gv) ** xi) <= C3 * norm w * norm xi) /\
     norm((mat 1 - P) ** w) <= C4 * norm w pow 2 /\
     (!a b. (P ** a) dot (Gv ** ((mat 1 - P) ** b)) = &0) /\
     P ** X = X
     ==> lam / &2 * norm Y pow 2 -
         (&2 * C3 pow 2 / lam + C2 + CG * C4 + &2 * CJ * C4 * Lam1) *
         norm w pow 2 * norm X pow 2
         <= (X + Y) dot (Gu ** (X + Y)) - X dot (Gv ** X) -
            (&2 * ((DJ w ** X + P ** Y) dot (Gv ** X)) + X dot (DG (P ** w) ** X))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `N = (mat 1 - P:real^K^K) ** (w:real^K)` THEN
  SUBGOAL_THEN `(P:real^K^K) ** (w:real^K) + N = w` ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB; MATRIX_VECTOR_MUL_LID] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(P:real^K^K) ** (Y:real^K) + (mat 1 - P) ** Y = Y` ASSUME_TAC THENL
   [REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB; MATRIX_VECTOR_MUL_LID] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  (* the normal part of Y is G-orthogonal to the tangent X *)
  SUBGOAL_THEN `((mat 1 - P:real^K^K) ** (Y:real^K)) dot ((Gv:real^K^K) ** (X:real^K)) = &0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`Gv:real^K^K`; `(mat 1 - P:real^K^K) ** Y`; `X:real^K`] HMC_SYM_DOT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SYM(ASSUME `(P:real^K^K) ** (X:real^K) = X`)] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the second fundamental form term in tangent directions is normal *)
  SUBGOAL_THEN `((DJ:real^K->real^K^K) ((P:real^K^K) ** (w:real^K)) ** (X:real^K)) dot ((Gv:real^K^K) ** X) = &0`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(P:real^K^K) ** ((DJ:real^K->real^K^K) (P ** (w:real^K)) ** (X:real^K)) = vec 0`
    ASSUME_TAC THENL
     [MATCH_MP_TAC(ASSUME `!a b. (P:real^K^K) ** a = a /\ P ** b = b
                                 ==> P ** ((DJ:real^K->real^K^K) a ** b) = vec 0`) THEN
      ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(mat 1 - P:real^K^K) ** ((DJ:real^K->real^K^K) (P ** (w:real^K)) ** (X:real^K)) =
                  DJ (P ** w) ** X` (SUBST1_TAC o SYM) THENL
     [ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB; MATRIX_VECTOR_MUL_LID] THEN
      VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`Gv:real^K^K`;
                   `(mat 1 - P:real^K^K) ** ((DJ:real^K->real^K^K) (P ** (w:real^K)) ** (X:real^K))`;
                   `X:real^K`] HMC_SYM_DOT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SYM(ASSUME `(P:real^K^K) ** (X:real^K) = X`)] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the relations between the dot products *)
  SUBGOAL_THEN `(Y:real^K) dot ((Gu:real^K^K) ** (X:real^K)) = X dot (Gu ** Y)` ASSUME_TAC THENL
   [MATCH_MP_TAC HMC_SYM_DOT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `((P:real^K^K) ** (Y:real^K)) dot ((Gv:real^K^K) ** (X:real^K)) = X dot (Gv ** Y)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`Gv:real^K^K`; `Y:real^K`; `X:real^K`] HMC_SYM_DOT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV)
      [SYM(ASSUME `(P:real^K^K) ** (Y:real^K) + (mat 1 - P) ** Y = Y`)] THEN
    ASM_REWRITE_TAC[DOT_LADD; REAL_ADD_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(DJ:real^K->real^K^K) (w:real^K) = DJ((P:real^K^K) ** w) + DJ N` ASSUME_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM(ASSUME `(P:real^K^K) ** (w:real^K) + N = w`)] THEN
    REWRITE_TAC[ASSUME `!a b. (DJ:real^K->real^K^K)(a + b) = DJ a + DJ b`];
    ALL_TAC] THEN
  SUBGOAL_THEN `(DG:real^K->real^K^K) ((P:real^K^K) ** (w:real^K)) = DG w - DG N` ASSUME_TAC THENL
   [GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV)
      [SYM(ASSUME `(P:real^K^K) ** (w:real^K) + N = w`)] THEN
    REWRITE_TAC[ASSUME `!a b. (DG:real^K->real^K^K)(a + b) = DG a + DG b`] THEN
    REWRITE_TAC[MATRIX_ARITH `(A:real^K^K) = (A + B) - B`];
    ALL_TAC] THEN
  (* the bounds *)
  SUBGOAL_THEN `lam * norm(Y:real^K) pow 2 <= Y dot ((Gu:real^K^K) ** Y)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `abs((X:real^K) dot (((Gu:real^K^K) - Gv) ** Y))
                <= C3 * norm(w:real^K) * norm X * norm(Y:real^K)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(X:real^K) * norm(((Gu:real^K^K) - Gv) ** (Y:real^K))` THEN
    REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(X:real^K) * (C3 * norm(w:real^K) * norm(Y:real^K))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[NORM_POS_LE]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs((X:real^K) dot (((Gu:real^K^K) - Gv - (DG:real^K->real^K^K) w) ** X))
                <= C2 * (norm(w:real^K) pow 2 * norm X pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(X:real^K) * norm(((Gu:real^K^K) - Gv - (DG:real^K->real^K^K) w) ** X)` THEN
    REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(X:real^K) * (C2 * norm(w:real^K) pow 2 * norm(X:real^K))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
      REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs((X:real^K) dot ((DG:real^K->real^K^K) (N:real^K) ** X))
                <= CG * C4 * (norm(w:real^K) pow 2 * norm X pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(X:real^K) * norm((DG:real^K->real^K^K) (N:real^K) ** X)` THEN
    REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(X:real^K) * (CG * norm(N:real^K) * norm(X:real^K))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(X:real^K) * (CG * (C4 * norm(w:real^K) pow 2) * norm(X:real^K))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      EXPAND_TAC "N" THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(((DJ:real^K->real^K^K) (N:real^K) ** (X:real^K)) dot ((Gv:real^K^K) ** X))
                <= CJ * C4 * Lam1 * (norm(w:real^K) pow 2 * norm(X:real^K) pow 2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm((DJ:real^K->real^K^K) (N:real^K) ** (X:real^K)) * norm((Gv:real^K^K) ** X)` THEN
    REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(CJ * norm(N:real^K) * norm(X:real^K)) * (Lam1 * norm X)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(CJ * (C4 * norm(w:real^K) pow 2) * norm(X:real^K)) * (Lam1 * norm X)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
        EXPAND_TAC "N" THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[NORM_POS_LE]];
      REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`C3 * norm(w:real^K) * norm(X:real^K)`; `norm(Y:real^K)`; `lam:real`]
                HMC_AMGM) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(C3 * norm(w:real^K) * norm(X:real^K)) pow 2 =
                C3 pow 2 * (norm w pow 2 * norm X pow 2)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  (* expand everything into the atoms and conclude *)
  RULE_ASSUM_TAC(REWRITE_RULE[MATRIX_VECTOR_MUL_SUB_RDISTRIB; DOT_RSUB]) THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_ADD_RDISTRIB;
                  MATRIX_VECTOR_MUL_SUB_RDISTRIB; DOT_LADD; DOT_RADD; DOT_RSUB] THEN
  SUBGOAL_THEN `&2 * C3 pow 2 / lam * (norm(w:real^K) pow 2 * norm(X:real^K) pow 2) =
                &2 / lam * (C3 pow 2 * (norm w pow 2 * norm X pow 2))` MP_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC);;

(* The Euler-Lagrange density is bounded by |h| |X|^2 + |X| |Y|.            *)

let HMC_LDENS_BOUND = prove
 (`!(P:real^K^K) (Gv:real^K^K) (DJ:real^K->real^K^K) (DG:real^K->real^K^K)
    (X:real^K) Y h Lam1 CJ CG.
     &0 <= Lam1 /\ &0 <= CJ /\ &0 <= CG /\ transp P = P /\ P ** P = P /\
     (!xi. norm(Gv ** xi) <= Lam1 * norm xi) /\
     (!a b. norm(DJ a ** b) <= CJ * norm a * norm b) /\
     (!a xi. norm(DG a ** xi) <= CG * norm a * norm xi)
     ==> abs(&2 * ((DJ h ** X + P ** Y) dot (Gv ** X)) + X dot (DG (P ** h) ** X))
         <= (&2 * CJ * Lam1 + CG) * norm h * norm X pow 2 + &2 * Lam1 * norm X * norm Y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `norm((P:real^K^K) ** (Y:real^K)) <= norm Y /\ norm(P ** (h:real^K)) <= norm h`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[HMC_PROJ_NORM]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(((DJ:real^K->real^K^K) h ** (X:real^K) + (P:real^K^K) ** (Y:real^K)) dot
                    ((Gv:real^K^K) ** X))
                <= (CJ * norm(h:real^K) * norm X + norm Y) * (Lam1 * norm X)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm((DJ:real^K->real^K^K) h ** (X:real^K) + (P:real^K^K) ** (Y:real^K)) *
                norm((Gv:real^K^K) ** X)` THEN
    REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC(NORM_ARITH `norm(a:real^K) <= x /\ norm(b:real^K) <= y
                             ==> norm(a + b) <= x + y`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs((X:real^K) dot ((DG:real^K->real^K^K) ((P:real^K^K) ** (h:real^K)) ** X))
                <= CG * norm h * norm X pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(X:real^K) * norm((DG:real^K->real^K^K) ((P:real^K^K) ** (h:real^K)) ** X)`
    THEN REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(X:real^K) * (CG * norm((P:real^K^K) ** (h:real^K)) * norm X)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(X:real^K) * (CG * norm(h:real^K) * norm X)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
      REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Bounds for matrices and derivatives on compact sets; linearity of mderiv. *)
(* ========================================================================= *)

let HMC_MAT_NORM = prove
 (`!(A:real^N^M) x. norm(A ** x) <= norm(vectorize A) * norm x`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `\x:real^N. (A:real^N^M) ** x` GRGE_ONORM_LE_VECTORIZE_LINEAR) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR; MATRIX_OF_MATRIX_VECTOR_MUL] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `onorm(\x:real^N. (A:real^N^M) ** x) * norm(x:real^N)` THEN CONJ_TAC THENL
   [MP_TAC(ISPEC `\x:real^N. (A:real^N^M) ** x` ONORM) THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN SIMP_TAC[];
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE]]);;

let HMC_CONT_BOUND = prove
 (`!k (f:real^M->real^N).
        compact k /\ f continuous_on k ==> ?B. &0 <= B /\ !z. z IN k ==> norm(f z) <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `k:real^M->bool`] COMPACT_CONTINUOUS_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
  MESON_TAC[REAL_LT_IMP_LE]);;

(* A uniform operator bound for the derivative of a smooth map on a compact *)
(* subset.                                                                   *)

let HMC_DERIV_BOUND = prove
 (`!s k (f:real^M->real^N).
        open s /\ smooth_map_on s f /\ compact k /\ k SUBSET s
        ==> ?B. &0 <= B /\
                !z a. z IN k ==> norm(frechet_derivative f (at z) a) <= B * norm a`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!j. ?Bj. &0 <= Bj /\
             !z. z IN k ==> norm(frechet_derivative (f:real^M->real^N) (at z) (basis j)) <= Bj`
  MP_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC HMC_CONT_BOUND THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^M->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE];
    REWRITE_TAC[SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `Bj:num->real` (LABEL_TAC "Bj"))] THEN
  EXISTS_TAC `sum(1..dimindex(:M)) (Bj:num->real)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`z:real^M`; `a:real^M`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `linear(frechet_derivative (f:real^M->real^N) (at z))` ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `s:real^M->bool` THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_VSUM_MUL (CONJ th (SPEC `dimindex(:M)`
    (SPEC `1` FINITE_NUMSEG)))]) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:M)) (\j. norm(a:real^M) * (Bj:num->real) j)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[NORM_MUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE] THEN
    ASM_SIMP_TAC[COMPONENT_LE_NORM];
    REWRITE_TAC[SUM_LMUL] THEN REAL_ARITH_TAC]);;

(* mderiv is additive in the direction where the field is differentiable.   *)

let HMC_MDERIV_ADD = prove
 (`!(G:real^N->real^N^N) z a b.
        ((vectorize:real^N^N->real^(N,N)finite_prod) o G) differentiable (at z)
        ==> mderiv G z (a + b) = mderiv G z a + mderiv G z b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mderiv; GSYM MATRIFY_ADD] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC LINEAR_ADD THEN
  ASM_SIMP_TAC[LINEAR_FRECHET_DERIVATIVE]);;

(* The bound for a matrix given by a vectorized matrix.                      *)

let HMC_MATRIFY_NORM = prove
 (`!(m:real^(N,N)finite_prod) x. norm((matrify m:real^N^N) ** x) <= norm m * norm x`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`matrify(m:real^(N,N)finite_prod):real^N^N`; `x:real^N`] HMC_MAT_NORM) THEN
  REWRITE_TAC[VECTORIZE_MATRIFY]);;

(* The constants of an embedded target.                                     *)

let HMC_TARGET_CONSTS = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> ?lam Lam1 CJ CG C2 C3 C4.
           &0 < lam /\ &0 <= Lam1 /\ &0 <= CJ /\ &0 <= CG /\ &0 <= C2 /\ &0 <= C3 /\
           &0 <= C4 /\
           (!z xi. lam * norm xi pow 2 <= xi dot (G z ** xi)) /\
           (!z xi. z IN S ==> norm(G z ** xi) <= Lam1 * norm xi) /\
           (!z a b. z IN S
                    ==> norm(mderiv (\y. jacobian (closest_point S) (at y)) z a ** b)
                        <= CJ * norm a * norm b) /\
           (!z a xi. z IN S ==> norm(mderiv G z a ** xi) <= CG * norm a * norm xi) /\
           (!y z xi. y IN S /\ z IN S
                     ==> norm((G y - G z - mderiv G z (y - z)) ** xi)
                         <= C2 * norm(y - z) pow 2 * norm xi) /\
           (!y z xi. y IN S /\ z IN S
                     ==> norm((G y - G z) ** xi) <= C3 * norm(y - z) * norm xi) /\
           (!x y. x IN S /\ y IN S
                  ==> norm((mat 1 - jacobian (closest_point S) (at x)) ** (y - x))
                      <= C4 * norm(y - x) pow 2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cm_target] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(cm_tube S d:real^K->bool) /\ (S:real^K->bool) SUBSET cm_tube S d`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[cm_tube; GRGE_TUBE_OPEN; SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^K` THEN DISCH_TAC THEN EXISTS_TAC `z:real^K` THEN
    ASM_REWRITE_TAC[DIST_REFL];
    ALL_TAC] THEN
  (* the bound for G on S *)
  MP_TAC(ISPECL [`S:real^K->bool`; `(vectorize:real^K^K->real^(K,K)finite_prod) o (G:real^K->real^K^K)`]
                HMC_CONT_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(:real^K)` THEN REWRITE_TAC[SUBSET_UNIV] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[o_THM] THEN DISCH_THEN(X_CHOOSE_THEN `B1:real` STRIP_ASSUME_TAC)] THEN
  (* the derivative bound for the tangent projection field on S *)
  MP_TAC(ISPECL [`cm_tube S d:real^K->bool`; `S:real^K->bool`;
                 `(vectorize:real^K^K->real^(K,K)finite_prod) o
                  (\y. matrix(frechet_derivative (closest_point S) (at y)))`]
                HMC_DERIV_BOUND) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[LRG_SMOOTH_JACOBIAN];
    DISCH_THEN(X_CHOOSE_THEN `BJ:real` STRIP_ASSUME_TAC)] THEN
  (* the derivative bound for G on S *)
  MP_TAC(ISPECL [`(:real^K)`; `S:real^K->bool`;
                 `(vectorize:real^K^K->real^(K,K)finite_prod) o (G:real^K->real^K^K)`] HMC_DERIV_BOUND) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `BG:real` STRIP_ASSUME_TAC) THEN
  (* the Taylor bound for G on a ball containing S *)
  MP_TAC(ISPECL [`S:real^K->bool`; `vec 0:real^K`] BOUNDED_SUBSET_CBALL) THEN
  ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`(:real^K)`; `cball(vec 0:real^K,R)`;
                 `(vectorize:real^K^K->real^(K,K)finite_prod) o (G:real^K->real^K^K)`] GRGE_SMOOTH_TAYLOR1) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; COMPACT_CBALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `B2:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!y z. y IN S /\ z IN S
          ==> norm((vectorize:real^K^K->real^(K,K)finite_prod) (G y) - vectorize(G z) -
                   frechet_derivative ((vectorize:real^K^K->real^(K,K)finite_prod) o (G:real^K->real^K^K)) (at z) (y - z))
              <= B2 * norm(y - z:real^K) pow 2`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`z:real^K`; `y:real^K`]) THEN
    REWRITE_TAC[o_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN REWRITE_TAC[CONVEX_CBALL] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y z. y IN S /\ z IN S ==> norm(y - z:real^K) <= &2 * R` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^K) IN cball(vec 0,R) /\ (z:real^K) IN cball(vec 0,R)` MP_TAC THENL
     [ASM SET_TAC[]; REWRITE_TAC[IN_CBALL_0] THEN NORM_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`lam:real`; `B1:real`; `BJ:real`; `BG:real`; `B2:real`;
                        `BG + &2 * R * B2`; `C:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm((vectorize:real^K^K->real^(K,K)finite_prod) ((G:real^K->real^K^K) z)) *
                norm(xi:real^K)` THEN
    REWRITE_TAC[HMC_MAT_NORM] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[NORM_POS_LE];
    REPEAT STRIP_TAC THEN REWRITE_TAC[mderiv; jacobian] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(frechet_derivative ((vectorize:real^K^K->real^(K,K)finite_prod) o
                  (\y. matrix(frechet_derivative (closest_point S) (at y)))) (at z) (a:real^K)) *
                norm(b:real^K)` THEN
    REWRITE_TAC[HMC_MATRIFY_NORM] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[NORM_POS_LE];
    REPEAT STRIP_TAC THEN REWRITE_TAC[mderiv] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(frechet_derivative ((vectorize:real^K^K->real^(K,K)finite_prod) o
                  (G:real^K->real^K^K)) (at z) (a:real^K)) * norm(xi:real^K)` THEN
    REWRITE_TAC[HMC_MATRIFY_NORM] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[NORM_POS_LE];
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `(G:real^K->real^K^K) y - G z - mderiv G z (y - z) =
      matrify((vectorize:real^K^K->real^(K,K)finite_prod) (G y) - vectorize(G z) -
              frechet_derivative (vectorize o G) (at z) (y - z))`
    SUBST1_TAC THENL [REWRITE_TAC[mderiv; MATRIFY_SUB; MATRIFY_VECTORIZE]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm((vectorize:real^K^K->real^(K,K)finite_prod) ((G:real^K->real^K^K) y) -
                     vectorize(G z) - frechet_derivative (vectorize o G) (at z) (y - z)) *
                norm(xi:real^K)` THEN
    REWRITE_TAC[HMC_MATRIFY_NORM] THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[NORM_POS_LE];
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `(G:real^K->real^K^K) y - G z =
      matrify((vectorize:real^K^K->real^(K,K)finite_prod) (G y) - vectorize(G z))`
    SUBST1_TAC THENL [REWRITE_TAC[MATRIFY_SUB; MATRIFY_VECTORIZE]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm((vectorize:real^K^K->real^(K,K)finite_prod) ((G:real^K->real^K^K) y) -
                     vectorize(G z)) * norm(xi:real^K)` THEN
    REWRITE_TAC[HMC_MATRIFY_NORM] THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    SUBGOAL_THEN
     `norm(frechet_derivative ((vectorize:real^K^K->real^(K,K)finite_prod) o
             (G:real^K->real^K^K)) (at z) (y - z)) <= BG * norm(y - z:real^K) /\
      norm((vectorize:real^K^K->real^(K,K)finite_prod) (G y) - vectorize(G z) -
           frechet_derivative (vectorize o G) (at z) (y - z)) <= B2 * norm(y - z) pow 2 /\
      norm(y - z:real^K) <= &2 * R`
    MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= norm(y - z:real^K)` MP_TAC THENL
     [REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
    ABBREV_TAC `t = norm(y - z:real^K)` THEN
    ABBREV_TAC `D = frechet_derivative ((vectorize:real^K^K->real^(K,K)finite_prod) o
                      (G:real^K->real^K^K)) (at z) (y - z)` THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(NORM_ARITH
     `!d:real^N x y. norm(a - b - d) <= x /\ norm d <= y /\ x + y <= z
                     ==> norm(a - b) <= z`) THEN
    EXISTS_TAC `D:real^(K,K)finite_prod` THEN
    EXISTS_TAC `B2 * t pow 2` THEN EXISTS_TAC `BG * t` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `B2 * t pow 2 <= B2 * (&2 * R) * t` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POW_2] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
      REAL_ARITH_TAC]]);;

(* ========================================================================= *)
(* The tangent projection field of the target.  Partials of maps into S are  *)
(* tangent; the derivative of the projection field in a tangent direction    *)
(* maps tangent vectors to normal vectors (J z (DJ_a b) = 0), by             *)
(* differentiating J^2 = J along a curve in S.                               *)
(* ========================================================================= *)

(* Copy of PDG_VDERIV_CHAIN (pc_pde_gauge, not in this load closure).        *)

let HMC_VDERIV_CHAIN = prove
 (`!(f:real^1->real^M) (g:real^M->real^P) f' x.
        (f has_vector_derivative f') (at x) /\ g differentiable (at (f x))
        ==> ((g o f) has_vector_derivative frechet_derivative g (at (f x)) f') (at x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_vector_derivative] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
  UNDISCH_TAC `(g:real^M->real^P) differentiable (at (f(x:real^1)))` THEN
  REWRITE_TAC[FRECHET_DERIVATIVE_WORKS] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`f:real^1->real^M`; `g:real^M->real^P`; `\s:real^1. drop s % (f':real^M)`;
                 `frechet_derivative (g:real^M->real^P) (at (f(x:real^1)))`;
                 `x:real^1`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN
  ASM_SIMP_TAC[LINEAR_CMUL]);;

(* The basic facts on the projection field of an embedded target.          *)

let HMC_TARGET_BASICS = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> compact S /\ ~(S = {}) /\ &0 < d /\
         open(cm_tube S d) /\ S SUBSET cm_tube S d /\
         (!z. closest_point S z IN S) /\
         (!z. z IN S ==> closest_point S z = z) /\
         smooth_map_on (cm_tube S d) (closest_point S) /\
         smooth_map_on (cm_tube S d)
           ((vectorize:real^K^K->real^(K,K)finite_prod) o
            (\y. jacobian (closest_point S) (at y))) /\
         (!z. z IN S
              ==> transp(jacobian (closest_point S) (at z)) =
                  jacobian (closest_point S) (at z) /\
                  jacobian (closest_point S) (at z) ** jacobian (closest_point S) (at z) =
                  jacobian (closest_point S) (at z)) /\
         (!z u v. z IN S
                  ==> (jacobian (closest_point S) (at z) ** u) dot
                      (G z ** ((mat 1 - jacobian (closest_point S) (at z)) ** v)) = &0) /\
         smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o G) /\
         (!z. transp(G z) = G z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cm_target] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `open(cm_tube S d:real^K->bool) /\ (S:real^K->bool) SUBSET cm_tube S d`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[cm_tube; GRGE_TUBE_OPEN; SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^K` THEN DISCH_TAC THEN EXISTS_TAC `z:real^K` THEN
    ASM_REWRITE_TAC[DIST_REFL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC CLOSEST_POINT_IN_SET THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    REWRITE_TAC[CLOSEST_POINT_SELF];
    REWRITE_TAC[jacobian] THEN MATCH_MP_TAC LRG_SMOOTH_JACOBIAN THEN
    ASM_REWRITE_TAC[]]);;

(* Partials of a map into S are tangent.                                     *)

let HMC_TANGENT_PARTIAL = prove
 (`!S (G:real^K->real^K^K) d s (v:real^N->real^K) x i.
     cm_target S G d /\ open s /\ smooth_map_on s v /\ (!y. y IN s ==> v y IN S) /\
     x IN s
     ==> jacobian (closest_point S) (at (v x)) ** partial_derivative i v x =
         partial_derivative i v x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  SUBGOAL_THEN `closest_point (S:real^K->bool) differentiable at ((v:real^N->real^K) x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `cm_tube S d:real^K->bool` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N->real^K) differentiable at x` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (v:real^N->real^K) (at x) =
    frechet_derivative (closest_point S) (at (v x)) o frechet_derivative v (at x)`
  ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    MAP_EVERY EXISTS_TAC
     [`closest_point (S:real^K->bool) o (v:real^N->real^K)`; `s:real^N->bool`] THEN
    ASM_SIMP_TAC[o_THM] THEN MATCH_MP_TAC DIFF_CHAIN_AT THEN
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  REWRITE_TAC[partial_derivative; jacobian] THEN
  GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV)
   [ASSUME `frechet_derivative (v:real^N->real^K) (at x) =
            frechet_derivative (closest_point S) (at (v x)) o frechet_derivative v (at x)`] THEN
  REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[MATRIX_WORKS; LINEAR_FRECHET_DERIVATIVE]);;

(* The derivative of the projection field in a tangent direction maps        *)
(* tangent vectors to normal vectors.                                        *)

let HMC_JDJ = prove
 (`!S (G:real^K->real^K^K) d z a b.
     cm_target S G d /\ z IN S /\
     jacobian (closest_point S) (at z) ** a = a /\
     jacobian (closest_point S) (at z) ** b = b
     ==> jacobian (closest_point S) (at z) **
         (mderiv (\y. jacobian (closest_point S) (at y)) z a ** b) = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  ABBREV_TAC `c = \t:real^1. z + drop t % (a:real^K)` THEN
  ABBREV_TAC `JJ = (vectorize:real^K^K->real^(K,K)finite_prod) o
                   (\y. jacobian (closest_point (S:real^K->bool)) (at y))` THEN
  SUBGOAL_THEN `(c:real^1->real^K) (vec 0) = z` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[DROP_VEC; VECTOR_MUL_LZERO; VECTOR_ADD_RID]; ALL_TAC] THEN
  SUBGOAL_THEN `((c:real^1->real^K) has_vector_derivative a) (at (vec 0))` ASSUME_TAC THENL
   [REWRITE_TAC[has_vector_derivative] THEN EXPAND_TAC "c" THEN
    SUBGOAL_THEN `(\h:real^1. drop h % (a:real^K)) = (\h. vec 0 + drop h % a)`
    SUBST1_TAC THENL [REWRITE_TAC[VECTOR_ADD_LID]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `closest_point (S:real^K->bool) differentiable at z` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `cm_tube S d:real^K->bool` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(JJ:real^K->real^(K,K)finite_prod) differentiable at z` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `cm_tube S d:real^K->bool` THEN EXPAND_TAC "JJ" THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `frechet_derivative (closest_point (S:real^K->bool)) (at z) a = a`
  ASSUME_TAC THENL
   [UNDISCH_TAC `jacobian (closest_point S) (at z) ** (a:real^K) = a` THEN
    REWRITE_TAC[jacobian] THEN ASM_SIMP_TAC[MATRIX_WORKS; LINEAR_FRECHET_DERIVATIVE];
    ALL_TAC] THEN
  SUBGOAL_THEN `((closest_point S o (c:real^1->real^K)) has_vector_derivative a) (at (vec 0))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:real^1->real^K`; `closest_point (S:real^K->bool)`; `a:real^K`;
                   `vec 0:real^1`] HMC_VDERIV_CHAIN) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `V = frechet_derivative (JJ:real^K->real^(K,K)finite_prod) (at z) a` THEN
  SUBGOAL_THEN
   `(((JJ:real^K->real^(K,K)finite_prod) o closest_point S o (c:real^1->real^K))
     has_vector_derivative V) (at (vec 0))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`closest_point S o (c:real^1->real^K)`;
                   `JJ:real^K->real^(K,K)finite_prod`; `a:real^K`;
                   `vec 0:real^1`] HMC_VDERIV_CHAIN) THEN
    ASM_REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `m = (JJ:real^K->real^(K,K)finite_prod) o closest_point S o (c:real^1->real^K)` THEN
  SUBGOAL_THEN `(matrify((m:real^1->real^(K,K)finite_prod) (vec 0)):real^K^K) =
                jacobian (closest_point S) (at z)` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN EXPAND_TAC "JJ" THEN ASM_SIMP_TAC[o_THM; MATRIFY_VECTORIZE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. (matrify((m:real^1->real^(K,K)finite_prod) t):real^K^K) **
                    (matrify(m t) ** b) - matrify(m t) ** b = vec 0` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "m" THEN EXPAND_TAC "JJ" THEN
    REWRITE_TAC[o_THM; MATRIFY_VECTORIZE; MATRIX_VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[VECTOR_SUB_REFL];
    ALL_TAC] THEN
  (* the derivative of t |-> J(t) J(t) b - J(t) b at 0 *)
  MP_TAC(ISPECL [`\(p:real^(K,K)finite_prod) (q:real^K). (matrify p:real^K^K) ** q`;
                 `m:real^1->real^(K,K)finite_prod`; `(\t:real^1. b:real^K)`;
                 `V:real^(K,K)finite_prod`; `vec 0:real^K`; `vec 0:real^1`]
                HAS_VECTOR_DERIVATIVE_BILINEAR_AT) THEN
  ASM_REWRITE_TAC[LRG_BILINEAR_MATRIFY_MUL; HAS_VECTOR_DERIVATIVE_CONST] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\(p:real^(K,K)finite_prod) (q:real^K). (matrify p:real^K^K) ** q`;
                 `m:real^1->real^(K,K)finite_prod`;
                 `\t:real^1. (matrify((m:real^1->real^(K,K)finite_prod) t):real^K^K) ** b`;
                 `V:real^(K,K)finite_prod`; `(matrify V:real^K^K) ** b`; `vec 0:real^1`]
                HAS_VECTOR_DERIVATIVE_BILINEAR_AT) THEN
  ASM_REWRITE_TAC[LRG_BILINEAR_MATRIFY_MUL] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\t:real^1. (matrify((m:real^1->real^(K,K)finite_prod) t):real^K^K) **
                             (matrify(m t) ** b)`;
                 `jacobian (closest_point (S:real^K->bool)) (at z) **
                  ((matrify V:real^K^K) ** (b:real^K)) +
                  matrify V ** jacobian (closest_point S) (at z) ** b`;
                 `\t:real^1. (matrify((m:real^1->real^(K,K)finite_prod) t):real^K^K) ** b`;
                 `(matrify V:real^K^K) ** b`; `at(vec 0:real^1)`]
                HAS_VECTOR_DERIVATIVE_SUB) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\t:real^1. (matrify((m:real^1->real^(K,K)finite_prod) t):real^K^K) **
                            (matrify(m t) ** b) - matrify(m t) ** b) = (\t. vec 0)`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`(\t:real^1. vec 0:real^K)`; `vec 0:real^1`;
                 `(jacobian (closest_point (S:real^K->bool)) (at z) **
                   ((matrify V:real^K^K) ** (b:real^K)) +
                   matrify V ** jacobian (closest_point S) (at z) ** b) - matrify V ** b`;
                 `vec 0:real^K`] VECTOR_DERIVATIVE_UNIQUE_AT) THEN
  ASM_REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST] THEN
  REWRITE_TAC[mderiv] THEN
  SUBGOAL_THEN `(vectorize:real^K^K->real^(K,K)finite_prod) o
                (\y. jacobian (closest_point (S:real^K->bool)) (at y)) = JJ`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC);;

(* ========================================================================= *)
(* Weak derivatives of smooth maps are the classical partials; the G-energy  *)
(* of a smooth map; restriction of harmonicity; monotonicity of the energy   *)
(* in the domain; the interior gradient bound from CM_EPS_REG.               *)
(* ========================================================================= *)

let HMC_LSPACE_SPIKE = prove
 (`!(f:real^M->real^N) g s k p.
        f IN lspace s p /\ negligible k /\ (!x. x IN s DIFF k ==> g x = f x)
        ==> g IN lspace s p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lspace; IN_ELIM_THM] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`f:real^M->real^N`; `g:real^M->real^N`; `k:real^M->bool`;
                   `s:real^M->bool`] MEASURABLE_ON_SPIKE) THEN
    ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`\x. lift(norm((f:real^M->real^N) x) rpow p)`;
                   `\x. lift(norm((g:real^M->real^N) x) rpow p)`; `k:real^M->bool`;
                   `s:real^M->bool`] INTEGRABLE_SPIKE) THEN
    ASM_SIMP_TAC[]]);;

(* The chosen weak partials of a C^1 map are its classical partials a.e.   *)

let HMC_WD_CLASSICAL = prove
 (`!s (v:real^N->real^K) i.
        open s /\ continuously_differentiable 1 s v /\ wan_w12 s v /\
        1 <= i /\ i <= dimindex(:N)
        ==> negligible {x | x IN s /\ ~(wan_wd s i v x = partial_derivative i v x)}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_WD_UNIQUE THEN
  ASM_SIMP_TAC[WAN_WPD_C1]);;

let HMC_PD_LSPACE = prove
 (`!s (v:real^N->real^K) i.
        open s /\ continuously_differentiable 1 s v /\ wan_w12 s v /\
        1 <= i /\ i <= dimindex(:N)
        ==> (\x. partial_derivative i v x) IN lspace s (&2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HMC_LSPACE_SPIKE THEN
  MAP_EVERY EXISTS_TAC
   [`wan_wd s i (v:real^N->real^K)`;
    `{x | x IN s /\ ~(wan_wd s i (v:real^N->real^K) x = partial_derivative i v x)}`] THEN
  ASM_SIMP_TAC[WAN_WD_WORKS; HMC_WD_CLASSICAL] THEN SET_TAC[]);;

(* The G-energy of a C^1 map in terms of classical partials.                *)

let HMC_GDIR_CLASSICAL = prove
 (`!s (G:real^K->real^K^K) (v:real^N->real^K).
        open s /\ continuously_differentiable 1 s v /\ wan_w12 s v
        ==> wan_gdir s G v =
            sum(1..dimindex(:N))
              (\i. drop(integral s (\x. lift(partial_derivative i v x dot
                                             (G(v x) ** partial_derivative i v x)))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_gdir] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_SPIKE THEN
  EXISTS_TAC `{x | x IN s /\ ~(wan_wd s i (v:real^N->real^K) x = partial_derivative i v x)}` THEN
  ASM_SIMP_TAC[HMC_WD_CLASSICAL] THEN
  REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN MESON_TAC[]);;

(* Harmonicity restricts to subsets.                                        *)

let HMC_HARMONIC_SUBSET = prove
 (`!S (G:real^K->real^K^K) s t (v:real^2->real^K).
        cm_harmonic S G s v /\ t SUBSET s ==> cm_harmonic S G t v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cm_harmonic] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    ASM SET_TAC[];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]]);;

(* Composition of a measurable map with a continuous map.                   *)

let HMC_MEAS_COMPOSE = prove
 (`!(f:real^M->real^N) (g:real^N->real^P) s.
        f measurable_on s /\ lebesgue_measurable s /\ g continuous_on (:real^N)
        ==> (g o f) measurable_on s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. if x IN s then (f:real^M->real^N) x else vec 0`;
                 `g:real^N->real^P`] MEASURABLE_ON_COMPOSE_CONTINUOUS) THEN
  ASM_REWRITE_TAC[MEASURABLE_ON_UNIV] THEN DISCH_TAC THEN
  MATCH_MP_TAC MEASURABLE_ON_EQ THEN
  EXISTS_TAC `(g:real^N->real^P) o (\x. if x IN s then (f:real^M->real^N) x else vec 0)` THEN
  CONJ_TAC THENL [SIMP_TAC[o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
  EXISTS_TAC `(:real^M)` THEN ASM_REWRITE_TAC[SUBSET_UNIV]);;

(* Integrability of a quadratic form with a measurable bounded coefficient. *)

let HMC_QUAD_INTEGRABLE = prove
 (`!s (X:real^N->real^K) (M:real^N->real^K^K) Lam.
        X IN lspace s (&2) /\
        ((vectorize:real^K^K->real^(K,K)finite_prod) o M) measurable_on s /\
        (!x xi. x IN s ==> abs(xi dot (M x ** xi)) <= Lam * norm xi pow 2)
        ==> (\x. lift(X x dot (M x ** X x))) integrable_on s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(X:real^N->real^K) measurable_on s` ASSUME_TAC THENL
   [UNDISCH_TAC `(X:real^N->real^K) IN lspace s (&2)` THEN SIMP_TAC[lspace; IN_ELIM_THM];
    ALL_TAC] THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `\x. Lam % lift(norm((X:real^N->real^K) x) pow 2)` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[] (ISPEC `\x y:real^K. lift(x dot y)` MEASURABLE_ON_BILINEAR)) THEN
    REWRITE_TAC[BILINEAR_DOT] THEN ASM_REWRITE_TAC[ETA_AX] THEN
    SUBGOAL_THEN
     `(\x. (M:real^N->real^K^K) x ** (X:real^N->real^K) x) =
      (\x. (\(p:real^(K,K)finite_prod) (q:real^K). (matrify p:real^K^K) ** q)
             (((vectorize:real^K^K->real^(K,K)finite_prod) o M) x) (X x))`
    SUBST1_TAC THENL [REWRITE_TAC[o_THM; MATRIFY_VECTORIZE]; ALL_TAC] THEN
    MATCH_MP_TAC MEASURABLE_ON_BILINEAR THEN
    ASM_REWRITE_TAC[LRG_BILINEAR_MATRIFY_MUL; ETA_AX];
    MATCH_MP_TAC INTEGRABLE_CMUL THEN MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[NORM_LIFT; DROP_CMUL; LIFT_DROP] THEN ASM_SIMP_TAC[]]);;

(* The G-energy of a smooth map is monotone in the open domain.             *)

let HMC_GDIR_MONO = prove
 (`!s t (G:real^K->real^K^K) (v:real^N->real^K) Lam.
        open s /\ open t /\ t SUBSET s /\ smooth_map_on s v /\ wan_w12 s v /\
        smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o G) /\
        (!z xi. &0 <= xi dot (G z ** xi) /\ xi dot (G z ** xi) <= Lam * norm xi pow 2)
        ==> wan_gdir t G v <= wan_gdir s G v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!w. open w /\ w SUBSET s
                    ==> smooth_map_on w (v:real^N->real^K) /\ wan_w12 w v /\
                        continuously_differentiable 1 w v` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `smooth_map_on w (v:real^N->real^K)` ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC WAN_W12_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[smooth_map_on]];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on t (v:real^N->real^K) /\ wan_w12 t v /\
                continuously_differentiable 1 t v /\ continuously_differentiable 1 s v`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[smooth_map_on]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[HMC_GDIR_CLASSICAL] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!w. open w /\ w SUBSET s
        ==> (\x. lift(partial_derivative i (v:real^N->real^K) x dot
                      ((G:real^K->real^K^K) (v x) ** partial_derivative i v x)))
            integrable_on w`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HMC_QUAD_INTEGRABLE THEN
    EXISTS_TAC `Lam:real` THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HMC_PD_LSPACE THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN] THEN
      SUBGOAL_THEN `(vectorize:real^K^K->real^(K,K)finite_prod) o (\x. (G:real^K->real^K^K) (v x)) =
                    (vectorize o G) o (v:real^N->real^K)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_SIMP_TAC[];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^K)` THEN
        REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
        ASM_REWRITE_TAC[]];
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y`) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN ASM_SIMP_TAC[SUBSET_REFL; LIFT_DROP]);;

(* The G-energy of a smooth W^{1,2} map is nonnegative.                    *)

let HMC_GDIR_POS = prove
 (`!s (G:real^K->real^K^K) (v:real^N->real^K) Lam.
        open s /\ smooth_map_on s v /\ wan_w12 s v /\
        smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o G) /\
        (!z xi. &0 <= xi dot (G z ** xi) /\ xi dot (G z ** xi) <= Lam * norm xi pow 2)
        ==> &0 <= wan_gdir s G v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `continuously_differentiable 1 s (v:real^N->real^K)` ASSUME_TAC THENL
   [ASM_MESON_TAC[smooth_map_on]; ALL_TAC] THEN
  ASM_SIMP_TAC[HMC_GDIR_CLASSICAL] THEN
  MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN
  MATCH_MP_TAC HMC_QUAD_INTEGRABLE THEN EXISTS_TAC `Lam:real` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HMC_PD_LSPACE THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN] THEN
    SUBGOAL_THEN `(vectorize:real^K^K->real^(K,K)finite_prod) o (\x. (G:real^K->real^K^K) (v x)) =
                  (vectorize o G) o (v:real^N->real^K)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^K)` THEN
      REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      ASM_REWRITE_TAC[]];
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y`) THEN ASM_REWRITE_TAC[]]);;

(* The interior gradient bound from the epsilon-regularity estimate.        *)

let HMC_GRAD_BOUND = prove
 (`!S (G:real^K->real^K^K) e0 (C:num->real) Lam (a:real^2) r (v:real^2->real^K).
     (!(a:real^2) r (u:real^2->real^K) l x.
        &0 < r /\ cm_harmonic S G (ball(a,r)) u /\ wan_w12 (ball(a,r)) u /\
        wan_gdir (ball(a,r)) G u <= e0 /\
        ALL (\i. 1 <= i /\ i <= 2) l /\ ~(l = []) /\ x IN ball(a,r / &2)
        ==> r pow (LENGTH l) * norm(iterated_partial l u x)
            <= C (LENGTH l) * sqrt(wan_gdir (ball(a,r)) G u)) /\
     (!k. &0 < C k) /\
     smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o G) /\
     (!z xi. &0 <= xi dot (G z ** xi) /\ xi dot (G z ** xi) <= Lam * norm xi pow 2) /\
     &0 < r /\ cm_harmonic S G (ball(a,r)) v /\ wan_w12 (ball(a,r)) v /\
     wan_gdir (ball(a,r)) G v <= e0
     ==> !x i. x IN ball(a,r) /\ 1 <= i /\ i <= 2
               ==> (r - norm(x - a)) * norm(partial_derivative i v x)
                   <= C 1 * sqrt(wan_gdir (ball(a,r)) G v)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "eps") STRIP_ASSUME_TAC) THEN
  MAP_EVERY X_GEN_TAC [`x:real^2`; `i:num`] THEN STRIP_TAC THEN
  ABBREV_TAC `rho = r - norm(x - a:real^2)` THEN
  SUBGOAL_THEN `&0 < rho` ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN UNDISCH_TAC `(x:real^2) IN ball(a,r)` THEN
    REWRITE_TAC[IN_BALL] THEN NORM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(x:real^2,rho) SUBSET ball(a,r)` ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN REWRITE_TAC[SUBSET; IN_BALL] THEN NORM_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_harmonic] o
    check (fun th -> concl th = `cm_harmonic S (G:real^K->real^K^K) (ball(a,r)) (v:real^2->real^K)`)) THEN
  SUBGOAL_THEN `wan_gdir (ball(x,rho)) (G:real^K->real^K^K) (v:real^2->real^K) <=
                wan_gdir (ball(a,r)) G v` ASSUME_TAC THENL
   [MATCH_MP_TAC HMC_GDIR_MONO THEN EXISTS_TAC `Lam:real` THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  USE_THEN "eps" (MP_TAC o SPECL [`x:real^2`; `rho:real`; `v:real^2->real^K`; `[i:num]`;
                                  `x:real^2`]) THEN
  REWRITE_TAC[ALL; NOT_CONS_NIL; LENGTH; iterated_partial] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CENTRE_IN_BALL; REAL_HALF] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HMC_HARMONIC_SUBSET THEN EXISTS_TAC `ball(a:real^2,r)` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC WAN_W12_SUBSET THEN EXISTS_TAC `ball(a:real^2,r)` THEN
      ASM_REWRITE_TAC[OPEN_BALL];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM ONE; REAL_POW_1] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL [ASM_MESON_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HMC_GDIR_POS THEN EXISTS_TAC `Lam:real` THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(a:real^2,r)` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC WAN_W12_SUBSET THEN EXISTS_TAC `ball(a:real^2,r)` THEN
    ASM_REWRITE_TAC[OPEN_BALL]]);;

(* ========================================================================= *)
(* The Euler-Lagrange density, and the derivative of the energy density of   *)
(* Pi(v + e phi) along the line in e.                                        *)
(* ========================================================================= *)

(* The i-th Euler-Lagrange density of v in the direction h with i-th        *)
(* partial Y (classical for test maps, weak for W^{1,2} maps).              *)

let hmc_ld = new_definition
 `hmc_ld (S:real^K->bool) (G:real^K->real^K^K) (v:real^2->real^K) (h:real^2->real^K)
         (Y:real^2->real^K) (i:num) (x:real^2) =
    &2 * ((mderiv (\y. jacobian (closest_point S) (at y)) (v x) (h x) **
             partial_derivative i v x +
           jacobian (closest_point S) (at (v x)) ** Y x) dot
          (G(v x) ** partial_derivative i v x)) +
    partial_derivative i v x dot
    (mderiv G (v x) (jacobian (closest_point S) (at (v x)) ** h x) **
     partial_derivative i v x)`;;

let HMC_AFFINE_VDERIV = prove
 (`!(u0:real^N) w0 t0. ((\t:real^1. u0 + drop t % w0) has_vector_derivative w0) (at t0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_vector_derivative] THEN
  SUBGOAL_THEN `(\h:real^1. drop h % (w0:real^N)) = (\h. vec 0 + drop h % w0)`
  SUBST1_TAC THENL [REWRITE_TAC[VECTOR_ADD_LID]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN
  VECTOR_ARITH_TAC);;

let HMC_VDERIV_EQ = prove
 (`!(f:real^1->real^N) g d1 d2 net.
        f = g /\ d1 = d2
        ==> (f has_vector_derivative d1) net ==> (g has_vector_derivative d2) net`,
  SIMP_TAC[]);;

(* The derivative of the energy density along the line e |-> v0 + e phi0,  *)
(* with partial p0 + e pi0.                                                  *)

let HMC_LINE_DERIV = prove
 (`!S (G:real^K->real^K^K) d v0 phi0 p0 pi0 e0.
     cm_target S G d /\ v0 + e0 % phi0 IN cm_tube S d
     ==> ((\e. (jacobian (closest_point S) (at (v0 + e % phi0)) ** (p0 + e % pi0)) dot
              (G(closest_point S (v0 + e % phi0)) **
               (jacobian (closest_point S) (at (v0 + e % phi0)) ** (p0 + e % pi0))))
          has_real_derivative
          (&2 * ((mderiv (\y. jacobian (closest_point S) (at y)) (v0 + e0 % phi0) phi0 **
                   (p0 + e0 % pi0) +
                  jacobian (closest_point S) (at (v0 + e0 % phi0)) ** pi0) dot
                 (G(closest_point S (v0 + e0 % phi0)) **
                  (jacobian (closest_point S) (at (v0 + e0 % phi0)) ** (p0 + e0 % pi0)))) +
           (jacobian (closest_point S) (at (v0 + e0 % phi0)) ** (p0 + e0 % pi0)) dot
           (mderiv G (closest_point S (v0 + e0 % phi0))
              (jacobian (closest_point S) (at (v0 + e0 % phi0)) ** phi0) **
            (jacobian (closest_point S) (at (v0 + e0 % phi0)) ** (p0 + e0 % pi0)))))
         (atreal e0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  ABBREV_TAC `(z0:real^K) = v0 + e0 % phi0` THEN
  ABBREV_TAC `JJ = (vectorize:real^K^K->real^(K,K)finite_prod) o
                   (\y. jacobian (closest_point (S:real^K->bool)) (at y))` THEN
  ABBREV_TAC `GG = (vectorize:real^K^K->real^(K,K)finite_prod) o (G:real^K->real^K^K)` THEN
  SUBGOAL_THEN `closest_point (S:real^K->bool) differentiable at z0 /\
                (JJ:real^K->real^(K,K)finite_prod) differentiable at z0 /\
                (GG:real^K->real^(K,K)finite_prod) differentiable at (closest_point S z0)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `cm_tube S d:real^K->bool` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `cm_tube S d:real^K->bool` THEN EXPAND_TAC "JJ" THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `(:real^K)` THEN EXPAND_TAC "GG" THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!xi. frechet_derivative (closest_point (S:real^K->bool)) (at z0) xi =
                     jacobian (closest_point S) (at z0) ** xi` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[jacobian] THEN
    ASM_SIMP_TAC[MATRIX_WORKS; LINEAR_FRECHET_DERIVATIVE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. (matrify((JJ:real^K->real^(K,K)finite_prod) y):real^K^K) =
                    jacobian (closest_point S) (at y) /\
                    (matrify((GG:real^K->real^(K,K)finite_prod) y):real^K^K) = G y`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "JJ" THEN EXPAND_TAC "GG" THEN
    REWRITE_TAC[o_THM; MATRIFY_VECTORIZE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y w. mderiv (\y. jacobian (closest_point (S:real^K->bool)) (at y)) y w =
                      matrify(frechet_derivative (JJ:real^K->real^(K,K)finite_prod) (at y) w) /\
                      mderiv (G:real^K->real^K^K) y w =
                      matrify(frechet_derivative (GG:real^K->real^(K,K)finite_prod) (at y) w)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "JJ" THEN EXPAND_TAC "GG" THEN REWRITE_TAC[mderiv];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT] THEN
  ABBREV_TAC `zt = \t:real^1. (v0:real^K) + drop t % phi0` THEN
  ABBREV_TAC `pt = \t:real^1. (p0:real^K) + drop t % pi0` THEN
  SUBGOAL_THEN `(zt:real^1->real^K) (lift e0) = z0 /\
                (pt:real^1->real^K) (lift e0) = p0 + e0 % pi0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "zt" THEN EXPAND_TAC "pt" THEN ASM_REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
  SUBGOAL_THEN `((zt:real^1->real^K) has_vector_derivative phi0) (at (lift e0)) /\
                ((pt:real^1->real^K) has_vector_derivative pi0) (at (lift e0))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "zt" THEN EXPAND_TAC "pt" THEN REWRITE_TAC[HMC_AFFINE_VDERIV]; ALL_TAC] THEN
  (* the projection field along the line *)
  MP_TAC(ISPECL [`zt:real^1->real^K`; `JJ:real^K->real^(K,K)finite_prod`; `phi0:real^K`;
                 `lift e0`] HMC_VDERIV_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* A(t) = J(z(t)) p(t) *)
  MP_TAC(ISPECL [`\(p:real^(K,K)finite_prod) (q:real^K). (matrify p:real^K^K) ** q`;
                 `(JJ:real^K->real^(K,K)finite_prod) o (zt:real^1->real^K)`;
                 `pt:real^1->real^K`;
                 `frechet_derivative (JJ:real^K->real^(K,K)finite_prod) (at z0) phi0`;
                 `pi0:real^K`; `lift e0`] HAS_VECTOR_DERIVATIVE_BILINEAR_AT) THEN
  ASM_REWRITE_TAC[LRG_BILINEAR_MATRIFY_MUL; o_THM] THEN DISCH_TAC THEN
  (* W(t) = Pi(z(t)) and G(W(t)) *)
  MP_TAC(ISPECL [`zt:real^1->real^K`; `closest_point (S:real^K->bool)`; `phi0:real^K`;
                 `lift e0`] HMC_VDERIV_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`closest_point (S:real^K->bool) o (zt:real^1->real^K)`;
                 `GG:real^K->real^(K,K)finite_prod`;
                 `jacobian (closest_point (S:real^K->bool)) (at z0) ** phi0`;
                 `lift e0`] HMC_VDERIV_CHAIN) THEN
  ASM_REWRITE_TAC[o_THM] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\(p:real^(K,K)finite_prod) (q:real^K). (matrify p:real^K^K) ** q`;
                 `(GG:real^K->real^(K,K)finite_prod) o closest_point S o (zt:real^1->real^K)`;
                 `\t:real^1. jacobian (closest_point (S:real^K->bool)) (at (zt t)) **
                             (pt:real^1->real^K) t`;
                 `frechet_derivative (GG:real^K->real^(K,K)finite_prod) (at (closest_point S z0))
                    (jacobian (closest_point (S:real^K->bool)) (at z0) ** phi0)`;
                 `jacobian (closest_point (S:real^K->bool)) (at z0) ** pi0 +
                  matrify(frechet_derivative (JJ:real^K->real^(K,K)finite_prod) (at z0) phi0) **
                  (p0 + e0 % pi0)`;
                 `lift e0`] HAS_VECTOR_DERIVATIVE_BILINEAR_AT) THEN
  ASM_REWRITE_TAC[LRG_BILINEAR_MATRIFY_MUL; o_THM] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\x y:real^K. lift(x dot y)`;
                 `\t:real^1. jacobian (closest_point (S:real^K->bool)) (at (zt t)) **
                             (pt:real^1->real^K) t`;
                 `\t:real^1. (G:real^K->real^K^K) (closest_point S (zt t)) **
                             jacobian (closest_point (S:real^K->bool)) (at (zt t)) **
                             (pt:real^1->real^K) t`;
                 `jacobian (closest_point (S:real^K->bool)) (at z0) ** pi0 +
                  matrify(frechet_derivative (JJ:real^K->real^(K,K)finite_prod) (at z0) phi0) **
                  (p0 + e0 % pi0)`;
                 `(G:real^K->real^K^K) (closest_point S z0) **
                  (jacobian (closest_point (S:real^K->bool)) (at z0) ** pi0 +
                   matrify(frechet_derivative (JJ:real^K->real^(K,K)finite_prod) (at z0) phi0) **
                   (p0 + e0 % pi0)) +
                  matrify(frechet_derivative (GG:real^K->real^(K,K)finite_prod)
                     (at (closest_point S z0))
                     (jacobian (closest_point (S:real^K->bool)) (at z0) ** phi0)) **
                  jacobian (closest_point S) (at z0) ** (p0 + e0 % pi0)`;
                 `lift e0`] HAS_VECTOR_DERIVATIVE_BILINEAR_AT) THEN
  ASM_REWRITE_TAC[BILINEAR_DOT] THEN
  MATCH_MP_TAC HMC_VDERIV_EQ THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `t:real^1` THEN
    EXPAND_TAC "zt" THEN EXPAND_TAC "pt" THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM LIFT_ADD] THEN AP_TERM_TAC THEN
  ABBREV_TAC `A = jacobian (closest_point (S:real^K->bool)) (at z0) ** (p0 + e0 % pi0:real^K)` THEN
  ABBREV_TAC `a1 = jacobian (closest_point (S:real^K->bool)) (at z0) ** (pi0:real^K)` THEN
  ABBREV_TAC `b1 = (matrify(frechet_derivative (JJ:real^K->real^(K,K)finite_prod) (at z0)
                     phi0):real^K^K) ** (p0 + e0 % pi0)` THEN
  ABBREV_TAC `Gm = (G:real^K->real^K^K) (closest_point S z0)` THEN
  ABBREV_TAC `Dm = (matrify(frechet_derivative (GG:real^K->real^(K,K)finite_prod)
                     (at (closest_point S z0))
                     (jacobian (closest_point (S:real^K->bool)) (at z0) ** phi0)):real^K^K)` THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; DOT_LADD; DOT_RADD] THEN
  SUBGOAL_THEN `(A:real^K) dot ((Gm:real^K^K) ** a1) = a1 dot (Gm ** A) /\
                A dot (Gm ** b1) = b1 dot (Gm ** A)` (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC HMC_SYM_DOT THEN EXPAND_TAC "Gm" THEN ASM_REWRITE_TAC[];
    REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The energy of Pi(v + e phi) as an integral of the explicit density; the   *)
(* compact sub-tube.                                                         *)
(* ========================================================================= *)

(* The partials of Pi(v + e phi).                                            *)

let HMC_PARTIAL_LINE = prove
 (`!S (G:real^K->real^K^K) d s (v:real^N->real^K) phi e x i.
     cm_target S G d /\ open s /\ smooth_map_on s v /\ smooth_map_on s phi /\ x IN s /\
     v x + e % phi x IN cm_tube S d
     ==> partial_derivative i (\y. closest_point S (v y + e % phi y)) x =
         jacobian (closest_point S) (at (v x + e % phi x)) **
         (partial_derivative i v x + e % partial_derivative i phi x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  SUBGOAL_THEN `closest_point (S:real^K->bool) differentiable at ((v:real^N->real^K) x + e % phi x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `cm_tube S d:real^K->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N->real^K) differentiable at x /\ (phi:real^N->real^K) differentiable at x`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\y. (v:real^N->real^K) y + e % phi y) has_derivative
     (\h. frechet_derivative v (at x) h + e % frechet_derivative phi (at x) h)) (at x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[ETA_AX; GSYM FRECHET_DERIVATIVE_WORKS];
      MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN
      ASM_REWRITE_TAC[ETA_AX; GSYM FRECHET_DERIVATIVE_WORKS]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\y. (v:real^N->real^K) y + e % phi y`; `closest_point (S:real^K->bool)`;
                 `\h. frechet_derivative (v:real^N->real^K) (at x) h +
                      e % frechet_derivative phi (at x) h`;
                 `frechet_derivative (closest_point (S:real^K->bool))
                    (at ((v:real^N->real^K) x + e % phi x))`;
                 `x:real^N`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[o_DEF] THEN DISCH_TAC THEN
  REWRITE_TAC[partial_derivative] THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[SYM th]) THEN
  REWRITE_TAC[jacobian] THEN ASM_SIMP_TAC[MATRIX_WORKS; LINEAR_FRECHET_DERIVATIVE]);;

(* The compact sub-tube of points within d/2 of S.                          *)

let HMC_SUBTUBE = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> compact {p + q | p IN S /\ q IN cball(vec 0:real^K,d / &2)} /\
         {p + q | p IN S /\ q IN cball(vec 0:real^K,d / &2)} SUBSET cm_tube S d /\
         !p q. p IN S /\ norm q <= d / &2
               ==> p + q IN {p + q | p IN S /\ q IN cball(vec 0:real^K,d / &2)}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_SUMS THEN ASM_REWRITE_TAC[COMPACT_CBALL];
    REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_CBALL_0; cm_tube; IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`p:real^K`; `q:real^K`] THEN STRIP_TAC THEN
    EXISTS_TAC `p:real^K` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[NORM_ARITH `dist(p + q:real^K,p) = norm q`] THEN ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN REWRITE_TAC[IN_ELIM_THM; IN_CBALL_0] THEN
    MAP_EVERY EXISTS_TAC [`p:real^K`; `q:real^K`] THEN ASM_REWRITE_TAC[]]);;

(* Bounded continuous functions on bounded open sets are square integrable. *)

let HMC_BOUNDED_LSPACE = prove
 (`!s (f:real^M->real^N) B.
        open s /\ bounded s /\ f continuous_on s /\ (!x. x IN s ==> norm(f x) <= B)
        ==> f IN lspace s (&2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `&2`; `f:real^M->real^N`; `\x:real^M. lift B`]
                LSPACE_BOUNDED_MEASURABLE) THEN
  DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [REAL_ARITH_TAC;
    MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN];
    MATCH_MP_TAC LSPACE_CONST THEN ASM_SIMP_TAC[MEASURABLE_OPEN];
    REWRITE_TAC[NORM_LIFT] THEN ASM_MESON_TAC[REAL_ARITH `x <= b ==> x <= abs b`]]);;

(* The energy of Pi(v + e phi) on an open bounded set where the line stays *)
(* in a compact part of the tube.                                           *)

let HMC_GEN_LINE = prove
 (`!S (G:real^K->real^K^K) d s t k (v:real^2->real^K) phi e M.
     cm_target S G d /\ open s /\ bounded s /\ open t /\ s SUBSET t /\
     smooth_map_on t v /\ smooth_map_on t phi /\ compact k /\ k SUBSET cm_tube S d /\
     (!x. x IN s ==> v x + e % phi x IN k) /\
     (!x i. x IN s /\ 1 <= i /\ i <= dimindex(:2)
            ==> norm(partial_derivative i v x + e % partial_derivative i phi x) <= M)
     ==> (!i. 1 <= i /\ i <= dimindex(:2)
              ==> (\x. lift((jacobian (closest_point S) (at (v x + e % phi x)) **
                             (partial_derivative i v x + e % partial_derivative i phi x)) dot
                            (G(closest_point S (v x + e % phi x)) **
                             (jacobian (closest_point S) (at (v x + e % phi x)) **
                              (partial_derivative i v x + e % partial_derivative i phi x)))))
                  integrable_on s) /\
         cm_gen G s (\x. closest_point S (v x + e % phi x)) =
         sum(1..dimindex(:2))
           (\i. drop(integral s
                  (\x. lift((jacobian (closest_point S) (at (v x + e % phi x)) **
                             (partial_derivative i v x + e % partial_derivative i phi x)) dot
                            (G(closest_point S (v x + e % phi x)) **
                             (jacobian (closest_point S) (at (v x + e % phi x)) **
                              (partial_derivative i v x + e % partial_derivative i phi x)))))))
         / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  SUBGOAL_THEN `smooth_map_on s (v:real^2->real^K) /\ smooth_map_on s (phi:real^2->real^K)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `t:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on s (\x. (v:real^2->real^K) x + e % phi x)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on s (\x. closest_point (S:real^K->bool) ((v:real^2->real^K) x + e % phi x))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\x. closest_point (S:real^K->bool) ((v:real^2->real^K) x + e % phi x)) =
                  closest_point S o (\x. v x + e % phi x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `cm_tube S d:real^K->bool` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^K->bool`;
                 `(vectorize:real^K^K->real^(K,K)finite_prod) o
                  (\y. jacobian (closest_point (S:real^K->bool)) (at y))`] HMC_CONT_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `cm_tube S d:real^K->bool` THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    REWRITE_TAC[o_THM] THEN DISCH_THEN(X_CHOOSE_THEN `CJ0:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPEC `S:real^K->bool` COMPACT_IMP_BOUNDED) THEN ASM_REWRITE_TAC[BOUNDED_POS] THEN
  DISCH_THEN(X_CHOOSE_THEN `RS:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!x i. x IN s
          ==> partial_derivative i
                (\x. closest_point (S:real^K->bool) ((v:real^2->real^K) x + e % phi x)) x =
              jacobian (closest_point S) (at (v x + e % phi x)) **
              (partial_derivative i v x + e % partial_derivative i phi x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HMC_PARTIAL_LINE THEN
    MAP_EVERY EXISTS_TAC [`G:real^K->real^K^K`; `d:real`; `s:real^2->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_w12 s (\x. closest_point (S:real^K->bool) ((v:real^2->real^K) x + e % phi x))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:2)`; `(:K)`] WAN_W12_C1) THEN REWRITE_TAC[WAN_W12_C1_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPECL [`s:real^2->bool`;
      `\x. closest_point (S:real^K->bool) ((v:real^2->real^K) x + e % phi x)`]) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[smooth_map_on];
      MATCH_MP_TAC HMC_BOUNDED_LSPACE THEN EXISTS_TAC `RS:real` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN MATCH_MP_TAC HMC_BOUNDED_LSPACE THEN
      EXISTS_TAC `CJ0 * M` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN REWRITE_TAC[ETA_AX] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN ASM_REWRITE_TAC[];
        X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `norm((vectorize:real^K^K->real^(K,K)finite_prod)
                     (jacobian (closest_point (S:real^K->bool))
                        (at ((v:real^2->real^K) x + e % phi x)))) *
                    norm(partial_derivative i v x + e % partial_derivative i phi x)` THEN
        REWRITE_TAC[HMC_MAT_NORM] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
        ASM_SIMP_TAC[NORM_POS_LE]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `continuously_differentiable 1 s
                  (\x. closest_point (S:real^K->bool) ((v:real^2->real^K) x + e % phi x))`
  ASSUME_TAC THENL [ASM_MESON_TAC[smooth_map_on]; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_EQ THEN
    EXISTS_TAC `\x. lift(partial_derivative i
                  (\x. closest_point (S:real^K->bool) ((v:real^2->real^K) x + e % phi x)) x dot
                  ((G:real^K->real^K^K) (closest_point S (v x + e % phi x)) **
                   partial_derivative i (\x. closest_point S (v x + e % phi x)) x))` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC HMC_QUAD_INTEGRABLE THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] HMC_TARGET_CONSTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXISTS_TAC `Lam1:real` THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HMC_PD_LSPACE THEN ASM_REWRITE_TAC[DIMINDEX_2] THEN
      ASM_MESON_TAC[DIMINDEX_2];
      MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN] THEN
      SUBGOAL_THEN `(vectorize:real^K^K->real^(K,K)finite_prod) o
                    (\x. (G:real^K->real^K^K) (closest_point S ((v:real^2->real^K) x + e % phi x))) =
                    (vectorize o G) o (\x. closest_point S (v x + e % phi x))` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^K)` THEN
        REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
        ASM_REWRITE_TAC[]];
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm(xi:real^K) * norm((G:real^K->real^K^K)
                   (closest_point S ((v:real^2->real^K) x + e % phi x)) ** xi)` THEN
      REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm(xi:real^K) * (Lam1 * norm xi)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[cm_gen] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[HMC_GDIR_CLASSICAL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_EQ THEN
  ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* The first variation of the energy of Pi(v + e phi) at e = 0, by           *)
(* differentiation under the integral sign.                                  *)
(* ========================================================================= *)

let HMC_PARTIALS_BOUND = prove
 (`!s k (f:real^M->real^N).
        open s /\ smooth_map_on s f /\ compact k /\ k SUBSET s
        ==> ?B. &0 <= B /\
                !x i. x IN k /\ 1 <= i /\ i <= dimindex(:M)
                      ==> norm(partial_derivative i f x) <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `k:real^M->bool`; `f:real^M->real^N`] HMC_DERIV_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[partial_derivative] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `B * norm(basis i:real^M)` THEN ASM_SIMP_TAC[NORM_BASIS; REAL_LE_REFL] THEN
  REWRITE_TAC[REAL_MUL_RID; REAL_LE_REFL]);;

(* The bound for the derivative of the density along the line.              *)

let HMC_FPRIME_BOUND = prove
 (`!(DJm:real^K^K) (Jm:real^K^K) (Gm:real^K^K) (DGm:real^K^K) (p:real^K) q c1 c2 c3 c4 P Q.
        &0 <= c1 /\ &0 <= c2 /\ &0 <= c3 /\ &0 <= c4 /\ &0 <= P /\ &0 <= Q /\
        (!xi. norm(DJm ** xi) <= c1 * norm xi) /\ (!xi. norm(Jm ** xi) <= c2 * norm xi) /\
        (!xi. norm(Gm ** xi) <= c3 * norm xi) /\ (!xi. norm(DGm ** xi) <= c4 * norm xi) /\
        norm p <= P /\ norm q <= Q
        ==> abs(&2 * ((DJm ** p + Jm ** q) dot (Gm ** (Jm ** p))) +
                (Jm ** p) dot (DGm ** (Jm ** p)))
            <= &2 * ((c1 * P + c2 * Q) * (c3 * (c2 * P))) + (c2 * P) * (c4 * (c2 * P))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `norm((Jm:real^K^K) ** (p:real^K)) <= c2 * P` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c2 * norm(p:real^K)` THEN
    ASM_SIMP_TAC[REAL_LE_LMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm((DJm:real^K^K) ** (p:real^K) + (Jm:real^K^K) ** (q:real^K))
                <= c1 * P + c2 * Q` ASSUME_TAC THENL
   [MATCH_MP_TAC(NORM_ARITH `norm(a:real^K) <= x /\ norm(b:real^K) <= y
                             ==> norm(a + b) <= x + y`) THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `c1 * norm(p:real^K)`; EXISTS_TAC `c2 * norm(q:real^K)`] THEN
    ASM_SIMP_TAC[REAL_LE_LMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm((Gm:real^K^K) ** ((Jm:real^K^K) ** (p:real^K))) <= c3 * (c2 * P) /\
                norm((DGm:real^K^K) ** ((Jm:real^K^K) ** (p:real^K))) <= c4 * (c2 * P)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `c3 * norm((Jm:real^K^K) ** (p:real^K))`;
      EXISTS_TAC `c4 * norm((Jm:real^K^K) ** (p:real^K))`] THEN
    ASM_SIMP_TAC[REAL_LE_LMUL];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `abs a <= x /\ abs b <= y ==> abs(&2 * a + b) <= &2 * x + y`) THEN
  CONJ_TAC THEN
  W(MP_TAC o PART_MATCH lhand NORM_CAUCHY_SCHWARZ_ABS o lhand o snd) THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE]);;

let HMC_E1_LEMMA = prove
 (`!d M. &0 < d /\ &0 <= M ==> d / (&2 * (M + &1)) * M <= d / &2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `d / (&2 * (M + &1)) * (M + &1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    SUBGOAL_THEN `&0 < M + &1` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]]);;

(* The first variation of the energy of Pi(v + e phi).                      *)

let HMC_FIRST_VARIATION = prove
 (`!S (G:real^K->real^K^K) d (a:real^2) r r' (v:real^2->real^K) (phi:real^2->real^K).
     cm_target S G d /\ &0 < r' /\ r' < r /\ smooth_map_on (ball(a,r)) v /\
     (!x. x IN ball(a,r) ==> v x IN S) /\ smooth_map_on (:real^2) phi
     ==> ((\e. cm_gen G (ball(a,r')) (\x. closest_point S (v x + e % phi x)))
          has_real_derivative
          sum(1..dimindex(:2))
            (\i. drop(integral (ball(a,r'))
                   (\x. lift(hmc_ld S G v phi (\y. partial_derivative i phi y) i x)))) / &2)
         (atreal (&0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_SUBTUBE) THEN
  ABBREV_TAC `T2 = {p + q | p IN S /\ q IN cball(vec 0:real^K,d / &2)}` THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] HMC_TARGET_CONSTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `cball(a:real^2,r') SUBSET ball(a,r)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ball(a:real^2,r') SUBSET cball(a,r')` ASSUME_TAC THENL
   [REWRITE_TAC[BALL_SUBSET_CBALL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`cball(a:real^2,r')`; `phi:real^2->real^K`] HMC_CONT_BOUND) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COMPACT_CBALL] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(:real^2)` THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SUBSET_UNIV];
    DISCH_THEN(X_CHOOSE_THEN `Mf:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`(:real^2)`; `cball(a:real^2,r')`; `phi:real^2->real^K`]
                HMC_PARTIALS_BOUND) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; COMPACT_CBALL; SUBSET_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `M1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`ball(a:real^2,r)`; `cball(a:real^2,r')`; `v:real^2->real^K`]
                HMC_PARTIALS_BOUND) THEN
  ASM_REWRITE_TAC[OPEN_BALL; COMPACT_CBALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `M2:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`T2:real^K->bool`;
                 `(vectorize:real^K^K->real^(K,K)finite_prod) o
                  (\y. jacobian (closest_point (S:real^K->bool)) (at y))`] HMC_CONT_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `cm_tube S d:real^K->bool` THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    REWRITE_TAC[o_THM] THEN DISCH_THEN(X_CHOOSE_THEN `CJ0:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`cm_tube S d:real^K->bool`; `T2:real^K->bool`;
                 `(vectorize:real^K^K->real^(K,K)finite_prod) o
                  (\y. jacobian (closest_point (S:real^K->bool)) (at y))`] HMC_DERIV_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `CJ1:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `e1 = d / (&2 * (Mf + &1))` THEN
  SUBGOAL_THEN `&0 < e1` ASSUME_TAC THENL
   [EXPAND_TAC "e1" THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!e x. abs e <= e1 /\ x IN cball(a:real^2,r')
                      ==> (v:real^2->real^K) x + e % phi x IN T2` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[NORM_MUL] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `e1 * Mf` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_ABS_POS; NORM_POS_LE];
      EXPAND_TAC "e1" THEN MATCH_MP_TAC HMC_E1_LEMMA THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC
   `FF = \i e x. (jacobian (closest_point S) (at ((v:real^2->real^K) x + e % phi x)) **
                  (partial_derivative i v x + e % partial_derivative i phi x)) dot
                 ((G:real^K->real^K^K) (closest_point S (v x + e % phi x)) **
                  (jacobian (closest_point S) (at (v x + e % phi x)) **
                   (partial_derivative i v x + e % partial_derivative i phi x)))` THEN
  ABBREV_TAC
   `FF' = \i e x.
      &2 * ((mderiv (\y. jacobian (closest_point (S:real^K->bool)) (at y))
                    ((v:real^2->real^K) x + e % phi x) (phi x) **
               (partial_derivative i v x + e % partial_derivative i phi x) +
             jacobian (closest_point S) (at (v x + e % phi x)) ** partial_derivative i phi x) dot
            ((G:real^K->real^K^K) (closest_point S (v x + e % phi x)) **
             (jacobian (closest_point S) (at (v x + e % phi x)) **
              (partial_derivative i v x + e % partial_derivative i phi x)))) +
      (jacobian (closest_point S) (at (v x + e % phi x)) **
       (partial_derivative i v x + e % partial_derivative i phi x)) dot
      (mderiv G (closest_point S (v x + e % phi x))
         (jacobian (closest_point S) (at (v x + e % phi x)) ** phi x) **
       (jacobian (closest_point S) (at (v x + e % phi x)) **
        (partial_derivative i v x + e % partial_derivative i phi x)))` THEN
  (* the energy along the line as a sum of integrals *)
  SUBGOAL_THEN
   `!e. abs e < e1
        ==> (!i. 1 <= i /\ i <= dimindex(:2)
                 ==> (\x. lift((FF:num->real->real^2->real) i e x)) integrable_on ball(a,r')) /\
            cm_gen G (ball(a,r')) (\x. closest_point S ((v:real^2->real^K) x + e % phi x)) =
            sum(1..dimindex(:2)) (\i. drop(integral (ball(a,r'))
                                     (\x. lift((FF:num->real->real^2->real) i e x)))) / &2`
  (LABEL_TAC "EN") THENL
   [GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "FF" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC HMC_GEN_LINE THEN
    MAP_EVERY EXISTS_TAC [`d:real`; `ball(a:real^2,r)`; `T2:real^K->bool`;
                          `M2 + e1 * M1`] THEN
    ASM_REWRITE_TAC[OPEN_BALL; BOUNDED_BALL] THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(NORM_ARITH `norm(a:real^K) <= x /\ norm(b:real^K) <= y
                               ==> norm(a + b) <= x + y`) THEN
      REWRITE_TAC[NORM_MUL] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
          `!x i. x IN cball(a:real^2,r') /\ 1 <= i /\ i <= dimindex(:2)
                 ==> norm(partial_derivative i (v:real^2->real^K) x) <= M2`) (concl th))) THEN
        ASM SET_TAC[];
        MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
          `!x i. x IN cball(a:real^2,r') /\ 1 <= i /\ i <= dimindex(:2)
                 ==> norm(partial_derivative i (phi:real^2->real^K) x) <= M1`) (concl th))) THEN
        ASM SET_TAC[]]];
    ALL_TAC] THEN
  ABBREV_TAC
   `Bd = &2 * (((CJ1 * Mf) * (M2 + e1 * M1) + CJ0 * M1) * (Lam1 * (CJ0 * (M2 + e1 * M1)))) +
         (CJ0 * (M2 + e1 * M1)) * ((CG * (CJ0 * Mf)) * (CJ0 * (M2 + e1 * M1)))` THEN
  SUBGOAL_THEN
   `!e x. abs e < e1 /\ x IN ball(a:real^2,r')
          ==> (v:real^2->real^K) x + e % phi x IN T2 /\ v x IN S /\
              norm(phi x) <= Mf /\
              (!i. 1 <= i /\ i <= dimindex(:2)
                   ==> norm(partial_derivative i v x + e % partial_derivative i phi x)
                       <= M2 + e1 * M1 /\
                       norm(partial_derivative i phi x) <= M1)`
  (LABEL_TAC "PT") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^2) IN cball(a,r')` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC(NORM_ARITH `norm(a:real^K) <= x /\ norm(b:real^K) <= y
                                 ==> norm(a + b) <= x + y`) THEN
        REWRITE_TAC[NORM_MUL] THEN CONJ_TAC THENL
         [ASM_SIMP_TAC[];
          MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE] THEN
          ASM_SIMP_TAC[REAL_LT_IMP_LE]];
        ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:2)
        ==> (\x. lift((FF':num->real->real^2->real) i (&0) x)) integrable_on ball(a,r') /\
            ((\e. drop(integral (ball(a:real^2,r'))
                         (\x. lift((FF:num->real->real^2->real) i e x))))
             has_real_derivative drop(integral (ball(a,r')) (\x. lift(FF' i (&0) x))))
            (atreal (&0))`
  (LABEL_TAC "DER") THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`(FF:num->real->real^2->real) i`; `(FF':num->real->real^2->real) i`;
                   `\x:real^2. Bd:real`; `real_interval(--e1,e1)`; `ball(a:real^2,r')`]
                  GRGT_HAS_REAL_DERIVATIVE_INTEGRAL_DOMINATED) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN REPEAT CONJ_TAC THENL
       [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
        USE_THEN "EN" (MP_TAC o SPEC `e:real`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT1) THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[INTEGRABLE_ON_CONST] THEN DISJ2_TAC THEN REWRITE_TAC[MEASURABLE_BALL];
        MAP_EVERY X_GEN_TAC [`e:real`; `x:real^2`] THEN STRIP_TAC THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
        EXPAND_TAC "FF" THEN EXPAND_TAC "FF'" THEN REWRITE_TAC[] THEN
        MATCH_MP_TAC HMC_LINE_DERIV THEN EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "PT" (MP_TAC o SPECL [`e:real`; `x:real^2`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
        MAP_EVERY X_GEN_TAC [`e:real`; `x:real^2`] THEN STRIP_TAC THEN
        USE_THEN "PT" (MP_TAC o SPECL [`e:real`; `x:real^2`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
          (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `i:num`)))) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        EXPAND_TAC "FF'" THEN EXPAND_TAC "Bd" THEN REWRITE_TAC[] THEN
        MATCH_MP_TAC HMC_FPRIME_BOUND THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN
         `!xi. norm(jacobian (closest_point (S:real^K->bool))
                     (at ((v:real^2->real^K) x + e % phi x)) ** xi) <= CJ0 * norm xi`
        ASSUME_TAC THENL
         [X_GEN_TAC `xi:real^K` THEN MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC `norm((vectorize:real^K^K->real^(K,K)finite_prod)
                       (jacobian (closest_point (S:real^K->bool))
                          (at ((v:real^2->real^K) x + e % phi x)))) * norm(xi:real^K)` THEN
          REWRITE_TAC[HMC_MAT_NORM] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
          ASM_SIMP_TAC[NORM_POS_LE];
          ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
          REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
          X_GEN_TAC `xi:real^K` THEN REWRITE_TAC[mderiv] THEN
          MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC `norm(frechet_derivative ((vectorize:real^K^K->real^(K,K)finite_prod) o
                        (\y. jacobian (closest_point (S:real^K->bool)) (at y)))
                        (at ((v:real^2->real^K) x + e % phi x)) (phi x)) * norm(xi:real^K)` THEN
          REWRITE_TAC[HMC_MATRIFY_NORM] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
          REWRITE_TAC[NORM_POS_LE] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC `CJ1 * norm((phi:real^2->real^K) x)` THEN
          CONJ_TAC THENL [ASM_SIMP_TAC[]; MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
          ASM_SIMP_TAC[];
          X_GEN_TAC `xi:real^K` THEN MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC `CG * norm(jacobian (closest_point (S:real^K->bool))
                         (at ((v:real^2->real^K) x + e % phi x)) ** phi x) * norm(xi:real^K)` THEN
          CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
          REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
          REWRITE_TAC[NORM_POS_LE; GSYM REAL_MUL_ASSOC] THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC `CJ0 * norm((phi:real^2->real^K) x)` THEN
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `&0`) THEN ANTS_TAC THENL
     [REWRITE_TAC[IN_REAL_INTERVAL] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      EXISTS_TAC `e1 / &2` THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC
     `((\x. drop(integral (ball(a:real^2,r')) (\v. lift((FF:num->real->real^2->real) i x v))))
       has_real_derivative drop(integral (ball(a,r')) (\v. lift(FF' i (&0) v))))
      (atreal (&0) within real_interval(--e1,e1))` THEN
    SIMP_TAC[HAS_REAL_DERIVATIVE_WITHIN_REAL_OPEN; REAL_OPEN_REAL_INTERVAL; IN_REAL_INTERVAL;
             REAL_ARITH `&0 < e1 ==> --e1 < &0 /\ &0 < e1`;
             ASSUME `&0 < e1`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i x. 1 <= i /\ i <= dimindex(:2) /\ x IN ball(a:real^2,r')
          ==> (FF':num->real->real^2->real) i (&0) x =
              hmc_ld (S:real^K->bool) (G:real^K->real^K^K) (v:real^2->real^K)
                     (phi:real^2->real^K) (\y. partial_derivative i phi y) i x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "FF'" THEN
    REWRITE_TAC[hmc_ld; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    SUBGOAL_THEN `(v:real^2->real^K) x IN S` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `jacobian (closest_point (S:real^K->bool)) (at ((v:real^2->real^K) x)) **
                  partial_derivative i v x = partial_derivative i v x` ASSUME_TAC THENL
     [MATCH_MP_TAC HMC_TANGENT_PARTIAL THEN
      MAP_EVERY EXISTS_TAC [`G:real^K->real^K^K`; `d:real`; `ball(a:real^2,r)`] THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:2))
      (\i. drop(integral (ball(a:real^2,r'))
             (\x. lift(hmc_ld (S:real^K->bool) (G:real^K->real^K^K) (v:real^2->real^K)
                              (phi:real^2->real^K) (\y. partial_derivative i phi y) i x)))) =
    sum(1..dimindex(:2))
      (\i. drop(integral (ball(a,r')) (\x. lift((FF':num->real->real^2->real) i (&0) x))))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_EQ THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  EXISTS_TAC `\e. sum(1..dimindex(:2))
                    (\i. drop(integral (ball(a:real^2,r'))
                           (\x. lift((FF:num->real->real^2->real) i e x)))) / &2` THEN
  EXISTS_TAC `e1:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "EN" (MP_TAC o SPEC `e:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_RMUL_ATREAL THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* The weak Euler-Lagrange equation of a harmonic map for test maps.         *)
(* ========================================================================= *)

let HMC_VTEST_PD_ZERO = prove
 (`!(f:real^N->real^K) k x i.
        smooth_map_on (:real^N) f /\ compact k /\ (!y. ~(y IN k) ==> f y = vec 0) /\
        ~(x IN k)
        ==> partial_derivative i f x = vec 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[partial_derivative] THEN
  SUBGOAL_THEN `frechet_derivative (f:real^N->real^K) (at x) = (\h. vec 0)`
  (fun th -> REWRITE_TAC[th]) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
  MAP_EVERY EXISTS_TAC [`\y:real^N. vec 0:real^K`; `(:real^N) DIFF k`] THEN
  ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED; IN_DIFF; IN_UNIV; HAS_DERIVATIVE_CONST]);;

let HMC_INTEGRAL_SUPPORT_SUBSET = prove
 (`!(g:real^N->real^K) k t s.
     k SUBSET t /\ t SUBSET s /\ (!x. x IN s DIFF k ==> g x = vec 0)
     ==> integral t g = integral s g`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM INTEGRAL_RESTRICT_UNIV] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^N` THEN
  ASM_CASES_TAC `(x:real^N) IN t` THENL
   [SUBGOAL_THEN `(x:real^N) IN s` ASSUME_TAC THENL [ASM SET_TAC[]; ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]]);;

let HMC_MDERIV_ZERO = prove
 (`!(G:real^N->real^N^N) z.
        ((vectorize:real^N^N->real^(N,N)finite_prod) o G) differentiable (at z)
        ==> mderiv G z (vec 0) = mat 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mderiv] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_0 (MATCH_MP LINEAR_FRECHET_DERIVATIVE th)]) THEN
  REWRITE_TAC[MATRIFY_0]);;

(* The Euler-Lagrange density vanishes where the variation and its partials *)
(* vanish.                                                                   *)

let HMC_LD_ZERO = prove
 (`!S (G:real^K->real^K^K) d (v:real^2->real^K) h (Y:real^2->real^K) i x.
     cm_target S G d /\ v x IN S /\ h x = vec 0 /\ Y x = vec 0
     ==> hmc_ld S G v h Y i x = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  ASM_REWRITE_TAC[hmc_ld; MATRIX_VECTOR_MUL_RZERO] THEN
  SUBGOAL_THEN
   `mderiv (\y. jacobian (closest_point (S:real^K->bool)) (at y)) ((v:real^2->real^K) x) (vec 0) =
    mat 0 /\ mderiv (G:real^K->real^K^K) (v x) (vec 0) = mat 0`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC HMC_MDERIV_ZERO THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `cm_tube S d:real^K->bool` THEN ASM SET_TAC[];
      EXISTS_TAC `(:real^K)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV]];
    REWRITE_TAC[MATRIX_VECTOR_MUL_LZERO; VECTOR_ADD_LID; DOT_LZERO; DOT_RZERO] THEN
    REAL_ARITH_TAC]);;

(* The weak Euler-Lagrange equation for test maps.                          *)

let HMC_EL_TEST = prove
 (`!S (G:real^K->real^K^K) d (a:real^2) r (v:real^2->real^K) (phi:real^2->real^K).
     cm_target S G d /\ &0 < r /\ cm_harmonic S G (ball(a,r)) v /\
     wan_vtest (ball(a,r)) phi
     ==> sum(1..dimindex(:2))
           (\i. drop(integral (ball(a,r))
                  (\x. lift(hmc_ld S G v phi (\y. partial_derivative i phi y) i x)))) = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_harmonic]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [wan_vtest]) THEN
  MP_TAC(ISPECL [`k:real^2->bool`; `a:real^2`; `r:real`] COMPACT_SHRINK_ENCLOSING_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r':real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `a:real^2`; `r:real`;
                 `r':real`; `v:real^2->real^K`; `phi:real^2->real^K`] HMC_FIRST_VARIATION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `((\e. cm_gen G (ball(a:real^2,r'))
            (\x. closest_point S ((v:real^2->real^K) x + e % phi x)))
     has_real_derivative &0) (atreal (&0))` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[OPEN_BALL; BOUNDED_BALL; CLOSURE_BALL] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[wan_vtest] THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `k:real^2->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:2))
      (\i. drop(integral (ball(a:real^2,r'))
             (\x. lift(hmc_ld (S:real^K->bool) (G:real^K->real^K^K) (v:real^2->real^K)
                              (phi:real^2->real^K) (\y. partial_derivative i phi y) i x)))) = &0`
  MP_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `x / &2 = &0 ==> x = &0`) THEN
    MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
    MAP_EVERY EXISTS_TAC
     [`\e. cm_gen G (ball(a:real^2,r'))
             (\x. closest_point S ((v:real^2->real^K) x + e % phi x))`; `&0`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC HMC_INTEGRAL_SUPPORT_SUBSET THEN
  EXISTS_TAC `k:real^2->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN MATCH_MP_TAC HMC_LD_ZERO THEN
  EXISTS_TAC `d:real` THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC HMC_VTEST_PD_ZERO THEN EXISTS_TAC `k:real^2->bool` THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Measurability and linearity of the Euler-Lagrange density; test maps and  *)
(* W^{1,2}_0.                                                                *)
(* ========================================================================= *)

(* A field of linear maps with continuous columns applied to a measurable   *)
(* map is measurable.                                                         *)

let HMC_MEAS_LINEAR_APPLY = prove
 (`!s (D:real^M->real^N->real^P) (h:real^M->real^N).
        lebesgue_measurable s /\ (!x. x IN s ==> linear(D x)) /\
        (!k. 1 <= k /\ k <= dimindex(:N) ==> (\x. D x (basis k)) continuous_on s) /\
        h measurable_on s
        ==> (\x. D x (h x)) measurable_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_ON_EQ THEN
  EXISTS_TAC `\x. vsum(1..dimindex(:N))
                    (\k. drop(lift((h:real^M->real^N) x$k)) %
                         (D:real^M->real^N->real^P) x (basis k))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
    ASM_SIMP_TAC[LINEAR_VSUM_MUL; FINITE_NUMSEG];
    MATCH_MP_TAC MEASURABLE_ON_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MEASURABLE_ON_DROP_MUL THEN CONJ_TAC THENL
     [UNDISCH_TAC `(h:real^M->real^N) measurable_on s` THEN
      GEN_REWRITE_TAC LAND_CONV [MEASURABLE_ON_COMPONENTWISE] THEN
      DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      ASM_SIMP_TAC[]]]);;

let HMC_MEAS_DOT = prove
 (`!s (f:real^M->real^N) g.
        f measurable_on s /\ g measurable_on s ==> (\x. lift(f x dot g x)) measurable_on s`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[] (ISPEC `\x y:real^N. lift(x dot y)` MEASURABLE_ON_BILINEAR)) THEN
  ASM_REWRITE_TAC[BILINEAR_DOT]);;

let HMC_MEAS_MATMUL = prove
 (`!s (P:real^M->real^(N,N)finite_prod) (X:real^M->real^N).
        P measurable_on s /\ X measurable_on s
        ==> (\x. (matrify(P x):real^N^N) ** X x) measurable_on s`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[] (ISPEC `\(p:real^(N,N)finite_prod) (q:real^N).
                                         (matrify p:real^N^N) ** q` MEASURABLE_ON_BILINEAR)) THEN
  ASM_REWRITE_TAC[LRG_BILINEAR_MATRIFY_MUL]);;

let HMC_LD_FORM_MEAS = prove
 (`!s (P1:real^M->real^(K,K)finite_prod) P2 P3 P4 (X:real^M->real^K) Y.
        P1 measurable_on s /\ P2 measurable_on s /\ P3 measurable_on s /\
        P4 measurable_on s /\ X measurable_on s /\ Y measurable_on s
        ==> (\x. lift(&2 * (((matrify(P1 x):real^K^K) ** X x +
                             (matrify(P2 x):real^K^K) ** Y x) dot
                            ((matrify(P3 x):real^K^K) ** X x)) +
                      X x dot ((matrify(P4 x):real^K^K) ** X x))) measurable_on s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN
  MATCH_MP_TAC MEASURABLE_ON_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_ON_CMUL THEN MATCH_MP_TAC HMC_MEAS_DOT THEN CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_ON_ADD THEN CONJ_TAC THEN MATCH_MP_TAC HMC_MEAS_MATMUL THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC HMC_MEAS_MATMUL THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC HMC_MEAS_DOT THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HMC_MEAS_MATMUL THEN ASM_REWRITE_TAC[]]);;

(* The Euler-Lagrange density of measurable data is measurable.             *)

let HMC_LD_MEASURABLE = prove
 (`!S (G:real^K->real^K^K) d s (v:real^2->real^K) (h:real^2->real^K) (Y:real^2->real^K) i.
     cm_target S G d /\ open s /\ smooth_map_on s v /\ (!x. x IN s ==> v x IN S) /\
     h measurable_on s /\ Y measurable_on s
     ==> (\x. lift(hmc_ld S G v h Y i x)) measurable_on s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  ABBREV_TAC `JJ = (vectorize:real^K^K->real^(K,K)finite_prod) o
                   (\y. jacobian (closest_point (S:real^K->bool)) (at y))` THEN
  ABBREV_TAC `GG = (vectorize:real^K^K->real^(K,K)finite_prod) o (G:real^K->real^K^K)` THEN
  SUBGOAL_THEN `lebesgue_measurable (s:real^2->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^2->real^K) continuous_on s` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (v:real^2->real^K) s SUBSET cm_tube S d` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!(Ff:real^K->real^(K,K)finite_prod) t.
                   open t /\ IMAGE (v:real^2->real^K) s SUBSET t /\ smooth_map_on t Ff
                   ==> (\x. Ff(v x)) continuous_on s /\
                       (!k. (\x. frechet_derivative Ff (at (v x)) (basis k)) continuous_on s) /\
                       (!x. x IN s ==> linear(frechet_derivative Ff (at (v x))))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `(\x. (Ff:real^K->real^(K,K)finite_prod) ((v:real^2->real^K) x)) = Ff o v`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `t:real^K->bool` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
      GEN_TAC THEN
      SUBGOAL_THEN `(\x. frechet_derivative (Ff:real^K->real^(K,K)finite_prod)
                           (at ((v:real^2->real^K) x)) (basis k)) =
                    (\z. frechet_derivative Ff (at z) (basis k)) o v` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `t:real^K->bool` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SMOOTH_MAP_ON_FRECHET_DERIVATIVE];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `t:real^K->bool` THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (cm_tube S d) (JJ:real^K->real^(K,K)finite_prod) /\
                smooth_map_on (:real^K) (GG:real^K->real^(K,K)finite_prod)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "JJ" THEN EXPAND_TAC "GG" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`JJ:real^K->real^(K,K)finite_prod`; `cm_tube S d:real^K->bool`]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`GG:real^K->real^(K,K)finite_prod`; `(:real^K)`]) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!w:real^2->real^K. w measurable_on s
                  ==> (\x. jacobian (closest_point (S:real^K->bool)) (at ((v:real^2->real^K) x)) **
                           w x) measurable_on s` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `\x. (JJ:real^K->real^(K,K)finite_prod) ((v:real^2->real^K) x)`;
                   `w:real^2->real^K`] HMC_MEAS_MATMUL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      ASM_REWRITE_TAC[];
      EXPAND_TAC "JJ" THEN REWRITE_TAC[o_THM; MATRIFY_VECTORIZE]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^2->bool`;
                 `\x. frechet_derivative (JJ:real^K->real^(K,K)finite_prod)
                        (at ((v:real^2->real^K) x)) ((h:real^2->real^K) x)`;
                 `\x. (JJ:real^K->real^(K,K)finite_prod) ((v:real^2->real^K) x)`;
                 `\x. (GG:real^K->real^(K,K)finite_prod) ((v:real^2->real^K) x)`;
                 `\x. frechet_derivative (GG:real^K->real^(K,K)finite_prod)
                        (at ((v:real^2->real^K) x))
                        (jacobian (closest_point (S:real^K->bool)) (at (v x)) ** (h:real^2->real^K) x)`;
                 `\x. partial_derivative i (v:real^2->real^K) x`; `Y:real^2->real^K`]
                HMC_LD_FORM_MEAS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[] (ISPECL
        [`s:real^2->bool`;
         `\x. frechet_derivative (JJ:real^K->real^(K,K)finite_prod) (at ((v:real^2->real^K) x))`]
        HMC_MEAS_LINEAR_APPLY)) THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC(REWRITE_RULE[] (ISPECL
        [`s:real^2->bool`;
         `\x. frechet_derivative (GG:real^K->real^(K,K)finite_prod) (at ((v:real^2->real^K) x))`]
        HMC_MEAS_LINEAR_APPLY)) THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      ASM_REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; hmc_ld; mderiv] THEN X_GEN_TAC `x:real^2` THEN
  EXPAND_TAC "JJ" THEN EXPAND_TAC "GG" THEN REWRITE_TAC[o_THM; MATRIFY_VECTORIZE]);;

let HMC_MDERIV_SUB = prove
 (`!(G:real^N->real^N^N) z a b.
        ((vectorize:real^N^N->real^(N,N)finite_prod) o G) differentiable (at z)
        ==> mderiv G z (a - b) = mderiv G z a - mderiv G z b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mderiv; GSYM MATRIFY_SUB] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC LINEAR_SUB THEN
  ASM_SIMP_TAC[LINEAR_FRECHET_DERIVATIVE]);;

(* The Euler-Lagrange density is linear in the direction and its partial.  *)

let HMC_LD_SUB = prove
 (`!S (G:real^K->real^K^K) d (v:real^2->real^K) h1 h2 (Y1:real^2->real^K) Y2 i x.
     cm_target S G d /\ v x IN S
     ==> hmc_ld S G v h1 Y1 i x - hmc_ld S G v h2 Y2 i x =
         hmc_ld S G v (\y. h1 y - h2 y) (\y. Y1 y - Y2 y) i x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  SUBGOAL_THEN
   `((vectorize:real^K^K->real^(K,K)finite_prod) o
     (\y. jacobian (closest_point (S:real^K->bool)) (at y))) differentiable (at ((v:real^2->real^K) x)) /\
    ((vectorize:real^K^K->real^(K,K)finite_prod) o (G:real^K->real^K^K)) differentiable (at (v x))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `cm_tube S d:real^K->bool` THEN ASM SET_TAC[];
      EXISTS_TAC `(:real^K)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV]];
    ALL_TAC] THEN
  REWRITE_TAC[hmc_ld] THEN ASM_SIMP_TAC[HMC_MDERIV_SUB; MATRIX_VECTOR_MUL_SUB_LDISTRIB] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB; MATRIX_VECTOR_MUL_SUB_LDISTRIB;
              DOT_LSUB; DOT_RSUB; DOT_LADD; DOT_RADD] THEN
  REAL_ARITH_TAC);;

(* The pointwise bound of the Euler-Lagrange density.                       *)

let HMC_LD_BOUND = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> ?Ca Cb. &0 <= Ca /\ &0 <= Cb /\
                 !(v:real^2->real^K) h Y i x.
                    v x IN S
                    ==> abs(hmc_ld S G v h Y i x)
                        <= Ca * norm(h x) * norm(partial_derivative i v x) pow 2 +
                           Cb * norm(partial_derivative i v x) * norm(Y x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_CONSTS) THEN
  MAP_EVERY EXISTS_TAC [`&2 * CJ * Lam1 + CG`; `&2 * Lam1`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[hmc_ld] THEN
  MP_TAC(ISPECL [`jacobian (closest_point (S:real^K->bool)) (at ((v:real^2->real^K) x))`;
                 `(G:real^K->real^K^K) ((v:real^2->real^K) x)`;
                 `mderiv (\y. jacobian (closest_point (S:real^K->bool)) (at y)) ((v:real^2->real^K) x)`;
                 `mderiv (G:real^K->real^K^K) ((v:real^2->real^K) x)`;
                 `partial_derivative i (v:real^2->real^K) x`; `(Y:real^2->real^K) x`;
                 `(h:real^2->real^K) x`; `Lam1:real`; `CJ:real`; `CG:real`] HMC_LDENS_BOUND) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `y = z ==> x <= y ==> x <= z`) THEN REAL_ARITH_TAC);;

(* Integrability of the Euler-Lagrange density for an a.e. bounded          *)
(* direction with square integrable partial.                                *)

let HMC_LD_INTEGRABLE = prove
 (`!S (G:real^K->real^K^K) d s (v:real^2->real^K) (h:real^2->real^K) (Y:real^2->real^K) i M Z.
     cm_target S G d /\ open s /\ smooth_map_on s v /\ (!x. x IN s ==> v x IN S) /\
     wan_w12 s v /\ 1 <= i /\ i <= dimindex(:2) /\
     h measurable_on s /\ negligible Z /\ (!x. x IN s DIFF Z ==> norm(h x) <= M) /\
     Y IN lspace s (&2)
     ==> (\x. lift(hmc_ld S G v h Y i x)) integrable_on s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Ca:real` (X_CHOOSE_THEN `Cb:real` STRIP_ASSUME_TAC) o
    MATCH_MP HMC_LD_BOUND) THEN
  SUBGOAL_THEN `(\x. partial_derivative i (v:real^2->real^K) x) IN lspace s (&2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HMC_PD_LSPACE THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[smooth_map_on];
    ALL_TAC] THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_AE_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `\x. (Ca * abs M) % lift(norm(partial_derivative i (v:real^2->real^K) x) pow 2) +
                  Cb % lift(norm(partial_derivative i v x) * norm((Y:real^2->real^K) x))` THEN
  EXISTS_TAC `Z:real^2->bool` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HMC_LD_MEASURABLE THEN EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[lspace; IN_ELIM_THM];
    MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC INTEGRABLE_CMUL THENL
     [MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC LSPACE_INTEGRABLE_PRODUCT THEN
      MAP_EVERY EXISTS_TAC [`&2`; `&2`] THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV];
    X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
    REWRITE_TAC[NORM_LIFT; DROP_ADD; DROP_CMUL; LIFT_DROP] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `Ca * norm((h:real^2->real^K) x) * norm(partial_derivative i (v:real^2->real^K) x) pow 2 +
                Cb * norm(partial_derivative i v x) * norm((Y:real^2->real^K) x)` THEN
    CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> a + c <= b + c`) THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= m ==> x <= abs m`) THEN ASM SET_TAC[]]);;

(* ========================================================================= *)
(* Test maps are W^{1,2} with classical weak partials; the Dirichlet         *)
(* integral of w - f; test maps minus W^{1,2}_0 maps are W^{1,2}_0.          *)
(* ========================================================================= *)

let HMC_VTEST_FACTS = prove
 (`!s (f:real^N->real^K).
        open s /\ bounded s /\ wan_vtest s f
        ==> wan_w12 s f /\ (?M. !x. norm(f x) <= M) /\
            (!i. 1 <= i /\ i <= dimindex(:N)
                 ==> (\x. partial_derivative i f x) IN lspace s (&2) /\
                     negligible {x | x IN s /\ ~(wan_wd s i f x = partial_derivative i f x)})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_vtest] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `f:real^N->real^K`] HMC_CONT_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(:real^N)` THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SUBSET_UNIV];
    DISCH_THEN(X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`(:real^N)`; `k:real^N->bool`; `f:real^N->real^K`] HMC_PARTIALS_BOUND) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `M1:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x. norm((f:real^N->real^K) x) <= M` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN ASM_CASES_TAC `(x:real^N) IN k` THEN ASM_SIMP_TAC[NORM_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x i. 1 <= i /\ i <= dimindex(:N)
                      ==> norm(partial_derivative i (f:real^N->real^K) x) <= M1`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_CASES_TAC `(x:real^N) IN k` THEN ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`f:real^N->real^K`; `k:real^N->bool`; `x:real^N`; `i:num`]
                  HMC_VTEST_PD_ZERO) THEN
    ASM_SIMP_TAC[NORM_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `continuously_differentiable 1 s (f:real^N->real^K)` ASSUME_TAC THENL
   [SUBGOAL_THEN `smooth_map_on s (f:real^N->real^K)` MP_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      SIMP_TAC[smooth_map_on]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= dimindex(:N)
                    ==> (\x. partial_derivative i (f:real^N->real^K) x) IN lspace s (&2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HMC_BOUNDED_LSPACE THEN EXISTS_TAC `M1:real` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
    REWRITE_TAC[SUBSET_UNIV; ETA_AX] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN ASM_REWRITE_TAC[OPEN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_w12 s (f:real^N->real^K)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:N)`; `(:K)`] WAN_W12_C1) THEN REWRITE_TAC[WAN_W12_C1_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPECL [`s:real^N->bool`; `f:real^N->real^K`]) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC HMC_BOUNDED_LSPACE THEN EXISTS_TAC `M:real` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SUBSET_UNIV];
    ALL_TAC] THEN
  ASM_SIMP_TAC[HMC_WD_CLASSICAL] THEN EXISTS_TAC `M:real` THEN ASM_REWRITE_TAC[]);;

(* The Dirichlet integral does not see the sign.                             *)

let HMC_DIR_SYM = prove
 (`!s (f:real^N->real^K) w.
        open s /\ wan_w12 s (\x. f x - w x)
        ==> wan_dir s (\x. w x - f x) = wan_dir s (\x. f x - w x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. (w:real^N->real^K) x - f x) = (\x. --(f x - w x))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\x. --((f:real^N->real^K) x - w x)`;
                 `\i x. --(wan_wd s i (\x. (f:real^N->real^K) x - w x) x)`] WAN_DIR_EQ) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[WAN_W12_NEG] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC WAN_WPD_NEG THEN ASM_SIMP_TAC[WAN_WD_WORKS; ETA_AX];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[wan_dir; NORM_NEG]]);;

(* A test map minus a W^{1,2}_0 map is W^{1,2}_0.                            *)

let HMC_W120_VTEST_SUB = prove
 (`!s (f:real^N->real^K) w.
        open s /\ bounded s /\ wan_vtest s f /\ wan_w120 s w
        ==> wan_w120 s (\x. f x - w x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `f:real^N->real^K`] HMC_VTEST_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `wan_w120 s (w:real^N->real^K)` THEN REWRITE_TAC[wan_w120] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `g:num->real^N->real^K` STRIP_ASSUME_TAC)) THEN
  CONJ_TAC THENL [MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `\n x. (f:real^N->real^K) x - (g:num->real^N->real^K) n x` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN
    UNDISCH_TAC `wan_vtest s (f:real^N->real^K)` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> can (term_match []
      `!n. wan_vtest s ((g:num->real^N->real^K) n)`) (concl th))) THEN
    REWRITE_TAC[wan_vtest] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k1:real^N->bool` STRIP_ASSUME_TAC)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k2:real^N->bool` STRIP_ASSUME_TAC)) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[OPEN_UNIV; ETA_AX]; ALL_TAC] THEN
    EXISTS_TAC `k1 UNION k2:real^N->bool` THEN ASM_SIMP_TAC[COMPACT_UNION; UNION_SUBSET] THEN
    REWRITE_TAC[IN_UNION; DE_MORGAN_THM] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[VECTOR_SUB_REFL];
    SUBGOAL_THEN
     `(\n. lnorm s (&2) (\x. ((f:real^N->real^K) x - (g:num->real^N->real^K) n x) -
                             (f x - (w:real^N->real^K) x))) =
      (\n. lnorm s (&2) (\x. g n x - w x))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN
      SUBGOAL_THEN `(\x. ((f:real^N->real^K) x - (g:num->real^N->real^K) n x) -
                         (f x - (w:real^N->real^K) x)) = (\x. --(g n x - w x))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[LNORM_NEG];
      ASM_REWRITE_TAC[]];
    SUBGOAL_THEN
     `(\n. wan_dir s (\x. ((f:real^N->real^K) x - (g:num->real^N->real^K) n x) -
                          (f x - (w:real^N->real^K) x))) =
      (\n. wan_dir s (\x. g n x - w x))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN
      SUBGOAL_THEN `(\x. ((f:real^N->real^K) x - (g:num->real^N->real^K) n x) -
                         (f x - (w:real^N->real^K) x)) = (\x. w x - g n x)`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC HMC_DIR_SYM THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `(g:num->real^N->real^K) n`] HMC_VTEST_FACTS) THEN
      ASM_SIMP_TAC[ETA_AX];
      ASM_REWRITE_TAC[]]]);;

(* ========================================================================= *)
(* The weak Euler-Lagrange equation in the direction w in W^{1,2}_0 (a.e.    *)
(* bounded): approximation by test maps, Hardy and the interior gradient     *)
(* bound.                                                                    *)
(* ========================================================================= *)

let HMC_AMGM2 = prove
 (`!t p q. &0 < t ==> p * q <= p pow 2 / (&2 * t) + t / &2 * q pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p pow 2 / (&2 * t) + t / &2 * q pow 2 =
                p * q + (p - t * q) pow 2 / (&2 * t)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> x <= x + y`) THEN
  MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC);;

let HMC_PT_BOUND = prove
 (`!t rho K p q z cA cB.
        &0 < t /\ &0 < rho /\ &0 <= p /\ &0 <= q /\ &0 <= z /\ &0 <= cA /\ &0 <= cB /\
        rho * q <= K
        ==> cA * p * q pow 2 + cB * q * z
            <= cA * (p pow 2 / rho pow 2 / (&2 * t) + t / &2 * K pow 2 * q pow 2) +
               cB * (t / &2 * q pow 2 + z pow 2 / (&2 * t))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THENL
   [MP_TAC(ISPECL [`t:real`; `p / rho`; `rho * q pow 2`] HMC_AMGM2) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `p / rho * rho * q pow 2 = p * q pow 2 /\
                  (p / rho) pow 2 = p pow 2 / rho pow 2` (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `&0 < rho` THEN CONV_TAC REAL_FIELD; REWRITE_TAC[REAL_POW_DIV]];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> x <= a + b ==> x <= a + c`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(rho * q pow 2) pow 2 = (rho * q) pow 2 * q pow 2` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE];
    MP_TAC(ISPECL [`t:real`; `z:real`; `q:real`] HMC_AMGM2) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC]);;

let HMC_INTEGRAL_LIN3 = prove
 (`!s (f1:real^N->real) f2 f3 c1 c2 c3.
        (\x. lift(f1 x)) integrable_on s /\ (\x. lift(f2 x)) integrable_on s /\
        (\x. lift(f3 x)) integrable_on s
        ==> (\x. lift(c1 * f1 x + c2 * f2 x + c3 * f3 x)) integrable_on s /\
            drop(integral s (\x. lift(c1 * f1 x + c2 * f2 x + c3 * f3 x))) =
            c1 * drop(integral s (\x. lift(f1 x))) + c2 * drop(integral s (\x. lift(f2 x))) +
            c3 * drop(integral s (\x. lift(f3 x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN
  ASM_SIMP_TAC[INTEGRABLE_ADD; INTEGRABLE_CMUL; INTEGRAL_ADD; INTEGRAL_CMUL;
               DROP_ADD; DROP_CMUL]);;

(* The core estimate: the Euler-Lagrange functional in a direction h with   *)
(* partials Z i is bounded by the Hardy integral of h and the L^2 norms of   *)
(* the Z i, with a free parameter t.                                         *)

let HMC_LD_DIFF_BOUND = prove
 (`!S (G:real^K->real^K^K) d (a:real^2) r (v:real^2->real^K) (h:real^2->real^K)
    (Z:num->real^2->real^K) Ca Cb K t M Zn.
     cm_target S G d /\ &0 < r /\ smooth_map_on (ball(a,r)) v /\
     (!x. x IN ball(a,r) ==> v x IN S) /\ wan_w12 (ball(a,r)) v /\
     &0 <= Ca /\ &0 <= Cb /\
     (!(v:real^2->real^K) h Y i x.
         v x IN S
         ==> abs(hmc_ld S G v h Y i x)
             <= Ca * norm(h x) * norm(partial_derivative i v x) pow 2 +
                Cb * norm(partial_derivative i v x) * norm(Y x)) /\
     (!x i. x IN ball(a,r) /\ 1 <= i /\ i <= 2
            ==> (r - norm(x - a)) * norm(partial_derivative i v x) <= K) /\
     h measurable_on ball(a,r) /\ negligible Zn /\
     (!x. x IN ball(a,r) DIFF Zn ==> norm(h x) <= M) /\
     (\x. lift(norm(h x) pow 2 / (r - norm(x - a)) pow 2)) integrable_on ball(a,r) /\
     (!i. 1 <= i /\ i <= 2 ==> Z i IN lspace (ball(a,r)) (&2)) /\ &0 < t
     ==> abs(sum(1..2) (\i. drop(integral (ball(a,r))
                               (\x. lift(hmc_ld S G v h (Z i) i x)))))
         <= Ca / t * drop(integral (ball(a,r))
                            (\x. lift(norm(h x) pow 2 / (r - norm(x - a)) pow 2))) +
            t / &2 * (Ca * K pow 2 + Cb) *
            sum(1..2) (\i. drop(integral (ball(a,r))
                                  (\x. lift(norm(partial_derivative i v x) pow 2)))) +
            Cb / (&2 * t) * sum(1..2) (\i. drop(integral (ball(a,r))
                                                (\x. lift(norm(Z i x) pow 2))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> abs(drop(integral (ball(a:real^2,r))
                   (\x. lift(hmc_ld S G (v:real^2->real^K) h ((Z:num->real^2->real^K) i) i x))))
            <= Ca / (&2 * t) * drop(integral (ball(a,r))
                    (\x. lift(norm((h:real^2->real^K) x) pow 2 / (r - norm(x - a)) pow 2))) +
               (t / &2 * (Ca * K pow 2 + Cb)) *
               drop(integral (ball(a,r)) (\x. lift(norm(partial_derivative i v x) pow 2))) +
               Cb / (&2 * t) * drop(integral (ball(a,r)) (\x. lift(norm(Z i x) pow 2)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `1 <= i /\ i <= dimindex(:2)` STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[DIMINDEX_2]; ALL_TAC] THEN
    SUBGOAL_THEN `(\x. partial_derivative i (v:real^2->real^K) x) IN lspace (ball(a,r)) (&2)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC HMC_PD_LSPACE THEN ASM_REWRITE_TAC[OPEN_BALL] THEN
      ASM_MESON_TAC[smooth_map_on];
      ALL_TAC] THEN
    SUBGOAL_THEN `partial_derivative i (v:real^2->real^K) IN lspace (ball(a,r)) (&2)`
    ASSUME_TAC THENL
     [UNDISCH_TAC `(\x. partial_derivative i (v:real^2->real^K) x) IN lspace (ball(a,r)) (&2)` THEN
      REWRITE_TAC[ETA_AX];
      ALL_TAC] THEN
    SUBGOAL_THEN `(Z:num->real^2->real^K) i IN lspace (ball(a,r)) (&2)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!i. 1 <= i /\ i <= 2 ==> (Z:num->real^2->real^K) i IN lspace (ball(a,r)) (&2)`)
        (concl th))) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`ball(a:real^2,r)`;
                   `\x. norm((h:real^2->real^K) x) pow 2 / (r - norm(x - a)) pow 2`;
                   `\x. norm(partial_derivative i (v:real^2->real^K) x) pow 2`;
                   `\x. norm((Z:num->real^2->real^K) i x) pow 2`;
                   `Ca / (&2 * t)`; `t / &2 * (Ca * K pow 2 + Cb)`; `Cb / (&2 * t)`]
                  HMC_INTEGRAL_LIN3) THEN
    ASM_SIMP_TAC[WAN_LSPACE2_SQNORM_INTEGRABLE; ETA_AX] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(fun th -> REWRITE_TAC[SYM th]) THEN
    REWRITE_TAC[GSYM NORM_LIFT; LIFT_DROP] THEN
    MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HMC_LD_INTEGRABLE THEN
      MAP_EVERY EXISTS_TAC [`d:real`; `M:real`; `Zn:real^2->bool`] THEN
      ASM_SIMP_TAC[OPEN_BALL];
      ALL_TAC] THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    REWRITE_TAC[NORM_LIFT; LIFT_DROP] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `Ca * norm((h:real^2->real^K) x) * norm(partial_derivative i (v:real^2->real^K) x) pow 2 +
                Cb * norm(partial_derivative i v x) * norm((Z:num->real^2->real^K) i x)` THEN
    CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`t:real`; `r - norm(x - a:real^2)`; `K:real`;
                   `norm((h:real^2->real^K) x)`; `norm(partial_derivative i (v:real^2->real^K) x)`;
                   `norm((Z:num->real^2->real^K) i x)`; `Ca:real`; `Cb:real`] HMC_PT_BOUND) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[NORM_POS_LE] THEN UNDISCH_TAC `(x:real^2) IN ball(a,r)` THEN
      REWRITE_TAC[IN_BALL] THEN NORM_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(1..2) (\i. abs(drop(integral (ball(a:real^2,r))
                 (\x. lift(hmc_ld S G (v:real^2->real^K) h ((Z:num->real^2->real^K) i) i x)))))` THEN
  CONJ_TAC THENL [MATCH_ACCEPT_TAC SUM_ABS_NUMSEG; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(1..2) (\i. Ca / (&2 * t) * drop(integral (ball(a:real^2,r))
                    (\x. lift(norm((h:real^2->real^K) x) pow 2 / (r - norm(x - a)) pow 2))) +
               (t / &2 * (Ca * K pow 2 + Cb)) *
               drop(integral (ball(a,r))
                  (\x. lift(norm(partial_derivative i (v:real^2->real^K) x) pow 2))) +
               Cb / (&2 * t) * drop(integral (ball(a,r))
                  (\x. lift(norm((Z:num->real^2->real^K) i x) pow 2))))` THEN
  CONJ_TAC THENL [MATCH_MP_TAC SUM_LE_NUMSEG THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG; SUM_LMUL; SUM_CONST_NUMSEG] THEN
  CONV_TAC NUM_REDUCE_CONV THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD);;

(* A quantity bounded by B D n / t + A t for all t > 0 and all n, with       *)
(* D n -> 0, vanishes.                                                        *)

let HMC_LIMIT_ZERO = prove
 (`!L A B (D:num->real).
        &0 <= A /\ &0 <= B /\ (D ---> &0) sequentially /\
        (!t n. &0 < t ==> abs L <= B * D n / t + A * t)
        ==> L = &0`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `L = &0` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < abs L` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `t = abs L / (&2 * (A + &1))` THEN
  SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `((D:num->real) ---> &0) sequentially` THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `abs L * t / (&2 * (B + &1))`) THEN ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (MP_TAC o SPEC `N:num`)) THEN
  REWRITE_TAC[LE_REFL] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `N:num`]) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `B * (D:num->real) N / t <= abs L / &2 * (B / (B + &1))` MP_TAC THENL
   [SUBGOAL_THEN `B * (D:num->real) N / t <= B * (abs L * t / (&2 * (B + &1))) / t`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `y = z ==> x <= y ==> x <= z`) THEN
    SUBGOAL_THEN `&0 < B + &1` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `A * t = abs L / &2 * (A / (A + &1))` SUBST1_TAC THENL
   [EXPAND_TAC "t" THEN SUBGOAL_THEN `&0 < A + &1` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `B / (B + &1) < &1 /\ A / (A + &1) < &1` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 <= x ==> &0 < x + &1`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs L / &2 * (B / (B + &1)) < abs L / &2 /\
                abs L / &2 * (A / (A + &1)) < abs L / &2` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 < a /\ a * x < a * &1 ==> a * x < a`) THEN
    ASM_SIMP_TAC[REAL_LT_LMUL_EQ; REAL_HALF] THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* The weak Euler-Lagrange equation in a W^{1,2}_0 direction bounded a.e.  *)

let HMC_EL_W120 = prove
 (`!S (G:real^K->real^K^K) d (a:real^2) r (v:real^2->real^K) (w:real^2->real^K) K CH M Zw.
     cm_target S G d /\ &0 < r /\ cm_harmonic S G (ball(a,r)) v /\ wan_w12 (ball(a,r)) v /\
     (!x i. x IN ball(a,r) /\ 1 <= i /\ i <= 2
            ==> (r - norm(x - a)) * norm(partial_derivative i v x) <= K) /\
     &0 <= CH /\
     (!h:real^2->real^K.
         wan_w120 (ball(a,r)) h
         ==> (\x. lift(norm(h x) pow 2 / (r - norm(x - a)) pow 2)) integrable_on ball(a,r) /\
             drop(integral (ball(a,r)) (\x. lift(norm(h x) pow 2 / (r - norm(x - a)) pow 2)))
             <= CH * wan_dir (ball(a,r)) h) /\
     wan_w120 (ball(a,r)) w /\ negligible Zw /\
     (!x. x IN ball(a,r) DIFF Zw ==> norm(w x) <= M)
     ==> sum(1..2) (\i. drop(integral (ball(a,r))
                          (\x. lift(hmc_ld S G v w (wan_wd (ball(a,r)) i w) i x)))) = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_harmonic]) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Ca:real` (X_CHOOSE_THEN `Cb:real` STRIP_ASSUME_TAC) o
    MATCH_MP HMC_LD_BOUND) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_w120] o
    check (fun th -> concl th = `wan_w120 (ball(a:real^2,r)) (w:real^2->real^K)`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `g:num->real^2->real^K` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(w:real^2->real^K) measurable_on ball(a,r)` ASSUME_TAC THENL
   [UNDISCH_TAC `wan_w12 (ball(a:real^2,r)) (w:real^2->real^K)` THEN
    SIMP_TAC[wan_w12; lspace; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= 2
                    ==> (\x. partial_derivative i (v:real^2->real^K) x) IN lspace (ball(a,r)) (&2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HMC_PD_LSPACE THEN
    ASM_REWRITE_TAC[OPEN_BALL; DIMINDEX_2] THEN ASM_MESON_TAC[smooth_map_on];
    ALL_TAC] THEN
  ABBREV_TAC `DV = sum(1..2) (\i. drop(integral (ball(a:real^2,r))
                       (\x. lift(norm(partial_derivative i (v:real^2->real^K) x) pow 2))))` THEN
  SUBGOAL_THEN `&0 <= DV` ASSUME_TAC THENL
   [EXPAND_TAC "DV" THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
    REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2] THEN
    MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HMC_LIMIT_ZERO THEN
  MAP_EVERY EXISTS_TAC
   [`(Ca * K pow 2 + Cb) / &2 * DV`; `Ca * CH + Cb / &2`;
    `\n. wan_dir (ball(a:real^2,r)) (\x. (g:num->real^2->real^K) n x - w x)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
    MATCH_MP_TAC REAL_LE_ADD THEN ASM_SIMP_TAC[REAL_LE_MUL] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `n:num`] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `wan_vtest (ball(a:real^2,r)) ((g:num->real^2->real^K) n)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(a:real^2,r)`; `(g:num->real^2->real^K) n`] HMC_VTEST_FACTS) THEN
  ASM_REWRITE_TAC[OPEN_BALL; BOUNDED_BALL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_TAC `Mg:real`) (LABEL_TAC "gpd"))) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `a:real^2`; `r:real`;
                 `v:real^2->real^K`; `(g:num->real^2->real^K) n`] HMC_EL_TEST) THEN
  ASM_REWRITE_TAC[DIMINDEX_2] THEN DISCH_TAC THEN
  ABBREV_TAC `h = \x. (g:num->real^2->real^K) n x - (w:real^2->real^K) x` THEN
  ABBREV_TAC `Zf = \i x. partial_derivative i ((g:num->real^2->real^K) n) x -
                         wan_wd (ball(a:real^2,r)) i (w:real^2->real^K) x` THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> (\x. lift(hmc_ld S G (v:real^2->real^K) ((g:num->real^2->real^K) n)
                       (\y. partial_derivative i (g n) y) i x)) integrable_on ball(a,r) /\
            (\x. lift(hmc_ld S G v (w:real^2->real^K) (wan_wd (ball(a,r)) i w) i x))
              integrable_on ball(a,r)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN CONJ_TAC THEN MATCH_MP_TAC HMC_LD_INTEGRABLE THENL
     [MAP_EVERY EXISTS_TAC [`d:real`; `Mg:real`; `{}:real^2->bool`] THEN
      ASM_REWRITE_TAC[OPEN_BALL; DIMINDEX_2; NEGLIGIBLE_EMPTY; IN_DIFF; NOT_IN_EMPTY] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
        REWRITE_TAC[LEBESGUE_MEASURABLE_BALL] THEN
        UNDISCH_TAC `wan_vtest (ball(a:real^2,r)) ((g:num->real^2->real^K) n)` THEN
        REWRITE_TAC[wan_vtest] THEN STRIP_TAC THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
        ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SUBSET_UNIV];
        USE_THEN "gpd" (MP_TAC o SPEC `i:num`) THEN ASM_SIMP_TAC[DIMINDEX_2]];
      MAP_EVERY EXISTS_TAC [`d:real`; `M:real`; `Zw:real^2->bool`] THEN
      ASM_SIMP_TAC[OPEN_BALL; DIMINDEX_2; WAN_WD_WORKS]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..2) (\i. drop(integral (ball(a,r))
                    (\x. lift(hmc_ld S G (v:real^2->real^K) h ((Zf:num->real^2->real^K) i) i x)))) =
    --sum(1..2) (\i. drop(integral (ball(a,r))
                    (\x. lift(hmc_ld S G v (w:real^2->real^K) (wan_wd (ball(a,r)) i w) i x))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `!b. a = b - c /\ b = &0 ==> a = --c`) THEN
    EXISTS_TAC `sum(1..2) (\i. drop(integral (ball(a:real^2,r))
                  (\x. lift(hmc_ld S G (v:real^2->real^K) ((g:num->real^2->real^K) n)
                                (\y. partial_derivative i (g n) y) i x))))` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[GSYM SUM_SUB_NUMSEG] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[GSYM DROP_SUB] THEN AP_TERM_TAC THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP INTEGRAL_SUB
      (MP (SPEC `i:num` th) (CONJ (ASSUME `1 <= i`) (ASSUME `i <= 2`))))]) THEN
    MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM LIFT_SUB] THEN AP_TERM_TAC THEN
    EXPAND_TAC "h" THEN EXPAND_TAC "Zf" THEN REWRITE_TAC[] THEN
    REWRITE_TAC[ETA_AX] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC HMC_LD_SUB THEN
    EXISTS_TAC `d:real` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_w120 (ball(a:real^2,r)) (h:real^2->real^K)` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN MATCH_MP_TAC HMC_W120_VTEST_SUB THEN
    ASM_REWRITE_TAC[OPEN_BALL; BOUNDED_BALL; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_w12 (ball(a:real^2,r)) (h:real^2->real^K)` ASSUME_TAC THENL
   [ASM_MESON_TAC[wan_w120]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(norm((h:real^2->real^K) x) pow 2 / (r - norm(x - a)) pow 2))
       integrable_on ball(a:real^2,r) /\
    drop(integral (ball(a,r)) (\x. lift(norm(h x) pow 2 / (r - norm(x - a)) pow 2)))
       <= CH * wan_dir (ball(a,r)) h`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `continuously_differentiable 1 (ball(a:real^2,r)) ((g:num->real^2->real^K) n)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `smooth_map_on (ball(a:real^2,r)) ((g:num->real^2->real^K) n)` MP_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      REWRITE_TAC[SUBSET_UNIV] THEN ASM_MESON_TAC[wan_vtest];
      SIMP_TAC[smooth_map_on]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= 2
                 ==> wan_wpd (ball(a:real^2,r)) i (h:real^2->real^K) ((Zf:num->real^2->real^K) i)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN EXPAND_TAC "h" THEN EXPAND_TAC "Zf" THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC WAN_WPD_SUB THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`ball(a:real^2,r)`; `(g:num->real^2->real^K) n`; `i:num`] WAN_WPD_C1) THEN
      ASM_REWRITE_TAC[ETA_AX; OPEN_BALL];
      REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[WAN_WD_WORKS; DIMINDEX_2]];
    ALL_TAC] THEN
  SUBGOAL_THEN `sum(1..2) (\i. drop(integral (ball(a:real^2,r))
                  (\x. lift(norm((Zf:num->real^2->real^K) i x) pow 2)))) =
                wan_dir (ball(a,r)) (h:real^2->real^K)`
  ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`ball(a:real^2,r)`; `h:real^2->real^K`; `Zf:num->real^2->real^K`]
                  WAN_DIR_EQ) THEN
    REWRITE_TAC[DIMINDEX_2; OPEN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= 2
                 ==> (Zf:num->real^2->real^K) i IN lspace (ball(a:real^2,r)) (&2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN EXPAND_TAC "Zf" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC LSPACE_SUB THEN REWRITE_TAC[REAL_POS] THEN CONJ_TAC THENL
     [USE_THEN "gpd" (MP_TAC o SPEC `i:num`) THEN ASM_SIMP_TAC[DIMINDEX_2; ETA_AX];
      REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[WAN_WD_WORKS; DIMINDEX_2]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^2->real^K) measurable_on ball(a:real^2,r)` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN MATCH_MP_TAC MEASURABLE_ON_SUB THEN ASM_REWRITE_TAC[ETA_AX] THEN
    UNDISCH_TAC `wan_w12 (ball(a:real^2,r)) ((g:num->real^2->real^K) n)` THEN
    SIMP_TAC[wan_w12; lspace; IN_ELIM_THM; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN ball(a:real^2,r) DIFF Zw ==> norm((h:real^2->real^K) x) <= Mg + M`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN EXPAND_TAC "h" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(NORM_ARITH `norm(p:real^K) <= m1 /\ norm(q:real^K) <= m2
                             ==> norm(p - q) <= m1 + m2`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `a:real^2`; `r:real`;
                 `v:real^2->real^K`; `h:real^2->real^K`; `Zf:num->real^2->real^K`;
                 `Ca:real`; `Cb:real`; `K:real`; `t:real`; `Mg + M:real`; `Zw:real^2->bool`]
                HMC_LD_DIFF_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_ABS_NEG] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP (REAL_ARITH `x <= y ==> y <= z ==> x <= z`)) THEN
  MATCH_MP_TAC(REAL_ARITH `!a'. a <= a' /\ a' + c = e /\ b = f ==> a + b + c <= e + f`) THEN
  EXISTS_TAC `Ca / t * (CH * wan_dir (ball(a:real^2,r)) (h:real^2->real^K))` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD;
    REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The pointwise expansion of the energy density at a harmonic map, its      *)
(* integrated form, the weighted gradient bound, and the chain theorem       *)
(* CM_CHAIN_HM_CONVEXITY.                                                    *)
(* ========================================================================= *)

(* The global bounds of the metric G of a target.                           *)

let HMC_G_BOUNDS = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> ?Lam. &0 <= Lam /\
               !z xi. &0 <= xi dot (G z ** xi) /\ xi dot (G z ** xi) <= Lam * norm xi pow 2`,
  REWRITE_TAC[cm_target] THEN REPEAT STRIP_TAC THEN EXISTS_TAC `Lam:real` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `lam * norm(xi:real^K) pow 2` THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2; REAL_LT_IMP_LE]);;

(* The pointwise expansion of the energy density of u around a harmonic v:  *)
(* the density of u minus the density of v minus the Euler-Lagrange density *)
(* in the direction u - v controls lam |Y|^2 up to |u - v|^2 |d_i v|^2.     *)

let HMC_POINT_INEQ = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> ?lam C7. &0 < lam /\ &0 <= C7 /\
           !s (u:real^2->real^K) (v:real^2->real^K) (Y:real^2->real^K) i x.
              open s /\ smooth_map_on s v /\ (!y. y IN s ==> v y IN S) /\
              x IN s /\ u x IN S
              ==> lam * norm(Y x) pow 2 -
                  C7 * norm(u x - v x) pow 2 * norm(partial_derivative i v x) pow 2
                  <= (partial_derivative i v x + Y x) dot
                     (G(u x) ** (partial_derivative i v x + Y x)) -
                     partial_derivative i v x dot (G(v x) ** partial_derivative i v x) -
                     hmc_ld S G v (\x. u x - v x) Y i x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_CONSTS) THEN
  MAP_EVERY EXISTS_TAC
   [`lam / &2`; `&2 * C3 pow 2 / lam + C2 + CG * C4 + &2 * CJ * C4 * Lam1`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b /\ &0 <= c /\ &0 <= e
                             ==> &0 <= a + b + c + e`) THEN
    REPEAT CONJ_TAC THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_DIV; REAL_LE_POW_2; REAL_LT_IMP_LE; REAL_POS];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(v:real^2->real^K) x IN S` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((vectorize:real^K^K->real^(K,K)finite_prod) o
     (\y. jacobian (closest_point (S:real^K->bool)) (at y)))
       differentiable (at ((v:real^2->real^K) x)) /\
    ((vectorize:real^K^K->real^(K,K)finite_prod) o (G:real^K->real^K^K))
       differentiable (at (v x))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `cm_tube S d:real^K->bool` THEN ASM SET_TAC[];
      EXISTS_TAC `(:real^K)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `jacobian (closest_point S) (at ((v:real^2->real^K) x)) ** partial_derivative i v x =
    partial_derivative i v x`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HMC_TANGENT_PARTIAL THEN
    MAP_EVERY EXISTS_TAC [`G:real^K->real^K^K`; `d:real`; `s:real^2->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. jacobian (closest_point S) (at ((v:real^2->real^K) x)) ** a = a /\
          jacobian (closest_point S) (at (v x)) ** b = b
          ==> jacobian (closest_point S) (at (v x)) **
              (mderiv (\y. jacobian (closest_point S) (at y)) (v x) a ** b) = vec 0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HMC_JDJ THEN
    MAP_EVERY EXISTS_TAC [`G:real^K->real^K^K`; `d:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[hmc_ld] THEN MATCH_MP_TAC HMC_DENSITY_ALG THEN
  ASM_SIMP_TAC[HMC_MDERIV_ADD]);;

(* Two linearity facts for integrals of real-valued functions.              *)

let HMC_INTEGRAL_LIN2 = prove
 (`!s (f1:real^N->real) f2 c1 c2.
        (\x. lift(f1 x)) integrable_on s /\ (\x. lift(f2 x)) integrable_on s
        ==> (\x. lift(c1 * f1 x - c2 * f2 x)) integrable_on s /\
            drop(integral s (\x. lift(c1 * f1 x - c2 * f2 x))) =
            c1 * drop(integral s (\x. lift(f1 x))) - c2 * drop(integral s (\x. lift(f2 x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[LIFT_SUB; LIFT_CMUL] THEN
  ASM_SIMP_TAC[INTEGRABLE_SUB; INTEGRABLE_CMUL; INTEGRAL_SUB; INTEGRAL_CMUL;
               DROP_SUB; DROP_CMUL]);;

let HMC_INTEGRAL_SUB3 = prove
 (`!s (f1:real^N->real) f2 f3.
        (\x. lift(f1 x)) integrable_on s /\ (\x. lift(f2 x)) integrable_on s /\
        (\x. lift(f3 x)) integrable_on s
        ==> (\x. lift(f1 x - f2 x - f3 x)) integrable_on s /\
            drop(integral s (\x. lift(f1 x - f2 x - f3 x))) =
            drop(integral s (\x. lift(f1 x))) - drop(integral s (\x. lift(f2 x))) -
            drop(integral s (\x. lift(f3 x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[LIFT_SUB] THEN
  ASM_SIMP_TAC[INTEGRABLE_SUB; INTEGRAL_SUB; DROP_SUB]);;

(* A bounded factor times an L^2 square is integrable.                      *)

let HMC_WX_INTEGRABLE = prove
 (`!s (w:real^N->real^K) (X:real^N->real^K) Z M.
        w IN lspace s (&2) /\ negligible Z /\ (!x. x IN s DIFF Z ==> norm(w x) <= M) /\
        X IN lspace s (&2)
        ==> (\x. lift(norm(w x) pow 2 * norm(X x) pow 2)) integrable_on s`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_AE_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  MAP_EVERY EXISTS_TAC
   [`\x. lift(M pow 2 * norm((X:real^N->real^K) x) pow 2)`; `Z:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_ON_LIFT_MUL THEN CONJ_TAC THEN
    MATCH_MP_TAC INTEGRABLE_IMP_MEASURABLE THEN
    MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
    MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[LIFT_DROP; NORM_LIFT; REAL_ABS_MUL; REAL_ABS_POW; REAL_ABS_NORM] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[NORM_POS_LE]]);;

(* The weighted bound: |w|^2 |d_i v|^2 against the Hardy integrand.        *)

let HMC_WEIGHT_PT = prove
 (`!n x rho K. &0 <= n /\ &0 < rho /\ rho * x <= K /\ &0 <= x
               ==> n * x pow 2 <= K pow 2 * (n / rho pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `K pow 2 * (n / rho pow 2) = n * (K pow 2 / rho pow 2)` SUBST1_TAC THENL
   [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_POW_LT] THEN
  REWRITE_TAC[GSYM REAL_POW_MUL] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC);;

let HMC_WEIGHTED_BOUND = prove
 (`!(a:real^2) r (v:real^2->real^K) (w:real^2->real^K) K.
     &0 < r /\
     (!x i. x IN ball(a,r) /\ 1 <= i /\ i <= 2
            ==> (r - norm(x - a)) * norm(partial_derivative i v x) <= K) /\
     (!i. 1 <= i /\ i <= 2
          ==> (\x. lift(norm(w x) pow 2 * norm(partial_derivative i v x) pow 2))
                integrable_on ball(a,r)) /\
     (\x. lift(norm(w x) pow 2 / (r - norm(x - a)) pow 2)) integrable_on ball(a,r)
     ==> sum(1..2) (\i. drop(integral (ball(a,r))
                          (\x. lift(norm(w x) pow 2 * norm(partial_derivative i v x) pow 2))))
         <= &2 * K pow 2 * drop(integral (ball(a,r))
                                 (\x. lift(norm(w x) pow 2 / (r - norm(x - a)) pow 2)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> drop(integral (ball(a,r))
                 (\x. lift(norm((w:real^2->real^K) x) pow 2 *
                           norm(partial_derivative i (v:real^2->real^K) x) pow 2)))
            <= K pow 2 * drop(integral (ball(a,r))
                                (\x. lift(norm(w x) pow 2 / (r - norm(x - a)) pow 2)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `K pow 2 * drop(integral (ball(a,r))
                       (\x. lift(norm((w:real^2->real^K) x) pow 2 / (r - norm(x - a)) pow 2))) =
      drop(integral (ball(a,r))
             (\x. lift(K pow 2 * norm(w x) pow 2 / (r - norm(x - a)) pow 2)))`
    SUBST1_TAC THENL
     [REWRITE_TAC[LIFT_CMUL] THEN ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL]; ALL_TAC] THEN
    MATCH_MP_TAC INTEGRAL_DROP_LE THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[];
      REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
    MATCH_MP_TAC HMC_WEIGHT_PT THEN
    ASM_SIMP_TAC[NORM_POS_LE; REAL_LE_POW_2] THEN
    UNDISCH_TAC `(x:real^2) IN ball(a,r)` THEN REWRITE_TAC[IN_BALL] THEN NORM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUM_2] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= k /\ y <= k ==> x + y <= &2 * k`) THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC);;

(* The integrated expansion for one partial derivative index i.             *)

let HMC_EXPANSION_I = prove
 (`!S (G:real^K->real^K^K) d lam C7 Lam (a:real^2) r (u:real^2->real^K)
    (v:real^2->real^K) Zu M i.
     cm_target S G d /\
     (!s (u:real^2->real^K) (v:real^2->real^K) (Y:real^2->real^K) i x.
         open s /\ smooth_map_on s v /\ (!y. y IN s ==> v y IN S) /\
         x IN s /\ u x IN S
         ==> lam * norm(Y x) pow 2 -
             C7 * norm(u x - v x) pow 2 * norm(partial_derivative i v x) pow 2
             <= (partial_derivative i v x + Y x) dot
                (G(u x) ** (partial_derivative i v x + Y x)) -
                partial_derivative i v x dot (G(v x) ** partial_derivative i v x) -
                hmc_ld S G v (\x. u x - v x) Y i x) /\
     (!z xi. &0 <= xi dot (G z ** xi) /\ xi dot (G z ** xi) <= Lam * norm xi pow 2) /\
     &0 < r /\ smooth_map_on (ball(a,r)) v /\ (!x. x IN ball(a,r) ==> v x IN S) /\
     wan_w12 (ball(a,r)) v /\ wan_w12 (ball(a,r)) u /\
     negligible Zu /\ (!x. x IN ball(a,r) DIFF Zu ==> u x IN S) /\
     (!x. x IN ball(a,r) DIFF Zu ==> norm(u x - v x) <= M) /\
     1 <= i /\ i <= 2
     ==> lam * drop(integral (ball(a,r))
                 (\x. lift(norm(wan_wd (ball(a,r)) i (\x. u x - v x) x) pow 2))) -
         C7 * drop(integral (ball(a,r))
                 (\x. lift(norm(u x - v x) pow 2 * norm(partial_derivative i v x) pow 2)))
         <= drop(integral (ball(a,r))
                 (\x. lift(wan_wd (ball(a,r)) i u x dot (G(u x) ** wan_wd (ball(a,r)) i u x)))) -
            drop(integral (ball(a,r))
                 (\x. lift(partial_derivative i v x dot (G(v x) ** partial_derivative i v x)))) -
            drop(integral (ball(a,r))
                 (\x. lift(hmc_ld S G v (\x. u x - v x)
                             (wan_wd (ball(a,r)) i (\x. u x - v x)) i x)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "pt") STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  SUBGOAL_THEN `continuously_differentiable 1 (ball(a:real^2,r)) (v:real^2->real^K)`
  ASSUME_TAC THENL [ASM_MESON_TAC[smooth_map_on]; ALL_TAC] THEN
  SUBGOAL_THEN `wan_w12 (ball(a:real^2,r)) (\x. (u:real^2->real^K) x - v x)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. partial_derivative i (v:real^2->real^K) x) IN lspace (ball(a:real^2,r)) (&2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HMC_PD_LSPACE THEN ASM_REWRITE_TAC[OPEN_BALL; DIMINDEX_2]; ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(a:real^2,r)`; `i:num`; `u:real^2->real^K`] WAN_WD_WORKS) THEN
  ASM_REWRITE_TAC[DIMINDEX_2] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ball(a:real^2,r)`; `i:num`; `\x. (u:real^2->real^K) x - v x`]
                WAN_WD_WORKS) THEN
  ASM_REWRITE_TAC[DIMINDEX_2] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `negligible {x | x IN ball(a:real^2,r) /\
                    ~(wan_wd (ball(a,r)) i (\x. (u:real^2->real^K) x - v x) x =
                      wan_wd (ball(a,r)) i u x - partial_derivative i v x)}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ball(a:real^2,r)`; `i:num`; `\x. (u:real^2->real^K) x - v x`;
                   `\x. wan_wd (ball(a:real^2,r)) i (u:real^2->real^K) x -
                        partial_derivative i (v:real^2->real^K) x`] WAN_WD_UNIQUE) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[OPEN_BALL; DIMINDEX_2] THEN
    MATCH_MP_TAC WAN_WPD_SUB THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MP_TAC(ISPECL [`ball(a:real^2,r)`; `v:real^2->real^K`; `i:num`] WAN_WPD_C1) THEN
    ASM_REWRITE_TAC[ETA_AX; OPEN_BALL];
    ALL_TAC] THEN
  ABBREV_TAC `W = wan_wd (ball(a:real^2,r)) i (\x. (u:real^2->real^K) x - v x)` THEN
  ABBREV_TAC `U = wan_wd (ball(a:real^2,r)) i (u:real^2->real^K)` THEN
  SUBGOAL_THEN
   `(\x. lift(norm((W:real^2->real^K) x) pow 2)) integrable_on ball(a:real^2,r) /\
    (\x. lift(norm((u:real^2->real^K) x - v x) pow 2 *
              norm(partial_derivative i (v:real^2->real^K) x) pow 2))
       integrable_on ball(a,r) /\
    (\x. lift((U:real^2->real^K) x dot (G(u x) ** U x))) integrable_on ball(a,r) /\
    (\x. lift(partial_derivative i v x dot (G(v x) ** partial_derivative i v x)))
       integrable_on ball(a,r) /\
    (\x. lift(hmc_ld S G v (\x. u x - v x) W i x)) integrable_on ball(a,r)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC HMC_WX_INTEGRABLE THEN
      MAP_EVERY EXISTS_TAC [`Zu:real^2->bool`; `M:real`] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `wan_w12 (ball(a:real^2,r)) (\x. (u:real^2->real^K) x - v x)` THEN
      SIMP_TAC[wan_w12];
      MATCH_MP_TAC HMC_QUAD_INTEGRABLE THEN EXISTS_TAC `Lam:real` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [SUBGOAL_THEN
         `(vectorize:real^K^K->real^(K,K)finite_prod) o (\x. (G:real^K->real^K^K) (u x)) =
          (vectorize o G) o (u:real^2->real^K)` SUBST1_TAC THENL
         [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC HMC_MEAS_COMPOSE THEN
        REWRITE_TAC[LEBESGUE_MEASURABLE_BALL] THEN CONJ_TAC THENL
         [UNDISCH_TAC `wan_w12 (ball(a:real^2,r)) (u:real^2->real^K)` THEN
          SIMP_TAC[wan_w12; lspace; IN_ELIM_THM];
          MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[]];
        REPEAT STRIP_TAC THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y`) THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC HMC_QUAD_INTEGRABLE THEN EXISTS_TAC `Lam:real` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
        REWRITE_TAC[LEBESGUE_MEASURABLE_BALL] THEN
        SUBGOAL_THEN
         `(vectorize:real^K^K->real^(K,K)finite_prod) o (\x. (G:real^K->real^K^K) (v x)) =
          (vectorize o G) o (v:real^2->real^K)` SUBST1_TAC THENL
         [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
         [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^K)` THEN
          REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
          ASM_REWRITE_TAC[]];
        REPEAT STRIP_TAC THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y`) THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC HMC_LD_INTEGRABLE THEN
      MAP_EVERY EXISTS_TAC [`d:real`; `M:real`; `Zu:real^2->bool`] THEN
      ASM_REWRITE_TAC[OPEN_BALL; DIMINDEX_2] THEN
      UNDISCH_TAC `wan_w12 (ball(a:real^2,r)) (\x. (u:real^2->real^K) x - v x)` THEN
      SIMP_TAC[wan_w12; lspace; IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN ball(a:real^2,r) DIFF
          (Zu UNION {x | x IN ball(a,r) /\
                         ~((W:real^2->real^K) x =
                           (U:real^2->real^K) x - partial_derivative i v x)})
        ==> lam * norm(W x) pow 2 -
            C7 * norm((u:real^2->real^K) x - v x) pow 2 *
            norm(partial_derivative i (v:real^2->real^K) x) pow 2
            <= U x dot (G(u x) ** U x) -
               partial_derivative i v x dot (G(v x) ** partial_derivative i v x) -
               hmc_ld S G v (\x. u x - v x) W i x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_DIFF; IN_UNION; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `(W:real^2->real^K) x = (U:real^2->real^K) x - partial_derivative i v x`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(u:real^2->real^K) x IN S` ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_DIFF]; ALL_TAC] THEN
    SUBGOAL_THEN `(U:real^2->real^K) x = partial_derivative i v x + W x` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "pt" MATCH_MP_TAC THEN EXISTS_TAC `ball(a:real^2,r)` THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(a:real^2,r)`; `\x. norm((W:real^2->real^K) x) pow 2`;
                 `\x. norm((u:real^2->real^K) x - v x) pow 2 *
                      norm(partial_derivative i (v:real^2->real^K) x) pow 2`;
                 `lam:real`; `C7:real`] HMC_INTEGRAL_LIN2) THEN
  MP_TAC(ISPECL [`ball(a:real^2,r)`;
                 `\x. (U:real^2->real^K) x dot ((G:real^K->real^K^K)(u x) ** U x)`;
                 `\x. partial_derivative i (v:real^2->real^K) x dot
                      ((G:real^K->real^K^K)(v x) ** partial_derivative i v x)`;
                 `\x. hmc_ld S (G:real^K->real^K^K) (v:real^2->real^K) (\x. u x - v x)
                        (W:real^2->real^K) i x`] HMC_INTEGRAL_SUB3) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  MATCH_MP_TAC INTEGRAL_DROP_LE_AE THEN
  EXISTS_TAC `Zu UNION {x | x IN ball(a:real^2,r) /\
                         ~((W:real^2->real^K) x =
                           (U:real^2->real^K) x - partial_derivative i v x)}` THEN
  ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ; LIFT_DROP]);;

(* The integrated expansion, summed over the two partial derivatives.       *)

let HMC_EXPANSION = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> ?lam C7. &0 < lam /\ &0 <= C7 /\
           !(a:real^2) r (u:real^2->real^K) (v:real^2->real^K) Zu M.
              &0 < r /\ cm_harmonic S G (ball(a,r)) v /\ wan_w12 (ball(a,r)) v /\
              wan_w12 (ball(a,r)) u /\ negligible Zu /\
              (!x. x IN ball(a,r) DIFF Zu ==> u x IN S) /\
              (!x. x IN ball(a,r) DIFF Zu ==> norm(u x - v x) <= M)
              ==> lam * wan_dir (ball(a,r)) (\x. u x - v x) -
                  C7 * sum(1..2) (\i. drop(integral (ball(a,r))
                         (\x. lift(norm(u x - v x) pow 2 *
                                   norm(partial_derivative i v x) pow 2))))
                  <= wan_gdir (ball(a,r)) G u - wan_gdir (ball(a,r)) G v -
                     sum(1..2) (\i. drop(integral (ball(a,r))
                         (\x. lift(hmc_ld S G v (\x. u x - v x)
                                     (wan_wd (ball(a,r)) i (\x. u x - v x)) i x))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `C7:real` STRIP_ASSUME_TAC) o
    MATCH_MP HMC_POINT_INEQ) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Lam:real` STRIP_ASSUME_TAC o MATCH_MP HMC_G_BOUNDS) THEN
  MAP_EVERY EXISTS_TAC [`lam:real`; `C7:real`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`a:real^2`; `r:real`; `u:real^2->real^K`; `v:real^2->real^K`;
                       `Zu:real^2->bool`; `M:real`] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_harmonic]) THEN
  SUBGOAL_THEN `continuously_differentiable 1 (ball(a:real^2,r)) (v:real^2->real^K)`
  ASSUME_TAC THENL [ASM_MESON_TAC[smooth_map_on]; ALL_TAC] THEN
  ASM_SIMP_TAC[HMC_GDIR_CLASSICAL; OPEN_BALL] THEN
  REWRITE_TAC[wan_dir; wan_gdir; DIMINDEX_2; SUM_2] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `lam:real`; `C7:real`;
                 `Lam:real`; `a:real^2`; `r:real`; `u:real^2->real^K`; `v:real^2->real^K`;
                 `Zu:real^2->bool`; `M:real`; `1`] HMC_EXPANSION_I) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `lam:real`; `C7:real`;
                 `Lam:real`; `a:real^2`; `r:real`; `u:real^2->real^K`; `v:real^2->real^K`;
                 `Zu:real^2->bool`; `M:real`; `2`] HMC_EXPANSION_I) THEN
  ASM_REWRITE_TAC[ARITH] THEN REAL_ARITH_TAC);;

(* The final arithmetic: absorb the weighted term for small energy.         *)

let HMC_FINAL_ARITH = prove
 (`!lam C7 c1 CH ee dd qq hw gu gv.
     &0 < lam /\ &0 <= C7 /\ &0 < CH /\ &0 <= ee /\ &0 <= dd /\
     ee * (&4 * C7 * c1 pow 2 * CH + &1) <= lam /\
     lam * dd - C7 * qq <= gu - gv /\
     qq <= &2 * (c1 * sqrt ee) pow 2 * hw /\ hw <= CH * dd
     ==> lam / &2 * dd <= gu - gv`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(c1 * sqrt ee) pow 2 = c1 pow 2 * ee` SUBST_ALL_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_MUL; SQRT_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN `C7 * qq <= (&2 * C7 * c1 pow 2 * ee) * (CH * dd)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C7 * (&2 * (c1 pow 2 * ee) * hw)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_ARITH `C7 * (&2 * (c * e) * h) = (&2 * C7 * c * e) * h`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * (C7 * c1 pow 2 * CH) * ee <= lam / &2` ASSUME_TAC THENL
   [UNDISCH_TAC `ee * (&4 * C7 * c1 pow 2 * CH + &1) <= lam` THEN
    UNDISCH_TAC `&0 <= ee` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&2 * C7 * c1 pow 2 * ee) * (CH * dd) <= lam / &2 * dd` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `(&2 * C7 * c * e) * (h * d) = (&2 * (C7 * c * h) * e) * d`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The chain theorem: CM Theorem 3.1 in the G form.                          *)
(* ------------------------------------------------------------------------- *)

let CM_CHAIN_HM_CONVEXITY = prove
 (`!kk:K->bool. CM_CHAIN_HM_CONVEXITY_STATEMENT kk`,
  GEN_TAC THEN REWRITE_TAC[CM_CHAIN_HM_CONVEXITY_STATEMENT; CM_CONVEXITY_STATEMENT] THEN
  REWRITE_TAC[WAN_HARDY_BALL_STATEMENT; CM_EPS_REG_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `CH:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "hardy")))
    (LABEL_TAC "rest")) THEN
  MAP_EVERY X_GEN_TAC [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] THEN DISCH_TAC THEN
  USE_THEN "rest" (MP_TAC o SPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] o
    CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real` (X_CHOOSE_THEN `C:num->real` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `C7:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "exp")))) o
    MATCH_MP HMC_EXPANSION) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Lam:real` STRIP_ASSUME_TAC o MATCH_MP HMC_G_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  SUBGOAL_THEN `?b. &0 < b /\ !z:real^K. z IN S ==> norm z <= b` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPACT_IMP_BOUNDED; BOUNDED_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &4 * C7 * (C:num->real) 1 pow 2 * CH + &1` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_LE_POW_2; REAL_LT_IMP_LE; REAL_POS];
    ALL_TAC] THEN
  EXISTS_TAC `min e0 (lam / (&4 * C7 * (C:num->real) 1 pow 2 * CH + &1))` THEN
  EXISTS_TAC `lam / &2` THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MIN; REAL_LT_DIV];
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:real^2`; `r:real`; `u:real^2->real^K`; `v:real^2->real^K`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_harmonic]) THEN
  UNDISCH_TAC `cm_wmap S (ball(a:real^2,r)) (u:real^2->real^K)` THEN
  REWRITE_TAC[cm_wmap] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `Zu:real^2->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `wan_w12 (ball(a:real^2,r)) (v:real^2->real^K)` ASSUME_TAC THENL
   [ASM_MESON_TAC[cm_wmap]; ALL_TAC] THEN
  SUBGOAL_THEN `wan_w12 (ball(a:real^2,r)) (\x. (u:real^2->real^K) x - v x)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(\x. (u:real^2->real^K) x - v x) IN lspace (ball(a:real^2,r)) (&2)`
  ASSUME_TAC THENL [ASM_MESON_TAC[wan_w12]; ALL_TAC] THEN
  SUBGOAL_THEN `continuously_differentiable 1 (ball(a:real^2,r)) (v:real^2->real^K)`
  ASSUME_TAC THENL [ASM_MESON_TAC[smooth_map_on]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> partial_derivative i (v:real^2->real^K) IN lspace (ball(a:real^2,r)) (&2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`ball(a:real^2,r)`; `v:real^2->real^K`; `i:num`] HMC_PD_LSPACE) THEN
    ASM_REWRITE_TAC[ETA_AX; OPEN_BALL; DIMINDEX_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN ball(a:real^2,r) DIFF Zu
                    ==> norm((u:real^2->real^K) x - v x) <= &2 * b`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    MATCH_MP_TAC(NORM_ARITH `norm(p:real^K) <= b /\ norm(q:real^K) <= b
                             ==> norm(p - q) <= &2 * b`) THEN
    SUBGOAL_THEN `(u:real^2->real^K) x IN S /\ (v:real^2->real^K) x IN S` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_DIFF]; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= wan_gdir (ball(a:real^2,r)) G (v:real^2->real^K)` ASSUME_TAC THENL
   [MATCH_MP_TAC HMC_GDIR_POS THEN EXISTS_TAC `Lam:real` THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e0:real`; `C:num->real`;
                 `Lam:real`; `a:real^2`; `r:real`; `v:real^2->real^K`] HMC_GRAD_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `!h:real^2->real^K.
       wan_w120 (ball(a:real^2,r)) h
       ==> (\x. lift(norm(h x) pow 2 / (r - norm(x - a)) pow 2)) integrable_on ball(a,r) /\
           drop(integral (ball(a,r)) (\x. lift(norm(h x) pow 2 / (r - norm(x - a)) pow 2)))
           <= CH * wan_dir (ball(a,r)) h`
  ASSUME_TAC THENL
   [X_GEN_TAC `h:real^2->real^K` THEN DISCH_TAC THEN
    USE_THEN "hardy" (MP_TAC o SPECL [`a:real^2`; `r:real`; `h:real^2->real^K`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(norm((u:real^2->real^K) x - v x) pow 2 / (r - norm(x - a)) pow 2))
       integrable_on ball(a:real^2,r) /\
    drop(integral (ball(a,r)) (\x. lift(norm(u x - v x) pow 2 / (r - norm(x - a)) pow 2)))
       <= CH * wan_dir (ball(a,r)) (\x. u x - v x)`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `\x. (u:real^2->real^K) x - v x`) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `a:real^2`; `r:real`;
                 `v:real^2->real^K`; `\x. (u:real^2->real^K) x - v x`;
                 `(C:num->real) 1 * sqrt(wan_gdir (ball(a:real^2,r)) G (v:real^2->real^K))`;
                 `CH:real`; `&2 * b`; `Zu:real^2->bool`] HMC_EL_W120) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; DISCH_TAC] THEN
  USE_THEN "exp" (MP_TAC o SPECL [`a:real^2`; `r:real`; `u:real^2->real^K`;
                                  `v:real^2->real^K`; `Zu:real^2->bool`; `&2 * b`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`a:real^2`; `r:real`; `v:real^2->real^K`; `\x. (u:real^2->real^K) x - v x`;
                 `(C:num->real) 1 * sqrt(wan_gdir (ball(a:real^2,r)) G (v:real^2->real^K))`]
                HMC_WEIGHTED_BOUND) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC HMC_WX_INTEGRABLE THEN
    MAP_EVERY EXISTS_TAC [`Zu:real^2->bool`; `&2 * b`] THEN ASM_SIMP_TAC[ETA_AX];
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `wan_gdir (ball(a:real^2,r)) G (v:real^2->real^K) *
    (&4 * C7 * (C:num->real) 1 pow 2 * CH + &1) <= lam`
  ASSUME_TAC THENL [ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= wan_dir (ball(a:real^2,r)) (\x. (u:real^2->real^K) x - v x)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[WAN_DIR_POS]; ALL_TAC] THEN
  MATCH_MP_TAC HMC_FINAL_ARITH THEN
  MAP_EVERY EXISTS_TAC
   [`C7:real`; `(C:num->real) 1`; `CH:real`;
    `wan_gdir (ball(a:real^2,r)) G (v:real^2->real^K)`;
    `sum(1..2) (\i. drop(integral (ball(a:real^2,r))
        (\x. lift(norm((u:real^2->real^K) x - v x) pow 2 *
                  norm(partial_derivative i (v:real^2->real^K) x) pow 2))))`;
    `drop(integral (ball(a:real^2,r))
        (\x. lift(norm((u:real^2->real^K) x - v x) pow 2 / (r - norm(x - a)) pow 2)))`] THEN
  ASM_REWRITE_TAC[]);;

let CM_CHAIN_HM_CONVEXITY_UNIV = prove
 (`CM_CHAIN_HM_CONVEXITY_STATEMENT (:K)`,
  REWRITE_TAC[CM_CHAIN_HM_CONVEXITY]);;


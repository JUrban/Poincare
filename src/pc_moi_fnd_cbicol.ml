(* ========================================================================= *)
(* pc_moi_fnd_cbicol: annular bicollars of 1-manifolds in the interior of    *)
(* orientable combinatorial surfaces with boundary (Moise GTM 47, 26.3 for   *)
(* 1-manifolds in 2-manifolds, p.192).  Main theorem:                        *)
(*   CURVE_BICOLLAR_ORIENTABLE : |- MOI_FND_BICOLLAR_CURVE_2                 *)
(* Route:                                                                    *)
(*   orientation transfer to refinements (MOI_FCB_ORIENT_REFINE);            *)
(*   the two sides of a polygon in a closed surface (after                   *)
(*          MOI_FSTR_TWO_SIDED of pc_moi_fnd_sptrace), with closure facts;   *)
(*   orientation signs near the lifted interior of the cap                   *)
(*          (pc_moi_fnd_cap);                                                *)
(*   the bicollar of a polygon in a closed surface (the split and            *)
(*          collar machinery of pc_moi_fnd_bcollar, glued as in bicol);      *)
(*   one polygon of the interior: inside the cap, then transported           *)
(*          back by fstcart;                                                 *)
(*   refinement, components (pc_moi_s28_cut), glue; the main theorem.        *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_bcollar.ml";;
needs "src/pc_moi_fnd_sptrace.ml";;
needs "src/pc_moi_s28_cut.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Affine coordinates with respect to a triangle p q r in real^N             *)
(* (moi_fcb_bc, a vector in real^3 with coordinate sum 1) and the            *)
(* determinant of the coordinates of three points (moi_fcb_det): affine in   *)
(* the third point, alternating in the points and in the frame, nonzero for  *)
(* non-collinear points of the plane of the triangle.                        *)
(* ========================================================================= *)

let moi_fcb_bc = new_definition
 `moi_fcb_bc (p:real^N) q r (x:real^N) =
    @w:real^3. w$1 + w$2 + w$3 = &1 /\ x = w$1 % p + w$2 % q + w$3 % r`;;

let moi_fcb_det = new_definition
 `moi_fcb_det (p:real^N) q r a b d =
    det(vector[moi_fcb_bc p q r a; moi_fcb_bc p q r b;
               moi_fcb_bc p q r d]:real^3^3)`;;

(* Linear independence of the edge vectors of a triangle.                   *)

let MOI_FCB_NONCOLL_EQ = prove
 (`!p q r:real^N s t.
     ~collinear {p,q,r} /\ s % (q - p) + t % (r - p) = vec 0 ==> s = &0 /\ t = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  UNDISCH_TAC `~collinear {p:real^N,q,r}` THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `{p:real^N,q,r} = {q,p,r}` SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[COLLINEAR_3; COLLINEAR_LEMMA_ALT] THEN
  ASM_CASES_TAC `t = &0` THENL
   [DISJ1_TAC THEN
    SUBGOAL_THEN `~(s = &0)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `s % (q - p) + t % (r - p) = vec 0:real^N` THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; VECTOR_MUL_EQ_0];
    DISJ2_TAC THEN EXISTS_TAC `--s / t` THEN
    MATCH_MP_TAC VECTOR_MUL_LCANCEL_IMP THEN EXISTS_TAC `t:real` THEN
    ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN ASM_SIMP_TAC[REAL_DIV_LMUL] THEN
    UNDISCH_TAC `s % (q - p) + t % (r - p) = vec 0:real^N` THEN VECTOR_ARITH_TAC]);;

(* Basic facts about a non-collinear triple.                                 *)

let MOI_FCB_TRI_FACTS = prove
 (`!p q r:real^N.
     ~collinear {p,q,r}
     ==> ~(p = q) /\ ~(p = r) /\ ~(q = r) /\ ~affine_dependent {p,q,r} /\
         aff_dim {p,q,r} = &2 /\ aff_dim(convex hull {p,q,r}) = &2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT; DE_MORGAN_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN
  ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT; MOI_FC2_CARD_3] THEN
  CONV_TAC INT_REDUCE_CONV);;

(* The coordinates.                                                           *)

let MOI_FCB_BC_UNIQUE = prove
 (`!p q r (x:real^N) (y:real^3).
     ~collinear {p,q,r} /\ y$1 + y$2 + y$3 = &1 /\ x = y$1 % p + y$2 % q + y$3 % r
     ==> moi_fcb_bc p q r x = y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_fcb_bc] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  X_GEN_TAC `z:real^3` THEN BETA_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN
    MP_TAC(ISPECL [`p:real^N`; `q:real^N`; `r:real^N`; `(z:real^3)$2 - (y:real^3)$2`;
                   `(z:real^3)$3 - (y:real^3)$3`] MOI_FCB_NONCOLL_EQ) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `x = (z:real^3)$1 % p + z$2 % q + z$3 % (r:real^N)` THEN
      UNDISCH_TAC `x = (y:real^3)$1 % p + y$2 % q + y$3 % (r:real^N)` THEN
      DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN `(y:real^3)$1 = &1 - y$2 - y$3 /\ (z:real^3)$1 = &1 - z$2 - z$3`
      (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    STRIP_TAC THEN REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

let MOI_FCB_BC = prove
 (`!p q r (x:real^N).
     ~collinear {p,q,r} /\ x IN affine hull {p,q,r}
     ==> (moi_fcb_bc p q r x)$1 + (moi_fcb_bc p q r x)$2 + (moi_fcb_bc p q r x)$3 = &1 /\
         x = (moi_fcb_bc p q r x)$1 % p + (moi_fcb_bc p q r x)$2 % q +
             (moi_fcb_bc p q r x)$3 % r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[AFFINE_HULL_3; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `u:real` (X_CHOOSE_THEN `v:real`
    (X_CHOOSE_THEN `w:real` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`p:real^N`; `q:real^N`; `r:real^N`; `x:real^N`; `vector[u;v;w]:real^3`]
    MOI_FCB_BC_UNIQUE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[VECTOR_3]; DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[VECTOR_3]);;

let MOI_FCB_BC_CONVEX = prove
 (`!p q r (x:real^N).
     ~collinear {p,q,r} /\ x IN convex hull {p,q,r}
     ==> &0 <= (moi_fcb_bc p q r x)$1 /\ &0 <= (moi_fcb_bc p q r x)$2 /\
         &0 <= (moi_fcb_bc p q r x)$3`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `u:real` (X_CHOOSE_THEN `v:real`
    (X_CHOOSE_THEN `w:real` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`p:real^N`; `q:real^N`; `r:real^N`; `x:real^N`; `vector[u;v;w]:real^3`]
    MOI_FCB_BC_UNIQUE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[VECTOR_3]; DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[VECTOR_3]);;

let MOI_FCB_BC_AFFINE = prove
 (`!p q r (a:real^N) b d u1 u2 u3.
     ~collinear {p,q,r} /\ a IN affine hull {p,q,r} /\ b IN affine hull {p,q,r} /\
     d IN affine hull {p,q,r} /\ u1 + u2 + u3 = &1
     ==> moi_fcb_bc p q r (u1 % a + u2 % b + u3 % d) =
         u1 % moi_fcb_bc p q r a + u2 % moi_fcb_bc p q r b + u3 % moi_fcb_bc p q r d`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:real^N`; `q:real^N`; `r:real^N`; `a:real^N`] MOI_FCB_BC) THEN
  MP_TAC(ISPECL [`p:real^N`; `q:real^N`; `r:real^N`; `b:real^N`] MOI_FCB_BC) THEN
  MP_TAC(ISPECL [`p:real^N`; `q:real^N`; `r:real^N`; `d:real^N`] MOI_FCB_BC) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`moi_fcb_bc p q r (a:real^N)`,`A:real^3`) THEN
  SPEC_TAC(`moi_fcb_bc p q r (b:real^N)`,`B:real^3`) THEN
  SPEC_TAC(`moi_fcb_bc p q r (d:real^N)`,`D:real^3`) THEN
  REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MOI_FCB_BC_UNIQUE THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `(u1 * (A:real^3)$1 + u2 * (B:real^3)$1 + u3 * (D:real^3)$1) +
      (u1 * A$2 + u2 * B$2 + u3 * D$2) + (u1 * A$3 + u2 * B$3 + u3 * D$3) =
      u1 * (A$1 + A$2 + A$3) + u2 * (B$1 + B$2 + B$3) + u3 * (D$1 + D$2 + D$3)`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_MUL_RID];
    VECTOR_ARITH_TAC]);;

(* Coordinates with respect to a reordered frame.                            *)

let MOI_FCB_BC_SWAP = prove
 (`!p q r (x:real^N).
     ~collinear {p,q,r} /\ x IN affine hull {p,q,r}
     ==> moi_fcb_bc q p r x =
         vector[(moi_fcb_bc p q r x)$2; (moi_fcb_bc p q r x)$1; (moi_fcb_bc p q r x)$3] /\
         moi_fcb_bc p r q x =
         vector[(moi_fcb_bc p q r x)$1; (moi_fcb_bc p q r x)$3; (moi_fcb_bc p q r x)$2]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p:real^N`; `q:real^N`; `r:real^N`; `x:real^N`] MOI_FCB_BC) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`moi_fcb_bc p q r (x:real^N)`,`y:real^3`) THEN GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `{q,p,r} = {p:real^N,q,r} /\ {p,r,q} = {p:real^N,q,r}` STRIP_ASSUME_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC MOI_FCB_BC_UNIQUE THEN ASM_REWRITE_TAC[VECTOR_3] THEN
  (CONJ_TAC THENL [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC]));;

(* The coordinate determinant.                                               *)

let MOI_FCB_DET_ROWS = prove
 (`!p q r (a:real^N) b d.
     moi_fcb_det p q r b a d = --(moi_fcb_det p q r a b d) /\
     moi_fcb_det p q r a d b = --(moi_fcb_det p q r a b d)`,
  REWRITE_TAC[moi_fcb_det; DET_3; VECTOR_3] THEN REAL_ARITH_TAC);;

let MOI_FCB_DET_SWAP = prove
 (`!p q r (a:real^N) b d.
     ~collinear {p,q,r} /\ a IN affine hull {p,q,r} /\ b IN affine hull {p,q,r} /\
     d IN affine hull {p,q,r}
     ==> moi_fcb_det q p r a b d = --(moi_fcb_det p q r a b d) /\
         moi_fcb_det p r q a b d = --(moi_fcb_det p q r a b d)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_fcb_det] THEN ASM_SIMP_TAC[MOI_FCB_BC_SWAP] THEN
  REWRITE_TAC[DET_3; VECTOR_3] THEN REAL_ARITH_TAC);;

let MOI_FCB_DET_AFF = prove
 (`!p q r (a:real^N) b d u1 u2 u3.
     ~collinear {p,q,r} /\ a IN affine hull {p,q,r} /\ b IN affine hull {p,q,r} /\
     d IN affine hull {p,q,r} /\ u1 + u2 + u3 = &1
     ==> moi_fcb_det p q r a b (u1 % a + u2 % b + u3 % d) =
         u3 * moi_fcb_det p q r a b d`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_fcb_det] THEN
  ASM_SIMP_TAC[MOI_FCB_BC_AFFINE] THEN
  REWRITE_TAC[DET_3; VECTOR_3; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  CONV_TAC REAL_RING);;

(* The coordinate determinant of three non-collinear points of the plane of *)
(* the triangle is nonzero.                                                   *)

let MOI_FCB_DET_NZ = prove
 (`!p q r (a:real^N) b d.
     ~collinear {p,q,r} /\ ~collinear {a,b,d} /\
     a IN affine hull {p,q,r} /\ b IN affine hull {p,q,r} /\ d IN affine hull {p,q,r}
     ==> ~(moi_fcb_det p q r a b d = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p:real^N`; `q:real^N`; `r:real^N`; `a:real^N`] MOI_FCB_BC) THEN
  MP_TAC(ISPECL [`p:real^N`; `q:real^N`; `r:real^N`; `b:real^N`] MOI_FCB_BC) THEN
  MP_TAC(ISPECL [`p:real^N`; `q:real^N`; `r:real^N`; `d:real^N`] MOI_FCB_BC) THEN
  ASM_REWRITE_TAC[moi_fcb_det] THEN
  SPEC_TAC(`moi_fcb_bc p q r (a:real^N)`,`A:real^3`) THEN
  SPEC_TAC(`moi_fcb_bc p q r (b:real^N)`,`B:real^3`) THEN
  SPEC_TAC(`moi_fcb_bc p q r (d:real^N)`,`D:real^3`) THEN
  REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `transp(vector[A:real^3; B; D]:real^3^3)` HOMOGENEOUS_LINEAR_EQUATIONS_DET) THEN
  ASM_REWRITE_TAC[DET_TRANSP] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; MATRIX_VECTOR_MUL_COMPONENT; ARITH; DOT_3;
           TRANSP_COMPONENT; VECTOR_3; VEC_COMPONENT] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z:real^3)$1 + z$2 + z$3 = &0` ASSUME_TAC THENL
   [MAP_EVERY (fun t -> MP_TAC(ASSUME t))
     [`(A:real^3)$1 + A$2 + A$3 = &1`; `(B:real^3)$1 + B$2 + B$3 = &1`;
      `(D:real^3)$1 + D$2 + D$3 = &1`;
      `(A:real^3)$1 * (z:real^3)$1 + (B:real^3)$1 * z$2 + (D:real^3)$1 * z$3 = &0`;
      `(A:real^3)$2 * (z:real^3)$1 + (B:real^3)$2 * z$2 + (D:real^3)$2 * z$3 = &0`;
      `(A:real^3)$3 * (z:real^3)$1 + (B:real^3)$3 * z$2 + (D:real^3)$3 * z$3 = &0`] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3)$2 % (b - a) + z$3 % (d - a:real^N) = vec 0` ASSUME_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `(z:real^3)$1 % a + z$2 % b + z$3 % (d:real^N)` THEN CONJ_TAC THENL
     [UNDISCH_TAC `(z:real^3)$1 + z$2 + z$3 = &0` THEN
      REWRITE_TAC[REAL_ARITH `x + y + w = &0 <=> x = --y - w`] THEN
      DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `((A:real^3)$1 * (z:real^3)$1 + (B:real^3)$1 * z$2 + (D:real^3)$1 * z$3) % p +
                (A$2 * z$1 + B$2 * z$2 + D$2 * z$3) % q +
                (A$3 * z$1 + B$3 * z$2 + D$3 * z$3) % (r:real^N)` THEN
    CONJ_TAC THENL [VECTOR_ARITH_TAC; ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d:real^N`; `(z:real^3)$2`; `(z:real^3)$3`]
    MOI_FCB_NONCOLL_EQ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `~(z:real^3 = vec 0)` THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VEC_COMPONENT] THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Orientation transfer to refinements.  A triangle of a refinement t of an  *)
(* oriented surface complex c gets the sign of its carrier triangle times    *)
(* the sign of its coordinate determinant there (moi_fcb_osg); the value     *)
(* does not depend on the frame (MOI_FCB_FRAME_PERM); two triangles of t on  *)
(* a common edge get opposite signs, inside one carrier (MOI_FCB_OPP_SIDES)  *)
(* or across a common edge of two carriers (MOI_FCB_EDGE_FRAMES).            *)
(* ========================================================================= *)

(* Swapping two frame points changes both factors.                           *)

let MOI_FCB_FRAME_SWAP = prove
 (`!(c:(real^N->bool)->bool) sg p q r a b d.
     (!a b d. convex hull {a,b,d} IN c /\ aff_dim(convex hull {a,b,d}) = &2
              ==> (sg a b d = &1 \/ sg a b d = -- &1) /\
                  sg b a d = --(sg a b d) /\ sg a d b = --(sg a b d)) /\
     convex hull {p,q,r} IN c /\ ~collinear {p,q,r} /\
     a IN affine hull {p,q,r} /\ b IN affine hull {p,q,r} /\ d IN affine hull {p,q,r}
     ==> sg q p r * real_sgn(moi_fcb_det q p r a b d) =
         sg p q r * real_sgn(moi_fcb_det p q r a b d) /\
         sg p r q * real_sgn(moi_fcb_det p r q a b d) =
         sg p q r * real_sgn(moi_fcb_det p q r a b d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p:real^N`; `q:real^N`; `r:real^N`]) THEN
  ASM_SIMP_TAC[MOI_FCB_TRI_FACTS] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MOI_FCB_DET_SWAP; REAL_SGN_NEG] THEN REAL_ARITH_TAC);;

(* The six orderings of three distinct points.                               *)

let MOI_FCB_PERM3_CASES = prove
 (`!p q r p' q' r':A.
     ~(p = q) /\ ~(p = r) /\ ~(q = r) /\ {p',q',r'} = {p,q,r}
     ==> (p' = p /\ q' = q /\ r' = r) \/ (p' = q /\ q' = p /\ r' = r) \/
         (p' = p /\ q' = r /\ r' = q) \/ (p' = q /\ q' = r /\ r' = p) \/
         (p' = r /\ q' = p /\ r' = q) \/ (p' = r /\ q' = q /\ r' = p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(q:A = p) /\ ~(r:A = p) /\ ~(r:A = q)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(p = p' \/ p = q' \/ p = r') /\ (q = p' \/ q = q' \/ q = r') /\
    (r = p' \/ r = q' \/ r = r':A)`
  MP_TAC THENL
   [UNDISCH_TAC `{p',q',r'} = {p:A,q,r}` THEN
    REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(p' = p \/ p' = q \/ p' = r) /\ (q' = p \/ q' = q \/ q' = r) /\
    (r' = p \/ r' = q \/ r' = r:A)`
  MP_TAC THENL
   [UNDISCH_TAC `{p',q',r'} = {p:A,q,r}` THEN
    REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC)
    (CONJUNCTS_THEN2 (REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC)
      (REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC))) THEN
  ASM_REWRITE_TAC[]);;

(* Any reordering of the frame.                                               *)

let MOI_FCB_FRAME_PERM = prove
 (`!(c:(real^N->bool)->bool) sg p q r p' q' r' a b d.
     (!a b d. convex hull {a,b,d} IN c /\ aff_dim(convex hull {a,b,d}) = &2
              ==> (sg a b d = &1 \/ sg a b d = -- &1) /\
                  sg b a d = --(sg a b d) /\ sg a d b = --(sg a b d)) /\
     convex hull {p,q,r} IN c /\ ~collinear {p,q,r} /\
     a IN affine hull {p,q,r} /\ b IN affine hull {p,q,r} /\ d IN affine hull {p,q,r} /\
     {p',q',r'} = {p,q,r}
     ==> sg p' q' r' * real_sgn(moi_fcb_det p' q' r' a b d) =
         sg p q r * real_sgn(moi_fcb_det p q r a b d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(p:real^N = q) /\ ~(p = r) /\ ~(q = r)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FCB_TRI_FACTS]; ALL_TAC] THEN
  SUBGOAL_THEN `{q,p,r} = {p:real^N,q,r} /\ {p,r,q} = {p,q,r} /\ {r,p,q} = {p,q,r}`
  STRIP_ASSUME_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `sg q p r * real_sgn(moi_fcb_det q p r a b d) =
    sg p q r * real_sgn(moi_fcb_det p q r a b (d:real^N)) /\
    sg p r q * real_sgn(moi_fcb_det p r q a b d) =
    sg p q r * real_sgn(moi_fcb_det p q r a b d) /\
    sg q r p * real_sgn(moi_fcb_det q r p a b d) =
    sg q p r * real_sgn(moi_fcb_det q p r a b d) /\
    sg r p q * real_sgn(moi_fcb_det r p q a b d) =
    sg p r q * real_sgn(moi_fcb_det p r q a b d) /\
    sg r q p * real_sgn(moi_fcb_det r q p a b d) =
    sg r p q * real_sgn(moi_fcb_det r p q a b d)`
  (LABEL_TAC "E") THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `sg:real^N->real^N->real^N->real`;
                   `p:real^N`; `q:real^N`; `r:real^N`; `a:real^N`; `b:real^N`; `d:real^N`]
      MOI_FCB_FRAME_SWAP) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `sg:real^N->real^N->real^N->real`;
                   `q:real^N`; `p:real^N`; `r:real^N`; `a:real^N`; `b:real^N`; `d:real^N`]
      MOI_FCB_FRAME_SWAP) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `sg:real^N->real^N->real^N->real`;
                   `p:real^N`; `r:real^N`; `q:real^N`; `a:real^N`; `b:real^N`; `d:real^N`]
      MOI_FCB_FRAME_SWAP) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `sg:real^N->real^N->real^N->real`;
                   `r:real^N`; `p:real^N`; `q:real^N`; `a:real^N`; `b:real^N`; `d:real^N`]
      MOI_FCB_FRAME_SWAP) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:real^N`; `q:real^N`; `r:real^N`; `p':real^N`; `q':real^N`; `r':real^N`]
    MOI_FCB_PERM3_CASES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC)) THEN
  USE_THEN "E" (fun th -> REWRITE_TAC[th]));;

(* Triangles of a simplicial complex.                                         *)

let MOI_FCB_TRI_FRAME = prove
 (`!(c:(real^N->bool)->bool) k.
     simplicial_complex c /\ k IN c /\ aff_dim k = &2
     ==> ?p q r. ~collinear {p,q,r} /\ k = convex hull {p,q,r}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&2 simplex (k:real^N->bool)` MP_TAC THENL
   [SUBGOAL_THEN `?n. n simplex (k:real^N->bool)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
    ASM_MESON_TAC[AFF_DIM_SIMPLEX];
    ALL_TAC] THEN
  REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(v:real^N->bool) HAS_SIZE 3` MP_TAC THENL
   [REWRITE_TAC[HAS_SIZE] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE];
      UNDISCH_TAC `&(CARD(v:real^N->bool)):int = &2 + &1` THEN
      REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ARITH_TAC];
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `q:real^N` (X_CHOOSE_THEN `r:real^N`
    STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`p:real^N`; `q:real^N`; `r:real^N`] THEN
  UNDISCH_TAC `~affine_dependent (v:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT]);;

(* Two triangles of a 2-dimensional complex containing a common 2-dimensional *)
(* set coincide.                                                              *)

let MOI_FCB_CARRIER_EQ = prove
 (`!(c:(real^N->bool)->bool) k1 k2 s.
     simplicial_complex c /\ k1 IN c /\ k2 IN c /\ aff_dim k1 <= &2 /\ aff_dim k2 <= &2 /\
     s SUBSET k1 /\ s SUBSET k2 /\ aff_dim s = &2
     ==> k1 = k2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(k1 INTER k2:real^N->bool) face_of k1 /\ (k1 INTER k2) face_of k2`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `convex(k1:real^N->bool) /\ convex(k2:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(s:real^N->bool) <= aff_dim(k1 INTER k2:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC AFF_DIM_SUBSET THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `k1 INTER k2 = (k1:real^N->bool) /\ k1 INTER k2 = (k2:real^N->bool)` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THENL
     [MP_TAC(ISPECL [`k1 INTER k2:real^N->bool`; `k1:real^N->bool`] FACE_OF_AFF_DIM_LT);
      MP_TAC(ISPECL [`k1 INTER k2:real^N->bool`; `k2:real^N->bool`] FACE_OF_AFF_DIM_LT)] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `aff_dim(k1:real^N->bool) <= &2` THEN
    UNDISCH_TAC `aff_dim(k2:real^N->bool) <= &2` THEN
    UNDISCH_TAC `aff_dim(s:real^N->bool) <= aff_dim(k1 INTER k2:real^N->bool)` THEN
    UNDISCH_TAC `aff_dim(s:real^N->bool) = &2` THEN INT_ARITH_TAC;
    MESON_TAC[]]);;

(* The vertex set of a triangle.                                              *)

let MOI_FCB_HULL_VERTS = prove
 (`!p q r p' q' r':real^N.
     ~collinear {p,q,r} /\ ~collinear {p',q',r'} /\
     convex hull {p,q,r} = convex hull {p',q',r'}
     ==> {p,q,r} = {p',q',r'}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~affine_dependent {p:real^N,q,r} /\ ~affine_dependent {p':real^N,q',r'}`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[MOI_FCB_TRI_FACTS]; ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
  ASM_MESON_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT]);;

let MOI_FCB_IN_AFF = prove
 (`!a b d p q r:real^N.
     convex hull {a,b,d} SUBSET convex hull {p,q,r}
     ==> a IN affine hull {p,q,r} /\ b IN affine hull {p,q,r} /\ d IN affine hull {p,q,r}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `{p:real^N,q,r}` CONVEX_HULL_SUBSET_AFFINE_HULL) THEN
  MP_TAC(ISPECL [`convex:(real^N->bool)->bool`; `{a:real^N,b,d}`] HULL_SUBSET) THEN
  UNDISCH_TAC `convex hull {a,b,d} SUBSET convex hull {p:real^N,q,r}` THEN
  SET_TAC[]);;

(* The transferred sign.                                                      *)

let moi_fcb_osg = new_definition
 `moi_fcb_osg (c:(real^N->bool)->bool) (sg:real^N->real^N->real^N->real)
              (a:real^N) b d =
    @s. ?p q r. convex hull {p,q,r} IN c /\ ~collinear {p,q,r} /\
                convex hull {a,b,d} SUBSET convex hull {p,q,r} /\
                s = sg p q r * real_sgn(moi_fcb_det p q r a b d)`;;

let MOI_FCB_OSG_EVAL = prove
 (`!(c:(real^N->bool)->bool) sg p q r a b d.
     simplicial_complex c /\ (!k. k IN c ==> aff_dim k <= &2) /\
     (!a b d. convex hull {a,b,d} IN c /\ aff_dim(convex hull {a,b,d}) = &2
              ==> (sg a b d = &1 \/ sg a b d = -- &1) /\
                  sg b a d = --(sg a b d) /\ sg a d b = --(sg a b d)) /\
     convex hull {p,q,r} IN c /\ ~collinear {p,q,r} /\ ~collinear {a,b,d} /\
     convex hull {a,b,d} SUBSET convex hull {p,q,r}
     ==> moi_fcb_osg c sg a b d = sg p q r * real_sgn(moi_fcb_det p q r a b d)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_fcb_osg] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  X_GEN_TAC `s:real` THEN BETA_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `p':real^N` (X_CHOOSE_THEN `q':real^N`
      (X_CHOOSE_THEN `r':real^N` STRIP_ASSUME_TAC))) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `convex hull {p',q',r'} = convex hull {p:real^N,q,r}` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FCB_CARRIER_EQ THEN
      MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `convex hull {a:real^N,b,d}`] THEN
      ASM_SIMP_TAC[MOI_FCB_TRI_FACTS];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d:real^N`; `p:real^N`; `q:real^N`; `r:real^N`]
      MOI_FCB_IN_AFF) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_FCB_FRAME_PERM THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FCB_HULL_VERTS THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN
    MAP_EVERY EXISTS_TAC [`p:real^N`; `q:real^N`; `r:real^N`] THEN ASM_REWRITE_TAC[]]);;

(* A small step from the midpoint of an edge.                                *)

let MOI_FCB_SMALL_STEP = prove
 (`!u1 u2. ?t. &0 < t /\ t < &1 /\
               &0 <= (&1 - t) / &2 + t * u1 /\ &0 <= (&1 - t) / &2 + t * u2`,
  REPEAT GEN_TAC THEN
  EXISTS_TAC `inv(&4 * (&1 + abs u1 + abs u2))` THEN
  ABBREV_TAC `t = inv(&4 * (&1 + abs u1 + abs u2))` THEN
  SUBGOAL_THEN `&0 < t /\ t * (&4 * (&1 + abs u1 + abs u2)) = &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_MUL_LINV THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= t * abs u1 /\ &0 <= t * abs u2 /\
    &0 <= t * (u1 + abs u1) /\ &0 <= t * (u2 + abs u2)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `t * (&4 * (&1 + abs u1 + abs u2)) = &1` THEN
  UNDISCH_TAC `&0 <= t * (u1 + abs u1)` THEN UNDISCH_TAC `&0 <= t * (u2 + abs u2)` THEN
  UNDISCH_TAC `&0 <= t * abs u1` THEN UNDISCH_TAC `&0 <= t * abs u2` THEN
  UNDISCH_TAC `&0 < t` THEN REAL_ARITH_TAC);;

(* Two triangles of a complex on a common edge inside one triangle of the  *)
(* plane lie on opposite sides of the edge.                                 *)

let MOI_FCB_OPP_SIDES = prove
 (`!(t:(real^N->bool)->bool) p q r a b d d'.
     simplicial_complex t /\ ~(d = d') /\
     convex hull {a,b,d} IN t /\ ~collinear {a,b,d} /\
     convex hull {a,b,d'} IN t /\ ~collinear {a,b,d'} /\
     ~collinear {p,q,r} /\
     convex hull {a,b,d} SUBSET convex hull {p,q,r} /\
     convex hull {a,b,d'} SUBSET convex hull {p,q,r}
     ==> moi_fcb_det p q r a b d * moi_fcb_det p q r a b d' < &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d:real^N`; `p:real^N`; `q:real^N`; `r:real^N`]
    MOI_FCB_IN_AFF) THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d':real^N`; `p:real^N`; `q:real^N`; `r:real^N`]
    MOI_FCB_IN_AFF) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(moi_fcb_det p q r a b (d:real^N) = &0) /\
                ~(moi_fcb_det p q r a b (d':real^N) = &0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_FCB_DET_NZ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(d:real^N) IN affine hull {a,b,d'}` MP_TAC THENL
   [SUBGOAL_THEN `affine hull {a,b,d'} = affine hull {p:real^N,q,r}` SUBST1_TAC THENL
     [MP_TAC(ISPECL [`{a:real^N,b,d'}`; `affine hull {p:real^N,q,r}`]
        AFF_DIM_EQ_AFFINE_HULL) THEN
      REWRITE_TAC[HULL_HULL; AFF_DIM_AFFINE_HULL] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[MOI_FCB_TRI_FACTS; INT_LE_REFL] THEN
      ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[AFFINE_HULL_3; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:real` (X_CHOOSE_THEN `v2:real` (X_CHOOSE_THEN `v3:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))))) THEN
  SUBGOAL_THEN `moi_fcb_det p q r a b (d:real^N) = v3 * moi_fcb_det p q r a b d'`
  ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> rhs(concl th) = `d:real^N`)) THEN
    MATCH_MP_TAC MOI_FCB_DET_AFF THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `v3 < &0` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < v3` ASSUME_TAC THENL
     [UNDISCH_TAC `~(v3 < &0)` THEN
      ASM_CASES_TAC `v3 = &0` THENL
       [UNDISCH_TAC `~(moi_fcb_det p q r a b (d:real^N) = &0)` THEN
        ASM_REWRITE_TAC[REAL_MUL_LZERO];
        UNDISCH_TAC `~(v3 = &0)` THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(SPECL [`v1:real`; `v2:real`] MOI_FCB_SMALL_STEP) THEN
    DISCH_THEN(X_CHOOSE_THEN `tau:real` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `X = ((&1 - tau) / &2) % a + ((&1 - tau) / &2) % b + tau % (d:real^N)` THEN
    SUBGOAL_THEN `(X:real^N) IN convex hull {a,b,d}` ASSUME_TAC THENL
     [EXPAND_TAC "X" THEN REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN
      MAP_EVERY EXISTS_TAC [`(&1 - tau) / &2`; `(&1 - tau) / &2`; `tau:real`] THEN
      REWRITE_TAC[] THEN
      UNDISCH_TAC `&0 < tau` THEN UNDISCH_TAC `tau < &1` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(X:real^N) IN convex hull {a,b,d'}` ASSUME_TAC THENL
     [REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN
      MAP_EVERY EXISTS_TAC [`(&1 - tau) / &2 + tau * v1`; `(&1 - tau) / &2 + tau * v2`;
                            `tau * v3`] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN
        UNDISCH_TAC `&0 < tau` THEN UNDISCH_TAC `&0 < v3` THEN REAL_ARITH_TAC;
        UNDISCH_TAC `v1 + v2 + v3 = &1` THEN CONV_TAC REAL_RING;
        EXPAND_TAC "X" THEN
        FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> rhs(concl th) = `d:real^N`)) THEN
        VECTOR_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(X:real^N) IN convex hull {a,b}` MP_TAC THENL
     [SUBGOAL_THEN `convex hull {a,b,d} INTER convex hull {a,b,d'} =
                    convex hull {a:real^N,b}` (fun th -> REWRITE_TAC[GSYM th]) THENL
       [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `{a:real^N,b,d}`; `{a:real^N,b,d'}`]
          MOI_REAL_SIMPLICIAL_COMPLEX_INTER_HULL) THEN
        ANTS_TAC THENL [ASM_MESON_TAC[MOI_FCB_TRI_FACTS]; DISCH_THEN SUBST1_TAC] THEN
        AP_TERM_TAC THEN
        SUBGOAL_THEN `~(d:real^N = a) /\ ~(d = b)` MP_TAC THENL
         [ASM_MESON_TAC[MOI_FCB_TRI_FACTS]; ALL_TAC] THEN
        UNDISCH_TAC `~(d:real^N = d')` THEN SET_TAC[];
        ASM_REWRITE_TAC[IN_INTER]];
      ALL_TAC] THEN
    REWRITE_TAC[CONVEX_HULL_2; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `mu:real` (X_CHOOSE_THEN `nu:real` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `moi_fcb_det p q r a b (X:real^N) = tau * moi_fcb_det p q r a b d`
    MP_TAC THENL
     [EXPAND_TAC "X" THEN MATCH_MP_TAC MOI_FCB_DET_AFF THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `moi_fcb_det p q r a b (X:real^N) = &0 * moi_fcb_det p q r a b d`
    SUBST1_TAC THENL
     [UNDISCH_TAC `X:real^N = mu % a + nu % b` THEN DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN `mu % a + nu % b = mu % a + nu % b + &0 % (d:real^N)` SUBST1_TAC THENL
       [VECTOR_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC MOI_FCB_DET_AFF THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `mu + nu = &1` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_LZERO] THEN
    DISCH_THEN(MP_TAC o SYM) THEN REWRITE_TAC[REAL_ENTIRE] THEN
    UNDISCH_TAC `~(moi_fcb_det p q r a b (d:real^N) = &0)` THEN
    UNDISCH_TAC `&0 < tau` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < --v * (x * x) ==> (v * x) * x < &0`) THEN
  MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_LT_SQUARE] THEN
  UNDISCH_TAC `v3 < &0` THEN REAL_ARITH_TAC);;

(* The third point of a 3-set.                                                *)

let MOI_FCB_THIRD = prove
 (`!x y p q r:A.
     x IN {p,q,r} /\ y IN {p,q,r} /\ ~(x = y) ==> ?z. {x,y,z} = {p,q,r}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  DISCH_THEN(fun th -> MP_TAC(CONJUNCT2(CONJUNCT2 th)) THEN
    MP_TAC(CONJUNCT1(CONJUNCT2 th)) THEN MP_TAC(CONJUNCT1 th)) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST [EXISTS_TAC `p:A` THEN SET_TAC[]; EXISTS_TAC `q:A` THEN SET_TAC[];
         EXISTS_TAC `r:A` THEN SET_TAC[]]);;

(* Two different triangles of a complex sharing two points share an edge   *)
(* through them.                                                             *)

let MOI_FCB_EDGE_FRAMES = prove
 (`!(c:(real^N->bool)->bool) p1 q1 r1 p2 q2 r2 a b.
     simplicial_complex c /\
     convex hull {p1,q1,r1} IN c /\ ~collinear {p1,q1,r1} /\
     convex hull {p2,q2,r2} IN c /\ ~collinear {p2,q2,r2} /\
     ~(convex hull {p1,q1,r1} = convex hull {p2,q2,r2}) /\ ~(a = b) /\
     a IN convex hull {p1,q1,r1} /\ a IN convex hull {p2,q2,r2} /\
     b IN convex hull {p1,q1,r1} /\ b IN convex hull {p2,q2,r2}
     ==> ?x y z1 z2. {x,y,z1} = {p1,q1,r1} /\ {x,y,z2} = {p2,q2,r2} /\ ~(z1 = z2) /\
                     a IN convex hull {x,y} /\ b IN convex hull {x,y}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `~affine_dependent {p1:real^N,q1,r1} /\ ~affine_dependent {p2:real^N,q2,r2} /\
    ~(p1 = q1) /\ ~(p1 = r1) /\ ~(q1 = r1) /\ ~(p2 = q2) /\ ~(p2 = r2) /\ ~(q2 = r2)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[MOI_FCB_TRI_FACTS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `{p1:real^N,q1,r1}`; `{p2:real^N,q2,r2}`]
    MOI_REAL_SIMPLICIAL_COMPLEX_INTER_HULL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(a:real^N) IN convex hull ({p1,q1,r1} INTER {p2,q2,r2}) /\
    (b:real^N) IN convex hull ({p1,q1,r1} INTER {p2,q2,r2})`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      is_comb(lhs(concl th)) &&
      can (find_term ((=) `(INTER):(real^N->bool)->(real^N->bool)->real^N->bool`))
          (lhs(concl th)))) THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?x y z1. {x,y,z1} = {p1:real^N,q1,r1} /\ x IN {p2,q2,r2} /\ y IN {p2,q2,r2} /\
             ~(z1 IN {p2,q2,r2}) /\ ~(x = y)`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `(p1:real^N) IN {p2,q2,r2}` THEN
    ASM_CASES_TAC `(q1:real^N) IN {p2,q2,r2}` THEN
    ASM_CASES_TAC `(r1:real^N) IN {p2,q2,r2}` THENL
     [MATCH_MP_TAC(TAUT `F ==> p`) THEN
      UNDISCH_TAC `~(convex hull {p1,q1,r1} = convex hull {p2:real^N,q2,r2})` THEN
      REWRITE_TAC[] THEN AP_TERM_TAC THEN MATCH_MP_TAC CARD_SUBSET_EQ THEN
      ASM_SIMP_TAC[FINITE_INSERT; FINITE_EMPTY; MOI_FC2_CARD_3; INSERT_SUBSET;
                   EMPTY_SUBSET];
      MAP_EVERY EXISTS_TAC [`p1:real^N`; `q1:real^N`; `r1:real^N`] THEN ASM_REWRITE_TAC[];
      MAP_EVERY EXISTS_TAC [`p1:real^N`; `r1:real^N`; `q1:real^N`] THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      SUBGOAL_THEN `{p1,q1,r1} INTER {p2,q2,r2} = {p1:real^N}` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(a:real^N) IN convex hull ({p1,q1,r1} INTER {p2,q2,r2})` THEN
      UNDISCH_TAC `(b:real^N) IN convex hull ({p1,q1,r1} INTER {p2,q2,r2})` THEN
      ASM_REWRITE_TAC[CONVEX_HULL_SING; IN_SING] THEN ASM_MESON_TAC[];
      MAP_EVERY EXISTS_TAC [`q1:real^N`; `r1:real^N`; `p1:real^N`] THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      SUBGOAL_THEN `{p1,q1,r1} INTER {p2,q2,r2} = {q1:real^N}` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(a:real^N) IN convex hull ({p1,q1,r1} INTER {p2,q2,r2})` THEN
      UNDISCH_TAC `(b:real^N) IN convex hull ({p1,q1,r1} INTER {p2,q2,r2})` THEN
      ASM_REWRITE_TAC[CONVEX_HULL_SING; IN_SING] THEN ASM_MESON_TAC[];
      SUBGOAL_THEN `{p1,q1,r1} INTER {p2,q2,r2} = {r1:real^N}` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(a:real^N) IN convex hull ({p1,q1,r1} INTER {p2,q2,r2})` THEN
      UNDISCH_TAC `(b:real^N) IN convex hull ({p1,q1,r1} INTER {p2,q2,r2})` THEN
      ASM_REWRITE_TAC[CONVEX_HULL_SING; IN_SING] THEN ASM_MESON_TAC[];
      SUBGOAL_THEN `{p1,q1,r1} INTER {p2,q2,r2} = {}:real^N->bool` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(a:real^N) IN convex hull ({p1,q1,r1} INTER {p2,q2,r2})` THEN
      ASM_REWRITE_TAC[CONVEX_HULL_EMPTY; NOT_IN_EMPTY]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`x:real^N`; `y:real^N`; `p2:real^N`; `q2:real^N`; `r2:real^N`]
    MOI_FCB_THIRD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `z2:real^N`) THEN
  MAP_EVERY EXISTS_TAC [`x:real^N`; `y:real^N`; `z1:real^N`; `z2:real^N`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `{p1,q1,r1} INTER {p2,q2,r2} = {x:real^N,y}` ASSUME_TAC THENL
   [UNDISCH_TAC `{x,y,z1} = {p1:real^N,q1,r1}` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `(x:real^N) IN {p2,q2,r2}` THEN UNDISCH_TAC `(y:real^N) IN {p2,q2,r2}` THEN
    UNDISCH_TAC `~((z1:real^N) IN {p2,q2,r2})` THEN SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `~((z1:real^N) IN {p2,q2,r2})` THEN
    UNDISCH_TAC `{x,y,z2} = {p2:real^N,q2,r2}` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SET_TAC[];
    UNDISCH_TAC `(a:real^N) IN convex hull ({p1,q1,r1} INTER {p2,q2,r2})` THEN
    UNDISCH_TAC `(b:real^N) IN convex hull ({p1,q1,r1} INTER {p2,q2,r2})` THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[]]);;

(* The sign of the coordinate determinant for two points on the edge x y of *)
(* the frame and a third point of the triangle.                              *)

let MOI_FCB_EDGE_DET = prove
 (`!x y z (a:real^N) b d u v u' v'.
     ~collinear {x,y,z} /\ ~collinear {a,b,d} /\
     u + v = &1 /\ a = u % x + v % y /\ u' + v' = &1 /\ b = u' % x + v' % y /\
     d IN convex hull {x,y,z}
     ==> real_sgn(moi_fcb_det x y z a b d) = real_sgn(u * v' - v * u')`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_fcb_bc x y z (a:real^N) = vector[u;v;&0] /\
                moi_fcb_bc x y z (b:real^N) = vector[u';v';&0]`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_FCB_BC_UNIQUE THEN ASM_REWRITE_TAC[VECTOR_3] THEN
    (CONJ_TAC THENL [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC]);
    ALL_TAC] THEN
  SUBGOAL_THEN `(d:real^N) IN affine hull {x,y,z}` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONVEX_HULL_SUBSET_AFFINE_HULL; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`x:real^N`; `y:real^N`; `z:real^N`; `d:real^N`] MOI_FCB_BC_CONVEX) THEN
  MP_TAC(ISPECL [`x:real^N`; `y:real^N`; `z:real^N`; `d:real^N`] MOI_FCB_BC) THEN
  ASM_REWRITE_TAC[moi_fcb_det] THEN
  SPEC_TAC(`moi_fcb_bc x y z (d:real^N)`,`D:real^3`) THEN GEN_TAC THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (D:real^3)$3` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `&0 = (D:real^3)$3`)) THEN
    UNDISCH_TAC `~collinear {a:real^N,b,d}` THEN REWRITE_TAC[COLLINEAR_AFFINE_HULL] THEN
    MAP_EVERY EXISTS_TAC [`x:real^N`; `y:real^N`] THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; AFFINE_HULL_2; IN_ELIM_THM] THEN
    REPEAT CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`u:real`; `v:real`] THEN ASM_REWRITE_TAC[];
      MAP_EVERY EXISTS_TAC [`u':real`; `v':real`] THEN ASM_REWRITE_TAC[];
      MAP_EVERY EXISTS_TAC [`(D:real^3)$1`; `(D:real^3)$2`] THEN
      CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV
          [check (fun th -> lhs(concl th) = `d:real^N`) th]) THEN
        VECTOR_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `det(vector[vector[u;v;&0]; vector[u';v';&0]; D]:real^3^3) =
    (D:real^3)$3 * (u * v' - v * u')`
  SUBST1_TAC THENL [REWRITE_TAC[DET_3; VECTOR_3] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_SGN_MUL] THEN
  SUBGOAL_THEN `real_sgn((D:real^3)$3) = &1` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[REAL_SGN_EQ; real_gt]; REAL_ARITH_TAC]);;

(* MOI_FCB_ORIENT_REFINE: orientability passes to refinements.               *)

let MOI_FCB_ORIENT_REFINE = prove
 (`!(c:(real^N->bool)->bool) t.
     simplicial_complex c /\ (!k. k IN c ==> aff_dim k <= &2) /\
     orientable_surface_complex c /\ simplicial_complex t /\
     (!s. s IN t ==> ?k. k IN c /\ s SUBSET k)
     ==> orientable_surface_complex t`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "DIM")
    (CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "REF"))))) THEN
  REWRITE_TAC[orientable_surface_complex] THEN
  DISCH_THEN(X_CHOOSE_THEN `sg:real^N->real^N->real^N->real`
    (CONJUNCTS_THEN2 (LABEL_TAC "A") (LABEL_TAC "B"))) THEN
  EXISTS_TAC `moi_fcb_osg (c:(real^N->bool)->bool) sg` THEN
  SUBGOAL_THEN
   `!a b d:real^N.
      convex hull {a,b,d} IN t /\ aff_dim(convex hull {a,b,d}) = &2
      ==> ~collinear {a,b,d} /\
          ?p q r. convex hull {p,q,r} IN c /\ ~collinear {p,q,r} /\
                  convex hull {a,b,d} SUBSET convex hull {p,q,r}`
  (LABEL_TAC "CAR") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [UNDISCH_TAC `aff_dim(convex hull {a:real^N,b,d}) = &2` THEN
      REWRITE_TAC[AFF_DIM_CONVEX_HULL; COLLINEAR_AFF_DIM] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "REF" (MP_TAC o C MP (ASSUME `convex hull {a:real^N,b,d} IN t`) o
      SPEC `convex hull {a:real^N,b,d}`) THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `aff_dim(k:real^N->bool) = &2` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM INT_LE_ANTISYM] THEN CONJ_TAC THENL
       [USE_THEN "DIM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `aff_dim(convex hull {a:real^N,b,d}) = &2` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC AFF_DIM_SUBSET THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `k:real^N->bool`] MOI_FCB_TRI_FRAME) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `q:real^N` (X_CHOOSE_THEN `r:real^N`
      STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`p:real^N`; `q:real^N`; `r:real^N`] THEN
    UNDISCH_TAC `(k:real^N->bool) IN c` THEN
    UNDISCH_TAC `convex hull {a,b,d} SUBSET (k:real^N->bool)` THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`; `d:real^N`] THEN DISCH_TAC THEN
    USE_THEN "CAR" (MP_TAC o C MP (ASSUME `convex hull {a:real^N,b,d} IN t /\
      aff_dim(convex hull {a:real^N,b,d}) = &2`) o SPECL [`a:real^N`; `b:real^N`; `d:real^N`]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `p:real^N`
      (X_CHOOSE_THEN `q:real^N` (X_CHOOSE_THEN `r:real^N` STRIP_ASSUME_TAC)))) THEN
    SUBGOAL_THEN `{b,a,d} = {a:real^N,b,d} /\ {a,d,b} = {a,b,d}` STRIP_ASSUME_TAC THENL
     [SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d:real^N`; `p:real^N`; `q:real^N`; `r:real^N`]
      MOI_FCB_IN_AFF) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `sg:real^N->real^N->real^N->real`;
                   `p:real^N`; `q:real^N`; `r:real^N`; `a:real^N`; `b:real^N`; `d:real^N`]
      MOI_FCB_OSG_EVAL) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `sg:real^N->real^N->real^N->real`;
                   `p:real^N`; `q:real^N`; `r:real^N`; `b:real^N`; `a:real^N`; `d:real^N`]
      MOI_FCB_OSG_EVAL) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `sg:real^N->real^N->real^N->real`;
                   `p:real^N`; `q:real^N`; `r:real^N`; `a:real^N`; `d:real^N`; `b:real^N`]
      MOI_FCB_OSG_EVAL) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
    MP_TAC(ISPECL [`p:real^N`; `q:real^N`; `r:real^N`; `a:real^N`; `b:real^N`; `d:real^N`]
      MOI_FCB_DET_ROWS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th; REAL_SGN_NEG]) THEN
    SUBGOAL_THEN
     `(sg p q r = &1 \/ sg p q r = -- &1) /\
      (real_sgn(moi_fcb_det p q r a b d) = &1 \/
       real_sgn(moi_fcb_det p q r a b (d:real^N)) = -- &1)`
    MP_TAC THENL
     [CONJ_TAC THENL
       [USE_THEN "A" (MP_TAC o SPECL [`p:real^N`; `q:real^N`; `r:real^N`]) THEN
        ASM_SIMP_TAC[MOI_FCB_TRI_FACTS] THEN SIMP_TAC[];
        MP_TAC(ISPEC `moi_fcb_det p q r a b (d:real^N)` REAL_SGN_CASES) THEN
        REWRITE_TAC[REAL_SGN_EQ] THEN
        MP_TAC(ISPECL [`p:real^N`; `q:real^N`; `r:real^N`; `a:real^N`; `b:real^N`;
                       `d:real^N`] MOI_FCB_DET_NZ) THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`; `d:real^N`; `d':real^N`] THEN STRIP_TAC THEN
  USE_THEN "CAR" (fun th -> MP_TAC(MP (SPECL [`a:real^N`; `b:real^N`; `d:real^N`] th)
    (CONJ (ASSUME `convex hull {a:real^N,b,d} IN t`)
          (ASSUME `aff_dim(convex hull {a:real^N,b,d}) = &2`)))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `p1:real^N`
    (X_CHOOSE_THEN `q1:real^N` (X_CHOOSE_THEN `r1:real^N` STRIP_ASSUME_TAC)))) THEN
  USE_THEN "CAR" (fun th -> MP_TAC(MP (SPECL [`a:real^N`; `b:real^N`; `d':real^N`] th)
    (CONJ (ASSUME `convex hull {a:real^N,b,d'} IN t`)
          (ASSUME `aff_dim(convex hull {a:real^N,b,d'}) = &2`)))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `p2:real^N`
    (X_CHOOSE_THEN `q2:real^N` (X_CHOOSE_THEN `r2:real^N` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN
   `(a:real^N) IN convex hull {a,b,d} /\ b IN convex hull {a,b,d} /\
    d IN convex hull {a,b,d} /\ a IN convex hull {a,b,d'} /\
    b IN convex hull {a,b,d'} /\ d' IN convex hull {a,b,d'}`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
  ASM_CASES_TAC `convex hull {p2,q2,r2} = convex hull {p1:real^N,q1,r1}` THENL
   [SUBGOAL_THEN `convex hull {a,b,d'} SUBSET convex hull {p1:real^N,q1,r1}` ASSUME_TAC THENL
     [UNDISCH_TAC `convex hull {a,b,d'} SUBSET convex hull {p2:real^N,q2,r2}` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `sg:real^N->real^N->real^N->real`;
                   `p1:real^N`; `q1:real^N`; `r1:real^N`; `a:real^N`; `b:real^N`; `d:real^N`]
      MOI_FCB_OSG_EVAL) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `sg:real^N->real^N->real^N->real`;
                   `p1:real^N`; `q1:real^N`; `r1:real^N`; `a:real^N`; `b:real^N`; `d':real^N`]
      MOI_FCB_OSG_EVAL) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `p1:real^N`; `q1:real^N`; `r1:real^N`;
                   `a:real^N`; `b:real^N`; `d:real^N`; `d':real^N`] MOI_FCB_OPP_SIDES) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP MOI_FM3_SGN_OPP) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(a:real^N = b)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d:real^N`] MOI_FCB_TRI_FACTS) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `p1:real^N`; `q1:real^N`; `r1:real^N`;
                 `p2:real^N`; `q2:real^N`; `r2:real^N`; `a:real^N`; `b:real^N`]
    MOI_FCB_EDGE_FRAMES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `y:real^N`
    (X_CHOOSE_THEN `z1:real^N` (X_CHOOSE_THEN `z2:real^N` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `sg:real^N->real^N->real^N->real`;
                 `x:real^N`; `y:real^N`; `z1:real^N`; `a:real^N`; `b:real^N`; `d:real^N`]
    MOI_FCB_OSG_EVAL) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `sg:real^N->real^N->real^N->real`;
                 `x:real^N`; `y:real^N`; `z2:real^N`; `a:real^N`; `b:real^N`; `d':real^N`]
    MOI_FCB_OSG_EVAL) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  SUBGOAL_THEN `(sg:real^N->real^N->real^N->real) x y z2 = --(sg x y z1)` SUBST1_TAC THENL
   [USE_THEN "B" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[MOI_FCB_TRI_FACTS];
    ALL_TAC] THEN
  UNDISCH_TAC `(a:real^N) IN convex hull {x,y}` THEN
  UNDISCH_TAC `(b:real^N) IN convex hull {x,y}` THEN
  REWRITE_TAC[CONVEX_HULL_2; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `u':real` (X_CHOOSE_THEN `v':real` STRIP_ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` (X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `a:real^N`)) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `b:real^N`)) THEN
  MP_TAC(ISPECL [`x:real^N`; `y:real^N`; `z1:real^N`; `a:real^N`; `b:real^N`; `d:real^N`;
                 `u:real`; `v:real`; `u':real`; `v':real`] MOI_FCB_EDGE_DET) THEN
  MP_TAC(ISPECL [`x:real^N`; `y:real^N`; `z2:real^N`; `a:real^N`; `b:real^N`; `d':real^N`;
                 `u:real`; `v:real`; `u':real`; `v':real`] MOI_FCB_EDGE_DET) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The two sides of a polygon in a closed combinatorial surface with         *)
(* orientation data near it (after MOI_FSTR_TWO_SIDED of                     *)
(* pc_moi_fnd_sptrace): the derived neighbourhood is the union of two closed *)
(* sets L and R meeting inside the polygon, each having the polygon in the   *)
(* closure of its part off the polygon.                                      *)
(* ========================================================================= *)

let MOI_FCB_TS_SPLIT = prove
 (`!(m:(real^N->bool)->bool) l (sg:real^N->real^N->real^N->real^N->real).
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l) /\
     (!w a b d. {w} IN barycentric_subdivision l /\
                convex hull {a,b,d} IN barycentric_subdivision m /\
                aff_dim(convex hull {a,b,d}) = &2 /\ w IN {a,b,d}
                ==> (sg w a b d = &1 \/ sg w a b d = -- &1) /\
                    sg w b a d = --(sg w a b d) /\ sg w a d b = --(sg w a b d)) /\
     (!w a b d d'. {w} IN barycentric_subdivision l /\ w IN {a,b} /\ ~(d = d') /\
                   convex hull {a,b,d} IN barycentric_subdivision m /\
                   aff_dim(convex hull {a,b,d}) = &2 /\
                   convex hull {a,b,d'} IN barycentric_subdivision m /\
                   aff_dim(convex hull {a,b,d'}) = &2
                   ==> sg w a b d' = --(sg w a b d)) /\
     (!v w x. segment[v,w] IN barycentric_subdivision l /\ ~(v = w) /\
              convex hull {v,w,x} IN barycentric_subdivision m /\
              aff_dim(convex hull {v,w,x}) = &2
              ==> sg w v w x = sg v v w x)
     ==> ?L R:real^N->bool.
           closed L /\ closed R /\ derived_nbhd m l = L UNION R /\
           L INTER R SUBSET UNIONS l /\
           UNIONS l SUBSET closure (L DIFF UNIONS l) /\
           UNIONS l SUBSET closure (R DIFF UNIONS l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_CONTEXT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPEC `barycentric_subdivision (l:(real^N->bool)->bool)` MOI_FN2_KCYC_EXISTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `Q:num->real^N` ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_NBHD_STARS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `n:num`;
                 `Q:num->real^N`] MOI_FN2_KSTARS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision (m:(real^N->bool)->bool)`;
                 `barycentric_subdivision (l:(real^N->bool)->bool)`;
                 `sg:real^N->real^N->real^N->real^N->real`; `n:num`; `Q:num->real^N`]
    MOI_FSTR_TS_LABELS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `LEFT:num->(real^N->bool)->bool`) THEN
  ABBREV_TAC `c = barycentric_subdivision (m:(real^N->bool)->bool)` THEN
  ABBREV_TAC `k = barycentric_subdivision (l:(real^N->bool)->bool)` THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rand(concl th) = `UNIONS (l:(real^N->bool)->bool)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_fn2_kcyc] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "moi_fn2_kcyc" with _ -> false)) THEN
  ABBREV_TAC
   `L = UNIONS {UNIONS (moi_fm3_cstar (barycentric_subdivision c) ((Q:num->real^N) i)) INTER
                UNIONS {t | t IN c /\ aff_dim t = &2 /\ Q i IN t /\
                            (LEFT:num->(real^N->bool)->bool) i t} | i | i < n}` THEN
  ABBREV_TAC
   `R = UNIONS {UNIONS (moi_fm3_cstar (barycentric_subdivision c) ((Q:num->real^N) i)) INTER
                UNIONS {t | t IN c /\ aff_dim t = &2 /\ Q i IN t /\
                            ~(LEFT:num->(real^N->bool)->bool) i t} | i | i < n}` THEN
  SUBGOAL_THEN `derived_nbhd m l = (L:real^N->bool) UNION R` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if is_eq(concl th) &&
       lhs(concl th) = `derived_nbhd (m:(real^N->bool)->bool) l`
     then SUBST1_TAC th else failwith "no") THEN
    MAP_EVERY EXPAND_TAC ["L"; "R"] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
    REWRITE_TAC[IN_UNION; IN_UNIONS; IN_ELIM_THM; IN_INTER] THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `s:real^N->bool`)) THEN
      FIRST_ASSUM(MP_TAC o SPEC `w:real^N` o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
        type_of(fst(dest_forall(concl th))) = `:real^N` &&
        is_exists(snd(dest_imp(snd(strip_forall(concl th))))))) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `w:real^N`)) THEN
      UNDISCH_TAC `(x:real^N) IN UNIONS (moi_fm3_cstar (barycentric_subdivision c) ((Q:num->real^N) i))` THEN
      REWRITE_TAC[IN_UNIONS] THEN
      DISCH_THEN(X_CHOOSE_THEN `s0:real^N->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `(Q:num->real^N) i`; `s0:real^N->bool`]
        MOI_FN2_CSTAR_IN_SIMPLEX) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `t0:real^N->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t0:real^N->bool`] MOI_FSA_CM_PURE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
      ASM_CASES_TAC `(LEFT:num->(real^N->bool)->bool) i t` THENL
       [DISJ1_TAC THEN
        EXISTS_TAC `UNIONS (moi_fm3_cstar (barycentric_subdivision c) ((Q:num->real^N) i)) INTER
                    UNIONS {t | t IN c /\ aff_dim t = &2 /\ Q i IN t /\
                                (LEFT:num->(real^N->bool)->bool) i t}`;
        DISJ2_TAC THEN
        EXISTS_TAC `UNIONS (moi_fm3_cstar (barycentric_subdivision c) ((Q:num->real^N) i)) INTER
                    UNIONS {t | t IN c /\ aff_dim t = &2 /\ Q i IN t /\
                                ~(LEFT:num->(real^N->bool)->bool) i t}`] THEN
      (CONJ_TAC THENL [EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
      REWRITE_TAC[IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
      (CONJ_TAC THENL [EXISTS_TAC `s0:real^N->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
      EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      STRIP_TAC THEN
      (EXISTS_TAC `UNIONS (moi_fm3_cstar (barycentric_subdivision c) ((Q:num->real^N) i))` THEN
       CONJ_TAC THENL
        [EXISTS_TAC `(Q:num->real^N) i` THEN ASM_REWRITE_TAC[];
         FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
           lhs(concl th) = `t:real^N->bool`)) THEN
         ASM SET_TAC[]])];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed(L:real^N->bool) /\ closed(R:real^N->bool)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_FSA_CM_SC]; ALL_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FSA_SC_FACTS) THEN
    SUBGOAL_THEN `(k:(real^N->bool)->bool) SUBSET c` ASSUME_TAC THENL
     [ASM_MESON_TAC[simplicial_subcomplex]; ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["L"; "R"] THEN CONJ_TAC THEN
    (MATCH_MP_TAC CLOSED_UNIONS THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC CLOSED_INTER THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FSTR_STAR_CLOSED THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        is_binary "SUBSET" (concl th) && lhand(concl th) = `k:(real^N->bool)->bool`)) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SET_TAC[]];
        REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
        MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
        FIRST_ASSUM(MP_TAC o SPEC `t:real^N->bool` o check (fun th ->
          is_forall(concl th) && can (find_term (fun tm ->
            try fst(dest_const tm) = "compact" with _ -> false)) (concl th))) THEN
        ASM_SIMP_TAC[]]]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!x. x IN L <=>
         ?i. i < n /\
             x IN UNIONS (moi_fm3_cstar (barycentric_subdivision c) ((Q:num->real^N) i)) /\
             ?t. (t IN c /\ aff_dim t = &2 /\ Q i IN t /\
                  (LEFT:num->(real^N->bool)->bool) i t) /\ x IN t) /\
    (!x. x IN R <=>
         ?i. i < n /\
             x IN UNIONS (moi_fm3_cstar (barycentric_subdivision c) ((Q:num->real^N) i)) /\
             ?t. (t IN c /\ aff_dim t = &2 /\ Q i IN t /\
                  ~(LEFT:num->(real^N->bool)->bool) i t) /\ x IN t)`
  (CONJUNCTS_THEN2 (LABEL_TAC "Lc") (LABEL_TAC "Rc")) THENL
   [MAP_EVERY EXPAND_TAC ["L"; "R"] THEN
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC; IN_INTER; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(L:real^N->bool) INTER R SUBSET UNIONS k` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^N` THEN
    USE_THEN "Lc" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "Rc" (fun th -> REWRITE_TAC[th]) THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `i:num` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC))))
      (X_CHOOSE_THEN `j:num` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `t':real^N->bool` STRIP_ASSUME_TAC))))) THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    ASM_CASES_TAC `i:num = j` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool) /\ {(Q:num->real^N) j} IN c`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL [ASM_MESON_TAC[MOI_FSA_CM_SC]; ALL_TAC] THEN
        SUBGOAL_THEN `(k:(real^N->bool)->bool) SUBSET c` MP_TAC THENL
         [ASM_MESON_TAC[simplicial_subcomplex]; ALL_TAC] THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `~(t:real^N->bool = t')` ASSUME_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `~(x:real^N = (Q:num->real^N) j)` ASSUME_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN
        UNDISCH_TAC `~((Q:num->real^N) j IN UNIONS k)` THEN REWRITE_TAC[IN_UNIONS] THEN
        EXISTS_TAC `{(Q:num->real^N) j}` THEN ASM_REWRITE_TAC[IN_SING];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`; `t':real^N->bool`;
                     `(Q:num->real^N) j`; `x:real^N`] MOI_FSTR_COMMON_EDGE) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC); ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `~((u:real^N) = Q(SUC j)) /\ ~(u = Q(j + n - 1))` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
        UNDISCH_TAC `~((x:real^N) IN UNIONS k)` THEN REWRITE_TAC[IN_UNIONS] THENL
         [EXISTS_TAC `segment[(Q:num->real^N) j,Q(SUC j)]` THEN ASM_REWRITE_TAC[];
          EXISTS_TAC `segment[(Q:num->real^N)(j + n - 1),Q(SUC(j + n - 1))]` THEN
          ASM_REWRITE_TAC[] THEN
          SUBGOAL_THEN `SUC(j + n - 1) = j + n` SUBST1_TAC THENL
           [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
          ONCE_REWRITE_TAC[SEGMENT_SYM] THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
        length(fst(strip_forall(concl th))) = 1 &&
        can (find_term ((=) `LEFT:num->(real^N->bool)->bool`)) (concl th) &&
        is_conj(snd(dest_imp(snd(strip_forall(concl th))))))) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPECL [`t:real^N->bool`; `t':real^N->bool`; `u:real^N`] o
        CONJUNCT1) THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `k:(real^N->bool)->bool`;
                     `sg:real^N->real^N->real^N->real^N->real`; `n:num`; `Q:num->real^N`;
                     `LEFT:num->(real^N->bool)->bool`; `i:num`; `j:num`; `x:real^N`;
                     `t:real^N->bool`; `t':real^N->bool`] MOI_FSTR_TS_CROSS) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
        GEN_TAC THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `i':num` o check (fun th -> is_forall(concl th) &&
          length(fst(strip_forall(concl th))) = 1 &&
          can (find_term ((=) `LEFT:num->(real^N->bool)->bool`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN SIMP_TAC[];
        STRIP_TAC THEN ASM_MESON_TAC[]]];
    ALL_TAC] THEN

  (* both sides accumulate on every edge of the polygon *)
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool) /\ (k:(real^N->bool)->bool) SUBSET c`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSA_CM_SC; simplicial_subcomplex]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t:real^N->bool. t IN c /\ aff_dim t = &2
                     ==> relative_interior t INTER UNIONS k = {}`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_UNIONS] THEN
    X_GEN_TAC `y:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(s:real^N->bool) IN c /\ aff_dim s <= &1` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`t INTER s:real^N->bool`; `t:real^N->bool`]
      FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
      DISCH_TAC THEN
      MP_TAC(ISPECL [`t:real^N->bool`; `s:real^N->bool`] AFF_DIM_SUBSET) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
      MP_TAC(ISPEC `t:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i t. i < n /\ t IN c /\ aff_dim t = &2 /\
          segment[(Q:num->real^N) i,Q(SUC i)] SUBSET t
          ==> segment[Q i,Q(SUC i)] SUBSET
              (if (LEFT:num->(real^N->bool)->bool) i t then closure (L DIFF UNIONS k)
               else closure (R DIFF UNIONS k))`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `t:real^N->bool`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~((Q:num->real^N) i = Q(SUC i))` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FN2_CYC_NEQ_SUC_ALL THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ABBREV_TAC `e = segment[(Q:num->real^N) i,Q(SUC i)]` THEN
    SUBGOAL_THEN `(e:real^N->bool) IN c /\ aff_dim e = &1 /\ {(Q:num->real^N) i} IN c /\
                  {Q(SUC i)} IN c`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [EXPAND_TAC "e" THEN ASM SET_TAC[];
        EXPAND_TAC "e" THEN ASM_REWRITE_TAC[AFF_DIM_SEGMENT];
        ASM SET_TAC[];
        ASM SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `?x0:real^N. t = convex hull {(Q:num->real^N) i,Q(SUC i),x0}`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`; `(Q:num->real^N) i`;
                     `(Q:num->real^N)(SUC i)`] MOI_FSTR_TRI_FORM) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN EXPAND_TAC "e" THEN
        MP_TAC(ISPECL [`(Q:num->real^N) i`; `(Q:num->real^N)(SUC i)`] ENDS_IN_SEGMENT) THEN
        ASM SET_TAC[];
        MESON_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `?j. j < n /\ (Q:num->real^N) j = Q(SUC i)` STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPEC `(Q:num->real^N)(SUC i)` o check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun tm -> try fst(dest_const tm) = "INSERT" with _ -> false))
            (concl th) &&
        length(fst(strip_forall(concl th))) = 1 &&
        is_exists(snd(dest_imp(snd(strip_forall(concl th))))))) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; MESON_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(LEFT:num->(real^N->bool)->bool) j t <=> LEFT i t`
    ASSUME_TAC THENL
     [FIRST_ASSUM(SUBST1_TAC o check (fun th ->
        concl th = `t = convex hull {(Q:num->real^N) i,Q(SUC i),x0}`)) THEN
      MATCH_MP_TAC MOI_FSTR_TS_CONSIST THEN
      MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `k:(real^N->bool)->bool`;
                            `sg:real^N->real^N->real^N->real^N->real`; `n:num`] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `t = convex hull {(Q:num->real^N) i,Q(SUC i),x0}` THEN
      DISCH_THEN(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `i':num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i':num` o check (fun th -> is_forall(concl th) &&
        length(fst(strip_forall(concl th))) = 1 &&
        can (find_term ((=) `LEFT:num->(real^N->bool)->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `simplex_barycentre t IN relative_interior (t:real^N->bool) /\ convex t /\
      simplex_barycentre e IN (e:real^N->bool) /\
      moi_bar_complex (c:(real^N->bool)->bool)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC SIMPLEX_BARYCENTRE_IN_RELATIVE_INTERIOR THEN
        EXISTS_TAC `&2:int` THEN
        CONJ_TAC THENL [ASM_MESON_TAC[MOI_FCB_SC_CONVEX; AFF_DIM_SIMPLEX]; ALL_TAC] THEN
        DISCH_THEN SUBST_ALL_TAC THEN
        UNDISCH_TAC `aff_dim ({}:real^N->bool) = &2` THEN REWRITE_TAC[AFF_DIM_EMPTY] THEN
        INT_ARITH_TAC;
        ASM_MESON_TAC[MOI_FCB_SC_CONVEX];
        MATCH_MP_TAC(SET_RULE `!s t x:A. x IN s /\ s SUBSET t ==> x IN t`) THEN
        EXISTS_TAC `relative_interior e:real^N->bool` THEN
        REWRITE_TAC[RELATIVE_INTERIOR_SUBSET] THEN
        MATCH_MP_TAC SIMPLEX_BARYCENTRE_IN_RELATIVE_INTERIOR THEN
        EXISTS_TAC `&1:int` THEN
        CONJ_TAC THENL [ASM_MESON_TAC[MOI_FCB_SC_CONVEX; AFF_DIM_SIMPLEX]; ALL_TAC] THEN
        DISCH_THEN SUBST_ALL_TAC THEN
        UNDISCH_TAC `aff_dim ({}:real^N->bool) = &1` THEN REWRITE_TAC[AFF_DIM_EMPTY] THEN
        INT_ARITH_TAC;
        ASM_MESON_TAC[]];
      ALL_TAC] THEN
    FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
      concl th = `t = convex hull {(Q:num->real^N) i,Q(SUC i),x0}`)) THEN
    (* the half-edges and their triangles of the barycentric subdivision *)
    SUBGOAL_THEN
     `!a. (a = (Q:num->real^N) i \/ a = Q(SUC i))
          ==> convex hull {a, simplex_barycentre e, simplex_barycentre t}
                IN barycentric_subdivision c /\
              a IN convex hull {a, simplex_barycentre e, simplex_barycentre t} /\
              convex hull {a, simplex_barycentre e, simplex_barycentre t} SUBSET t`
    ASSUME_TAC THENL
     [X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN `{a:real^N} IN c /\ {a} SUBSET e /\ (e:real^N->bool) SUBSET t /\ a IN t`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `a = (Q:num->real^N) i \/ a = Q(SUC i)` THEN
        EXPAND_TAC "e" THEN
        MP_TAC(ISPECL [`(Q:num->real^N) i`; `(Q:num->real^N)(SUC i)`] ENDS_IN_SEGMENT) THEN
        ASM SET_TAC[];
        ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[barycentric_subdivision; IN_ELIM_THM] THEN
        EXISTS_TAC `{{a:real^N}, e, t}` THEN
        REWRITE_TAC[IMAGE_CLAUSES; MOI_FRN_BARYCENTRE_SING] THEN
        REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; FINITE_INSERT; FINITE_EMPTY;
                    IN_INSERT; NOT_IN_EMPTY] THEN
        ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
         [REWRITE_TAC[DE_MORGAN_THM; NOT_EMPTY_INSERT] THEN
          CONJ_TAC THEN DISCH_THEN(ASSUME_TAC o SYM) THENL
           [UNDISCH_TAC `aff_dim (e:real^N->bool) = &1`;
            UNDISCH_TAC `aff_dim (t:real^N->bool) = &2`] THEN
          ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
          REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN ASM SET_TAC[]];
        MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
        MATCH_MP_TAC HULL_MINIMAL THEN ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
        REPEAT CONJ_TAC THENL
         [ASM SET_TAC[];
          MP_TAC(ISPEC `t:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN ASM SET_TAC[]]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!a y. (a = (Q:num->real^N) i \/ a = Q(SUC i)) /\
            y IN convex hull {a, simplex_barycentre e, simplex_barycentre t}
            ==> y IN (if (LEFT:num->(real^N->bool)->bool) i t then L else R)`
    ASSUME_TAC THENL
     [MAP_EVERY X_GEN_TAC [`a:real^N`; `y:real^N`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `a:real^N` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun tm -> try fst(dest_const tm) = "barycentric_subdivision"
                                  with _ -> false)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN `?j0. j0 < n /\ (Q:num->real^N) j0 = a /\
                         ((LEFT:num->(real^N->bool)->bool) j0 t <=> LEFT i t)`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `a = (Q:num->real^N) i \/ a = Q(SUC i)` THEN STRIP_TAC THENL
         [EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[];
          EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `y IN UNIONS (moi_fm3_cstar (barycentric_subdivision c) ((Q:num->real^N) j0))`
      ASSUME_TAC THENL
       [REWRITE_TAC[IN_UNIONS; moi_fm3_cstar; IN_ELIM_THM] THEN
        EXISTS_TAC `convex hull {a:real^N, simplex_barycentre e, simplex_barycentre t}` THEN
        ASM_REWRITE_TAC[] THEN
        EXISTS_TAC `convex hull {a:real^N, simplex_barycentre e, simplex_barycentre t}` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FACE_OF_REFL THEN
        REWRITE_TAC[CONVEX_CONVEX_HULL];
        ALL_TAC] THEN
      SUBGOAL_THEN `(y:real^N) IN t` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_CASES_TAC `(LEFT:num->(real^N->bool)->bool) i t` THEN ASM_REWRITE_TAC[] THENL
       [USE_THEN "Lc" (fun th -> REWRITE_TAC[th]);
        USE_THEN "Rc" (fun th -> REWRITE_TAC[th])] THEN
      EXISTS_TAC `j0:num` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `a IN convex hull {a:real^N, simplex_barycentre e, simplex_barycentre t}` THEN
      UNDISCH_TAC `convex hull {a:real^N, simplex_barycentre e, simplex_barycentre t}
                   SUBSET t` THEN
      UNDISCH_TAC `(Q:num->real^N) j0 = a` THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `?a. (a = (Q:num->real^N) i \/ a = Q(SUC i)) /\
          x IN convex hull {a, simplex_barycentre e, simplex_barycentre t}`
    (X_CHOOSE_THEN `a:real^N` (CONJUNCTS_THEN ASSUME_TAC)) THENL
     [MP_TAC(ISPECL [`(Q:num->real^N) i`; `simplex_barycentre (e:real^N->bool)`;
                     `(Q:num->real^N)(SUC i)`] UNION_SEGMENT) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SYM) THEN
      FIRST_X_ASSUM(fun th -> if concl th = `segment[(Q:num->real^N) i,Q(SUC i)] = e`
                              then REWRITE_TAC[th] else failwith "no") THEN
      DISCH_THEN(fun th -> MP_TAC(ONCE_REWRITE_RULE[th] (ASSUME `(x:real^N) IN e`))) THEN
      REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
       [EXISTS_TAC `(Q:num->real^N) i` THEN REWRITE_TAC[];
        EXISTS_TAC `(Q:num->real^N)(SUC i)` THEN REWRITE_TAC[]] THEN
      MATCH_MP_TAC(SET_RULE `!s t x:A. x IN s /\ s SUBSET t ==> x IN t`) THEN
      FIRST_ASSUM(fun th -> EXISTS_TAC (rand(concl th))) THEN
      ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(x:real^N = simplex_barycentre t)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `(x:real^N) IN UNIONS k` ASSUME_TAC THENL
       [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          concl th = `segment[(Q:num->real^N) i,Q(SUC i)] = e`)) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `!t:real^N->bool. t IN c /\ aff_dim t = &2
                                    ==> relative_interior t INTER UNIONS k = {}` THEN
      DISCH_THEN(MP_TAC o SPEC `t:real^N->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `simplex_barycentre t IN relative_interior (t:real^N->bool)` THEN
      UNDISCH_TAC `(x:real^N) IN UNIONS k` THEN UNDISCH_TAC `x:real^N = simplex_barycentre t` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `segment(simplex_barycentre t,x) SUBSET
      (if (LEFT:num->(real^N->bool)->bool) i t then L else R) DIFF UNIONS k`
    ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_DIFF] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term (fun tm -> try fst(dest_const tm) = "COND" with _ -> false))
              (concl th) &&
          length(fst(strip_forall(concl th))) = 2)) THEN
        EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(SET_RULE `!s t x:A. x IN s /\ s SUBSET t ==> x IN t`) THEN
        EXISTS_TAC `segment(simplex_barycentre t,x:real^N)` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `segment[simplex_barycentre t,x:real^N]` THEN
        REWRITE_TAC[SEGMENT_OPEN_SUBSET_CLOSED; SEGMENT_CONVEX_HULL] THEN
        MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
        ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
        MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
        MP_TAC(ISPECL [`t:real^N->bool`; `simplex_barycentre (t:real^N->bool)`; `x:real^N`]
          IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(SET_RULE `!s t x:A. x IN s /\ s SUBSET t ==> x IN t`) THEN
          EXISTS_TAC `t:real^N->bool` THEN REWRITE_TAC[CLOSURE_SUBSET] THEN
          ASM SET_TAC[];
          ALL_TAC] THEN
        DISCH_TAC THEN
        UNDISCH_TAC `!t:real^N->bool. t IN c /\ aff_dim t = &2
                                      ==> relative_interior t INTER UNIONS k = {}` THEN
        DISCH_THEN(MP_TAC o SPEC `t:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(y:real^N) IN segment(simplex_barycentre t,x)` THEN
        UNDISCH_TAC `segment(simplex_barycentre t,x) SUBSET relative_interior (t:real^N->bool)` THEN
        SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^N) IN closure (segment(simplex_barycentre t,x))` MP_TAC THENL
     [ASM_REWRITE_TAC[CLOSURE_SEGMENT; ENDS_IN_SEGMENT]; ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `!s t x:A. s SUBSET t ==> x IN s ==> x IN t`) THEN
    COND_CASES_TAC THEN MATCH_MP_TAC SUBSET_CLOSURE THEN
    UNDISCH_TAC `segment(simplex_barycentre t,x) SUBSET
                 (if (LEFT:num->(real^N->bool)->bool) i t then L else R) DIFF UNIONS k` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`L:real^N->bool`; `R:real^N->bool`] THEN
  REPEAT(CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) THEN
  (* every point of the polygon: an edge, its two triangles, one on each side *)
  SUBGOAL_THEN
   `!x:real^N. x IN UNIONS k ==> x IN closure (L DIFF UNIONS k) /\ x IN closure (R DIFF UNIONS k)`
  (fun th -> REWRITE_TAC[SUBSET] THEN MESON_TAC[th]) THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?i. i < n /\ x IN segment[(Q:num->real^N) i,Q(SUC i)]` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN UNIONS k` THEN
    FIRST_ASSUM(fun th -> if is_eq(concl th) &&
        lhs(concl th) = `UNIONS (k:(real^N->bool)->bool)` &&
        can (find_term (fun tm -> try fst(dest_const tm) = "closed_segment" with _ -> false))
            (rhs(concl th))
      then REWRITE_TAC[th] else failwith "no") THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((Q:num->real^N) i = Q(SUC i))` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FN2_CYC_NEQ_SUC_ALL THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[(Q:num->real^N) i,Q(SUC i)] IN c /\
                aff_dim (segment[(Q:num->real^N) i,Q(SUC i)]) = &1`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `segment[(Q:num->real^N) i,Q(SUC i)]`]
    MOI_FN2_DUAL_EDGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real^N->bool` (X_CHOOSE_THEN `t2:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `t1 IN c /\ aff_dim t1 = &2 /\ segment[(Q:num->real^N) i,Q(SUC i)] SUBSET t1 /\
                t2 IN c /\ aff_dim t2 = &2 /\ segment[(Q:num->real^N) i,Q(SUC i)] SUBSET t2`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `{t1:real^N->bool,t2}`)) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((LEFT:num->(real^N->bool)->bool) i t1 <=> ~LEFT i t2)` ASSUME_TAC THENL
   [SUBGOAL_THEN `{(Q:num->real^N) i} IN c /\ {Q(SUC i)} IN c /\
                  Q i IN segment[Q i,Q(SUC i)] /\ Q(SUC i) IN segment[Q i,Q(SUC i)]`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[ENDS_IN_SEGMENT] THEN ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t1:real^N->bool`; `(Q:num->real^N) i`;
                   `(Q:num->real^N)(SUC i)`] MOI_FSTR_TRI_FORM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x1:real^N`
      (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t2:real^N->bool`; `(Q:num->real^N) i`;
                   `(Q:num->real^N)(SUC i)`] MOI_FSTR_TRI_FORM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x2:real^N`
      (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `~(x1:real^N = x2)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `~(t1:real^N->bool = t2)` THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 1 &&
      can (find_term ((=) `LEFT:num->(real^N->bool)->bool`)) (concl th) &&
      is_conj(snd(dest_imp(snd(strip_forall(concl th))))))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2)] THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `x1:real^N` th) THEN MP_TAC(SPEC `x2:real^N` th)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN
     `(sg:real^N->real^N->real^N->real^N->real) (Q i) (Q i) (Q(SUC i)) x2 =
      --(sg (Q i) (Q i) (Q(SUC i)) x1) /\
      (sg (Q i) (Q i) (Q(SUC i)) x1 = &1 \/ sg (Q i) (Q i) (Q(SUC i)) x1 = -- &1)`
    (CONJUNCTS_THEN ASSUME_TAC) THENL
     [CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          length(fst(strip_forall(concl th))) = 5)) THEN
        ASM_REWRITE_TAC[IN_INSERT];
        FIRST_X_ASSUM(MP_TAC o SPECL [`(Q:num->real^N) i`; `(Q:num->real^N) i`;
                                      `(Q:num->real^N)(SUC i)`; `x1:real^N`] o
          check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 4)) THEN
        ASM_REWRITE_TAC[IN_INSERT] THEN SIMP_TAC[]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (fun th ->
      is_disj(concl th) && can (find_term ((=) `x1:real^N`)) (concl th))) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
      can (find_term (fun tm -> try fst(dest_const tm) = "COND" with _ -> false)) (concl th)
    then MP_TAC(SPECL [`i:num`; `t1:real^N->bool`] th) THEN
         MP_TAC(SPECL [`i:num`; `t2:real^N->bool`] th)
    else failwith "no") THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(LEFT:num->(real^N->bool)->bool) i t2` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(x:real^N) IN segment[(Q:num->real^N) i,Q(SUC i)]` THEN SET_TAC[]);;

(* ========================================================================= *)
(* Orientation signs near the lifted interior.  Iterated barycentric         *)
(* subdivisions refine; the lifted complex is a simplicial complex,          *)
(* orientable with c; simplices of a refinement of the cap meeting the       *)
(* lifted interior lie in the lifted surface, so ORIENT_REFINE gives signs   *)
(* on the triangles there.                                                   *)
(* ========================================================================= *)


(* Iterated barycentric subdivisions refine the complex.                      *)

let MOI_FCB_ITER_REFINES = prove
 (`!(c:(real^N->bool)->bool) n s.
     lf_simplicial_complex c /\ s IN ITER n barycentric_subdivision c /\ ~(s = {})
     ==> ?t. t IN c /\ s SUBSET t`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[ITER] THENL
   [MESON_TAC[SUBSET_REFL]; ALL_TAC] THEN
  X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `c:(real^N->bool)->bool`; `n:num`]
    MOI_FDN_ITER_SUBCOMPLEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[simplicial_subcomplex; SUBSET_REFL] THEN
    ASM_MESON_TAC[MOI_FM3_LF_FACE];
    STRIP_TAC] THEN
  MP_TAC(ISPEC `ITER n barycentric_subdivision (c:(real^N->bool)->bool)`
    BARYCENTRIC_SUBDIVISION_REFINES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC[]);;

(* The lifted complex is a simplicial complex, orientable if c is.            *)

let MOI_FCB_LIFT_SC = prove
 (`!(c:(real^N->bool)->bool).
     simplicial_complex c
     ==> simplicial_complex
           (IMAGE (IMAGE moi_fcb_lift) c:(real^(N,2)finite_sum->bool)->bool)`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[simplicial_complex] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE THEN ASM_MESON_TAC[simplicial_complex];
    X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FCB_SC_CONVEX) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `n:int` o CONJUNCT2) THEN
    EXISTS_TAC `n:int` THEN ASM_SIMP_TAC[SIMPLEX_LINEAR_IMAGE_EQ; MOI_FCB_LIFT];
    X_GEN_TAC `f:real^(N,2)finite_sum->bool` THEN X_GEN_TAC `s:real^N->bool` THEN
    DISCH_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC o
      MATCH_MP MOI_FCB_LIFT_FACES) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_MESON_TAC[MOI_FCB_SC_FACES];
    X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN X_GEN_TAC `s':real^N->bool` THEN
    DISCH_TAC THEN REWRITE_TAC[MOI_FCB_LIFT_INTER] THEN
    CONJ_TAC THEN MATCH_MP_TAC MOI_FCB_LIFT_FACE_OF THEN
    ASM_MESON_TAC[simplicial_complex]]);;

let MOI_FCB_LIFT_ORIENT = prove
 (`!(c:(real^N->bool)->bool).
     orientable_surface_complex c
     ==> orientable_surface_complex
           (IMAGE (IMAGE moi_fcb_lift) c:(real^(N,2)finite_sum->bool)->bool)`,
  GEN_TAC THEN REWRITE_TAC[orientable_surface_complex] THEN
  DISCH_THEN(X_CHOOSE_THEN `sg:real^N->real^N->real^N->real`
    (CONJUNCTS_THEN2 (LABEL_TAC "A") (LABEL_TAC "B"))) THEN
  EXISTS_TAC `\(a:real^(N,2)finite_sum) (b:real^(N,2)finite_sum) (d:real^(N,2)finite_sum).
                (sg:real^N->real^N->real^N->real) (fstcart a) (fstcart b) (fstcart d)` THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!a b d:real^(N,2)finite_sum.
       convex hull {a,b,d} IN IMAGE (IMAGE moi_fcb_lift) c
       ==> convex hull {fstcart a,fstcart b,fstcart d} IN c /\
           aff_dim (convex hull {fstcart a,fstcart b,fstcart d}) =
           aff_dim (convex hull {a,b,d}) /\
           moi_fcb_lift (fstcart d) = d`
  (LABEL_TAC "T") THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `convex hull {fstcart(a:real^(N,2)finite_sum),fstcart(b:real^(N,2)finite_sum),
                               fstcart(d:real^(N,2)finite_sum)} = (s:real^N->bool)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `convex hull (IMAGE fstcart {a,b,d:real^(N,2)finite_sum})` THEN
      CONJ_TAC THENL [REWRITE_TAC[IMAGE_CLAUSES]; ALL_TAC] THEN
      SIMP_TAC[CONVEX_HULL_LINEAR_IMAGE; LINEAR_FSTCART] THEN
      ASM_REWRITE_TAC[GSYM IMAGE_o; o_DEF; MOI_FCB_LIFT; IMAGE_ID];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC AFF_DIM_INJECTIVE_LINEAR_IMAGE THEN
      REWRITE_TAC[MOI_FCB_LIFT];
      ALL_TAC] THEN
    SUBGOAL_THEN `(d:real^(N,2)finite_sum) IN IMAGE moi_fcb_lift (s:real^N->bool)` MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC HULL_INC THEN
      REWRITE_TAC[IN_INSERT];
      REWRITE_TAC[IN_IMAGE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[MOI_FCB_LIFT]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "T" (MP_TAC o SPECL [`a:real^(N,2)finite_sum`; `b:real^(N,2)finite_sum`;
                                  `d:real^(N,2)finite_sum`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "A" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "T" (MP_TAC o SPECL [`a:real^(N,2)finite_sum`; `b:real^(N,2)finite_sum`;
                                  `d:real^(N,2)finite_sum`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "T" (MP_TAC o SPECL [`a:real^(N,2)finite_sum`; `b:real^(N,2)finite_sum`;
                                  `d':real^(N,2)finite_sum`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "B" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* A simplex of the cap meeting the lifted interior lies in the lifted       *)
(* surface.                                                                   *)

let MOI_FCB_MEET_INTERIOR = prove
 (`!(c:(real^N->bool)->bool) ix k z.
     simplicial_complex c /\ k IN moi_fcb_cap c ix /\ z IN k /\
     z IN IMAGE moi_fcb_lift (UNIONS c DIFF surface_boundary c)
     ==> k SUBSET IMAGE moi_fcb_lift (UNIONS c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOI_FCB_CAP_IN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (DISJ_CASES_THEN2 (X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC)
       (X_CHOOSE_THEN `P:real^N->bool` (X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC)))
    STRIP_ASSUME_TAC)) THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    MATCH_MP_TAC(SET_RULE `!x:A->bool u. x IN u ==> x SUBSET UNIONS u`) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC(TAUT `F ==> p`) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `r:real^N->bool`] MOI_FCB_SC_CONVEX) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`(ix:(real^N->bool)->num) P`; `r:real^N->bool`;
                   `UNIONS c:real^N->bool`] MOI_FCB_CONE_INTER_FLAT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `P SUBSET surface_boundary (c:(real^N->bool)->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
    UNDISCH_TAC `(z:real^(N,2)finite_sum) IN
                 IMAGE moi_fcb_lift (UNIONS c DIFF surface_boundary c)` THEN
    REWRITE_TAC[IN_IMAGE; IN_DIFF] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(z:real^(N,2)finite_sum) IN
                  convex hull (moi_fcb_apex ((ix:(real^N->bool)->num) P) INSERT
                               IMAGE moi_fcb_lift r) INTER IMAGE moi_fcb_lift (UNIONS c)`
    MP_TAC THENL
     [REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[];
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
      ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[IN_IMAGE; MOI_FCB_LIFT; IN_INTER] THEN ASM SET_TAC[]]);;

(* Orientation signs on the simplices of a refinement of the cap that meet  *)
(* a set X in the lifted interior of the surface.                           *)

let MOI_FCB_LIFT_SIGNS = prove
 (`!(c:(real^N->bool)->bool) ix (t:(real^(N,2)finite_sum->bool)->bool) X.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\ orientable_surface_complex c /\
     simplicial_complex t /\
     (!s. s IN t /\ ~(s = {}) ==> ?k. k IN moi_fcb_cap c ix /\ s SUBSET k) /\
     X SUBSET IMAGE moi_fcb_lift (UNIONS c DIFF surface_boundary c)
     ==> ?sg:real^(N,2)finite_sum->real^(N,2)finite_sum->real^(N,2)finite_sum->real.
           (!a b d. convex hull {a,b,d} IN t /\ aff_dim (convex hull {a,b,d}) = &2 /\
                    ~(convex hull {a,b,d} INTER X = {})
                    ==> (sg a b d = &1 \/ sg a b d = -- &1) /\
                        sg b a d = --(sg a b d) /\ sg a d b = --(sg a b d)) /\
           (!a b d d'. ~(d = d') /\ ~(convex hull {a,b} INTER X = {}) /\
                       convex hull {a,b,d} IN t /\ aff_dim(convex hull {a,b,d}) = &2 /\
                       convex hull {a,b,d'} IN t /\ aff_dim(convex hull {a,b,d'}) = &2
                       ==> sg a b d' = --(sg a b d))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "REF") ASSUME_TAC))))) THEN
  ASM_CASES_TAC `c:(real^N->bool)->bool = {}` THENL
   [SUBGOAL_THEN `X:real^(N,2)finite_sum->bool = {}` SUBST1_TAC THENL
     [UNDISCH_TAC `X SUBSET IMAGE moi_fcb_lift (UNIONS (c:(real^N->bool)->bool) DIFF
                                               surface_boundary c)` THEN
      ASM_REWRITE_TAC[UNIONS_0; EMPTY_DIFF; IMAGE_CLAUSES; SUBSET_EMPTY];
      REWRITE_TAC[INTER_EMPTY]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `ix:(real^N->bool)->num`]
    MOI_FCB_CAP_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `({}:real^N->bool) IN c` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY] o
      check (fun th -> concl th = `~(c:(real^N->bool)->bool = {})`)) THEN
    DISCH_THEN(X_CHOOSE_TAC `s0:real^N->bool`) THEN
    ASM_MESON_TAC[MOI_FCB_SC_FACES; EMPTY_FACE_OF];
    ALL_TAC] THEN
  (* simplices of t meeting X lie in the lifted surface *)
  SUBGOAL_THEN
   `!s. s IN t /\ ~(s INTER X = {})
        ==> s SUBSET IMAGE moi_fcb_lift (UNIONS (c:(real^N->bool)->bool))`
  (LABEL_TAC "MEET") THENL
   [X_GEN_TAC `s:real^(N,2)finite_sum->bool` THEN STRIP_TAC THEN
    USE_THEN "REF" (MP_TAC o SPEC `s:real^(N,2)finite_sum->bool`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^(N,2)finite_sum->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `~((s:real^(N,2)finite_sum->bool) INTER X = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^(N,2)finite_sum` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `k:real^(N,2)finite_sum->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FCB_MEET_INTERIOR THEN
    MAP_EVERY EXISTS_TAC [`ix:(real^N->bool)->num`; `z:real^(N,2)finite_sum`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `t' = {s | s IN t /\
                        s SUBSET IMAGE moi_fcb_lift (UNIONS (c:(real^N->bool)->bool))}` THEN
  SUBGOAL_THEN `orientable_surface_complex (t':(real^(N,2)finite_sum->bool)->bool)`
  MP_TAC THENL
   [MATCH_MP_TAC MOI_FCB_ORIENT_REFINE THEN
    EXISTS_TAC `IMAGE (IMAGE moi_fcb_lift) c:(real^(N,2)finite_sum->bool)->bool` THEN
    ASM_SIMP_TAC[MOI_FCB_LIFT_SC; MOI_FCB_LIFT_ORIENT] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN
      SIMP_TAC[AFF_DIM_INJECTIVE_LINEAR_IMAGE; MOI_FCB_LIFT] THEN
      ASM_MESON_TAC[MOI_FSB_DIM];
      UNDISCH_TAC `simplicial_complex (t:(real^(N,2)finite_sum->bool)->bool)` THEN
      EXPAND_TAC "t'" THEN REWRITE_TAC[simplicial_complex; IN_ELIM_THM] THEN
      STRIP_TAC THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
        ASM_MESON_TAC[];
        ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET_TRANS];
        ASM_MESON_TAC[]];
      EXPAND_TAC "t'" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `s:real^(N,2)finite_sum->bool` THEN STRIP_TAC THEN
      ASM_CASES_TAC `s:real^(N,2)finite_sum->bool = {}` THENL
       [EXISTS_TAC `{}:real^(N,2)finite_sum->bool` THEN
        ASM_REWRITE_TAC[EMPTY_SUBSET; IN_IMAGE] THEN
        EXISTS_TAC `{}:real^N->bool` THEN ASM_REWRITE_TAC[IMAGE_CLAUSES];
        ALL_TAC] THEN
      USE_THEN "REF" (MP_TAC o SPEC `s:real^(N,2)finite_sum->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `k:real^(N,2)finite_sum->bool` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `(k:real^(N,2)finite_sum->bool) IN moi_fcb_cap c ix` THEN
      REWRITE_TAC[MOI_FCB_CAP_IN] THEN
      DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC)
        (X_CHOOSE_THEN `P:real^N->bool` (X_CHOOSE_THEN `r:real^N->bool`
          STRIP_ASSUME_TAC))) THENL
       [EXISTS_TAC `k:real^(N,2)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      EXISTS_TAC `IMAGE moi_fcb_lift r:real^(N,2)finite_sum->bool` THEN
      CONJ_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `r:real^N->bool`] MOI_FCB_SC_CONVEX) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`(ix:(real^N->bool)->num) P`; `r:real^N->bool`;
                     `UNIONS c:real^N->bool`] MOI_FCB_CONE_INTER_FLAT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `r INTER UNIONS c = (r:real^N->bool)` ASSUME_TAC THENL
       [MATCH_MP_TAC(SET_RULE `!s u:A->bool. s SUBSET u ==> s INTER u = s`) THEN
        MATCH_MP_TAC(SET_RULE `!x:A->bool u. x IN u ==> x SUBSET UNIONS u`) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `(s:real^(N,2)finite_sum->bool) SUBSET k` THEN
      UNDISCH_TAC `s SUBSET IMAGE moi_fcb_lift (UNIONS (c:(real^N->bool)->bool))` THEN
      UNDISCH_TAC `convex hull (moi_fcb_apex ((ix:(real^N->bool)->num) P) INSERT
                                IMAGE moi_fcb_lift r) INTER IMAGE moi_fcb_lift (UNIONS c) =
                   IMAGE moi_fcb_lift (r INTER UNIONS c):real^(N,2)finite_sum->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[orientable_surface_complex] THEN
  DISCH_THEN(X_CHOOSE_THEN
    `sg:real^(N,2)finite_sum->real^(N,2)finite_sum->real^(N,2)finite_sum->real`
    (CONJUNCTS_THEN2 (LABEL_TAC "A") (LABEL_TAC "B"))) THEN
  EXISTS_TAC
    `sg:real^(N,2)finite_sum->real^(N,2)finite_sum->real^(N,2)finite_sum->real` THEN
  SUBGOAL_THEN
   `!s. s IN t /\ ~(s INTER X = {}) ==> (s:real^(N,2)finite_sum->bool) IN t'`
  (LABEL_TAC "INT") THENL
   [X_GEN_TAC `s:real^(N,2)finite_sum->bool` THEN STRIP_TAC THEN
    EXPAND_TAC "t'" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "MEET" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN USE_THEN "A" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "INT" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN USE_THEN "B" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN USE_THEN "INT" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(convex hull {a,b} INTER (X:real^(N,2)finite_sum->bool) = {})` THEN
    MATCH_MP_TAC(SET_RULE
     `!s t x:A->bool. s SUBSET t ==> ~(s INTER x = {}) ==> ~(t INTER x = {})`) THEN
    MATCH_MP_TAC HULL_MONO THEN SET_TAC[]]);;

(* ========================================================================= *)
(* The bicollar of a polygon in a closed surface with orientation signs near *)
(* it (TS_SPLIT, GEOM_SPLIT, SPLIT_COLLAR on both sides, glue).              *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The bicollar of a polygon in a closed combinatorial surface carrying      *)
(* orientation signs near the polygon: the derived neighbourhood is split    *)
(* by the two sides (TS_SPLIT), each side is an annulus with the polygon as  *)
(* one end (SPLIT_COLLAR), and the two collars are glued.                    *)
(* ------------------------------------------------------------------------- *)

let MOI_FCB_POLY_BICOLLAR = prove
 (mk_imp(MOI_FND_SURFACE_PLANAR,
  `!(m:(real^N->bool)->bool) l sg.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l) /\
     (!a b d. convex hull {a,b,d} IN barycentric_subdivision m /\
              aff_dim (convex hull {a,b,d}) = &2 /\
              ~(convex hull {a,b,d} INTER UNIONS l = {})
              ==> (sg a b d = &1 \/ sg a b d = -- &1) /\
                  sg b a d = --(sg a b d) /\ sg a d b = --(sg a b d)) /\
     (!a b d d'. ~(d = d') /\ ~(convex hull {a,b} INTER UNIONS l = {}) /\
                 convex hull {a,b,d} IN barycentric_subdivision m /\
                 aff_dim(convex hull {a,b,d}) = &2 /\
                 convex hull {a,b,d'} IN barycentric_subdivision m /\
                 aff_dim(convex hull {a,b,d'}) = &2
                 ==> sg a b d' = --(sg a b d))
     ==> ?p q. pl_homeomorphism (UNIONS l PCROSS interval[--vec 1:real^1,vec 1],
                                 derived_nbhd m l) (p,q) /\
               !x. x IN UNIONS l ==> p(pastecart x (vec 0)) = x`),
  DISCH_THEN(LABEL_TAC "PLANAR") THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "SG1") (LABEL_TAC "SG2")))))) THEN
  SUBGOAL_THEN `lf_simplicial_complex (m:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (l:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; FINITE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `lf_simplicial_complex (l:(real^N->bool)->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `lf_simplicial_complex (m:(real^N->bool)->bool)` THEN
    UNDISCH_TAC `simplicial_subcomplex (l:(real^N->bool)->bool) m` THEN
    UNDISCH_TAC `FINITE (l:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex; simplicial_subcomplex; SUBSET] THEN
    REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC[]; ASM_MESON_TAC[]; ASM_MESON_TAC[]; ASM_MESON_TAC[];
      EXISTS_TAC `(:real^N)` THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
      MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS (barycentric_subdivision l) = UNIONS (l:(real^N->bool)->bool)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[UNIONS_BARYCENTRIC_SUBDIVISION]; ALL_TAC] THEN
  (* the two sides *)
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `\w:real^N. (sg:real^N->real^N->real^N->real)`] MOI_FCB_TS_SPLIT) THEN
  BETA_TAC THEN REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
     [USE_THEN "SG1" MATCH_MP_TAC; USE_THEN "SG2" MATCH_MP_TAC] THEN
    ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `w:real^N` THEN CONJ_TAC THENL
     [MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(MESON[IN_UNIONS; IN_SING]
        `!x:A u v. {x} IN u /\ UNIONS u = v ==> x IN v`) THEN
      EXISTS_TAC `barycentric_subdivision l:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(MESON[IN_UNIONS; IN_SING]
        `!x:A u v. {x} IN u /\ UNIONS u = v ==> x IN v`) THEN
      EXISTS_TAC `barycentric_subdivision l:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real^N->bool` (X_CHOOSE_THEN `R:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `derived_nbhd (m:(real^N->bool)->bool) l`)) THEN
  SUBGOAL_THEN `closure (L DIFF UNIONS l) SUBSET (L:real^N->bool) /\
                closure (R DIFF UNIONS l) SUBSET (R:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(L:real^N->bool) INTER R = UNIONS l` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THEN ASM_MESON_TAC[SUBSET_TRANS]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] DERIVED_NBHD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the split of the derived neighbourhood *)
  MP_TAC(MATCH_MP MOI_FCB_GEOM_SPLIT (ASSUME MOI_FND_SURFACE_PLANAR)) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `L:real^N->bool`; `R:real^N->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_REFL] THEN
    UNDISCH_TAC `derived_nbhd m l SUBSET UNIONS (m:(real^N->bool)->bool)` THEN
    UNDISCH_TAC `(L:real^N->bool) UNION R = derived_nbhd m l` THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Z1 = derived_nbhd m l INTER L DIFF UNIONS (l:(real^N->bool)->bool)` THEN
  ABBREV_TAC `Z2 = derived_nbhd m l INTER R DIFF UNIONS (l:(real^N->bool)->bool)` THEN
  STRIP_TAC THEN
  (* the collars of the two sides *)
  MP_TAC(MATCH_MP MOI_FCB_SPLIT_COLLAR (ASSUME MOI_FND_SURFACE_PLANAR)) THEN
  DISCH_THEN(fun th ->
    MP_TAC(SPECL [`derived_nbhd_complex m (l:(real^N->bool)->bool)`;
                  `barycentric_subdivision (barycentric_subdivision
                     (l:(real^N->bool)->bool))`;
                  `Z1:real^N->bool`; `Z2:real^N->bool`] th) THEN
    MP_TAC(SPECL [`derived_nbhd_complex m (l:(real^N->bool)->bool)`;
                  `barycentric_subdivision (barycentric_subdivision
                     (l:(real^N->bool)->bool))`;
                  `Z2:real^N->bool`; `Z1:real^N->bool`] th)) THEN
  ASM_SIMP_TAC[MOI_FCB_SPLIT_SYM] THEN
  DISCH_THEN(X_CHOOSE_THEN `p2:real^(N,1)finite_sum->real^N`
    (X_CHOOSE_THEN `q2:real^N->real^(N,1)finite_sum` STRIP_ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `p1:real^(N,1)finite_sum->real^N`
    (X_CHOOSE_THEN `q1:real^N->real^(N,1)finite_sum` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `UNIONS l SUBSET closure (Z1:real^N->bool) /\
                UNIONS l SUBSET closure (Z2:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_fcb_split (derived_nbhd_complex m l)
                   (barycentric_subdivision (barycentric_subdivision l)) Z1
                   (Z2:real^N->bool)` THEN
    REWRITE_TAC[moi_fcb_split] THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closure Z1 SUBSET (L:real^N->bool) /\ closure Z2 SUBSET (R:real^N->bool) /\
                closure Z1 SUBSET derived_nbhd m l /\
                closure Z2 SUBSET derived_nbhd m (l:(real^N->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN MAP_EVERY EXPAND_TAC ["Z1"; "Z2"] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closure Z1 UNION closure Z2 = derived_nbhd m (l:(real^N->bool)->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[UNION_SUBSET] THEN
    MP_TAC(ISPEC `Z1:real^N->bool` CLOSURE_SUBSET) THEN
    MP_TAC(ISPEC `Z2:real^N->bool` CLOSURE_SUBSET) THEN
    MAP_EVERY UNDISCH_TAC
     [`UNIONS l SUBSET closure (Z1:real^N->bool)`;
      `derived_nbhd m l INTER L DIFF UNIONS (l:(real^N->bool)->bool) = Z1`;
      `derived_nbhd m l INTER R DIFF UNIONS (l:(real^N->bool)->bool) = Z2`;
      `(L:real^N->bool) UNION R = derived_nbhd m l`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* glue *)
  MP_TAC(ISPECL [`UNIONS l:real^N->bool`; `closure Z1:real^N->bool`;
                 `closure Z2:real^N->bool`;
                 `p1:real^(N,1)finite_sum->real^N`; `q1:real^N->real^(N,1)finite_sum`;
                 `p2:real^(N,1)finite_sum->real^N`; `q2:real^N->real^(N,1)finite_sum`]
    MOI_FBC_GLUE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `pl_polyhedron (UNIONS l:real^N->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_S4O_SPHERE_POLY]; ALL_TAC] THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON; PL_POLYHEDRON_IMP_COMPACT] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[SUBSET_INTER] THEN
    UNDISCH_TAC `(L:real^N->bool) INTER R = UNIONS l` THEN
    UNDISCH_TAC `closure Z1 SUBSET (L:real^N->bool)` THEN
    UNDISCH_TAC `closure Z2 SUBSET (R:real^N->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* One polygon of the interior: an open set of the cap missing the cones     *)
(* (UINT), the bicollar of the lifted polygon in the cap (CURVE_CAP),        *)
(* transported back by fstcart (CURVE_ONE).                                  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Open sets of the cap around a lifted subset of the interior that miss    *)
(* all the cones.                                                            *)
(* ------------------------------------------------------------------------- *)

let MOI_FCB_UINT = prove
 (`!(c:(real^N->bool)->bool) ix J u.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     open_in (subtopology euclidean (UNIONS c)) u /\ J SUBSET u /\
     DISJOINT J (surface_boundary c)
     ==> ?U. open_in (subtopology euclidean (UNIONS (moi_fcb_cap c ix))) U /\
             IMAGE moi_fcb_lift J SUBSET U /\
             U SUBSET IMAGE moi_fcb_lift (u DIFF surface_boundary c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `ix:(real^N->bool)->num`]
    MOI_FCB_CAP_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `u SUBSET UNIONS (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
  ABBREV_TAC `Tz = IMAGE moi_fcb_lift (UNIONS c DIFF u) UNION
                  UNIONS {moi_fcb_cone c ix Q | Q | Q IN components (surface_boundary c)}:
                  real^(N,2)finite_sum->bool` THEN
  SUBGOAL_THEN `closed (Tz:real^(N,2)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Tz" THEN MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_LINEAR_IMAGE THEN
      REWRITE_TAC[MOI_FCB_LIFT] THEN
      UNDISCH_TAC `open_in (subtopology euclidean (UNIONS c)) (u:real^N->bool)` THEN
      REWRITE_TAC[OPEN_IN_OPEN] THEN
      DISCH_THEN(X_CHOOSE_THEN `O:real^N->bool` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[SET_RULE `s DIFF (s INTER t) = s INTER ((:real^N) DIFF t)`] THEN
      MATCH_MP_TAC COMPACT_INTER_CLOSED THEN ASM_REWRITE_TAC[GSYM OPEN_CLOSED] THEN
      MATCH_MP_TAC COMPACT_UNIONS THEN
      CONJ_TAC THENL [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
      ASM_MESON_TAC[MOI_FCB_SC_CONVEX; SIMPLEX_IMP_COMPACT];
      MATCH_MP_TAC CLOSED_UNIONS THEN REWRITE_TAC[SIMPLE_IMAGE] THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
        MATCH_MP_TAC COMPACT_IMP_CLOSED THEN ASM_SIMP_TAC[MOI_FCB_CONE_COMPACT]]];
    ALL_TAC] THEN
  EXISTS_TAC `UNIONS (moi_fcb_cap c ix) DIFF Tz:real^(N,2)finite_sum->bool` THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `ix:(real^N->bool)->num`] MOI_FCB_CAP_UNIONS) THEN
  DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[OPEN_IN_OPEN] THEN
    EXISTS_TAC `(:real^(N,2)finite_sum) DIFF Tz` THEN
    ASM_REWRITE_TAC[GSYM closed] THEN SET_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF] THEN X_GEN_TAC `y:real^N` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN u /\ ~(y IN surface_boundary c)` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `moi_fcb_lift (y:real^N) IN IMAGE moi_fcb_lift (UNIONS c)` ASSUME_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[IN_UNION]; ALL_TAC] THEN
    EXPAND_TAC "Tz" THEN REWRITE_TAC[IN_UNION; DE_MORGAN_THM] THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_IMAGE; IN_DIFF] THEN ASM_MESON_TAC[MOI_FCB_LIFT];
      ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; NOT_EXISTS_THM] THEN
    X_GEN_TAC `t:real^(N,2)finite_sum->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `Q:real^N->bool` STRIP_ASSUME_TAC)
      ASSUME_TAC) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `ix:(real^N->bool)->num`; `Q:real^N->bool`]
      MOI_FCB_CONE_LIFT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `Q SUBSET surface_boundary (c:(real^N->bool)->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `moi_fcb_lift (y:real^N) IN IMAGE moi_fcb_lift Q` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; MOI_FCB_LIFT] THEN ASM SET_TAC[];
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "Tz" THEN
    REWRITE_TAC[SUBSET; IN_DIFF; IN_UNION; DE_MORGAN_THM] THEN
    X_GEN_TAC `z:real^(N,2)finite_sum` THEN STRIP_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[]] THEN
    UNDISCH_TAC `(z:real^(N,2)finite_sum) IN IMAGE moi_fcb_lift (UNIONS c)` THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL
     [UNDISCH_TAC `~((z:real^(N,2)finite_sum) IN IMAGE moi_fcb_lift (UNIONS c DIFF u))` THEN
      ASM_REWRITE_TAC[IN_IMAGE; IN_DIFF] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `?Q:real^N->bool. Q IN components (surface_boundary c) /\ y IN Q`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPEC `surface_boundary (c:(real^N->bool)->bool)` UNIONS_COMPONENTS) THEN
      UNDISCH_TAC `(y:real^N) IN surface_boundary c` THEN
      REWRITE_TAC[EXTENSION; IN_UNIONS] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^(N,2)finite_sum) IN
                  UNIONS {moi_fcb_cone c ix Q | Q | Q IN components (surface_boundary c)}`
    MP_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `moi_fcb_cone (c:(real^N->bool)->bool) ix Q` THEN CONJ_TAC THENL
     [EXISTS_TAC `Q:real^N->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `ix:(real^N->bool)->num`; `Q:real^N->bool`]
      MOI_FCB_CONE_LIFT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC(SET_RULE `!s t x:A. x IN s /\ s SUBSET t ==> x IN t`) THEN
    EXISTS_TAC `IMAGE moi_fcb_lift (Q:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The bicollar of a lifted polygon of the interior inside the cap.          *)
(* ------------------------------------------------------------------------- *)

let MOI_FCB_CURVE_CAP = prove
 (mk_imp(inst [`:(N,2)finite_sum`,`:N`] MOI_FND_SURFACE_PLANAR,
  `!(c:(real^N->bool)->bool) ix (lJ:(real^N->bool)->bool) U.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\ orientable_surface_complex c /\
     (!P Q. P IN components (surface_boundary c) /\
            Q IN components (surface_boundary c) /\ ix P = ix Q ==> P = Q) /\
     simplicial_subcomplex lJ c /\ pl_sphere 1 (UNIONS lJ) /\
     open_in (subtopology euclidean (UNIONS (moi_fcb_cap c ix))) U /\
     IMAGE moi_fcb_lift (UNIONS lJ) SUBSET U /\
     U SUBSET IMAGE moi_fcb_lift (UNIONS c DIFF surface_boundary c)
     ==> ?W (p:real^((N,2)finite_sum,1)finite_sum->real^(N,2)finite_sum) q.
           pl_homeomorphism (IMAGE moi_fcb_lift (UNIONS lJ) PCROSS
                             interval[--vec 1:real^1,vec 1],W) (p,q) /\
           (!x. x IN IMAGE moi_fcb_lift (UNIONS lJ) ==> p(pastecart x (vec 0)) = x) /\
           W SUBSET U /\ pl_polyhedron W /\
           (?O. open O /\ IMAGE moi_fcb_lift (UNIONS lJ) SUBSET O /\
                O INTER IMAGE moi_fcb_lift (UNIONS c) SUBSET W)`),
  DISCH_THEN(LABEL_TAC "PLANAR") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `ix:(real^N->bool)->num`]
    MOI_FCB_CAP_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `ix:(real^N->bool)->num`] MOI_FCB_CAP_CM2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_polyhedron (UNIONS (lJ:(real^N->bool)->bool))` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4O_SPHERE_POLY]; ALL_TAC] THEN
  SUBGOAL_THEN `pl_sphere 1 (IMAGE moi_fcb_lift (UNIONS lJ):real^(N,2)finite_sum->bool)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`moi_fcb_lift:real^N->real^(N,2)finite_sum`;
                   `UNIONS lJ:real^N->bool`; `1`] MOI_FM3_PL_LINEAR_IMAGE_EQ) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[MOI_FCB_LIFT]; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the lifted polygon as a subcomplex of the cap *)
  SUBGOAL_THEN
   `simplicial_subcomplex (IMAGE (IMAGE moi_fcb_lift) lJ)
                          (moi_fcb_cap (c:(real^N->bool)->bool) ix)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_subcomplex (lJ:(real^N->bool)->bool) c` THEN
    REWRITE_TAC[simplicial_subcomplex; SUBSET; IMP_CONJ; RIGHT_FORALL_IMP_THM;
                FORALL_IN_IMAGE; MOI_FCB_CAP_IN] THEN
    REPEAT DISCH_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[];
      X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
      X_GEN_TAC `f:real^(N,2)finite_sum->bool` THEN
      DISCH_THEN(X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC o
        MATCH_MP MOI_FCB_LIFT_FACES) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIONS (IMAGE (IMAGE moi_fcb_lift) lJ) =
    IMAGE moi_fcb_lift (UNIONS (lJ:(real^N->bool)->bool)):real^(N,2)finite_sum->bool`
  ASSUME_TAC THENL [REWRITE_TAC[IMAGE_UNIONS]; ALL_TAC] THEN
  (* fine subdivision inside U *)
  MP_TAC(ISPECL [`moi_fcb_cap (c:(real^N->bool)->bool) ix`;
                 `IMAGE (IMAGE moi_fcb_lift) (lJ:(real^N->bool)->bool):
                  (real^(N,2)finite_sum->bool)->bool`;
                 `U:real^(N,2)finite_sum->bool`] DERIVED_NBHD_SMALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_TAC `n:num`)] THEN
  MP_TAC(ISPECL [`moi_fcb_cap (c:(real^N->bool)->bool) ix`;
                 `IMAGE (IMAGE moi_fcb_lift) (lJ:(real^N->bool)->bool):
                  (real^(N,2)finite_sum->bool)->bool`; `n:num`]
    MOI_FDN_ITER_SUBCOMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`moi_fcb_cap (c:(real^N->bool)->bool) ix`; `n:num`] MOI_FBC_ITER_CM2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`moi_fcb_cap (c:(real^N->bool)->bool) ix`; `SUC n`] MOI_FBC_ITER_CM2) THEN
  ASM_REWRITE_TAC[ITER] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`moi_fcb_cap (c:(real^N->bool)->bool) ix`;
                 `IMAGE (IMAGE moi_fcb_lift) (lJ:(real^N->bool)->bool):
                  (real^(N,2)finite_sum->bool)->bool`; `SUC n`]
    MOI_FDN_ITER_SUBCOMPLEX) THEN
  ASM_REWRITE_TAC[ITER] THEN STRIP_TAC THEN
  ABBREV_TAC `m = ITER n barycentric_subdivision (moi_fcb_cap (c:(real^N->bool)->bool) ix)` THEN
  ABBREV_TAC `l = ITER n barycentric_subdivision
                    (IMAGE (IMAGE moi_fcb_lift) (lJ:(real^N->bool)->bool):
                     (real^(N,2)finite_sum->bool)->bool)` THEN
  (* orientation signs near the lifted polygon *)
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `ix:(real^N->bool)->num`;
                 `barycentric_subdivision m:(real^(N,2)finite_sum->bool)->bool`;
                 `IMAGE moi_fcb_lift (UNIONS lJ):real^(N,2)finite_sum->bool`]
    MOI_FCB_LIFT_SIGNS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `lf_simplicial_complex
                    (barycentric_subdivision m:(real^(N,2)finite_sum->bool)->bool)` THEN
      UNDISCH_TAC `FINITE (barycentric_subdivision m:(real^(N,2)finite_sum->bool)->bool)` THEN
      REWRITE_TAC[lf_simplicial_complex; simplicial_complex] THEN MESON_TAC[];
      X_GEN_TAC `s:real^(N,2)finite_sum->bool` THEN STRIP_TAC THEN
      MATCH_MP_TAC MOI_FCB_ITER_REFINES THEN EXISTS_TAC `SUC n` THEN
      ASM_REWRITE_TAC[ITER];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `U:real^(N,2)finite_sum->bool` THEN
      ASM_REWRITE_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN
      `sg:real^(N,2)finite_sum->real^(N,2)finite_sum->real^(N,2)finite_sum->real`
      STRIP_ASSUME_TAC)] THEN
  (* the bicollar in the cap *)
  MP_TAC(MATCH_MP (INST_TYPE [`:(N,2)finite_sum`,`:N`] MOI_FCB_POLY_BICOLLAR)
    (ASSUME (inst [`:(N,2)finite_sum`,`:N`] MOI_FND_SURFACE_PLANAR))) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`m:(real^(N,2)finite_sum->bool)->bool`; `l:(real^(N,2)finite_sum->bool)->bool`;
    `sg:real^(N,2)finite_sum->real^(N,2)finite_sum->real^(N,2)finite_sum->real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^((N,2)finite_sum,1)finite_sum->real^(N,2)finite_sum`
    (X_CHOOSE_THEN `q:real^(N,2)finite_sum->real^((N,2)finite_sum,1)finite_sum`
      STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `FINITE (l:(real^(N,2)finite_sum->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; FINITE_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`m:(real^(N,2)finite_sum->bool)->bool`;
                 `l:(real^(N,2)finite_sum->bool)->bool`] DERIVED_NBHD_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`UNIONS (moi_fcb_cap (c:(real^N->bool)->bool) ix)`;
                 `derived_nbhd m (l:(real^(N,2)finite_sum->bool)->bool)`;
                 `IMAGE moi_fcb_lift (UNIONS lJ):real^(N,2)finite_sum->bool`]
    MOI_FCB_INTERIOR_OPEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `O:real^(N,2)finite_sum->bool` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC
   [`derived_nbhd m (l:(real^(N,2)finite_sum->bool)->bool)`;
    `p:real^((N,2)finite_sum,1)finite_sum->real^(N,2)finite_sum`;
    `q:real^(N,2)finite_sum->real^((N,2)finite_sum,1)finite_sum`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[pl_polyhedron] THEN
    EXISTS_TAC `derived_nbhd_complex m (l:(real^(N,2)finite_sum->bool)->bool)` THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[lf_simplicial_complex; SIMPLEX_IMP_POLYTOPE];
    EXISTS_TAC `O:real^(N,2)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `ix:(real^N->bool)->num`]
      MOI_FCB_CAP_UNIONS) THEN
    UNDISCH_TAC `UNIONS (moi_fcb_cap (c:(real^N->bool)->bool) ix) INTER O SUBSET
                 derived_nbhd m (l:(real^(N,2)finite_sum->bool)->bool)` THEN
    SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The bicollar of one polygon of the interior, transported back from the    *)
(* cap by fstcart.                                                           *)
(* ------------------------------------------------------------------------- *)

let MOI_FCB_CURVE_ONE = prove
 (mk_imp(inst [`:(N,2)finite_sum`,`:N`] MOI_FND_SURFACE_PLANAR,
  `!(c:(real^N->bool)->bool) lJ u.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\ orientable_surface_complex c /\
     simplicial_subcomplex lJ c /\ pl_sphere 1 (UNIONS lJ) /\
     DISJOINT (UNIONS lJ) (surface_boundary c) /\
     open_in (subtopology euclidean (UNIONS c)) u /\ UNIONS lJ SUBSET u
     ==> ?w (p:real^(N,1)finite_sum->real^N) q.
           pl_homeomorphism (UNIONS lJ PCROSS interval[--vec 1:real^1,vec 1],w) (p,q) /\
           w SUBSET u /\ UNIONS lJ SUBSET (subtopology euclidean (UNIONS c)) interior_of w /\
           !x. x IN UNIONS lJ ==> p(pastecart x (vec 0)) = x`),
  DISCH_THEN(LABEL_TAC "PLANAR") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `(\P. 0):(real^N->bool)->num`]
    MOI_FCB_CAP_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `components (surface_boundary (c:(real^N->bool)->bool))`
    MOI_FCB_INDEX_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `ix:(real^N->bool)->num`) THEN
  SUBGOAL_THEN `u SUBSET UNIONS (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS lJ SUBSET UNIONS (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `ix:(real^N->bool)->num`;
                 `UNIONS lJ:real^N->bool`; `u:real^N->bool`] MOI_FCB_UINT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:real^(N,2)finite_sum->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(MATCH_MP MOI_FCB_CURVE_CAP
    (ASSUME (inst [`:(N,2)finite_sum`,`:N`] MOI_FND_SURFACE_PLANAR))) THEN
  DISCH_THEN(MP_TAC o SPECL [`c:(real^N->bool)->bool`; `ix:(real^N->bool)->num`;
                             `lJ:(real^N->bool)->bool`; `U:real^(N,2)finite_sum->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE moi_fcb_lift (u DIFF surface_boundary c):real^(N,2)finite_sum->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:real^(N,2)finite_sum->bool`
   (X_CHOOSE_THEN `p':real^((N,2)finite_sum,1)finite_sum->real^(N,2)finite_sum`
    (X_CHOOSE_THEN `q':real^(N,2)finite_sum->real^((N,2)finite_sum,1)finite_sum`
      STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `pl_polyhedron (UNIONS (lJ:(real^N->bool)->bool))` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4O_SPHERE_POLY]; ALL_TAC] THEN
  (* the lift as a PL homeomorphism onto its image *)
  SUBGOAL_THEN
   `pl_homeomorphism (UNIONS lJ,IMAGE moi_fcb_lift (UNIONS lJ))
                     (moi_fcb_lift:real^N->real^(N,2)finite_sum,fstcart)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN CONJ_TAC THENL
     [REWRITE_TAC[homeomorphism] THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; MOI_FCB_LIFT; FORALL_IN_IMAGE] THEN
      REWRITE_TAC[GSYM IMAGE_o; o_DEF; MOI_FCB_LIFT; IMAGE_ID];
      MP_TAC(ISPECL [`UNIONS lJ:real^N->bool`; `moi_fcb_lift:real^N->real^(N,2)finite_sum`;
                     `vec 0:real^(N,2)finite_sum`] PL_MAP_ON_AFFINE) THEN
      ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON; MOI_FCB_LIFT; VECTOR_ADD_RID; ETA_AX]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS lJ:real^N->bool`;
                 `IMAGE moi_fcb_lift (UNIONS lJ):real^(N,2)finite_sum->bool`;
                 `moi_fcb_lift:real^N->real^(N,2)finite_sum`;
                 `fstcart:real^(N,2)finite_sum->real^N`; `interval[--vec 1:real^1,vec 1]`]
    MOI_FCL_PLH_PCROSS_ID) THEN
  ASM_REWRITE_TAC[POLYTOPE_INTERVAL] THEN DISCH_TAC THEN
  (* fstcart on the bicollar *)
  SUBGOAL_THEN `W SUBSET IMAGE moi_fcb_lift (UNIONS (c:(real^N->bool)->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `U:real^(N,2)finite_sum->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE moi_fcb_lift (u DIFF surface_boundary c):real^(N,2)finite_sum->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_homeomorphism (W,IMAGE fstcart W)
                     (fstcart:real^(N,2)finite_sum->real^N,moi_fcb_lift)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN CONJ_TAC THENL
     [REWRITE_TAC[homeomorphism] THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; MOI_FCB_LIFT; FORALL_IN_IMAGE] THEN
      SUBGOAL_THEN `!z:real^(N,2)finite_sum. z IN W ==> moi_fcb_lift(fstcart z) = z`
      ASSUME_TAC THENL
       [X_GEN_TAC `z:real^(N,2)finite_sum` THEN DISCH_TAC THEN
        SUBGOAL_THEN `?y:real^N. z = moi_fcb_lift y` STRIP_ASSUME_TAC THENL
         [ASM SET_TAC[]; ASM_REWRITE_TAC[MOI_FCB_LIFT]];
        ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
      MATCH_MP_TAC(SET_RULE `(!x. x IN s ==> (k:A->A) x = x) ==> IMAGE k s = s`) THEN
      ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`W:real^(N,2)finite_sum->bool`; `fstcart:real^(N,2)finite_sum->real^N`;
                     `vec 0:real^N`] PL_MAP_ON_AFFINE) THEN
      ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON; LINEAR_FSTCART; VECTOR_ADD_RID;
                   ETA_AX]];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE fstcart (W:real^(N,2)finite_sum->bool)` THEN
  EXISTS_TAC `fstcart o ((p':real^((N,2)finite_sum,1)finite_sum->real^(N,2)finite_sum) o
              (\z:real^(N,1)finite_sum. pastecart (moi_fcb_lift (fstcart z)) (sndcart z)))` THEN
  EXISTS_TAC `((\z:real^((N,2)finite_sum,1)finite_sum. pastecart (fstcart (fstcart z)) (sndcart z)) o
               (q':real^(N,2)finite_sum->real^((N,2)finite_sum,1)finite_sum)) o moi_fcb_lift` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `W:real^(N,2)finite_sum->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `IMAGE moi_fcb_lift (UNIONS (lJ:(real^N->bool)->bool)) PCROSS
                interval[--vec 1:real^1,vec 1]` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE fstcart (IMAGE moi_fcb_lift (u:real^N->bool))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `U:real^(N,2)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE moi_fcb_lift (u DIFF surface_boundary c):real^(N,2)finite_sum->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
      REWRITE_TAC[GSYM IMAGE_o; o_DEF; MOI_FCB_LIFT; IMAGE_ID; SUBSET_REFL]];
    REWRITE_TAC[SUBSET; interior_of; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
    DISCH_TAC THEN
    EXISTS_TAC `UNIONS c INTER {y:real^N | moi_fcb_lift y IN O}` THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[OPEN_IN_OPEN] THEN EXISTS_TAC `{y:real^N | moi_fcb_lift y IN O}` THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
      ASM_SIMP_TAC[LINEAR_CONTINUOUS_AT; MOI_FCB_LIFT];
      REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN CONJ_TAC THENL
       [ASM SET_TAC[];
        UNDISCH_TAC `IMAGE moi_fcb_lift (UNIONS lJ) SUBSET (O:real^(N,2)finite_sum->bool)` THEN
        UNDISCH_TAC `(x:real^N) IN UNIONS lJ` THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
        MESON_TAC[]];
      REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; IN_IMAGE] THEN
      X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
      EXISTS_TAC `moi_fcb_lift (y:real^N)` THEN REWRITE_TAC[MOI_FCB_LIFT] THEN
      UNDISCH_TAC `O INTER IMAGE moi_fcb_lift (UNIONS (c:(real^N->bool)->bool)) SUBSET W` THEN
      REWRITE_TAC[SUBSET; IN_INTER; IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_MESON_TAC[]];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[o_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    SUBGOAL_THEN `moi_fcb_lift (x:real^N) IN IMAGE moi_fcb_lift (UNIONS lJ)` ASSUME_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[MOI_FCB_LIFT]]);;

(* ========================================================================= *)
(* The curve bicollar: refine c so that the curve is a union of simplices,   *)
(* bicollar each component (PL circle), glue; CURVE_BICOLLAR_ORIENTABLE.     *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The curve bicollar (with the planar-surface theorem at the cap's type as  *)
(* a hypothesis): refine c so that the curve is a subcomplex, take the       *)
(* bicollars of its components, and glue them.                               *)
(* ------------------------------------------------------------------------- *)

let MOI_FCB_CURVE_BICOLLAR_COND = prove
 (mk_imp(inst [`:(N,2)finite_sum`,`:N`] MOI_FND_SURFACE_PLANAR,
  `!(c:(real^N->bool)->bool) (l:(real^N->bool)->bool) v.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     orientable_surface_complex c /\
     FINITE l /\ combinatorial_manifold 1 l /\
     UNIONS l SUBSET UNIONS c DIFF surface_boundary c /\
     open_in (subtopology euclidean (UNIONS c)) v /\ UNIONS l SUBSET v
     ==> ?w (p:real^(N,1)finite_sum->real^N) q.
           pl_homeomorphism
             (UNIONS l PCROSS interval[--vec 1:real^1,vec 1],w) (p,q) /\
           w SUBSET v /\
           UNIONS l SUBSET (subtopology euclidean (UNIONS c)) interior_of w /\
           !x. x IN UNIONS l ==> p(pastecart x (vec 0)) = x`),
  DISCH_THEN(LABEL_TAC "PLANAR") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `(\P. 0):(real^N->bool)->num`]
      MOI_FCB_CAP_CONTEXT) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* the components of the curve are PL circles *)
  SUBGOAL_THEN
   `FINITE (components (UNIONS l:real^N->bool)) /\
    !J. J IN components (UNIONS l) ==> pl_sphere 1 (J:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `UNIONS l:real^N->bool = {}` THENL
     [ASM_REWRITE_TAC[COMPONENTS_EMPTY; FINITE_EMPTY; NOT_IN_EMPTY]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_S8CU_CM1_CIRCLES THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_TAC `x:real^N`) THEN
    SUBGOAL_THEN `?s:real^N->bool. s IN c /\ x IN s` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FSB_PURE) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPEC `r:real^N->bool` AFF_DIM_LE_UNIV) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[INT_OF_NUM_LE];
    ALL_TAC] THEN
  (* a common refinement of c in which the curve is a union of simplices *)
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    SIMPLICIAL_COMPLEX_REFINE_POLYTOPES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[combinatorial_manifold; lf_simplicial_complex; SIMPLEX_IMP_POLYTOPE];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(real^N->bool)->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "TC")
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "TL")))))) THEN
  SUBGOAL_THEN `FINITE (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:(real^N->bool)->bool`;
                 `\x:real^N. x`; `\x:real^N. x`] MOI_FBC_SURF_INVARIANT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[HOMEOMORPHISM_ID]; REWRITE_TAC[IMAGE_ID] THEN STRIP_TAC] THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `surface_boundary (c:(real^N->bool)->bool)`)) THEN
  SUBGOAL_THEN `orientable_surface_complex (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FCB_ORIENT_REFINE THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MOI_FSB_DIM];
    ALL_TAC] THEN
  (* separating neighbourhoods of the components *)
  SUBGOAL_THEN `!J. J IN components (UNIONS l) ==> compact (J:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4O_SPHERE_POLY; PL_POLYHEDRON_IMP_COMPACT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!C D. C IN components (UNIONS l) /\ D IN components (UNIONS l) /\
          ~(C = D) ==> DISJOINT (C:real^N->bool) D`
  ASSUME_TAC THENL [REWRITE_TAC[DISJOINT] THEN MESON_TAC[COMPONENTS_NONOVERLAP]; ALL_TAC] THEN
  MP_TAC(ISPEC `components (UNIONS l:real^N->bool)` MOI_FBC_SEPARATE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `O:(real^N->bool)->real^N->bool` STRIP_ASSUME_TAC) THEN
  (* the bicollar of each component *)
  SUBGOAL_THEN
   `!J. J IN components (UNIONS l)
        ==> ?w (p:real^(N,1)finite_sum->real^N) q.
              pl_homeomorphism (J PCROSS interval[--vec 1:real^1,vec 1],w) (p,q) /\
              w SUBSET v INTER O J /\
              J SUBSET (subtopology euclidean (UNIONS c)) interior_of w /\
              !x. x IN J ==> p(pastecart x (vec 0)) = x`
  MP_TAC THENL
   [X_GEN_TAC `J:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `J SUBSET UNIONS (l:(real^N->bool)->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `pl_sphere 1 (J:real^N->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ABBREV_TAC `lJ = {s:real^N->bool | s IN t /\ s SUBSET J}` THEN
    SUBGOAL_THEN `simplicial_subcomplex lJ (t:(real^N->bool)->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "lJ" THEN REWRITE_TAC[simplicial_subcomplex] THEN CONJ_TAC THENL
       [SET_TAC[];
        REWRITE_TAC[IN_ELIM_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
         [ASM_MESON_TAC[MOI_FCB_SC_FACES];
          ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET_TRANS]]];
      ALL_TAC] THEN
    SUBGOAL_THEN `UNIONS lJ = (J:real^N->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "lJ" THEN GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EQ_TAC THENL
       [MESON_TAC[SUBSET]; ALL_TAC] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `(x:real^N) IN UNIONS l` MP_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_UNIONS] THEN
      DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC) THEN
      USE_THEN "TL" (MP_TAC o SPEC `k:real^N->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `?s:real^N->bool. s IN f /\ x IN s` STRIP_ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC COMPONENTS_MAXIMAL THEN EXISTS_TAC `UNIONS l:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONVEX_CONNECTED THEN ASM_MESON_TAC[MOI_FCB_SC_CONVEX; SUBSET];
        ASM SET_TAC[];
        ASM SET_TAC[]];
      ALL_TAC] THEN
    MP_TAC(MATCH_MP MOI_FCB_CURVE_ONE
      (ASSUME (inst [`:(N,2)finite_sum`,`:N`] MOI_FND_SURFACE_PLANAR))) THEN
    DISCH_THEN(MP_TAC o SPECL [`t:(real^N->bool)->bool`; `lJ:(real^N->bool)->bool`;
                               `v INTER (O:(real^N->bool)->real^N->bool) J`]) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL [MATCH_MP_TAC OPEN_IN_INTER_OPEN THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[SUBSET_INTER] THEN ASM_SIMP_TAC[] THEN ASM SET_TAC[];
      DISCH_THEN ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `W:(real^N->bool)->real^N->bool`
   (X_CHOOSE_THEN `Pm:(real^N->bool)->real^(N,1)finite_sum->real^N`
    (X_CHOOSE_TAC `Qm:(real^N->bool)->real^N->real^(N,1)finite_sum`))) THEN
  MP_TAC(ISPECL [`W:(real^N->bool)->real^N->bool`;
                 `Pm:(real^N->bool)->real^(N,1)finite_sum->real^N`;
                 `Qm:(real^N->bool)->real^N->real^(N,1)finite_sum`;
                 `components (UNIONS l:real^N->bool)`] MOI_FBC_FAMILY_GLUE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`C:real^N->bool`; `D:real^N->bool`] THEN STRIP_TAC THEN
    TRY(CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
    SUBGOAL_THEN `(W:(real^N->bool)->real^N->bool) C SUBSET O C /\ W D SUBSET O D /\
                  DISJOINT ((O:(real^N->bool)->real^N->bool) C) (O D)`
    MP_TAC THENL [ASM_MESON_TAC[SUBSET_INTER]; SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^(N,1)finite_sum->real^N`
   (X_CHOOSE_THEN `q:real^N->real^(N,1)finite_sum` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `UNIONS (components (UNIONS l)) = UNIONS (l:(real^N->bool)->bool)`
  ASSUME_TAC THENL [REWRITE_TAC[GSYM UNIONS_COMPONENTS]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`UNIONS (IMAGE (W:(real^N->bool)->real^N->bool) (components (UNIONS l)))`;
    `p:real^(N,1)finite_sum->real^N`; `q:real^N->real^(N,1)finite_sum`] THEN
  UNDISCH_TAC
   `pl_homeomorphism
     (UNIONS (components (UNIONS l)) PCROSS interval[--vec 1:real^1,vec 1],
      UNIONS (IMAGE (W:(real^N->bool)->real^N->bool) (components (UNIONS l))))
     (p:real^(N,1)finite_sum->real^N,q)` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `C:real^N->bool` THEN
    DISCH_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `v INTER (O:(real^N->bool)->real^N->bool) C` THEN
    ASM_SIMP_TAC[] THEN SET_TAC[];
    GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?C:real^N->bool. C IN components (UNIONS l) /\ x IN C`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^N) IN UNIONS l` THEN
      UNDISCH_TAC `UNIONS (components (UNIONS l)) = UNIONS (l:(real^N->bool)->bool)` THEN
      REWRITE_TAC[EXTENSION; IN_UNIONS] THEN MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `!s t x:A. x IN s /\ s SUBSET t ==> x IN t`) THEN
    EXISTS_TAC `subtopology euclidean (UNIONS c) interior_of
                (W:(real^N->bool)->real^N->bool) C` THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC INTERIOR_OF_MONO THEN
    MATCH_MP_TAC(SET_RULE `!x:A->bool u. x IN u ==> x SUBSET UNIONS u`) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?C:real^N->bool. C IN components (UNIONS l) /\ x IN C`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^N) IN UNIONS l` THEN
      UNDISCH_TAC `UNIONS (components (UNIONS l)) = UNIONS (l:(real^N->bool)->bool)` THEN
      REWRITE_TAC[EXTENSION; IN_UNIONS] THEN MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `(Pm:(real^N->bool)->real^(N,1)finite_sum->real^N) C (pastecart x (vec 0))` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `p:real^(N,1)finite_sum->real^N`)) (concl th) &&
        can (find_term ((=) `Pm:(real^N->bool)->real^(N,1)finite_sum->real^N`)) (concl th))) THEN
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; DROP_NEG; DROP_VEC] THEN
      REAL_ARITH_TAC;
      ASM_SIMP_TAC[]]]);;

(* The curve bicollar CURVE_BICOLLAR_ORIENTABLE, with SURFACE_EULER_PLANAR   *)
(* of pc_moi_fnd_surfb at the type of the cap.                               *)

let CURVE_BICOLLAR_ORIENTABLE = prove
 (MOI_FND_BICOLLAR_CURVE_2,
  MATCH_ACCEPT_TAC(MP MOI_FCB_CURVE_BICOLLAR_COND
    (INST_TYPE [`:(N,2)finite_sum`,`:N`] SURFACE_EULER_PLANAR)));;


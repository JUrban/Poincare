needs "src/pc_moi_s2628_stmt.ml";;
needs "src/pc_moi_fnd_gpa.ml";;
needs "src/pc_moi_fnd_surfa.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* pc_moi_s26_cross: the even crossing lemma for Moise Sec 26 Theorem 6      *)
(* (MOISE_266).  A closed polygon in general position with a finite          *)
(* simplicial 2-complex in real^3 all of whose edges lie in an even number   *)
(* of triangles crosses the complex an even number of times.  Route: cone    *)
(* the polygon from a generic apex; each fan triangle meets each triangle of *)
(* the complex in a segment or not at all (MOI_S6X_PAIR), so the boundary of *)
(* each fan triangle meets the complex evenly (edges count twice by the      *)
(* parity hypothesis), and summing over the fan the radial edges count       *)
(* twice.  Main theorem: EVEN_CROSSING : |- MOI_S26_EVEN_CROSSING.           *)
(* ========================================================================= *)

(* General position facts. *)

let MOI_S6X_GP_LOW = prove
 (`!(s:real^3->bool) t.
     affine_gp_3 s t /\ aff_dim s + aff_dim t < &3 ==> DISJOINT s t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[affine_gp_3] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_INT_ARITH_TAC);;

let MOI_S6X_GP_SEG_TRI = prove
 (`!(u:real^3) v q.
     ~(u = v) /\ aff_dim q = &2 /\ affine_gp_3 (segment[u,v]) q
     ==> ?z. segment[u,v] INTER q SUBSET {z}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `affine_gp_3 (segment[u:real^3,v]) q` THEN
  ASM_REWRITE_TAC[affine_gp_3; AFF_DIM_SEGMENT] THEN CONV_TAC INT_REDUCE_CONV THEN
  STRIP_TAC THENL
   [EXISTS_TAC `u:real^3` THEN ASM SET_TAC[];
    UNDISCH_TAC `aff_dim (affine hull segment[u,v] INTER affine hull q:real^3->bool) = &0` THEN
    REWRITE_TAC[AFF_DIM_EQ_0] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `z:real^3` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`affine:(real^3->bool)->bool`; `segment[u:real^3,v]`] HULL_SUBSET) THEN
    MP_TAC(ISPECL [`affine:(real^3->bool)->bool`; `q:real^3->bool`] HULL_SUBSET) THEN SET_TAC[]]);;

(* Positive barycentric coordinates give relative interior points of a triangle. *)

let MOI_S6X_RELINT_TRI = prove
 (`!(a:real^N) b c s1 s2 s3.
     ~collinear {a,b,c} /\ &0 < s1 /\ &0 < s2 /\ &0 < s3 /\ s1 + s2 + s3 = &1
     ==> s1 % a + s2 % b + s3 % c IN relative_interior(convex hull {a,b,c})`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `~collinear {a:real^N,b,c}` THEN
  REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT; DE_MORGAN_THM] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[RELATIVE_INTERIOR_CONVEX_HULL_EXPLICIT; IN_ELIM_THM] THEN
  EXISTS_TAC `\p:real^N. if p = a then s1 else if p = b then s2 else s3:real` THEN
  SUBGOAL_THEN `~(b:real^N = a) /\ ~(c:real^N = a) /\ ~(c:real^N = b)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SIMP_TAC[SUM_CLAUSES; VSUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ADD_RID; VECTOR_ADD_RID] THEN CONJ_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[]]);;

(* A relative interior point of q on an open edge of the triangle T, with   *)
(* the edge line not in the plane of q and the planes meeting in a line,    *)
(* gives a common relative interior point of T and q.                       *)

let MOI_S6X_EDGE_PUSH = prove
 (`!(a:real^3) b c q x.
     ~collinear {a,b,c} /\ convex q /\
     x IN segment(a,b) /\ x IN relative_interior q /\
     aff_dim (affine hull {a,b,c} INTER affine hull q) = &1 /\
     ~(affine hull {a,b} SUBSET affine hull q)
     ==> ?z. z IN relative_interior(convex hull {a,b,c}) /\ z IN relative_interior q`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(a:real^3 = b)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~collinear {a:real^3,b,c}` THEN
    ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2];
    ALL_TAC] THEN
  UNDISCH_TAC `(x:real^3) IN segment(a,b)` THEN REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `A = affine hull {a:real^3,b,c} INTER affine hull q` THEN
  SUBGOAL_THEN `affine (A:real^3->bool) /\ (x:real^3) IN A` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN SIMP_TAC[AFFINE_INTER; AFFINE_AFFINE_HULL] THEN
    REWRITE_TAC[IN_INTER; AFFINE_HULL_3; IN_ELIM_THM] THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`&1 - u`; `u:real`; `&0`] THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; VECTOR_ARITH_TAC];
      MATCH_MP_TAC(REWRITE_RULE[SUBSET] (ISPECL [`affine:(real^3->bool)->bool`;
        `q:real^3->bool`] HULL_SUBSET)) THEN
      MATCH_MP_TAC(REWRITE_RULE[SUBSET] RELATIVE_INTERIOR_SUBSET) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?y:real^3. y IN A /\ ~(y IN affine hull {a,b})` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!s t:real^3->bool. ~(s SUBSET t) ==> ?y. y IN s /\ ~(y IN t)`) THEN DISCH_TAC THEN
    UNDISCH_TAC `~(affine hull {a:real^3,b} SUBSET affine hull q)` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `affine hull {a:real^3,b} = A` SUBST1_TAC THENL
     [MP_TAC(ISPECL [`A:real^3->bool`; `affine hull {a:real^3,b}`] AFF_DIM_EQ_AFFINE_HULL) THEN
      ASM_REWRITE_TAC[AFF_DIM_AFFINE_HULL; AFF_DIM_2] THEN
      ASM_SIMP_TAC[HULL_P; HULL_HULL; INT_LE_REFL] THEN MESON_TAC[];
      EXPAND_TAC "A" THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?t1 t2 t3. &0 < t3 /\ t1 + t2 + t3 = &1 /\
                           t1 % a + t2 % b + t3 % c IN (A:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(y:real^3) IN affine hull {a,b,c}` MP_TAC THENL
     [EXPAND_TAC "A" THEN UNDISCH_TAC `(y:real^3) IN A` THEN EXPAND_TAC "A" THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[AFFINE_HULL_3; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `r1:real` (X_CHOOSE_THEN `r2:real` (X_CHOOSE_THEN `r3:real`
      STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `~(r3 = &0)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~((y:real^3) IN affine hull {a,b})` THEN
      ASM_REWRITE_TAC[AFFINE_HULL_2; IN_ELIM_THM] THEN
      MAP_EVERY EXISTS_TAC [`r1:real`; `r2:real`] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC];
      ALL_TAC] THEN
    ASM_CASES_TAC `&0 < r3` THENL
     [MAP_EVERY EXISTS_TAC [`r1:real`; `r2:real`; `r3:real`] THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(y:real^3) IN A` THEN ASM_REWRITE_TAC[];
      MAP_EVERY EXISTS_TAC [`&2 * (&1 - u) - r1`; `&2 * u - r2`; `--r3`] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(&2 * (&1 - u) - r1) % a + (&2 * u - r2) % b + --r3 % c =
                    x + &1 % (x - y:real^3)` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC IN_AFFINE_ADD_MUL_DIFF THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?e. &0 < e /\ ball(x:real^3,e) INTER affine hull q SUBSET relative_interior q`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `q:real^3->bool` OPEN_IN_RELATIVE_INTERIOR) THEN
    REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^3` o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `w = t1 % a + t2 % b + t3 % c:real^3` THEN
  ABBREV_TAC `D = norm(w - x:real^3)` THEN
  ABBREV_TAC `t = min (&1 / &2) (min ((&1 - u) / (&2 * (&1 + abs t1)))
                                     (min (u / (&2 * (&1 + abs t2))) (e / (&2 * (D + &1)))))` THEN
  SUBGOAL_THEN `&0 <= D` ASSUME_TAC THENL [EXPAND_TAC "D" THEN REWRITE_TAC[NORM_POS_LE];
                                           ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 + abs t1 /\ &0 < &1 + abs t2 /\ &0 < D + &1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&1 - u) / (&2 * (&1 + abs t1)) /\ &0 < u / (&2 * (&1 + abs t2)) /\
                &0 < e / (&2 * (D + &1))` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t /\ t <= &1 / &2 /\ t <= (&1 - u) / (&2 * (&1 + abs t1)) /\
                t <= u / (&2 * (&1 + abs t2)) /\ t <= e / (&2 * (D + &1))`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "t" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `t * (&1 + abs t1) <= (&1 - u) / &2 /\ t * (&1 + abs t2) <= u / &2 /\
                t * D < e` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(&1 - u) / (&2 * (&1 + abs t1)) * (&1 + abs t1)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < &1 + abs t1` THEN
        CONV_TAC REAL_FIELD];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `u / (&2 * (&1 + abs t2)) * (&1 + abs t2)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < &1 + abs t2` THEN
        CONV_TAC REAL_FIELD];
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `e / (&2 * (D + &1)) * (D + &1)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `e / (&2 * (D + &1)) * (D + &1) = e / &2` SUBST1_TAC THENL
         [UNDISCH_TAC `&0 < D + &1` THEN CONV_TAC REAL_FIELD; ASM_REAL_ARITH_TAC]]];
    ALL_TAC] THEN
  EXISTS_TAC `x + t % (w - x:real^3)` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `x + t % (w - x:real^3) =
                  ((&1 - u) * (&1 - t) + t * t1) % a + (u * (&1 - t) + t * t2) % b +
                  (t * t3) % c` SUBST1_TAC THENL
     [SUBST1_TAC(ASSUME `x = (&1 - u) % a + u % b:real^3`) THEN EXPAND_TAC "w" THEN
      VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_S6X_RELINT_TRI THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `--(t * abs t1) <= t * t1 /\ --(t * abs t2) <= t * t2 /\
                  &0 <= t * u /\ t * u <= t /\ &0 < t * t3 /\ t * t1 + t * t2 + t * t3 = t`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [REWRITE_TAC[REAL_ARITH `--(t * a) <= t * b <=> &0 <= t * (b + a)`] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_ARITH `--(t * a) <= t * b <=> &0 <= t * (b + a)`] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_ARITH `t * u <= t <=> &0 <= t * (&1 - u)`] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN ASM_REWRITE_TAC[REAL_MUL_RID]];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `ball(x:real^3,e) INTER affine hull q SUBSET relative_interior q` THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[dist; VECTOR_ARITH `x - (x + t % (w - x)):real^3 = --(t % (w - x))`] THEN
      REWRITE_TAC[NORM_NEG; NORM_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`];
      SUBGOAL_THEN `x + t % (w - x:real^3) IN A` MP_TAC THENL
       [MATCH_MP_TAC IN_AFFINE_ADD_MUL_DIFF THEN ASM_REWRITE_TAC[] THEN
        EXPAND_TAC "w" THEN ASM_REWRITE_TAC[];
        EXPAND_TAC "A" THEN SET_TAC[]]]]);;

(* Faces of a triangle and their dimensions. *)

let MOI_S6X_TRI_FACE_FACTS = prove
 (`!(a:real^3) b c.
     ~collinear {a,b,c}
     ==> ~(a = b) /\ ~(b = c) /\ ~(c = a) /\
         segment[a,b] face_of convex hull {a,b,c} /\
         segment[b,c] face_of convex hull {a,b,c} /\
         segment[c,a] face_of convex hull {a,b,c} /\
         {a} face_of convex hull {a,b,c} /\ {b} face_of convex hull {a,b,c} /\
         {c} face_of convex hull {a,b,c} /\
         convex hull {a,b,c} face_of convex hull {a,b,c} /\
         aff_dim(segment[a,b]) = &1 /\ aff_dim(segment[b,c]) = &1 /\
         aff_dim(segment[c,a]) = &1 /\
         aff_dim{a} = &0 /\ aff_dim{b} = &0 /\ aff_dim{c} = &0 /\
         aff_dim(convex hull {a,b,c}) = &2 /\
         relative_frontier(convex hull {a,b,c}) =
           segment[a,b] UNION segment[b,c] UNION segment[c,a] /\
         convex(convex hull {a,b,c}) /\ compact(convex hull {a,b,c})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [COLLINEAR_3_EQ_AFFINE_DEPENDENT]) THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_TRIANGLE; AFF_DIM_SEGMENT; AFF_DIM_SING;
               CONVEX_CONVEX_HULL; COMPACT_CONVEX_HULL; FINITE_IMP_COMPACT;
               FINITE_INSERT; FINITE_EMPTY; FACE_OF_REFL] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[SEGMENT_CONVEX_HULL; FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    EXISTS_TAC `{a:real^3,b}` THEN SET_TAC[];
    ASM_SIMP_TAC[SEGMENT_CONVEX_HULL; FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    EXISTS_TAC `{b:real^3,c}` THEN SET_TAC[];
    ASM_SIMP_TAC[SEGMENT_CONVEX_HULL; FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    EXISTS_TAC `{c:real^3,a}` THEN SET_TAC[];
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    EXISTS_TAC `{a:real^3}` THEN REWRITE_TAC[CONVEX_HULL_SING] THEN SET_TAC[];
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    EXISTS_TAC `{b:real^3}` THEN REWRITE_TAC[CONVEX_HULL_SING] THEN SET_TAC[];
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    EXISTS_TAC `{c:real^3}` THEN REWRITE_TAC[CONVEX_HULL_SING] THEN SET_TAC[];
    ASM_SIMP_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_AFFINE_INDEPENDENT] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV]);;

let MOI_S6X_GP_SYM = prove
 (`!s t:real^3->bool. affine_gp_3 s t <=> affine_gp_3 t s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[affine_gp_3] THEN
  SUBGOAL_THEN `affine hull s INTER affine hull t =
                affine hull t INTER affine hull (s:real^3->bool)` SUBST1_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(a <=> a') /\ (b <=> b') ==> (a \/ b <=> a' \/ b')`) THEN
  CONJ_TAC THENL [REWRITE_TAC[DISJOINT_SYM]; INT_ARITH_TAC]);;

(* An edge meeting a triangle in general position does not lie in its plane. *)

let MOI_S6X_EDGE_NOT_IN_PLANE = prove
 (`!(a:real^3) b q.
     ~(a = b) /\ aff_dim q = &2 /\ affine_gp_3 (segment[a,b]) q /\
     ~(segment[a,b] INTER q = {})
     ==> ~(affine hull {a,b} SUBSET affine hull q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `affine_gp_3 (segment[a:real^3,b]) q` THEN
  ASM_REWRITE_TAC[affine_gp_3; AFF_DIM_SEGMENT; DISJOINT; AFFINE_HULL_SEGMENT] THEN
  CONV_TAC INT_REDUCE_CONV THEN DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `affine hull {a:real^3,b} INTER affine hull q = affine hull {a,b}`
  (fun th -> UNDISCH_TAC `aff_dim (affine hull {a:real^3,b} INTER affine hull q) = &0` THEN
             REWRITE_TAC[th]) THENL
   [ASM SET_TAC[]; ASM_REWRITE_TAC[AFF_DIM_AFFINE_HULL; AFF_DIM_2] THEN INT_ARITH_TAC]);;

(* A relative boundary point of a triangle inside the relative interior of q *)
(* gives a common relative interior point (edges transverse to q).          *)

let MOI_S6X_RELBD_PUSH = prove
 (`!(a:real^3) b c q x.
     ~collinear {a,b,c} /\ convex q /\ aff_dim q = &2 /\
     ~(a IN q) /\ ~(b IN q) /\ ~(c IN q) /\
     affine_gp_3 (segment[a,b]) q /\ affine_gp_3 (segment[b,c]) q /\
     affine_gp_3 (segment[c,a]) q /\
     aff_dim (affine hull {a,b,c} INTER affine hull q) = &1 /\
     x IN relative_frontier(convex hull {a,b,c}) /\ x IN relative_interior q
     ==> ?z. z IN relative_interior(convex hull {a,b,c}) /\ z IN relative_interior q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^3`; `b:real^3`; `c:real^3`] MOI_S6X_TRI_FACE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^3) IN q` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  UNDISCH_TAC `(x:real^3) IN relative_frontier(convex hull {a,b,c})` THEN
  ASM_REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
   [MATCH_MP_TAC MOI_S6X_EDGE_PUSH THEN EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN segment[a,b]` THEN REWRITE_TAC[SEGMENT_CLOSED_OPEN] THEN
      ASM SET_TAC[];
      MATCH_MP_TAC MOI_S6X_EDGE_NOT_IN_PLANE THEN ASM SET_TAC[]];
    MP_TAC(ISPECL [`b:real^3`; `c:real^3`; `a:real^3`; `q:real^3->bool`; `x:real^3`]
                  MOI_S6X_EDGE_PUSH) THEN
    SUBGOAL_THEN `{b:real^3,c,a} = {a,b,c}` SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN segment[b,c]` THEN REWRITE_TAC[SEGMENT_CLOSED_OPEN] THEN
      ASM SET_TAC[];
      MATCH_MP_TAC MOI_S6X_EDGE_NOT_IN_PLANE THEN ASM SET_TAC[]];
    MP_TAC(ISPECL [`c:real^3`; `a:real^3`; `b:real^3`; `q:real^3->bool`; `x:real^3`]
                  MOI_S6X_EDGE_PUSH) THEN
    SUBGOAL_THEN `{c:real^3,a,b} = {a,b,c}` SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN segment[c,a]` THEN REWRITE_TAC[SEGMENT_CLOSED_OPEN] THEN
      ASM SET_TAC[];
      MATCH_MP_TAC MOI_S6X_EDGE_NOT_IN_PLANE THEN ASM SET_TAC[]]]);;

(* The relative frontier of a nondegenerate segment. *)

let MOI_S6X_RELBD_SEGMENT = prove
 (`!a b:real^N. ~(a = b) ==> relative_frontier(segment[a,b]) = {a,b}`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[relative_frontier; RELATIVE_INTERIOR_SEGMENT; CLOSURE_SEGMENT] THEN
  REWRITE_TAC[SEGMENT_CLOSED_OPEN] THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`] ENDS_NOT_IN_SEGMENT) THEN SET_TAC[]);;

(* Two triangles of real^3 whose nonempty faces are pairwise in general     *)
(* position: the boundary points of one lying in the other, together with   *)
(* the converse ones, are the two ends of the segment T INTER q (or none).  *)

let MOI_S6X_PAIR = prove
 (`!(a:real^3) b c va vb vc.
     ~collinear {a,b,c} /\ ~collinear {va,vb,vc} /\
     (!f g. f face_of convex hull {a,b,c} /\ g face_of convex hull {va,vb,vc} /\
            ~(f = {}) /\ ~(g = {}) ==> affine_gp_3 f g)
     ==> FINITE (relative_frontier(convex hull {a,b,c}) INTER convex hull {va,vb,vc}) /\
         FINITE (convex hull {a,b,c} INTER relative_frontier(convex hull {va,vb,vc})) /\
         EVEN (CARD (relative_frontier(convex hull {a,b,c}) INTER convex hull {va,vb,vc}) +
               CARD (convex hull {a,b,c} INTER relative_frontier(convex hull {va,vb,vc})))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^3`; `b:real^3`; `c:real^3`] MOI_S6X_TRI_FACE_FACTS) THEN
  MP_TAC(ISPECL [`va:real^3`; `vb:real^3`; `vc:real^3`] MOI_S6X_TRI_FACE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "fq") THEN DISCH_THEN(LABEL_TAC "ft") THEN
  ABBREV_TAC `tt = convex hull {a:real^3,b,c}` THEN
  ABBREV_TAC `qq = convex hull {va:real^3,vb,vc}` THEN
  SUBGOAL_THEN `!f g:real^3->bool. f face_of tt /\ g face_of qq /\ aff_dim f + aff_dim g < &3
                                   ==> DISJOINT f g` (LABEL_TAC "low") THENL
   [REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `f:real^3->bool = {}` THEN ASM_REWRITE_TAC[DISJOINT_EMPTY] THEN
    ASM_CASES_TAC `g:real^3->bool = {}` THEN ASM_REWRITE_TAC[DISJOINT_EMPTY] THEN
    MATCH_MP_TAC MOI_S6X_GP_LOW THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (relative_frontier tt) (relative_frontier (qq:real^3->bool))`
  ASSUME_TAC THENL
   [USE_THEN "ft" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "fq" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[DISJOINT_UNION;
                SET_RULE `!s t u:real^3->bool. DISJOINT s (t UNION u) <=> DISJOINT s t /\ DISJOINT s u`] THEN
    REPEAT CONJ_TAC THEN
    USE_THEN "low" MATCH_MP_TAC THEN
    USE_THEN "ft" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "fq" (fun th -> REWRITE_TAC[th]) THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~((a:real^3) IN qq) /\ ~(b IN qq) /\ ~(c IN qq)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SET_RULE `~((x:real^3) IN s) <=> DISJOINT {x} s`] THEN
    REPEAT CONJ_TAC THEN USE_THEN "low" MATCH_MP_TAC THEN
    USE_THEN "ft" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "fq" (fun th -> REWRITE_TAC[th]) THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~((va:real^3) IN tt) /\ ~(vb IN tt) /\ ~(vc IN tt)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SET_RULE `~((x:real^3) IN s) <=> DISJOINT s {x}`] THEN
    REPEAT CONJ_TAC THEN USE_THEN "low" MATCH_MP_TAC THEN
    USE_THEN "ft" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "fq" (fun th -> REWRITE_TAC[th]) THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `convex (tt:real^3->bool) /\ convex (qq:real^3->bool) /\
                closed tt /\ closed qq /\ compact tt /\ compact qq /\
                aff_dim tt = &2 /\ aff_dim qq = &2 /\ ~(tt = {}) /\ ~(qq = {})`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC COMPACT_IMP_CLOSED) THEN
    TRY(USE_THEN "ft" (fun th -> REWRITE_TAC[th]) THEN NO_TAC) THEN
    TRY(USE_THEN "fq" (fun th -> REWRITE_TAC[th]) THEN NO_TAC) THENL
     [EXPAND_TAC "tt" THEN REWRITE_TAC[CONVEX_HULL_EQ_EMPTY; NOT_INSERT_EMPTY];
      EXPAND_TAC "qq" THEN REWRITE_TAC[CONVEX_HULL_EQ_EMPTY; NOT_INSERT_EMPTY]];
    ALL_TAC] THEN
  SUBGOAL_THEN `affine_gp_3 (tt:real^3->bool) qq /\
                affine_gp_3 (segment[a,b]) qq /\ affine_gp_3 (segment[b,c]) qq /\
                affine_gp_3 (segment[c,a]) qq /\
                affine_gp_3 (segment[va,vb]) tt /\ affine_gp_3 (segment[vb,vc]) tt /\
                affine_gp_3 (segment[vc,va]) tt`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `!x y:real^3. ~(segment[x,y] = {})` ASSUME_TAC THENL
     [MESON_TAC[ENDS_IN_SEGMENT; NOT_IN_EMPTY]; ALL_TAC] THEN
    REPEAT CONJ_TAC THEN
    TRY(ONCE_REWRITE_TAC[MOI_S6X_GP_SYM] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `affine_gp_3:(real^3->bool)->(real^3->bool)->bool`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN
        USE_THEN "ft" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "fq" (fun th -> REWRITE_TAC[th]) THEN
        NO_TAC) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `affine_gp_3:(real^3->bool)->(real^3->bool)->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "ft" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "fq" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  REMOVE_THEN "ft" (K ALL_TAC) THEN REMOVE_THEN "fq" (K ALL_TAC) THEN
  SUBGOAL_THEN `affine hull {a:real^3,b,c} = affine hull tt /\
                affine hull {va:real^3,vb,vc} = affine hull qq`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "tt" THEN EXPAND_TAC "qq" THEN REWRITE_TAC[AFFINE_HULL_CONVEX_HULL];
    ALL_TAC] THEN
  ASM_CASES_TAC `tt INTER qq:real^3->bool = {}` THENL
   [SUBGOAL_THEN `relative_frontier tt INTER qq = {} /\
                  tt INTER relative_frontier qq:real^3->bool = {}`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [MP_TAC(ISPEC `tt:real^3->bool` RELATIVE_FRONTIER_SUBSET) THEN
      MP_TAC(ISPEC `qq:real^3->bool` RELATIVE_FRONTIER_SUBSET) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `tt INTER qq:real^3->bool = {}` THEN SET_TAC[];
      REWRITE_TAC[FINITE_EMPTY; CARD_CLAUSES; ADD_CLAUSES; EVEN]];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (affine hull tt INTER affine hull qq:real^3->bool) = &1`
  ASSUME_TAC THENL
   [UNDISCH_TAC `affine_gp_3 (tt:real^3->bool) qq` THEN
    ASM_REWRITE_TAC[affine_gp_3; DISJOINT] THEN CONV_TAC INT_REDUCE_CONV THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (affine hull qq INTER affine hull tt:real^3->bool) = &1`
  ASSUME_TAC THENL [ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?z:real^3. z IN relative_interior tt /\ z IN relative_interior qq`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(tt INTER qq:real^3->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `(x:real^3) IN relative_interior tt` THEN
    ASM_CASES_TAC `(x:real^3) IN relative_interior qq` THENL
     [EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`va:real^3`; `vb:real^3`; `vc:real^3`; `tt:real^3->bool`; `x:real^3`]
                    MOI_S6X_RELBD_PUSH) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [REWRITE_TAC[relative_frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED; IN_DIFF];
        MESON_TAC[]];
      MP_TAC(ISPECL [`a:real^3`; `b:real^3`; `c:real^3`; `qq:real^3->bool`; `x:real^3`]
                    MOI_S6X_RELBD_PUSH) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [REWRITE_TAC[relative_frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED; IN_DIFF];
        MESON_TAC[]];
      UNDISCH_TAC `DISJOINT (relative_frontier tt) (relative_frontier (qq:real^3->bool))` THEN
      REWRITE_TAC[relative_frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `kk = (tt:real^3->bool) INTER qq` THEN
  SUBGOAL_THEN `relative_interior kk = relative_interior tt INTER
                                       relative_interior (qq:real^3->bool)`
  ASSUME_TAC THENL
   [EXPAND_TAC "kk" THEN MATCH_MP_TAC RELATIVE_INTERIOR_INTER THEN
    ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier kk =
                relative_frontier tt INTER qq UNION
                tt INTER relative_frontier (qq:real^3->bool)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `closed (kk:real^3->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "kk" THEN MATCH_MP_TAC CLOSED_INTER THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[relative_frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED] THEN
    EXPAND_TAC "kk" THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?e. &0 < e /\
      ball(z:real^3,e) INTER affine hull tt SUBSET relative_interior tt /\
      ball(z,e) INTER affine hull qq SUBSET relative_interior qq`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `tt:real^3->bool` OPEN_IN_RELATIVE_INTERIOR) THEN
    REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^3` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPEC `qq:real^3->bool` OPEN_IN_RELATIVE_INTERIOR) THEN
    REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^3` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e2:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min e1 e2:real` THEN
    ASM_REWRITE_TAC[REAL_LT_MIN; BALL_MIN_INTER] THEN
    MAP_EVERY UNDISCH_TAC
     [`ball(z:real^3,e1) INTER affine hull tt SUBSET relative_interior tt`;
      `ball(z:real^3,e2) INTER affine hull qq SUBSET relative_interior qq`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (kk:real^3->bool) = &1` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM INT_LE_ANTISYM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC INT_LE_TRANS THEN
      EXISTS_TAC `aff_dim (affine hull tt INTER affine hull qq:real^3->bool)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC AFF_DIM_SUBSET THEN EXPAND_TAC "kk" THEN
        MP_TAC(ISPECL [`affine:(real^3->bool)->bool`; `tt:real^3->bool`] HULL_SUBSET) THEN
        MP_TAC(ISPECL [`affine:(real^3->bool)->bool`; `qq:real^3->bool`] HULL_SUBSET) THEN
        SET_TAC[];
        ASM_REWRITE_TAC[INT_LE_REFL]];
      MP_TAC(ISPECL [`affine hull tt INTER affine hull qq:real^3->bool`;
                     `ball(z:real^3,e)`] AFF_DIM_CONVEX_INTER_OPEN) THEN
      ANTS_TAC THENL
       [SIMP_TAC[AFFINE_IMP_CONVEX; AFFINE_INTER; AFFINE_AFFINE_HULL; OPEN_BALL] THEN
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `z:real^3` THEN
        REWRITE_TAC[IN_INTER; CENTRE_IN_BALL] THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPEC `tt:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
        MP_TAC(ISPEC `qq:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
        MP_TAC(ISPECL [`affine:(real^3->bool)->bool`; `tt:real^3->bool`] HULL_SUBSET) THEN
        MP_TAC(ISPECL [`affine:(real^3->bool)->bool`; `qq:real^3->bool`] HULL_SUBSET) THEN
        UNDISCH_TAC `(z:real^3) IN relative_interior tt` THEN
        UNDISCH_TAC `(z:real^3) IN relative_interior qq` THEN
        SET_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC AFF_DIM_SUBSET THEN EXPAND_TAC "kk" THEN
      MP_TAC(ISPEC `tt:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
      MP_TAC(ISPEC `qq:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
      MAP_EVERY UNDISCH_TAC
       [`ball(z:real^3,e) INTER affine hull tt SUBSET relative_interior tt`;
        `ball(z:real^3,e) INTER affine hull qq SUBSET relative_interior qq`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?k1 k2:real^3. kk = segment[k1,k2]` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_CONVEX_COLLINEAR_SEGMENT THEN
    ASM_REWRITE_TAC[COLLINEAR_AFF_DIM; INT_LE_REFL] THEN
    EXPAND_TAC "kk" THEN ASM_SIMP_TAC[COMPACT_INTER; CONVEX_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(k1:real^3 = k2)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `aff_dim (kk:real^3->bool) = &1` THEN
    ASM_REWRITE_TAC[SEGMENT_REFL; AFF_DIM_SING] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier tt INTER qq UNION
                tt INTER relative_frontier (qq:real^3->bool) = {k1,k2}`
  ASSUME_TAC THENL
   [UNDISCH_TAC `relative_frontier kk =
                relative_frontier tt INTER qq UNION
                tt INTER relative_frontier (qq:real^3->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S6X_RELBD_SEGMENT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(relative_frontier tt INTER qq) INTER
                (tt INTER relative_frontier (qq:real^3->bool)) = {}`
  ASSUME_TAC THENL
   [UNDISCH_TAC `DISJOINT (relative_frontier tt) (relative_frontier (qq:real^3->bool))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (relative_frontier tt INTER (qq:real^3->bool)) /\
                FINITE (tt INTER relative_frontier (qq:real^3->bool))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{k1:real^3,k2}` THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN
    UNDISCH_TAC `relative_frontier tt INTER qq UNION
                 tt INTER relative_frontier (qq:real^3->bool) = {k1,k2}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`relative_frontier tt INTER (qq:real^3->bool)`;
                 `tt INTER relative_frontier (qq:real^3->bool)`] CARD_UNION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* Counting lemmas: disjoint unions of an indexed family, dependent pairs, *)
(* a cyclic shift of a finite sum, and the subsets of a pair.               *)

let MOI_S6X_CARD_UNIONS_IMAGE = prove
 (`!(f:B->A->bool) s.
     FINITE s /\ (!i. i IN s ==> FINITE (f i)) /\
     (!i j. i IN s /\ j IN s /\ ~(i = j) ==> f i INTER f j = {})
     ==> FINITE (UNIONS (IMAGE f s)) /\
         CARD (UNIONS (IMAGE f s)) = nsum s (\i. CARD (f i))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[FINITE_UNIONS; FINITE_IMAGE; FORALL_IN_IMAGE]; ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (f:B->A->bool) s` CARD_UNIONS) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`CARD:(A->bool)->num`; `f:B->A->bool`; `s:B->bool`]
    NSUM_IMAGE_NONZERO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(f:B->A->bool) x = {}` (fun th -> REWRITE_TAC[th; CARD_CLAUSES]) THEN
    ASM_MESON_TAC[INTER_IDEMPOT];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF]]);;

let MOI_S6X_CARD_SIGMA = prove
 (`!(t:B->A->bool) s.
     FINITE s /\ (!i. i IN s ==> FINITE (t i))
     ==> FINITE {(i,x) | i IN s /\ x IN t i} /\
         CARD {(i,x) | i IN s /\ x IN t i} = nsum s (\i. CARD (t i))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `{(i,x) | i IN s /\ x IN (t:B->A->bool) i} =
                UNIONS (IMAGE (\i:B. IMAGE (\x:A. (i,x)) (t i)) s)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; UNIONS_IMAGE; IN_ELIM_THM; IN_IMAGE;
                PAIR_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\i:B. IMAGE (\x:A. (i,x)) ((t:B->A->bool) i)`; `s:B->bool`]
    MOI_S6X_CARD_UNIONS_IMAGE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMAGE] THEN
    REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_INTER; IN_IMAGE; NOT_IN_EMPTY;
                PAIR_EQ] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> REWRITE_TAC[th]) SUBST1_TAC) THEN
  MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `i:B` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_SIMP_TAC[PAIR_EQ]);;

let MOI_S6X_NSUM_SHIFT = prove
 (`!(f:num->num) n.
     f n = f 0 ==> nsum {i | i < n} (\i. f (SUC i)) = nsum {i | i < n} f`,
  SUBGOAL_THEN
   `!(f:num->num) n. nsum {i | i < n} (\i. f (SUC i)) + f 0 =
                     nsum {i | i < n} f + f n`
  (fun th -> REPEAT STRIP_TAC THEN MP_TAC(SPECL [`f:num->num`; `n:num`] th) THEN
             ASM_REWRITE_TAC[EQ_ADD_RCANCEL]) THEN
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[LT; EMPTY_GSPEC; NSUM_CLAUSES]; ALL_TAC] THEN
  SUBGOAL_THEN `{i | i < SUC n} = n INSERT {i | i < n}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT] THEN ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[NSUM_CLAUSES; FINITE_NUMSEG_LT; IN_ELIM_THM; LT_REFL] THEN
  POP_ASSUM MP_TAC THEN ARITH_TAC);;

let MOI_S6X_SUBSET_PAIR = prove
 (`!(t:A->bool) b c.
     t SUBSET {b,c} ==> t = {} \/ t = {b} \/ t = {c} \/ t = {b,c}`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `(b:A) IN t` THEN ASM_CASES_TAC `(c:A) IN t` THENL
   [REPEAT DISJ2_TAC THEN ASM SET_TAC[];
    DISJ2_TAC THEN DISJ1_TAC THEN ASM SET_TAC[];
    DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN ASM SET_TAC[];
    DISJ1_TAC THEN ASM SET_TAC[]]);;

(* Simplicial complex facts: triangles, intersections of distinct simplices *)
(* of the same dimension, and the boundary of a triangle as the union of    *)
(* the edges of the complex inside it.                                      *)

let MOI_S6X_SC_TRI = prove
 (`!(c:(real^3->bool)->bool) q.
     simplicial_complex c /\ q IN c /\ aff_dim q = &2
     ==> ?va vb vc. ~collinear {va,vb,vc} /\ q = convex hull {va,vb,vc}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplicial_complex] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&2 simplex (q:real^3->bool)` MP_TAC THENL
   [SUBGOAL_THEN `?n. n simplex (q:real^3->bool)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[AFF_DIM_SIMPLEX];
    REWRITE_TAC[MOI_PL2_SIMPLEX_2] THEN MESON_TAC[]]);;

let MOI_S6X_SC_INTER_LOW = prove
 (`!(c:(real^3->bool)->bool) s t.
     simplicial_complex c /\ s IN c /\ t IN c /\ ~(s = t) /\
     aff_dim s = aff_dim t
     ==> s INTER t IN c /\ aff_dim (s INTER t) < aff_dim s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplicial_complex] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(s INTER t:real^3->bool) face_of s /\ (s INTER t) face_of t`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `convex (s:real^3->bool) /\ convex (t:real^3->bool)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  ASM_CASES_TAC `s INTER t:real^3->bool = s` THENL
   [MP_TAC(ISPECL [`s:real^3->bool`; `t:real^3->bool`] FACE_OF_AFF_DIM_LT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[INT_LT_REFL]];
    MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN ASM_REWRITE_TAC[]]);;

let MOI_S6X_SC_RELBD_TRI = prove
 (`!(c:(real^3->bool)->bool) q.
     simplicial_complex c /\ q IN c /\ aff_dim q = &2
     ==> relative_frontier q =
         UNIONS {e | e IN c /\ aff_dim e = &1 /\ e SUBSET q}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!f s:real^3->bool. s IN c /\ f face_of s ==> f IN c`
  ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_complex (c:(real^3->bool)->bool)` THEN
    REWRITE_TAC[simplicial_complex] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `q:real^3->bool`] MOI_S6X_SC_TRI) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `va:real^3` (X_CHOOSE_THEN `vb:real^3`
    (X_CHOOSE_THEN `vc:real^3` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S6X_TRI_FACE_FACTS) THEN
  UNDISCH_THEN `q = convex hull {va:real^3,vb,vc}` (SUBST_ALL_TAC o SYM) THEN
  STRIP_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^3` THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EQ_TAC THENL
   [ASM_REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
     [EXISTS_TAC `segment[va:real^3,vb]`;
      EXISTS_TAC `segment[vb:real^3,vc]`;
      EXISTS_TAC `segment[vc:real^3,va]`] THEN
    ASM_REWRITE_TAC[] THEN
    (CONJ_TAC THENL
      [FIRST_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `q:real^3->bool` THEN
       ASM_REWRITE_TAC[];
       MATCH_MP_TAC FACE_OF_IMP_SUBSET THEN ASM_REWRITE_TAC[]]);
    DISCH_THEN(X_CHOOSE_THEN `e:real^3->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(e:real^3->bool) face_of q` ASSUME_TAC THENL
     [UNDISCH_TAC `simplicial_complex (c:(real^3->bool)->bool)` THEN
      REWRITE_TAC[simplicial_complex] THEN
      DISCH_THEN(MP_TAC o SPECL [`e:real^3->bool`; `q:real^3->bool`] o
                 last o CONJUNCTS) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `e INTER q:real^3->bool = e` SUBST1_TAC THENL
       [UNDISCH_TAC `(e:real^3->bool) SUBSET q` THEN SET_TAC[]; SIMP_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`q:real^3->bool`; `e:real^3->bool`]
      FACE_OF_SUBSET_RELATIVE_FRONTIER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      UNDISCH_TAC `aff_dim (e:real^3->bool) = &1` THEN ASM_REWRITE_TAC[] THEN
      INT_ARITH_TAC;
      UNDISCH_TAC `(x:real^3) IN e` THEN SET_TAC[]]]);;

(* A nondegenerate triangle whose nonempty faces are in general position   *)
(* with every simplex of the complex: its boundary misses the simplices of *)
(* dimension at most 1 and the triangle misses the vertices.                *)

let MOI_S6X_FAN_LOW = prove
 (`!(c:(real^3->bool)->bool) a b d.
     ~collinear {a,b,d} /\
     (!f s. f face_of convex hull {a,b,d} /\ ~(f = {}) /\ s IN c
            ==> affine_gp_3 f s)
     ==> (!f. f IN c /\ aff_dim f <= &1
              ==> DISJOINT (relative_frontier (convex hull {a,b,d})) f) /\
         (!f. f IN c /\ aff_dim f <= &0
              ==> DISJOINT (convex hull {a,b,d}) f)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6X_TRI_FACE_FACTS) THEN
  CONJ_TAC THEN X_GEN_TAC `f:real^3->bool` THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[DISJOINT_UNION] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC MOI_S6X_GP_LOW THEN ASM_REWRITE_TAC[] THEN
    (CONJ_TAC THENL
      [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[SEGMENT_EQ_EMPTY];
       ASM_INT_ARITH_TAC]);
    MATCH_MP_TAC MOI_S6X_GP_LOW THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[CONVEX_HULL_EQ_EMPTY; NOT_INSERT_EMPTY];
      ASM_INT_ARITH_TAC]]);;

(* The boundary of such a triangle meets a complex all of whose edges lie  *)
(* in an even number of triangles in an even number of points.              *)

let MOI_S6X_TRI_EVEN = prove
 (`!(c:(real^3->bool)->bool) a b d.
     FINITE c /\ simplicial_complex c /\ (!s. s IN c ==> aff_dim s <= &2) /\
     (!e. e IN c /\ aff_dim e = &1
          ==> EVEN (CARD {t | t IN c /\ aff_dim t = &2 /\ e SUBSET t})) /\
     ~collinear {a,b,d} /\
     (!f s. f face_of convex hull {a,b,d} /\ ~(f = {}) /\ s IN c
            ==> affine_gp_3 f s)
     ==> FINITE (relative_frontier (convex hull {a,b,d}) INTER UNIONS c) /\
         EVEN (CARD (relative_frontier (convex hull {a,b,d}) INTER UNIONS c))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `b:real^3`; `d:real^3`]
    MOI_S6X_FAN_LOW) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "l1") (LABEL_TAC "l0")) THEN
  UNDISCH_THEN
   `!f s:real^3->bool. f face_of convex hull {a:real^3,b,d} /\ ~(f = {}) /\
                       s IN c ==> affine_gp_3 f s` (LABEL_TAC "gp") THEN
  SUBGOAL_THEN `!f s:real^3->bool. s IN c /\ f face_of s ==> f IN c`
  (LABEL_TAC "clo") THENL
   [UNDISCH_TAC `simplicial_complex (c:(real^3->bool)->bool)` THEN
    REWRITE_TAC[simplicial_complex] THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `tt = convex hull {a:real^3,b,d}` THEN
  ABBREV_TAC `tri = {q:real^3->bool | q IN c /\ aff_dim q = &2}` THEN
  ABBREV_TAC `edg = {e:real^3->bool | e IN c /\ aff_dim e = &1}` THEN
  SUBGOAL_THEN `FINITE (tri:(real^3->bool)->bool) /\
                FINITE (edg:(real^3->bool)->bool)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "tri" THEN EXPAND_TAC "edg" THEN ASM_SIMP_TAC[FINITE_RESTRICT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!q:real^3->bool. q IN tri
      ==> FINITE (relative_frontier tt INTER q) /\
          FINITE (tt INTER relative_frontier q) /\
          EVEN (CARD (relative_frontier tt INTER q) +
                CARD (tt INTER relative_frontier q))`
  (LABEL_TAC "pq") THENL
   [X_GEN_TAC `q:real^3->bool` THEN EXPAND_TAC "tri" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `q:real^3->bool`] MOI_S6X_SC_TRI) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `va:real^3` (X_CHOOSE_THEN `vb:real^3`
      (X_CHOOSE_THEN `vc:real^3` STRIP_ASSUME_TAC))) THEN
    UNDISCH_THEN `q = convex hull {va:real^3,vb,vc}` SUBST_ALL_TAC THEN
    EXPAND_TAC "tt" THEN MATCH_MP_TAC MOI_S6X_PAIR THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`f:real^3->bool`; `g:real^3->bool`] THEN STRIP_TAC THEN
    USE_THEN "gp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "clo" MATCH_MP_TAC THEN
    EXISTS_TAC `convex hull {va:real^3,vb,vc}` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `relative_frontier tt INTER UNIONS c =
    UNIONS (IMAGE (\q:real^3->bool. relative_frontier tt INTER q) tri)`
  SUBST1_TAC THENL
   [EXPAND_TAC "tri" THEN
    REWRITE_TAC[UNIONS_IMAGE] THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `aff_dim (s:real^3->bool) <= &1` THENL
       [USE_THEN "l1" (MP_TAC o SPEC `s:real^3->bool`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
        UNDISCH_TAC `(x:real^3) IN s` THEN
        UNDISCH_TAC `(x:real^3) IN relative_frontier tt` THEN SET_TAC[];
        SUBGOAL_THEN `aff_dim (s:real^3->bool) <= &2` MP_TAC THENL
         [ASM_SIMP_TAC[]; ASM_INT_ARITH_TAC]];
      MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\q:real^3->bool. relative_frontier tt INTER q`;
                 `tri:(real^3->bool)->bool`] MOI_S6X_CARD_UNIONS_IMAGE) THEN
  ANTS_TAC THENL
   [BETA_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      X_GEN_TAC `q:real^3->bool` THEN DISCH_TAC THEN
      USE_THEN "pq" (MP_TAC o SPEC `q:real^3->bool`) THEN ASM_SIMP_TAC[];
      MAP_EVERY X_GEN_TAC [`q1:real^3->bool`; `q2:real^3->bool`] THEN
      EXPAND_TAC "tri" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `q1:real^3->bool`; `q2:real^3->bool`]
        MOI_S6X_SC_INTER_LOW) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      USE_THEN "l1" (MP_TAC o SPEC `q1 INTER q2:real^3->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC; SET_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> REWRITE_TAC[th]) SUBST1_TAC) THEN
  BETA_TAC THEN
  SUBGOAL_THEN
   `!q:real^3->bool. q IN tri
      ==> CARD (tt INTER relative_frontier q) =
          nsum {e | e IN edg /\ e SUBSET q} (\e. CARD (tt INTER e))`
  (LABEL_TAC "eq") THENL
   [X_GEN_TAC `q:real^3->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `FINITE (tt INTER relative_frontier q:real^3->bool)` ASSUME_TAC THENL
     [USE_THEN "pq" (MP_TAC o SPEC `q:real^3->bool`) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `relative_frontier q = UNIONS {e:real^3->bool | e IN edg /\ e SUBSET q}`
    (LABEL_TAC "rq") THENL
     [MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `q:real^3->bool`] MOI_S6X_SC_RELBD_TRI) THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `(q:real^3->bool) IN tri` THEN EXPAND_TAC "tri" THEN
        REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[];
        ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "edg" THEN
      REWRITE_TAC[IN_ELIM_THM; CONJ_ASSOC];
      ALL_TAC] THEN
    SUBGOAL_THEN `!e:real^3->bool. e IN edg /\ e SUBSET q
                    ==> tt INTER e SUBSET tt INTER relative_frontier q`
    ASSUME_TAC THENL
     [USE_THEN "rq" SUBST1_TAC THEN
      REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `tt INTER relative_frontier q =
                  UNIONS (IMAGE (\e:real^3->bool. tt INTER e)
                                {e | e IN edg /\ e SUBSET q})` SUBST1_TAC THENL
     [USE_THEN "rq" SUBST1_TAC THEN
      REWRITE_TAC[UNIONS_IMAGE] THEN
      REWRITE_TAC[EXTENSION; IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\e:real^3->bool. tt INTER e`;
                   `{e:real^3->bool | e IN edg /\ e SUBSET q}`]
      MOI_S6X_CARD_UNIONS_IMAGE) THEN
    ANTS_TAC THENL
     [BETA_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC[FINITE_RESTRICT];
        X_GEN_TAC `e:real^3->bool` THEN STRIP_TAC THEN
        MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `tt INTER relative_frontier q:real^3->bool` THEN
        ASM_SIMP_TAC[];
        MAP_EVERY X_GEN_TAC [`e1:real^3->bool`; `e2:real^3->bool`] THEN
        EXPAND_TAC "edg" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
        MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `e1:real^3->bool`; `e2:real^3->bool`]
          MOI_S6X_SC_INTER_LOW) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        USE_THEN "l0" (MP_TAC o SPEC `e1 INTER e2:real^3->bool`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC; SET_TAC[]]];
      DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `EVEN (nsum tri (\q:real^3->bool. CARD (tt INTER relative_frontier q)))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `nsum tri (\q:real^3->bool. CARD (tt INTER relative_frontier q)) =
      nsum tri (\q. nsum {e | e IN edg /\ e SUBSET q} (\e. CARD (tt INTER e)))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `q:real^3->bool` THEN DISCH_TAC THEN
      BETA_TAC THEN USE_THEN "eq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\q:real^3->bool e:real^3->bool. e SUBSET q`;
                   `\q:real^3->bool e:real^3->bool. CARD (tt INTER e)`;
                   `tri:(real^3->bool)->bool`; `edg:(real^3->bool)->bool`]
      NSUM_NSUM_RESTRICT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC MOI_FSA_EVEN_NSUM THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `e:real^3->bool` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[NSUM_CONST; FINITE_RESTRICT; EVEN_MULT] THEN DISJ1_TAC THEN
    SUBGOAL_THEN `{q:real^3->bool | q IN tri /\ e SUBSET q} =
                  {t | t IN c /\ aff_dim t = &2 /\ e SUBSET t}` SUBST1_TAC THENL
     [EXPAND_TAC "tri" THEN REWRITE_TAC[IN_ELIM_THM; CONJ_ASSOC];
      FIRST_X_ASSUM MATCH_MP_TAC THEN UNDISCH_TAC `(e:real^3->bool) IN edg` THEN
      EXPAND_TAC "edg" THEN REWRITE_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `EVEN (nsum tri (\q:real^3->bool. CARD (relative_frontier tt INTER q) +
                                     CARD (tt INTER relative_frontier q)))`
  MP_TAC THENL
   [MATCH_MP_TAC MOI_FSA_EVEN_NSUM THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `q:real^3->bool` THEN DISCH_TAC THEN BETA_TAC THEN
    USE_THEN "pq" (MP_TAC o SPEC `q:real^3->bool`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[NSUM_ADD; ASSUME `FINITE (tri:(real^3->bool)->bool)`; EVEN_ADD] THEN
  ASM_REWRITE_TAC[]);;

(* The convex hull of a subset of the ends of a segment in general position *)
(* with s whose ends avoid s is in general position with s.                 *)

let MOI_S6X_GP_SUBEDGE = prove
 (`!(u:real^3) v s t.
     ~(u IN s) /\ ~(v IN s) /\ affine_gp_3 (segment[u,v]) s /\ t SUBSET {u,v}
     ==> affine_gp_3 (convex hull t) s`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN2 SUBST1_TAC MP_TAC o MATCH_MP MOI_S6X_SUBSET_PAIR) THENL
   [REWRITE_TAC[CONVEX_HULL_EMPTY; affine_gp_3; DISJOINT_EMPTY]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC MP_TAC) THENL
   [REWRITE_TAC[CONVEX_HULL_SING; affine_gp_3] THEN DISJ1_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC SUBST1_TAC) THENL
   [REWRITE_TAC[CONVEX_HULL_SING; affine_gp_3] THEN DISJ1_TAC THEN ASM SET_TAC[];
    ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL]]);;

(* A generic cone point for a closed polygon: every fan triangle is         *)
(* nondegenerate and all its nonempty faces are in general position with    *)
(* every simplex of the complex.                                             *)

let MOI_S6X_APEX = prove
 (`!(c:(real^3->bool)->bool) (p:num->real^3) n.
     FINITE c /\ (!s. s IN c ==> aff_dim s <= &2) /\
     (!i. i < n ==> ~(p i = p (SUC i))) /\
     (!i. i <= n ==> ~(p i IN UNIONS c)) /\
     (!i s. i < n /\ s IN c ==> affine_gp_3 (segment[p i,p (SUC i)]) s)
     ==> ?a. !i. i < n
              ==> ~collinear {a, p i, p (SUC i)} /\
                  (!f s. f face_of convex hull {a, p i, p (SUC i)} /\
                         ~(f = {}) /\ s IN c ==> affine_gp_3 f s)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "dim")
    (CONJUNCTS_THEN2 (LABEL_TAC "dst") (CONJUNCTS_THEN2 (LABEL_TAC "out")
      (LABEL_TAC "seg"))))) THEN
  ABBREV_TAC `pt = {t:real^3->bool | ?i. i < n /\ t SUBSET {p i, p (SUC i)}}` THEN
  SUBGOAL_THEN `FINITE (pt:(real^3->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{t:real^3->bool | t SUBSET IMAGE (p:num->real^3) {i | i <= n}}` THEN
    SIMP_TAC[FINITE_POWERSET; FINITE_IMAGE; FINITE_NUMSEG_LE] THEN
    EXPAND_TAC "pt" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE] THEN
    X_GEN_TAC `t:real^3->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THENL
     [EXISTS_TAC `i:num`; EXISTS_TAC `SUC i`] THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `fs = {A:real^3->bool | A IN {affine hull (convex hull t UNION s) |
                                 t IN (pt:(real^3->bool)->bool) /\
                                 s IN (c:(real^3->bool)->bool)} /\
                           ~(A = (:real^3))} UNION
         {affine hull {(p:num->real^3) i, p (SUC i)} | i < n}` THEN
  SUBGOAL_THEN `FINITE (fs:(real^3->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "fs" THEN REWRITE_TAC[FINITE_UNION] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_RESTRICT THEN
      MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`fs:(real^3->bool)->bool`; `(:real^3)`] MOI_FGP_AVOID_AFFINE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[AFFINE_HULL_UNIV; UNIV_SUBSET] THEN
    EXPAND_TAC "fs" THEN REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN
    X_GEN_TAC `A:real^3->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
    ASM_REWRITE_TAC[AFFINE_AFFINE_HULL] THEN
    DISCH_THEN(MP_TAC o AP_TERM `aff_dim:(real^3->bool)->int`) THEN
    REWRITE_TAC[AFF_DIM_AFFINE_HULL; AFF_DIM_UNIV; DIMINDEX_3; AFF_DIM_2] THEN
    COND_CASES_TAC THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `(:real^3)`) THEN
  REWRITE_TAC[AFFINE_HULL_UNIV; OPEN_IN_REFL; UNIV_NOT_EMPTY; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^3` (LABEL_TAC "av")) THEN
  EXISTS_TAC `a:real^3` THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~((a:real^3) IN affine hull {p i, p (SUC i)})` ASSUME_TAC THENL
   [USE_THEN "av" MATCH_MP_TAC THEN EXPAND_TAC "fs" THEN
    REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN DISJ2_TAC THEN
    EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((p:num->real^3) i = p (SUC i))` ASSUME_TAC THENL
   [USE_THEN "dst" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~collinear {a:real^3, p i, p (SUC i)}` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[SET_RULE `{x:real^3,y,z} = {y,z,x}`] THEN
    ASM_SIMP_TAC[COLLINEAR_3_AFFINE_HULL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`f:real^3->bool`; `s:real^3->bool`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!t1:real^3->bool. t1 SUBSET {p i, p (SUC i)}
                  ==> affine_gp_3 (convex hull t1) s`
  (LABEL_TAC "sub") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S6X_GP_SUBEDGE THEN
    MAP_EVERY EXISTS_TAC [`(p:num->real^3) i`; `(p:num->real^3) (SUC i)`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~((p:num->real^3) i IN UNIONS c) /\ ~(p (SUC i) IN UNIONS c)`
    MP_TAC THENL
     [CONJ_TAC THEN USE_THEN "out" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[]; ASM_MESON_TAC[];
      USE_THEN "seg" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~affine_dependent {a:real^3, p i, p (SUC i)}` ASSUME_TAC THENL
   [UNDISCH_TAC `~collinear {a:real^3, p i, p (SUC i)}` THEN
    REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{a:real^3, p i, p (SUC i)}`; `f:real^3->bool`]
    FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real^3->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
  ASM_CASES_TAC `(a:real^3) IN t0` THENL
   [SUBGOAL_THEN `t0 = (a:real^3) INSERT (t0 DELETE a)` SUBST1_TAC THENL
     [UNDISCH_TAC `(a:real^3) IN t0` THEN SET_TAC[]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[HULL_INSERT] THEN
    MATCH_MP_TAC MOI_FGP_GP_ADD THEN EXISTS_TAC `(:real^3)` THEN
    REWRITE_TAC[CONVEX_CONVEX_HULL; CONVEX_UNIV; SUBSET_UNIV; IN_UNIV;
                MOI_FGP_GP_UNIV; AFFINE_HULL_UNIV; UNIV_SUBSET] THEN
    SUBGOAL_THEN `t0 DELETE (a:real^3) SUBSET {p i, p (SUC i)}` ASSUME_TAC THENL
     [UNDISCH_TAC `t0 SUBSET {a:real^3, p i, p (SUC i)}` THEN SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL [USE_THEN "sub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `affine hull (convex hull (t0 DELETE (a:real^3)) UNION s) = (:real^3)` THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "av" MATCH_MP_TAC THEN EXPAND_TAC "fs" THEN
    REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`t0 DELETE (a:real^3)`; `s:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "pt" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[];
    USE_THEN "sub" MATCH_MP_TAC THEN
    UNDISCH_TAC `t0 SUBSET {a:real^3, p i, p (SUC i)}` THEN
    UNDISCH_TAC `~((a:real^3) IN t0)` THEN SET_TAC[]]);;

(* One fan triangle conv{a,u,v}: the crossings of its three edges with the *)
(* complex are finite and their total number is even.                      *)

let MOI_S6X_FAN_STEP = prove
 (`!(c:(real^3->bool)->bool) a u v.
     FINITE c /\ simplicial_complex c /\ (!s. s IN c ==> aff_dim s <= &2) /\
     (!e. e IN c /\ aff_dim e = &1
          ==> EVEN (CARD {t | t IN c /\ aff_dim t = &2 /\ e SUBSET t})) /\
     ~collinear {a,u,v} /\
     (!f s. f face_of convex hull {a,u,v} /\ ~(f = {}) /\ s IN c
            ==> affine_gp_3 f s) /\
     ~(u IN UNIONS c) /\ ~(v IN UNIONS c)
     ==> FINITE (segment[u,v] INTER UNIONS c) /\
         FINITE (segment[a,u] INTER UNIONS c) /\
         FINITE (segment[a,v] INTER UNIONS c) /\
         EVEN (CARD (segment[u,v] INTER UNIONS c) +
               CARD (segment[a,u] INTER UNIONS c) +
               CARD (segment[a,v] INTER UNIONS c))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `u:real^3`; `v:real^3`]
    MOI_S6X_TRI_EVEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_THEN
   `!f s:real^3->bool. f face_of convex hull {a:real^3,u,v} /\ ~(f = {}) /\
                       s IN c ==> affine_gp_3 f s` (LABEL_TAC "gp") THEN
  UNDISCH_THEN `!s:real^3->bool. s IN c ==> aff_dim s <= &2` (LABEL_TAC "dim") THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6X_TRI_FACE_FACTS) THEN
  SUBGOAL_THEN `~((a:real^3) IN UNIONS c)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS; NOT_EXISTS_THM] THEN
    X_GEN_TAC `s:real^3->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`{a:real^3}`; `s:real^3->bool`] MOI_S6X_GP_LOW) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [USE_THEN "gp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[NOT_INSERT_EMPTY];
        ASM_REWRITE_TAC[] THEN
        USE_THEN "dim" (fun th -> MP_TAC(MATCH_MP th
          (ASSUME `(s:real^3->bool) IN c`))) THEN
        INT_ARITH_TAC];
      UNDISCH_TAC `(a:real^3) IN s` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[a,u] INTER segment[u,v] = {u:real^3}` ASSUME_TAC THENL
   [MATCH_MP_TAC INTER_SEGMENT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `segment[u,v] INTER segment[a,v] = {v:real^3}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`u:real^3`; `v:real^3`; `a:real^3`] INTER_SEGMENT) THEN
    ANTS_TAC THENL
     [DISJ2_TAC THEN UNDISCH_TAC `~collinear {a:real^3,u,v}` THEN
      MATCH_MP_TAC(TAUT `(p <=> q) ==> ~p ==> ~q`) THEN AP_TERM_TAC THEN SET_TAC[];
      REWRITE_TAC[CONJUNCT1 SEGMENT_SYM] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[a,u] INTER segment[a,v] = {a:real^3}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`u:real^3`; `a:real^3`; `v:real^3`] INTER_SEGMENT) THEN
    ANTS_TAC THENL
     [DISJ2_TAC THEN UNDISCH_TAC `~collinear {a:real^3,u,v}` THEN
      MATCH_MP_TAC(TAUT `(p <=> q) ==> ~p ==> ~q`) THEN AP_TERM_TAC THEN SET_TAC[];
      REWRITE_TAC[CONJUNCT1 SEGMENT_SYM] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `relative_frontier (convex hull {a,u,v}) INTER UNIONS c =
    (segment[u,v] INTER UNIONS c) UNION (segment[a,u] INTER UNIONS c) UNION
    (segment[a,v] INTER UNIONS (c:(real^3->bool)->bool))`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `segment[v,a] = segment[a,v:real^3]` SUBST1_TAC THENL
     [MATCH_ACCEPT_TAC (CONJUNCT1 SEGMENT_SYM); SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[FINITE_UNION] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(segment[u,v] INTER UNIONS c) INTER
    ((segment[a,u] INTER UNIONS c) UNION (segment[a,v] INTER UNIONS c)) = {} /\
    (segment[a,u] INTER UNIONS c) INTER
    (segment[a,v] INTER UNIONS (c:(real^3->bool)->bool)) = {}`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`segment[a,u] INTER segment[u,v] = {u:real^3}`;
      `segment[u,v] INTER segment[a,v] = {v:real^3}`;
      `segment[a,u] INTER segment[a,v] = {a:real^3}`;
      `~((u:real^3) IN UNIONS c)`; `~((v:real^3) IN UNIONS c)`;
      `~((a:real^3) IN UNIONS c)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD ((segment[u,v] INTER UNIONS c) UNION (segment[a,u] INTER UNIONS c) UNION
          (segment[a,v] INTER UNIONS c)) =
    CARD (segment[u,v] INTER UNIONS c) + CARD (segment[a,u] INTER UNIONS c) +
    CARD (segment[a,v] INTER UNIONS (c:(real^3->bool)->bool))`
  (fun th -> REWRITE_TAC[GSYM th] THEN ASM_REWRITE_TAC[]) THEN
  ASM_SIMP_TAC[CARD_UNION; FINITE_UNION]);;

(* The main theorem: the even crossing lemma (Moise Sec 26 Theorem 6,        *)
(* steps (1)-(5)).                                                           *)

let EVEN_CROSSING = prove
 (MOI_S26_EVEN_CROSSING,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[LT] THEN
    REWRITE_TAC[SET_RULE `{(i:num,x:real^3) | F} = {}`; FINITE_EMPTY; CARD_CLAUSES;
                EVEN];
    ALL_TAC] THEN
  UNDISCH_THEN
   `!i. i < n ==> ~((p:num->real^3) i = p (SUC i)) /\ ~(p i IN UNIONS c)`
   (LABEL_TAC "pp") THEN
  UNDISCH_THEN
   `!i s. i < n /\ s IN c ==> affine_gp_3 (segment[(p:num->real^3) i,p (SUC i)]) s`
   (LABEL_TAC "seg") THEN
  SUBGOAL_THEN `!i. i <= n ==> ~((p:num->real^3) i IN UNIONS c)` (LABEL_TAC "out")
  THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_CASES_TAC `i:num = n` THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "pp" (MP_TAC o SPEC `0`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
      USE_THEN "pp" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `p:num->real^3`; `n:num`] MOI_S6X_APEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "pp" (fun th -> MP_TAC(MATCH_MP th (ASSUME `i:num < n`))) THEN
    SIMP_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `a:real^3` (LABEL_TAC "fan"))] THEN
  SUBGOAL_THEN
   `!i. i < n
        ==> FINITE (segment[(p:num->real^3) i,p (SUC i)] INTER UNIONS c) /\
            FINITE (segment[a,p i] INTER UNIONS c) /\
            FINITE (segment[a,p (SUC i)] INTER UNIONS c) /\
            EVEN (CARD (segment[p i,p (SUC i)] INTER UNIONS c) +
                  CARD (segment[a,p i] INTER UNIONS c) +
                  CARD (segment[a,p (SUC i)] INTER UNIONS c))`
  (LABEL_TAC "per") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_S6X_FAN_STEP THEN
    USE_THEN "fan" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `i:num < n`)]) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN USE_THEN "out" MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `EVEN (nsum {i | i < n}
           (\i. CARD (segment[(p:num->real^3) i,p (SUC i)] INTER UNIONS c) +
                CARD (segment[a,p i] INTER UNIONS c) +
                CARD (segment[a,p (SUC i)] INTER UNIONS c)))`
  MP_TAC THENL
   [MATCH_MP_TAC MOI_FSA_EVEN_NSUM THEN REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "per" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `i:num < n`)]);
    ALL_TAC] THEN
  SIMP_TAC[NSUM_ADD; FINITE_NUMSEG_LT] THEN
  MP_TAC(ISPECL [`\i. CARD (segment[a:real^3,(p:num->real^3) i] INTER
                            UNIONS (c:(real^3->bool)->bool))`; `n:num`]
    MOI_S6X_NSUM_SHIFT) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`\i. segment[(p:num->real^3) i,p (SUC i)] INTER
                      UNIONS (c:(real^3->bool)->bool)`; `{i:num | i < n}`]
    MOI_S6X_CARD_SIGMA) THEN
  REWRITE_TAC[IN_ELIM_THM; IN_INTER; FINITE_NUMSEG_LT] THEN
  ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "per" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `i:num < n`)]);
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> REWRITE_TAC[th]) SUBST1_TAC) THEN
  REWRITE_TAC[EVEN_ADD]);;


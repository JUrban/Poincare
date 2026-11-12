(* ========================================================================= *)
(* pc_moi_s34_op1b: Moise Sec 34, Operation 1 with the compressing disk      *)
(* OUTSIDE the face ball (p.241, Lemma 6, the case the book omits).  Main    *)
(* theorem OP1_OUT_FROM_UNCLEAN : |- MOI_S4V_UNCLEAN ==> MOI_S34_OP1_OUT     *)
(* (pc_moi_s34_stmt.ml), where MOI_S4V_UNCLEAN (pc_moi_s34_op1bstmt.ml) is   *)
(* the unclean-pocket case, proved as UNCLEAN in pc_moi_s34_op1bu.ml.        *)
(* Route: the rim j of the disk d cuts the frontier sphere of the face ball  *)
(* c into two disks; d and one of them bound the pocket q (the theta lemma); *)
(* for a clean pocket the new ball is c UNION q pushed slightly beyond d,    *)
(* whose trace is the old trace minus j, so the H_1 clause survives by       *)
(* dropping the null-homologous component j.                                 *)
(* ========================================================================= *)

needs "src/pc_moi_s34_stmt.ml";;
needs "src/pc_moi_s34_op1bstmt.ml";;
needs "src/pc_moi_sch3_stmt.ml";;
needs "src/pc_moi_sch3_s2.ml";;
needs "src/pc_moi_sch3_push.ml";;
needs "src/pc_moi_s35_finb1.ml";;
needs "src/pc_moi_s35_charts.ml";;
needs "src/pc_moi_s27.ml";;
needs "src/pc_moi_fnd_tubea.ml";;
needs "src/pc_moi_fnd_gpb.ml";;
needs "src/pc_moi_plmap.ml";;
needs "src/pc_moi_polytope.ml";;
needs "src/pc_moi_s34_tinf.ml";;
needs "src/pc_moi_s34_l910.ml";;
needs "src/pc_moi_s34_fball.ml";;
needs "src/pc_moi_fnd_h1.ml";;
needs "src/pc_moi_s34_h1.ml";;
needs "src/pc_moi_s34_op1a.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Local and global sides of PL balls and spheres.  The outside              *)
(* of a polyhedron with nonempty interior is locally connected at frontier  *)
(* points (no two active facet normals are antiparallel), hence, by the     *)
(* ambient Schoenflies theorem, so is the outside of a PL 2-sphere.          *)
(* ------------------------------------------------------------------------- *)

let MOI_S4V_POLY_OUT_LOCAL = prove
 (`!k (y:real^N).
     polyhedron k /\ ~(interior k = {}) /\ y IN frontier k
     ==> ?r0. &0 < r0 /\ !r. &0 < r /\ r <= r0 ==> connected (ball(y,r) DIFF k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[polyhedron] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] o
    check (fun th -> is_forall(concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:(real^N->bool)->real^N`
    (X_CHOOSE_THEN `b:(real^N->bool)->real` (LABEL_TAC "ab"))) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    concl th = `k = INTERS (f:(real^N->bool)->bool)`)) THEN
  SUBGOAL_THEN `(y:real^N) IN k` ASSUME_TAC THENL
   [MP_TAC(ISPEC `k:real^N->bool` FRONTIER_SUBSET_CLOSED) THEN
    ANTS_TAC THENL
     [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `INTERS (f:(real^N->bool)->bool) = k`)) THEN
      MATCH_MP_TAC CLOSED_INTERS THEN
      X_GEN_TAC `h:real^N->bool` THEN DISCH_TAC THEN
      USE_THEN "ab" (MP_TAC o C MP (ASSUME `(h:real^N->bool) IN f`) o SPEC `h:real^N->bool`) THEN
      DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN REWRITE_TAC[CLOSED_HALFSPACE_LE];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  (* the inactive half-spaces contain a ball around y *)
  SUBGOAL_THEN
   `?r0. &0 < r0 /\
         !h. h IN f /\ (a:(real^N->bool)->real^N) h dot y < b h
             ==> ball(y:real^N,r0) SUBSET h`
  (X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THENL
   [SUBGOAL_THEN
     `open (INTERS {{x:real^N | (a:(real^N->bool)->real^N) h dot x < b h} | h |
                    h IN f /\ a h dot y < b h})`
    MP_TAC THENL
     [MATCH_MP_TAC OPEN_INTERS THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `IMAGE (\h. {x:real^N | (a:(real^N->bool)->real^N) h dot x < b h}) f` THEN
        ASM_SIMP_TAC[FINITE_IMAGE] THEN SET_TAC[];
        REWRITE_TAC[FORALL_IN_GSPEC; OPEN_HALFSPACE_LT]];
      ALL_TAC] THEN
    REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
    REWRITE_TAC[INTERS_GSPEC; IN_ELIM_THM] THEN
    ANTS_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `r0:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `h:real^N->bool` THEN STRIP_TAC THEN
    USE_THEN "ab" (MP_TAC o C MP (ASSUME `(h:real^N->bool) IN f`) o SPEC `h:real^N->bool`) THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
    UNDISCH_TAC `ball(y:real^N,r0) SUBSET
                 {x | !h. h IN f /\ (a:(real^N->bool)->real^N) h dot y < b h
                          ==> a h dot x < b h}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    DISCH_THEN(fun th -> X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      MP_TAC(SPEC `x:real^N` th)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `h:real^N->bool`) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `r0:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  (* y lies in every half-space *)
  SUBGOAL_THEN `!h. h IN f ==> (a:(real^N->bool)->real^N) h dot y <= b h`
  (LABEL_TAC "yin") THENL
   [X_GEN_TAC `h:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN h` MP_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`(y:real^N) IN k`; `INTERS (f:(real^N->bool)->bool) = k`;
                             `(h:real^N->bool) IN f`] THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "ab" (MP_TAC o C MP (ASSUME `(h:real^N->bool) IN f`) o SPEC `h:real^N->bool`) THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [CONJUNCT2 th]) THEN
    REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ball(y:real^N,r) DIFF k =
    UNIONS {ball(y,r) DIFF h | h | h IN f /\ (a:(real^N->bool)->real^N) h dot y = b h}`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_UNIONS; IN_DIFF; EXISTS_IN_GSPEC] THEN
      X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
      UNDISCH_TAC `~((x:real^N) IN k)` THEN
      FIRST_ASSUM(fun th -> if concl th = `INTERS (f:(real^N->bool)->bool) = k`
                            then REWRITE_TAC[SYM th] else NO_TAC) THEN
      REWRITE_TAC[IN_INTERS; NOT_FORALL_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `h:real^N->bool` MP_TAC) THEN
      REWRITE_TAC[NOT_IMP] THEN STRIP_TAC THEN
      EXISTS_TAC `h:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "yin" (MP_TAC o C MP (ASSUME `(h:real^N->bool) IN f`) o SPEC `h:real^N->bool`) THEN
      REWRITE_TAC[REAL_LE_LT] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `h:real^N->bool` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `ball(y:real^N,r0)`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(x:real^N) IN ball(y,r0)` MP_TAC THENL
       [UNDISCH_TAC `(x:real^N) IN ball(y,r)` THEN REWRITE_TAC[IN_BALL] THEN
        UNDISCH_TAC `r <= r0` THEN REAL_ARITH_TAC;
        ASM SET_TAC[]];
      REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
      X_GEN_TAC `h:real^N->bool` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(SET_RULE `!t. k SUBSET t ==> b DIFF t SUBSET (b:real^N->bool) DIFF k`) THEN
      UNDISCH_TAC `(h:real^N->bool) IN f` THEN
      UNDISCH_TAC `INTERS (f:(real^N->bool)->bool) = k` THEN SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_UNIONS_PAIRWISE THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `h:real^N->bool` THEN STRIP_TAC THEN
    USE_THEN "ab" (MP_TAC o C MP (ASSUME `(h:real^N->bool) IN f`) o SPEC `h:real^N->bool`) THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
    MATCH_MP_TAC CONVEX_CONNECTED THEN
    REWRITE_TAC[SET_RULE `(s:real^N->bool) DIFF {x | P x} = s INTER {x | ~P x}`] THEN
    MATCH_MP_TAC CONVEX_INTER THEN REWRITE_TAC[CONVEX_BALL; REAL_NOT_LE] THEN
    REWRITE_TAC[GSYM real_gt; CONVEX_HALFSPACE_GT];
    ALL_TAC] THEN
  REWRITE_TAC[pairwise; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
  X_GEN_TAC `h1:real^N->bool` THEN DISCH_TAC THEN DISCH_TAC THEN
  X_GEN_TAC `h2:real^N->bool` THEN DISCH_TAC THEN DISCH_TAC THEN
  DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  USE_THEN "ab" (MP_TAC o C MP (ASSUME `(h1:real^N->bool) IN f`) o SPEC `h1:real^N->bool`) THEN
  USE_THEN "ab" (MP_TAC o C MP (ASSUME `(h2:real^N->bool) IN f`) o SPEC `h2:real^N->bool`) THEN
  ABBREV_TAC `a1 = (a:(real^N->bool)->real^N) h1` THEN
  ABBREV_TAC `a2 = (a:(real^N->bool)->real^N) h2` THEN
  ABBREV_TAC `b1 = (b:(real^N->bool)->real) h1` THEN
  ABBREV_TAC `b2 = (b:(real^N->bool)->real) h2` THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  (* the active normals are not antiparallel *)
  SUBGOAL_THEN `&0 < norm(a1:real^N) * norm(a2:real^N) + a1 dot a2` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `~(x + y = &0) /\ abs y <= x ==> &0 < x + y`) THEN
    REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN DISCH_TAC THEN
    SUBGOAL_THEN `norm(a1:real^N) % --a2 = norm(a2:real^N) % a1` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`a1:real^N`; `--a2:real^N`] NORM_CAUCHY_SCHWARZ_EQ) THEN
      REWRITE_TAC[DOT_RNEG; NORM_NEG] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `norm(a1:real^N) * norm(a2:real^N) + a1 dot a2 = &0` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `k SUBSET {x:real^N | a1 dot x = b1}` MP_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `h1 INTER h2:real^N->bool` THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `(h1:real^N->bool) IN f` THEN UNDISCH_TAC `(h2:real^N->bool) IN f` THEN
        UNDISCH_TAC `INTERS (f:(real^N->bool)->bool) = k` THEN SET_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
      SUBGOAL_THEN `norm(a1:real^N) * ((a2:real^N) dot (x:real^N)) =
                    --(norm(a2:real^N) * ((a1:real^N) dot x)) /\
                    norm(a1:real^N) * ((a2:real^N) dot (y:real^N)) =
                    --(norm(a2:real^N) * ((a1:real^N) dot y))`
      STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[GSYM DOT_LMUL] THEN
        UNDISCH_TAC `norm(a1:real^N) % --a2 = norm(a2:real^N) % a1` THEN
        REWRITE_TAC[VECTOR_MUL_RNEG; VECTOR_ARITH `--x:real^N = y <=> x = --y`] THEN
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DOT_LNEG] THEN REWRITE_TAC[DOT_LMUL];
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 < norm(a1:real^N) /\ &0 < norm(a2:real^N)` STRIP_ASSUME_TAC THENL
       [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
      SUBGOAL_THEN `(a1:real^N) dot y = b1 /\ (a2:real^N) dot y = b2` STRIP_ASSUME_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `b1 <= (a1:real^N) dot (x:real^N)` MP_TAC THENL
       [SUBGOAL_THEN `norm(a2:real^N) * b1 <= norm a2 * ((a1:real^N) dot (x:real^N))` MP_TAC THENL
         [SUBGOAL_THEN `norm(a1:real^N) * ((a2:real^N) dot (x:real^N)) <= norm a1 * b2` MP_TAC THENL
           [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
            ALL_TAC] THEN
          UNDISCH_TAC `norm(a1:real^N) * ((a2:real^N) dot (x:real^N)) = --(norm(a2:real^N) * ((a1:real^N) dot x))` THEN
          UNDISCH_TAC `norm(a1:real^N) * ((a2:real^N) dot (y:real^N)) = --(norm(a2:real^N) * ((a1:real^N) dot y))` THEN
          ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
          ASM_SIMP_TAC[REAL_LE_LMUL_EQ]];
        UNDISCH_TAC `(a1:real^N) dot (x:real^N) <= b1` THEN REAL_ARITH_TAC];
      DISCH_THEN(MP_TAC o MATCH_MP SUBSET_INTERIOR) THEN
      ASM_SIMP_TAC[INTERIOR_HYPERPLANE] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  (* a common point beyond both active facets *)
  SUBGOAL_THEN `&0 < norm(a1:real^N) /\ &0 < norm(a2:real^N)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `u = inv(norm(a1:real^N)) % a1 + inv(norm(a2:real^N)) % a2` THEN
  ABBREV_TAC `t = r / (&2 * (norm(u:real^N) + &1))` THEN
  SUBGOAL_THEN `&0 < t /\ t * norm(u:real^N) < r` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `u:real^N` NORM_POS_LE) THEN REAL_ARITH_TAC;
      SIMP_TAC[REAL_FIELD `&0 <= n ==> r / (&2 * (n + &1)) * n = r * (n / (&2 * (n + &1)))`;
               NORM_POS_LE] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `u:real^N` NORM_POS_LE) THEN
      SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 <= n ==> &0 < &2 * (n + &1)`] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (a1:real^N) dot u /\ &0 < (a2:real^N) dot u` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[DOT_RADD; DOT_RMUL; DOT_SQUARE_NORM] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `inv(norm(a1:real^N)) * norm a1 pow 2 + inv(norm(a2:real^N)) * (a1 dot a2) =
                    (norm a1 * norm a2 + a1 dot a2) / norm a2` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < norm(a1:real^N)` THEN UNDISCH_TAC `&0 < norm(a2:real^N)` THEN
        CONV_TAC REAL_FIELD;
        MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]];
      ONCE_REWRITE_TAC[DOT_SYM] THEN
      SUBGOAL_THEN `inv(norm(a1:real^N)) * (a1 dot a2) + inv(norm(a2:real^N)) * norm a2 pow 2 =
                    (norm a1 * norm a2 + a1 dot a2) / norm a1` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < norm(a1:real^N)` THEN UNDISCH_TAC `&0 < norm(a2:real^N)` THEN
        CONV_TAC REAL_FIELD;
        MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `y + t % u:real^N` THEN
  ASM_REWRITE_TAC[IN_INTER; IN_DIFF; IN_BALL; IN_ELIM_THM; REAL_NOT_LE] THEN
  REWRITE_TAC[NORM_ARITH `dist(y:real^N,y + x) = norm x`; NORM_MUL; DOT_RADD; DOT_RMUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`] THEN
  CONJ_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 < y ==> b < b + y`) THEN
  ASM_SIMP_TAC[REAL_LT_MUL]);;

(* The outside of a PL 2-sphere is locally connected at its points: through *)
(* the ambient Schoenflies theorem the sphere becomes the boundary of a     *)
(* 3-simplex, where MOI_S4V_POLY_OUT_LOCAL applies.                         *)

let MOI_S4V_SPHERE_OUT_LOCAL = prove
 (`!s u (y:real^3).
     PL_SCHOENFLIES_3_AMBIENT_STATEMENT /\ pl_sphere 2 s /\ y IN s /\
     open u /\ y IN u
     ==> ?v cc. open v /\ y IN v /\ v SUBSET u /\ connected cc /\
                v INTER outside s SUBSET cc /\ cc SUBSET u INTER outside s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `(:real^3)`]
    (MATCH_MP MOI_SCD_COR_AMBIENT_BALL
      (ASSUME `PL_SCHOENFLIES_3_AMBIENT_STATEMENT`))) THEN
  ASM_REWRITE_TAC[CONVEX_UNIV; OPEN_UNIV; SUBSET_UNIV; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SCD_PL_HOMEO_UNIV) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SCD_FILLED_FRONTIER) THEN
  (* the simplex k: polyhedron with nonempty interior and frontier f(s) *)
  SUBGOAL_THEN `polyhedron (k:real^3->bool) /\ ~(interior k = {}) /\
                relative_frontier k = frontier k` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `~(interior (k:real^3->bool) = {})` ASSUME_TAC THENL
     [SUBGOAL_THEN `aff_dim (k:real^3->bool) = &(dimindex(:3))` MP_TAC THENL
       [REWRITE_TAC[DIMINDEX_3] THEN ASM_MESON_TAC[AFF_DIM_SIMPLEX];
        ASM_MESON_TAC[AFF_DIM_NONEMPTY_INTERIOR_EQ; SIMPLEX_IMP_CONVEX]];
      ASM_SIMP_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR] THEN
      ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE; POLYTOPE_IMP_POLYHEDRON]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN outside s <=> ~((f:real^3->real^3) x IN (k:real^3->bool))` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN
    UNDISCH_TAC `IMAGE (f:real^3->real^3) (s UNION inside s) = k` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `s UNION inside s = (:real^3) DIFF outside s` THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IN_IMAGE; IN_DIFF; IN_UNIV] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `(f:real^3->real^3) y`] MOI_S4V_POLY_OUT_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (f:real^3->real^3) s = relative_frontier k` THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `open (IMAGE (f:real^3->real^3) u)` MP_TAC THENL
   [MATCH_MP_TAC MOI_SCD_OPEN_HOMEO THEN EXISTS_TAC `g:real^3->real^3` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `(f:real^3->real^3) y` o REWRITE_RULE[OPEN_CONTAINS_BALL]) THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `r = min r0 r1` THEN
  SUBGOAL_THEN `&0 < r /\ r <= r0 /\ r <= r1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `IMAGE (g:real^3->real^3) (ball((f:real^3->real^3) y,r))` THEN
  EXISTS_TAC `IMAGE (g:real^3->real^3) (ball((f:real^3->real^3) y,r) DIFF k)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_SCD_OPEN_HOMEO THEN EXISTS_TAC `f:real^3->real^3` THEN
    REWRITE_TAC[OPEN_BALL] THEN ASM_MESON_TAC[HOMEOMORPHISM_SYM];
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(f:real^3->real^3) y` THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (g:real^3->real^3) (IMAGE (f:real^3->real^3) (u:real^3->bool))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `ball((f:real^3->real^3) y,r1)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_BALL THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]];
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    REWRITE_TAC[SUBSET; IN_INTER; IN_IMAGE; IN_DIFF] THEN
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    EXISTS_TAC `x':real^3` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^3) IN outside s` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; IN_INTER; FORALL_IN_IMAGE; IN_DIFF] THEN
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ball((f:real^3->real^3) y,r1) SUBSET IMAGE f (u:real^3->bool)` THEN
    REWRITE_TAC[SUBSET; IN_IMAGE] THEN DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN ball((f:real^3->real^3) y,r)` THEN
      REWRITE_TAC[IN_BALL] THEN UNDISCH_TAC `r <= r1` THEN REAL_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The theta lemma.  The rim j of a disk d that meets the ball               *)
(* c only in j cuts the frontier sphere of c into disks e, e'; d UNION e and *)
(* d UNION e' are PL spheres, and exactly one of them, say d UNION e, bounds *)
(* a ball q (the pocket) missing the interior of c; then c UNION q is the    *)
(* ball bounded by d UNION e'.                                               *)
(* ------------------------------------------------------------------------- *)

let MOI_S4V_CONNECTED_SIDE = prove
 (`!s t:real^N->bool.
     connected t /\ DISJOINT s t ==> t SUBSET inside s \/ t SUBSET outside s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`] INSIDE_OUTSIDE_INTERSECT_CONNECTED) THEN
  MP_TAC(ISPEC `s:real^N->bool` INSIDE_UNION_OUTSIDE) THEN ASM SET_TAC[]);;

let MOI_S4V_UNBOUNDED_OUTSIDE = prove
 (`!s t:real^N->bool.
     bounded s /\ connected t /\ ~bounded t /\ DISJOINT s t ==> t SUBSET outside s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`] MOI_S4V_CONNECTED_SIDE) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `~p ==> p \/ q ==> q`) THEN DISCH_TAC THEN
  UNDISCH_TAC `~bounded(t:real^N->bool)` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `inside s:real^N->bool` THEN
  ASM_SIMP_TAC[BOUNDED_INSIDE]);;

(* Facts on a PL 3-ball and on the ball bounded by a PL 2-sphere. *)

let MOI_S4V_BALL_SIDES = prove
 (`!c:real^3->bool.
     pl_ball 3 c
     ==> compact c /\ closed c /\ bounded c /\ pl_sphere 2 (frontier c) /\
         frontier c SUBSET c /\
         inside (frontier c) = interior c /\ frontier c UNION interior c = c /\
         outside (frontier c) = (:real^3) DIFF c /\
         open (interior c) /\ connected (interior c) /\ ~(interior c = {}) /\
         frontier c SUBSET closure (interior c) /\
         connected (outside (frontier c)) /\ ~bounded (outside (frontier c))`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5C_PL_BALL_3_FILL) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5C_JB_CLOSURE) THEN
  SUBGOAL_THEN `closed (c:real^3->bool) /\ bounded c` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED; COMPACT_IMP_BOUNDED]; ALL_TAC] THEN
  SUBGOAL_THEN `frontier c SUBSET (c:real^3->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FRONTIER_SUBSET_CLOSED]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(inside(frontier c:real^3->bool) = {})` ASSUME_TAC THENL
   [MP_TAC(ISPEC `frontier c:real^3->bool` MOI_S5C_PLSPH_JB) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `frontier c:real^3->bool` INSIDE_UNION_OUTSIDE) THEN
  MP_TAC(ISPEC `frontier c:real^3->bool` INSIDE_INTER_OUTSIDE) THEN
  UNDISCH_TAC `c = frontier c UNION inside(frontier c:real^3->bool)` THEN
  MP_TAC(ISPEC `frontier c:real^3->bool` OUTSIDE_NO_OVERLAP) THEN
  SET_TAC[]);;

let MOI_S4V_SPHERE_FILL = prove
 (`!s:real^3->bool.
     PL_SCHOENFLIES_3_STATEMENT /\ pl_sphere 2 s
     ==> pl_ball 3 (s UNION inside s) /\ frontier (s UNION inside s) = s /\
         interior (s UNION inside s) = inside s /\
         (:real^3) DIFF outside s = s UNION inside s /\
         compact (s UNION inside s) /\
         open (inside s) /\ connected (inside s) /\ bounded (inside s) /\
         ~(inside s = {}) /\ s SUBSET closure (inside s) /\
         open (outside s) /\ connected (outside s) /\ ~bounded (outside s) /\
         DISJOINT s (inside s) /\ DISJOINT s (outside s) /\
         DISJOINT (inside s) (outside s)`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_ball 3 (s UNION inside s:real^3->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `PL_SCHOENFLIES_3_STATEMENT` THEN
    REWRITE_TAC[PL_SCHOENFLIES_3_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SCD_FILLED_FRONTIER) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5C_JB_CLOSURE) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5C_PLSPH_JB) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `s UNION inside s = (:real^3) DIFF outside s` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC MOI_S4D_PL_BALL_COMPACT THEN EXISTS_TAC `3` THEN
    FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[DISJOINT; INSIDE_INTER_OUTSIDE]]);;

(* The glueing step: if the ball q bounded by d UNION e misses the interior *)
(* of c, every point of e off its rim is interior to c UNION q.              *)

let MOI_S4V_GLUE_FRONTIER = prove
 (`!c d j e e':real^3->bool.
     PL_SCHOENFLIES_3_STATEMENT /\ PL_SCHOENFLIES_3_AMBIENT_STATEMENT /\
     pl_ball 3 c /\ pl_cell_with_boundary 2 d j /\
     pl_cell_with_boundary 2 e j /\ pl_cell_with_boundary 2 e' j /\
     e UNION e' = frontier c /\ e INTER e' = j /\ d INTER frontier c = j /\
     pl_sphere 2 (d UNION e) /\
     interior c INTER ((d UNION e) UNION inside (d UNION e)) = {}
     ==> frontier (c UNION ((d UNION e) UNION inside (d UNION e))) SUBSET d UNION e'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `c:real^3->bool` MOI_S4V_BALL_SIDES) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `(d UNION e):real^3->bool` MOI_S4V_SPHERE_FILL) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(j:real^3->bool) SUBSET d /\ j SUBSET e /\ j SUBSET e' /\ closed d /\
                closed e /\ closed e'` STRIP_ASSUME_TAC THENL
   [MP_TAC(MATCH_MP MOI_S4L_PL_CELL2_TOPO
      (ASSUME `pl_cell_with_boundary 2 (d:real^3->bool) j`)) THEN
    MP_TAC(MATCH_MP MOI_S4L_PL_CELL2_TOPO
      (ASSUME `pl_cell_with_boundary 2 (e:real^3->bool) j`)) THEN
    MP_TAC(MATCH_MP MOI_S4L_PL_CELL2_TOPO
      (ASSUME `pl_cell_with_boundary 2 (e':real^3->bool) j`)) THEN
    SIMP_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `(frontier c UNION frontier ((d UNION e) UNION inside (d UNION e))) DIFF (e DIFF j:real^3->bool)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[ASSUME `frontier ((d UNION e) UNION inside (d UNION e)) = (d UNION e):real^3->bool`] THEN
    UNDISCH_TAC `e UNION e' = frontier c:real^3->bool` THEN
    UNDISCH_TAC `e INTER e' = j:real^3->bool` THEN
    UNDISCH_TAC `(j:real^3->bool) SUBSET d` THEN SET_TAC[]] THEN
  REWRITE_TAC[SUBSET; IN_DIFF] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`c:real^3->bool`; `((d UNION e) UNION inside (d UNION e)):real^3->bool`] FRONTIER_UNION_SUBSET) THEN
    UNDISCH_TAC `(y:real^3) IN frontier (c UNION ((d UNION e) UNION inside (d UNION e)))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[GSYM IN_DIFF]) THEN
  UNDISCH_TAC `(y:real^3) IN frontier (c UNION ((d UNION e) UNION inside (d UNION e)))` THEN
  REWRITE_TAC[frontier; IN_DIFF] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  REWRITE_TAC[] THEN
  (* y is interior to c UNION ((d UNION e) UNION inside (d UNION e)) *)
  SUBGOAL_THEN `~((y:real^3) IN d UNION e')` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN e DIFF j` THEN
    UNDISCH_TAC `e INTER e' = j:real^3->bool` THEN
    UNDISCH_TAC `d INTER frontier c = j:real^3->bool` THEN
    UNDISCH_TAC `e UNION e' = frontier c:real^3->bool` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(d UNION e):real^3->bool`; `(:real^3) DIFF (d UNION e')`; `y:real^3`]
    MOI_S4V_SPHERE_OUT_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN e DIFF j` THEN SET_TAC[];
      MATCH_MP_TAC OPEN_DIFF THEN REWRITE_TAC[OPEN_UNIV] THEN
      MATCH_MP_TAC CLOSED_UNION THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^3->bool` (X_CHOOSE_THEN `cc:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  (* cc misses the frontier of c, so it lies in int c or outside it *)
  SUBGOAL_THEN `DISJOINT (frontier c) (cc:real^3->bool)` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`cc SUBSET ((:real^3) DIFF (d UNION e')) INTER outside (d UNION e)`;
      `DISJOINT (d UNION e) (outside (d UNION e):real^3->bool)`;
      `e UNION e' = frontier c:real^3->bool`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(cc:real^3->bool) SUBSET interior c` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`frontier c:real^3->bool`; `cc:real^3->bool`]
      MOI_S4V_CONNECTED_SIDE) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `inside (frontier c) = interior (c:real^3->bool)`] THEN
    MATCH_MP_TAC(TAUT `~q ==> p \/ q ==> p`) THEN DISCH_TAC THEN
    (* a point of int c near y lies in cc *)
    SUBGOAL_THEN `?z:real^3. z IN v /\ z IN interior c` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `frontier c SUBSET closure (interior c:real^3->bool)` THEN
      REWRITE_TAC[SUBSET; CLOSURE_APPROACHABLE] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `(y:real^3) IN e DIFF j` THEN
        UNDISCH_TAC `e UNION e' = frontier c:real^3->bool` THEN SET_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPEC `v:real^3->bool` OPEN_CONTAINS_BALL) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
      DISCH_THEN(MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `ball(y:real^3,r) SUBSET v` THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
      DISCH_THEN MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^3) IN outside (d UNION e)` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`interior c INTER ((d UNION e) UNION inside (d UNION e)) = {}:real^3->bool`;
        `(z:real^3) IN interior c`;
        `(:real^3) DIFF outside (d UNION e) = (d UNION e) UNION inside (d UNION e)`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPEC `c:real^3->bool` INTERIOR_SUBSET) THEN
    MAP_EVERY UNDISCH_TAC
     [`(cc:real^3->bool) SUBSET outside (frontier c)`;
      `v INTER outside (d UNION e) SUBSET (cc:real^3->bool)`; `(z:real^3) IN v`;
      `(z:real^3) IN interior c`; `(z:real^3) IN outside (d UNION e)`;
      `outside (frontier c) = (:real^3) DIFF (c:real^3->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_INTERIOR] THEN
  MP_TAC(ISPEC `v:real^3->bool` OPEN_CONTAINS_BALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `c:real^3->bool` INTERIOR_SUBSET) THEN
  MAP_EVERY UNDISCH_TAC
   [`ball(y:real^3,r) SUBSET v`; `v INTER outside (d UNION e) SUBSET (cc:real^3->bool)`;
    `(cc:real^3->bool) SUBSET interior c`;
    `(:real^3) DIFF outside (d UNION e) = (d UNION e) UNION inside (d UNION e)`] THEN
  SET_TAC[]);;

(* The pocket from the side information: int c outside d UNION e and inside *)
(* d UNION e'.                                                               *)

let MOI_S4V_POCKET_FROM = prove
 (`!c d j e e':real^3->bool.
     PL_SCHOENFLIES_3_STATEMENT /\ PL_SCHOENFLIES_3_AMBIENT_STATEMENT /\
     pl_ball 3 c /\ pl_cell_with_boundary 2 d j /\
     pl_cell_with_boundary 2 e j /\ pl_cell_with_boundary 2 e' j /\
     e UNION e' = frontier c /\ e INTER e' = j /\ d INTER frontier c = j /\
     DISJOINT (d DIFF j) c /\
     pl_sphere 2 (d UNION e) /\ pl_sphere 2 (d UNION e') /\
     interior c SUBSET outside (d UNION e) /\
     interior c SUBSET inside (d UNION e')
     ==> moi_s4v_pocket c d j ((d UNION e) UNION inside (d UNION e)) e e'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `c:real^3->bool` MOI_S4V_BALL_SIDES) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `(d UNION e):real^3->bool` MOI_S4V_SPHERE_FILL) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `(d UNION e'):real^3->bool` MOI_S4V_SPHERE_FILL) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(j:real^3->bool) SUBSET d /\ j SUBSET e /\ j SUBSET e' /\
                connected (e' DIFF j:real^3->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4L_PL_CELL2_TOPO; MOI_SS2_CELL_FACTS];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior c INTER ((d UNION e) UNION inside (d UNION e)) = {}:real^3->bool` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`interior c SUBSET outside ((d UNION e):real^3->bool)`;
      `(:real^3) DIFF outside (d UNION e) = (d UNION e) UNION inside (d UNION e)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* e' minus its rim lies outside (d UNION e) *)
  SUBGOAL_THEN `e' DIFF j SUBSET outside ((d UNION e):real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(d UNION e):real^3->bool`; `e' DIFF j:real^3->bool`] MOI_S4V_CONNECTED_SIDE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MAP_EVERY UNDISCH_TAC
       [`e INTER e' = j:real^3->bool`; `d INTER frontier c = j:real^3->bool`;
        `e UNION e' = frontier c:real^3->bool`] THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `~p ==> p \/ q ==> q`) THEN DISCH_TAC THEN
    ASM_CASES_TAC `e' DIFF j = {}:real^3->bool` THENL
     [ASM_MESON_TAC[MOI_S4L_PL_CELL2_TOPO]; ALL_TAC] THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `y:real^3` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
    SUBGOAL_THEN `(y:real^3) IN closure (interior c)` MP_TAC THENL
     [UNDISCH_TAC `frontier c SUBSET closure (interior c:real^3->bool)` THEN
      UNDISCH_TAC `(y:real^3) IN e' DIFF j` THEN
      UNDISCH_TAC `e UNION e' = frontier c:real^3->bool` THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
    MP_TAC(ISPEC `inside (d UNION e):real^3->bool` OPEN_CONTAINS_BALL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(z:real^3) IN inside (d UNION e)` ASSUME_TAC THENL
     [UNDISCH_TAC `ball(y:real^3,r) SUBSET inside (d UNION e)` THEN
      REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
      ONCE_REWRITE_TAC[DIST_SYM] THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`interior c INTER ((d UNION e) UNION inside (d UNION e)) = {}:real^3->bool`; `(z:real^3) IN interior c`;
      `(z:real^3) IN inside (d UNION e)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* c UNION ((d UNION e) UNION inside (d UNION e)) is the ball ((d UNION e') UNION inside (d UNION e')) bounded by d UNION e' *)
  SUBGOAL_THEN `frontier (c UNION ((d UNION e) UNION inside (d UNION e))) SUBSET ((d UNION e'):real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4V_GLUE_FRONTIER THEN EXISTS_TAC `j:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `c UNION ((d UNION e) UNION inside (d UNION e)) = ((d UNION e') UNION inside (d UNION e')):real^3->bool` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [(* c and ((d UNION e) UNION inside (d UNION e)) lie in ((d UNION e') UNION inside (d UNION e')) *)
      SUBGOAL_THEN `(c:real^3->bool) SUBSET ((d UNION e') UNION inside (d UNION e'))` ASSUME_TAC THENL
       [UNDISCH_TAC `frontier c UNION interior c = (c:real^3->bool)` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
         [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `closure(interior c:real^3->bool)` THEN
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THENL
           [MAP_EVERY UNDISCH_TAC [`interior c SUBSET inside ((d UNION e'):real^3->bool)`] THEN
            SET_TAC[];
            MATCH_MP_TAC COMPACT_IMP_CLOSED THEN FIRST_ASSUM ACCEPT_TAC];
          UNDISCH_TAC `interior c SUBSET inside ((d UNION e'):real^3->bool)` THEN
          SET_TAC[]];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[UNION_SUBSET] THEN
      SUBGOAL_THEN `outside (d UNION e') SUBSET outside ((d UNION e):real^3->bool)` MP_TAC THENL
       [MATCH_MP_TAC MOI_S4V_UNBOUNDED_OUTSIDE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN
          MP_TAC(MATCH_MP MOI_S5C_PLSPH_JB
            (ASSUME `pl_sphere 2 (d UNION e:real^3->bool)`)) THEN SIMP_TAC[];
          SUBGOAL_THEN `((d UNION e):real^3->bool) SUBSET ((d UNION e') UNION inside (d UNION e'))` MP_TAC THENL
           [REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
             [SET_TAC[];
              MAP_EVERY UNDISCH_TAC [`(c:real^3->bool) SUBSET ((d UNION e') UNION inside (d UNION e'))`;
                                     `frontier c SUBSET (c:real^3->bool)`;
                                     `e UNION e' = frontier c:real^3->bool`] THEN
              SET_TAC[]];
            MAP_EVERY UNDISCH_TAC [`(:real^3) DIFF outside (d UNION e') = (d UNION e') UNION inside (d UNION e')`] THEN
            SET_TAC[]]];
        MAP_EVERY UNDISCH_TAC [`(:real^3) DIFF outside (d UNION e) = (d UNION e) UNION inside (d UNION e)`;
                               `(:real^3) DIFF outside (d UNION e') = (d UNION e') UNION inside (d UNION e')`] THEN
        SET_TAC[]];
      (* ((d UNION e') UNION inside (d UNION e')) lies in c UNION ((d UNION e) UNION inside (d UNION e)) *)
      REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`frontier c SUBSET (c:real^3->bool)`;
                               `e UNION e' = frontier c:real^3->bool`] THEN
        SET_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`inside (d UNION e'):real^3->bool`;
                     `c UNION ((d UNION e) UNION inside (d UNION e)):real^3->bool`]
        CONNECTED_INTER_FRONTIER) THEN
      MATCH_MP_TAC(TAUT `a /\ b /\ c /\ ~d ==> (a /\ b /\ c ==> d) ==> F`) THEN
      REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        MP_TAC(ISPEC `c:real^3->bool` INTERIOR_SUBSET) THEN
        MAP_EVERY UNDISCH_TAC [`interior c SUBSET inside ((d UNION e'):real^3->bool)`;
                               `~(interior c = {}:real^3->bool)`] THEN SET_TAC[];
        UNDISCH_TAC `~(inside (d UNION e') SUBSET
                       c UNION ((d UNION e) UNION inside (d UNION e)):real^3->bool)` THEN
        SET_TAC[];
        MAP_EVERY UNDISCH_TAC
         [`frontier (c UNION ((d UNION e) UNION inside (d UNION e))) SUBSET
           ((d UNION e'):real^3->bool)`;
          `DISJOINT (d UNION e') (inside (d UNION e'):real^3->bool)`] THEN
        SET_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s4v_pocket] THEN ASM_REWRITE_TAC[] THEN
  (* ((d UNION e) UNION inside (d UNION e)) INTER c = e *)
  MAP_EVERY UNDISCH_TAC
   [`interior c INTER ((d UNION e) UNION inside (d UNION e)) = {}:real^3->bool`; `e' DIFF j SUBSET outside ((d UNION e):real^3->bool)`;
    `(:real^3) DIFF outside (d UNION e) = (d UNION e) UNION inside (d UNION e)`;
    `frontier c UNION interior c = (c:real^3->bool)`;
    `e UNION e' = frontier c:real^3->bool`; `(j:real^3->bool) SUBSET e`] THEN
  SET_TAC[]);;

(* Two helpers for the theta lemma. *)

let MOI_S4V_BALL_IN_FILL = prove
 (`!c s:real^3->bool.
     PL_SCHOENFLIES_3_STATEMENT /\ pl_ball 3 c /\ pl_sphere 2 s /\
     interior c SUBSET inside s
     ==> c SUBSET s UNION inside s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `c:real^3->bool` MOI_S4V_BALL_SIDES) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^3->bool` MOI_S4V_SPHERE_FILL) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `frontier c UNION interior c = (c:real^3->bool)` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `closure(interior c:real^3->bool)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THENL
     [UNDISCH_TAC `interior c SUBSET inside (s:real^3->bool)` THEN SET_TAC[];
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN FIRST_ASSUM ACCEPT_TAC];
    UNDISCH_TAC `interior c SUBSET inside (s:real^3->bool)` THEN SET_TAC[]]);;

let MOI_S4V_FILL_MONO = prove
 (`!s t:real^3->bool.
     PL_SCHOENFLIES_3_STATEMENT /\ pl_sphere 2 s /\ pl_sphere 2 t /\
     s SUBSET t UNION inside t
     ==> s UNION inside s SUBSET t UNION inside t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^3->bool` MOI_S4V_SPHERE_FILL) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `t:real^3->bool` MOI_S4V_SPHERE_FILL) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `outside t SUBSET outside (s:real^3->bool)` MP_TAC THENL
   [MATCH_MP_TAC MOI_S4V_UNBOUNDED_OUTSIDE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN
      MP_TAC(MATCH_MP MOI_S5C_PLSPH_JB (ASSUME `pl_sphere 2 (s:real^3->bool)`)) THEN
      SIMP_TAC[];
      MAP_EVERY UNDISCH_TAC [`(s:real^3->bool) SUBSET t UNION inside t`;
                             `(:real^3) DIFF outside t = t UNION inside t`] THEN
      SET_TAC[]];
    MAP_EVERY UNDISCH_TAC [`(:real^3) DIFF outside s = s UNION inside s`;
                           `(:real^3) DIFF outside t = t UNION inside t`] THEN
    SET_TAC[]]);;

(* The theta lemma. *)

let MOI_S4V_THETA = prove
 (`!c d j:real^3->bool.
     PL_SCHOENFLIES_3_STATEMENT /\ PL_SCHOENFLIES_3_AMBIENT_STATEMENT /\
     pl_ball 3 c /\ pl_cell_with_boundary 2 d j /\ d INTER frontier c = j /\
     DISJOINT (d DIFF j) c
     ==> ?q e e'. moi_s4v_pocket c d j q e e'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `c:real^3->bool` MOI_S4V_BALL_SIDES) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(j:real^3->bool) SUBSET d /\ pl_sphere 1 j` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4L_PL_CELL2_TOPO; MOI_S5E_CELL_SPHERE1];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`frontier c:real^3->bool`; `j:real^3->bool`] SPHERE_SPLIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `d INTER frontier c = j:real^3->bool` THEN SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `e1:real^3->bool` (X_CHOOSE_THEN `e2:real^3->bool`
      STRIP_ASSUME_TAC))] THEN
  SUBGOAL_THEN `(j:real^3->bool) SUBSET e1 /\ j SUBSET e2 /\
                ~(e1 DIFF j = {}) /\ ~(e2 DIFF j = {})` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4L_PL_CELL2_TOPO]; ALL_TAC] THEN
  SUBGOAL_THEN `pl_sphere 2 (d UNION e1:real^3->bool) /\ pl_sphere 2 (d UNION e2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC DISK_UNION THEN EXISTS_TAC `j:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`d INTER frontier c = j:real^3->bool`;
                           `e1 UNION e2 = frontier c:real^3->bool`;
                           `(j:real^3->bool) SUBSET d`; `(j:real^3->bool) SUBSET e1`;
                           `(j:real^3->bool) SUBSET e2`] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `d UNION e1:real^3->bool` MOI_S4V_SPHERE_FILL) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `d UNION e2:real^3->bool` MOI_S4V_SPHERE_FILL) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  (* int c lies on one side of each sphere *)
  SUBGOAL_THEN `!e:real^3->bool. e SUBSET frontier c
                  ==> DISJOINT (d UNION e) (interior c)` ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPEC `c:real^3->bool` INTERIOR_SUBSET) THEN
    MAP_EVERY UNDISCH_TAC [`DISJOINT (d DIFF j) (c:real^3->bool)`;
                           `d INTER frontier c = j:real^3->bool`;
                           `(e:real^3->bool) SUBSET frontier c`] THEN
    REWRITE_TAC[frontier] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`d UNION e1:real^3->bool`; `interior c:real^3->bool`]
    MOI_S4V_CONNECTED_SIDE) THEN
  MP_TAC(ISPECL [`d UNION e2:real^3->bool`; `interior c:real^3->bool`]
    MOI_S4V_CONNECTED_SIDE) THEN
  ASM_SIMP_TAC[SUBSET_UNION] THEN
  SUBGOAL_THEN `(e1:real^3->bool) SUBSET frontier c /\ e2 SUBSET frontier c`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  (* not both inside *)
  SUBGOAL_THEN `~(interior c SUBSET inside (d UNION e1:real^3->bool) /\
                  interior c SUBSET inside (d UNION e2))` ASSUME_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `(c:real^3->bool) SUBSET (d UNION e1) UNION inside (d UNION e1) /\
                  c SUBSET (d UNION e2) UNION inside (d UNION e2)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC MOI_S4V_BALL_IN_FILL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(d UNION e1) UNION inside (d UNION e1) =
                  (d UNION e2) UNION inside (d UNION e2:real^3->bool)` MP_TAC THENL
     [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN MATCH_MP_TAC MOI_S4V_FILL_MONO THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`(c:real^3->bool) SUBSET (d UNION e1) UNION inside (d UNION e1)`;
                             `(c:real^3->bool) SUBSET (d UNION e2) UNION inside (d UNION e2)`;
                             `frontier c SUBSET (c:real^3->bool)`;
                             `e1 UNION e2 = frontier c:real^3->bool`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `frontier:(real^3->bool)->real^3->bool`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(e1 DIFF j = {}:real^3->bool)` THEN REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`d UNION e1 = d UNION e2:real^3->bool`;
                           `d INTER frontier c = j:real^3->bool`;
                           `e1 UNION e2 = frontier c:real^3->bool`;
                           `e1 INTER e2 = j:real^3->bool`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* not both outside *)
  SUBGOAL_THEN `~(interior c SUBSET outside (d UNION e1:real^3->bool) /\
                  interior c SUBSET outside (d UNION e2))` ASSUME_TAC THENL
   [STRIP_TAC THEN
    MP_TAC(ISPECL [`c:real^3->bool`; `d:real^3->bool`; `j:real^3->bool`;
                   `e1:real^3->bool`; `e2:real^3->bool`] MOI_S4V_GLUE_FRONTIER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`interior c SUBSET outside (d UNION e1:real^3->bool)`;
                             `(:real^3) DIFF outside (d UNION e1) =
                              (d UNION e1) UNION inside (d UNION e1:real^3->bool)`] THEN
      SET_TAC[];
      DISCH_TAC] THEN
    MP_TAC(ISPECL [`outside (d UNION e2):real^3->bool`;
                   `c UNION (d UNION e1) UNION inside (d UNION e1):real^3->bool`]
      CONNECTED_INTER_FRONTIER) THEN
    MATCH_MP_TAC(TAUT `a /\ b /\ c /\ ~d ==> (a /\ b /\ c ==> d) ==> F`) THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      MP_TAC(ISPEC `c:real^3->bool` INTERIOR_SUBSET) THEN
      MAP_EVERY UNDISCH_TAC [`interior c SUBSET outside (d UNION e2:real^3->bool)`;
                             `~(interior c = {}:real^3->bool)`] THEN SET_TAC[];
      DISCH_TAC THEN
      UNDISCH_TAC `~bounded(outside (d UNION e2:real^3->bool))` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC BOUNDED_SUBSET THEN
      EXISTS_TAC `c UNION (d UNION e1) UNION inside (d UNION e1):real^3->bool` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN MATCH_MP_TAC COMPACT_UNION THEN
        CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        UNDISCH_TAC `outside (d UNION e2) DIFF
                     (c UNION (d UNION e1) UNION inside (d UNION e1)) = {}:real^3->bool` THEN
        SET_TAC[]];
      MAP_EVERY UNDISCH_TAC
       [`frontier (c UNION (d UNION e1) UNION inside (d UNION e1)) SUBSET
         (d UNION e2:real^3->bool)`;
        `DISJOINT (d UNION e2) (outside (d UNION e2:real^3->bool))`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
   [UNDISCH_TAC `~(interior c SUBSET inside (d UNION e1:real^3->bool) /\
                   interior c SUBSET inside (d UNION e2))` THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`(d UNION e1) UNION inside (d UNION e1:real^3->bool)`;
                          `e1:real^3->bool`; `e2:real^3->bool`] THEN
    MATCH_MP_TAC MOI_S4V_POCKET_FROM THEN ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`(d UNION e2) UNION inside (d UNION e2:real^3->bool)`;
                          `e2:real^3->bool`; `e1:real^3->bool`] THEN
    MATCH_MP_TAC MOI_S4V_POCKET_FROM THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[UNION_COMM; INTER_COMM] THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `~(interior c SUBSET outside (d UNION e1:real^3->bool) /\
                   interior c SUBSET outside (d UNION e2))` THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Near the outside compressing disk d.  The tube boundary B                *)
(* meets the complement of int c near d only in d (MOI_S4V_KEY_OUT, as op1a *)
(* MOI_S4N_KEY with the crossing charts applied to the closure of the       *)
(* complement of c); the other face balls are avoided near points of car s *)
(* outside them (MOI_S4V_FB_AVOID); the open set O of the outward push      *)
(* (MOI_S4V_O_CHOICE).                                                       *)
(* ------------------------------------------------------------------------- *)

let MOI_S4V_KEY_OUT = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v d j.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fbinv tt kk h f1 car cb /\ s IN moi_s34_simp kk (&2) /\
     moi_s34_op1w tt kk f1 cb s v d j /\ DISJOINT (d DIFF j) (cb s)
     ==> !y. y IN d ==> ?u. open u /\ y IN u /\
                            u INTER IMAGE f1 (moi_s34_bd tt kk) SUBSET
                            d UNION interior (cb s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  UNDISCH_TAC `moi_s34_op1w tt kk (f1:real^N->real^3) cb s v d j` THEN
  REWRITE_TAC[moi_s34_op1w] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`] MOI_S4L_TRACE_COMP_FACTS) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[moi_s34_fb1] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `v:real^N`] MOI_S4L_AV_BASIC) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  ABBREV_TAC `c = (cb:(real^N->bool)->real^3->bool) s` THEN
  ABBREV_TAC `B = IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)` THEN
  ABBREV_TAC `Av = IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
  ABBREV_TAC `S = frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v))` THEN
  (* y lies in no other vertex ball *)
  SUBGOAL_THEN `!w. {w} IN kk /\ ~(w = v)
                    ==> ~((y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w))`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `v:real^N`; `w:real^N`;
                   `y:real^3`] MOI_S4L_AV_NO_OTHER) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      UNDISCH_TAC `(y:real^3) IN d` THEN UNDISCH_TAC `(d:real^3->bool) SUBSET Av` THEN
      EXPAND_TAC "Av" THEN SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[moi_s34_rims; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `g:real^N->bool` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s34_sd")) (concl th) &&
      can (find_term ((=) `DISJOINT:(real^3->bool)->(real^3->bool)->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`(y:real^3) IN t`; `(y:real^3) IN d`] THEN
    REWRITE_TAC[ASSUME `t = IMAGE (f1:real^N->real^3)
                              (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the local form of B near y *)
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `v:real^N`; `y:real^3`]
    MOI_S4L_LOCAL_AV) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    UNDISCH_TAC `(y:real^3) IN d` THEN UNDISCH_TAC `(d:real^3->bool) SUBSET Av` THEN
    EXPAND_TAC "Av" THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[ASSUME `IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) = B`;
              ASSUME `IMAGE (f1:real^N->real^3)
                        (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) = Av`] THEN
  DISCH_THEN(X_CHOOSE_THEN `oo:real^3->bool` STRIP_ASSUME_TAC) THEN
  (* the vertex sphere and the complementary disk *)
  SUBGOAL_THEN `(Av:real^3->bool) SUBSET S /\ pl_sphere 2 S` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `(S:real^3->bool) =
                   Av UNION UNIONS {IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) | g |
                                    g IN moi_s34_simp kk (&1) /\ v IN g}` THEN
      SET_TAC[];
      EXPAND_TAC "S" THEN MATCH_MP_TAC MOI_S4L_BALL_FRONTIER_SPHERE THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(d:real^3->bool) SUBSET S /\ d SUBSET B` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(d:real^3->bool) SUBSET Av`; `(Av:real^3->bool) SUBSET S`;
                           `(Av:real^3->bool) SUBSET B`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `d:real^3->bool`; `j:real^3->bool`] DISK_COMPLEMENT) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  ABBREV_TAC `E = ((S:real^3->bool) DIFF d) UNION j` THEN
  MP_TAC(MATCH_MP MOI_S4L_PL_CELL2_TOPO
    (ASSUME `pl_cell_with_boundary 2 (d:real^3->bool) j`)) THEN STRIP_TAC THEN
  SUBGOAL_THEN `closed (E:real^3->bool) /\ closed (d:real^3->bool)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THENL
     [MP_TAC(MATCH_MP MOI_S4L_PL_CELL2_TOPO
        (ASSUME `pl_cell_with_boundary 2 (E:real^3->bool) j`)) THEN SIMP_TAC[];
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(S:real^3->bool) DIFF E SUBSET d /\ d INTER E = j`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN UNDISCH_TAC `(j:real^3->bool) SUBSET d` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(y:real^3) IN j` THENL
   [(* on the rim: the crossing chart, for the closure of the complement of c *)
    MP_TAC(ISPEC `c:real^3->bool` MOI_S4V_BALL_SIDES) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `closure (interior c) = (c:real^3->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[INTERIOR_SUBSET];
        UNDISCH_TAC `frontier c UNION interior c = (c:real^3->bool)` THEN
        DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
        ASM_REWRITE_TAC[UNION_SUBSET; CLOSURE_SUBSET]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`(:real^3) DIFF interior c`; `B:real^3->bool`; `S:real^3->bool`;
                   `d:real^3->bool`; `E:real^3->bool`; `y:real^3`; `oo:real^3->bool`]
      MOI_S4N_CROSS_DISK) THEN
    SUBGOAL_THEN `frontier ((:real^3) DIFF interior c) = frontier c` ASSUME_TAC THENL
     [REWRITE_TAC[FRONTIER_COMPLEMENT; frontier; INTERIOR_INTERIOR] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `c:real^3->bool` CLOSURE_CLOSED) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^3) IN frontier c` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`(y:real^3) IN j`; `d INTER frontier c = (j:real^3->bool)`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[GSYM OPEN_CLOSED; OPEN_INTERIOR];
        UNDISCH_TAC `!x. x IN moi_s34_trace tt kk (f1:real^N->real^3) c
                         ==> pl_crossing_at (frontier c) B x` THEN
        REWRITE_TAC[moi_s34_trace; ASSUME `IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) = B`] THEN
        DISCH_THEN MATCH_MP_TAC THEN
        REWRITE_TAC[IN_INTER; ASSUME `(y:real^3) IN frontier c`] THEN
        UNDISCH_TAC `(y:real^3) IN d` THEN UNDISCH_TAC `(d:real^3->bool) SUBSET B` THEN
        SET_TAC[];
        MAP_EVERY UNDISCH_TAC [`B INTER oo SUBSET (Av:real^3->bool)`;
                               `(Av:real^3->bool) SUBSET S`] THEN
        SET_TAC[];
        UNDISCH_TAC `d INTER E = (j:real^3->bool)` THEN DISCH_THEN SUBST1_TAC THEN
        UNDISCH_TAC `d INTER frontier c = (j:real^3->bool)` THEN SET_TAC[];
        REWRITE_TAC[INTERIOR_COMPLEMENT] THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(SET_RULE `!s. y IN s /\ s SUBSET t ==> (y:real^3) IN t`) THEN
        EXISTS_TAC `closure (d DIFF j:real^3->bool)` THEN CONJ_TAC THENL
         [UNDISCH_TAC `(d:real^3->bool) SUBSET closure (d DIFF j)` THEN
          UNDISCH_TAC `(y:real^3) IN d` THEN SET_TAC[];
          MATCH_MP_TAC SUBSET_CLOSURE THEN
          UNDISCH_TAC `DISJOINT (d DIFF j) (c:real^3->bool)` THEN SET_TAC[]]];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^3->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `u INTER ((:real^3) DIFF interior c) INTER B SUBSET (d:real^3->bool)` THEN
    SET_TAC[];
    (* off the rim: d is open in the sphere *)
    EXISTS_TAC `oo DIFF E:real^3->bool` THEN
    CONJ_TAC THENL [MATCH_MP_TAC OPEN_DIFF THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
                    ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      EXPAND_TAC "E" THEN
      MAP_EVERY UNDISCH_TAC [`(y:real^3) IN d`; `~((y:real^3) IN j)`] THEN SET_TAC[];
      MAP_EVERY UNDISCH_TAC [`B INTER oo SUBSET (Av:real^3->bool)`;
                             `(Av:real^3->bool) SUBSET S`;
                             `(S:real^3->bool) DIFF E SUBSET d`] THEN
      SET_TAC[]]]);;

(* Other face balls near a point of car s that lies in none of them. *)

let MOI_S4V_FB_AVOID = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s y.
     moi_s34_frame tt kk h ep f1 car /\ moi_s34_fbinv tt kk h f1 car cb /\
     s IN moi_s34_simp kk (&2) /\ y IN car s /\
     (!s'. s' IN moi_s34_simp kk (&2) /\ ~(s' = s) ==> ~(y IN cb s'))
     ==> ?u. open u /\ y IN u /\
             FINITE {s' | s' IN moi_s34_simp kk (&2) /\ ~(s' = s) /\ ~(cb s' INTER u = {})}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(s:real^N->bool) IN kk /\ ~(s = {})` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(s:real^N->bool) IN moi_s34_simp kk (&2)` THEN
    REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `aff_dim({}:real^N->bool) = &2` THEN
    REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ASSUME `moi_s34_frame tt kk (h:real^N->real^3) ep f1 car`) THEN
  REWRITE_TAC[moi_s34_frame] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^3` o CONJUNCT1 o funpow 11 CONJUNCT2) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `(car:(real^N->bool)->real^3->bool) s` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u0:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `u0:real^3->bool` OPEN_CONTAINS_BALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `ball(y:real^3,r)` THEN ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{q | q IN kk /\ ~(q = {}) /\
                   ~((car:(real^N->bool)->real^3->bool) q INTER u0 = {})}` THEN
  ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `s':real^N->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(s':real^N->bool) IN kk /\ ~(s' = {})` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(s':real^N->bool) IN moi_s34_simp kk (&2)` THEN
    REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `aff_dim({}:real^N->bool) = &2` THEN
    REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* the ball misses the frontier of cb s', and y is not in cb s' *)
  MP_TAC(ISPECL [`ball(y:real^3,r)`; `(cb:(real^N->bool)->real^3->bool) s'`]
    CONNECTED_INTER_FRONTIER) THEN
  REWRITE_TAC[CONNECTED_BALL] THEN
  MATCH_MP_TAC(TAUT `a /\ b /\ x ==> ~(a /\ b ==> ~x)`) THEN
  REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `y:real^3` THEN
    REWRITE_TAC[IN_DIFF; CENTRE_IN_BALL] THEN ASM_SIMP_TAC[];
    SUBGOAL_THEN `frontier((cb:(real^N->bool)->real^3->bool) s') SUBSET car s'`
    MP_TAC THENL
     [UNDISCH_TAC `moi_s34_fbinv tt kk (h:real^N->real^3) f1 car cb` THEN
      REWRITE_TAC[moi_s34_fbinv; moi_s34_fb1] THEN
      DISCH_THEN(MP_TAC o SPEC `s':real^N->bool` o CONJUNCT1) THEN
      ASM_SIMP_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`(car:(real^N->bool)->real^3->bool) s' INTER u0 = {}`;
        `ball(y:real^3,r) SUBSET u0`] THEN
      SET_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Dropping a clopen piece j of a carrying set z whose H_1                   *)
(* image is trivial (j lies in a contractible d SUBSET t) keeps the carrying *)
(* property (additivity of homology over the clopen decomposition of z).    *)
(* ------------------------------------------------------------------------- *)

let MOI_S4V_CARRIES_DROP = prove
 (`!(z:real^N->bool) j d t.
     carries_h1 z t /\ z SUBSET t /\ j SUBSET z /\ j SUBSET d /\ d SUBSET t /\
     contractible d /\
     open_in (subtopology euclidean z) j /\ open_in (subtopology euclidean z) (z DIFF j)
     ==> carries_h1 (z DIFF j) t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `carries_h1 (z:real^N->bool) t` THEN
  REWRITE_TAC[carries_h1; group_image] THEN DISCH_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`&1:int`; `subtopology euclidean ((z:real^N->bool) DIFF j)`;
                   `subtopology euclidean (t:real^N->bool)`; `\x:real^N. x`]
                  GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY) THEN
    SIMP_TAC[group_homomorphism];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:((num->real)->real^N)frag->bool` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `?a. a IN group_carrier (homology_group(&1,subtopology euclidean (z:real^N->bool))) /\
        hom_induced (&1) (subtopology euclidean z,{}) (subtopology euclidean t,{})
                    (\x. x) a = y`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC
     `IMAGE (hom_induced (&1) (subtopology euclidean (z:real^N->bool),{})
                             (subtopology euclidean t,{}) (\x. x))
            (group_carrier (homology_group (&1,subtopology euclidean z))) =
      group_carrier (homology_group (&1,subtopology euclidean t))` THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `y:((num->real)->real^N)frag->bool`) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  (* additivity over z = (z DIFF j) UNION j *)
  MP_TAC(ISPECL [`&1:int`; `subtopology euclidean (z:real^N->bool)`;
                 `z DIFF j:real^N->bool`; `j:real^N->bool`]
    HOMOLOGY_ADDITIVITY_EXPLICIT) THEN
  ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `subtopology (subtopology euclidean (z:real^N->bool)) (z DIFF j) =
    subtopology euclidean (z DIFF j) /\
    subtopology (subtopology euclidean (z:real^N->bool)) j = subtopology euclidean j`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_S4J_SUBTOP THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP GROUP_ISOMORPHISM_IMP_EPIMORPHISM) THEN
  REWRITE_TAC[group_epimorphism] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  REWRITE_TAC[PROD_GROUP] THEN
  DISCH_THEN(MP_TAC o SPEC `a:((num->real)->real^N)frag->bool` o REWRITE_RULE[EXTENSION]) THEN
  ASM_REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM; IN_CROSS] THEN
  CONV_TAC(LAND_CONV(DEPTH_CONV GEN_BETA_CONV)) THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:((num->real)->real^N)frag->bool`
    (X_CHOOSE_THEN `a2:((num->real)->real^N)frag->bool` STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `a1:((num->real)->real^N)frag->bool` THEN
  ASM_REWRITE_TAC[] THEN
  (* the j-part dies in t *)
  SUBGOAL_THEN
   `hom_induced (&1) (subtopology euclidean (j:real^N->bool),{})
                     (subtopology euclidean t,{}) (\x. x) a2 =
    group_id (homology_group(&1,subtopology euclidean (t:real^N->bool)))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `hom_induced (&1) (subtopology euclidean (j:real^N->bool),{})
                       (subtopology euclidean t,{}) (\x. x) =
      hom_induced (&1) (subtopology euclidean d,{}) (subtopology euclidean t,{}) (\x. x) o
      hom_induced (&1) (subtopology euclidean j,{}) (subtopology euclidean d,{}) (\x. x)`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC ATOP_HOM_INDUCED_INCLUSIONS THEN
      ASM_SIMP_TAC[ATOP_CONTINUOUS_MAP_INCLUSION; SUBSET_REFL];
      ALL_TAC] THEN
    REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN
     `hom_induced (&1) (subtopology euclidean (j:real^N->bool),{})
                       (subtopology euclidean d,{}) (\x. x) a2 =
      group_id (homology_group(&1,subtopology euclidean (d:real^N->bool)))`
    SUBST1_TAC THENL
     [MP_TAC(ISPEC `d:real^N->bool` MOI_S4J_H1_CONTRACTIBLE) THEN
      ASM_REWRITE_TAC[trivial_group] THEN DISCH_TAC THEN
      MATCH_MP_TAC(SET_RULE `!s (x:((num->real)->real^N)frag->bool) a. x IN s /\ s = {a} ==> x = a`) THEN
      EXISTS_TAC `group_carrier (homology_group(&1,subtopology euclidean (d:real^N->bool)))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MOI_S4J_HOM_IN THEN
        EXISTS_TAC `homology_group(&1,subtopology euclidean (j:real^N->bool))` THEN
        ASM_REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY];
        FIRST_ASSUM ACCEPT_TAC];
      MATCH_MP_TAC ATOP_GROUP_HOM_ID THEN
      REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY]];
    ALL_TAC] THEN
  (* y = image of a = image of a1 times image of a2 *)
  UNDISCH_TAC `hom_induced (&1) (subtopology euclidean (z:real^N->bool),{})
                           (subtopology euclidean t,{}) (\x. x) a = y` THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
    is_eq (concl th) && lhs (concl th) = `a:((num->real)->real^N)frag->bool`)) THEN
  SUBGOAL_THEN
   `!x1 x2. x1 IN group_carrier (homology_group(&1,subtopology euclidean (z:real^N->bool))) /\
            x2 IN group_carrier (homology_group(&1,subtopology euclidean z))
            ==> hom_induced (&1) (subtopology euclidean z,{}) (subtopology euclidean t,{})
                  (\x. x) (group_mul (homology_group(&1,subtopology euclidean z)) x1 x2) =
                group_mul (homology_group(&1,subtopology euclidean (t:real^N->bool)))
                  (hom_induced (&1) (subtopology euclidean z,{}) (subtopology euclidean t,{})
                     (\x. x) x1)
                  (hom_induced (&1) (subtopology euclidean z,{}) (subtopology euclidean t,{})
                     (\x. x) x2)`
  MP_TAC THENL
   [MP_TAC(ISPECL [`&1:int`; `subtopology euclidean (z:real^N->bool)`;
                   `subtopology euclidean (t:real^N->bool)`; `\x:real^N. x`]
      GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY) THEN
    REWRITE_TAC[group_homomorphism] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(fun th ->
    MP_TAC(SPECL
      [`hom_induced (&1) (subtopology euclidean ((z:real^N->bool) DIFF j),{})
                         (subtopology euclidean z,{}) (\x. x) a1`;
       `hom_induced (&1) (subtopology euclidean (j:real^N->bool),{})
                         (subtopology euclidean z,{}) (\x. x) a2`] th)) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_S4J_HOM_IN THENL
     [EXISTS_TAC `homology_group(&1,subtopology euclidean ((z:real^N->bool) DIFF j))`;
      EXISTS_TAC `homology_group(&1,subtopology euclidean (j:real^N->bool))`] THEN
    ASM_REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `!(u:real^N->bool) (b:((num->real)->real^N)frag->bool).
      u SUBSET z
      ==> hom_induced (&1) (subtopology euclidean z,{}) (subtopology euclidean t,{}) (\x. x)
            (hom_induced (&1) (subtopology euclidean u,{}) (subtopology euclidean z,{}) (\x. x)
               b) =
          hom_induced (&1) (subtopology euclidean u,{}) (subtopology euclidean t,{}) (\x. x) b`
  (fun th -> SIMP_TAC[th; SUBSET_DIFF; ASSUME `(j:real^N->bool) SUBSET z`]) THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`&1:int`; `subtopology euclidean (u:real^N->bool)`; `{}:real^N->bool`;
                   `subtopology euclidean (z:real^N->bool)`; `{}:real^N->bool`;
                   `subtopology euclidean (t:real^N->bool)`; `{}:real^N->bool`]
      ATOP_HOM_INDUCED_INCLUSIONS) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[ATOP_CONTINUOUS_MAP_INCLUSION; EMPTY_SUBSET]; ALL_TAC] THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC GROUP_MUL_RID THEN MATCH_MP_TAC MOI_S4J_HOM_IN THEN
  EXISTS_TAC `homology_group(&1,subtopology euclidean ((z:real^N->bool) DIFF j))` THEN
  ASM_REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY]);;

(* ------------------------------------------------------------------------- *)
(* The outward push.  A PL ball w with a disk dd in its                     *)
(* frontier is straightened, on a polytope neighbourhood k2 of the standard *)
(* simplex k0, so that w becomes k0 and dd the facet F0 opposite the        *)
(* origin (ambient Schoenflies, MOI_SPU_SPHERE_DISK_PLH and                  *)
(* MOI_SPU_EXTEND_SPHERE_PLH); the dilated simplex (1 + t) k0 then gives a  *)
(* ball w2 = w UNION y with y a thin slab beyond dd.                         *)
(* ------------------------------------------------------------------------- *)

(* Coordinates of the standard simplex, its dilation and its facet F0. *)

let MOI_S4V_K0_DIL = prove
 (`!t x:real^3.
     &0 <= t
     ==> (x IN IMAGE (\x. (&1 + t) % x) (convex hull {vec 0,basis 1,basis 2,basis 3}) <=>
          &0 <= x$1 /\ &0 <= x$2 /\ &0 <= x$3 /\ x$1 + x$2 + x$3 <= &1 + t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MOI_SPU_K0; IN_IMAGE; IN_ELIM_THM] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN
    REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN
    REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC) THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC THEN EXISTS_TAC `inv(&1 + t) % x:real^3` THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC; VECTOR_MUL_COMPONENT] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_ARITH `&0 <= t ==> ~(&1 + t = &0)`; VECTOR_MUL_LID] THEN
    REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN
    SUBGOAL_THEN `&0 < inv(&1 + t)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC) THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_ARITH `&0 <= t ==> &0 < &1 + t`] THEN
    ASM_REAL_ARITH_TAC]);;

let MOI_S4V_F0_COORDS = prove
 (`!x:real^3.
     x IN convex hull {basis 1,basis 2,basis 3} <=>
     &0 <= x$1 /\ &0 <= x$2 /\ &0 <= x$3 /\ x$1 + x$2 + x$3 = &1`,
  GEN_TAC THEN
  SUBGOAL_THEN `convex hull {basis 1:real^3,basis 2,basis 3} =
                relative_interior (convex hull {basis 1,basis 2,basis 3}) UNION
                relative_frontier (convex hull {basis 1,basis 2,basis 3})`
  SUBST1_TAC THENL
   [REWRITE_TAC[relative_frontier] THEN
    MP_TAC(ISPEC `convex hull {basis 1:real^3,basis 2,basis 3}` RELATIVE_INTERIOR_SUBSET) THEN
    SUBGOAL_THEN `closure (convex hull {basis 1:real^3,basis 2,basis 3}) =
                  convex hull {basis 1,basis 2,basis 3}` SUBST1_TAC THENL
     [MATCH_MP_TAC CLOSURE_CLOSED THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      MATCH_MP_TAC COMPACT_CONVEX_HULL THEN
      MATCH_MP_TAC FINITE_IMP_COMPACT THEN REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
      SET_TAC[]];
    REWRITE_TAC[IN_UNION; MOI_SPU_RELINT_F0; MOI_SPU_BDF0; IN_ELIM_THM] THEN
    REAL_ARITH_TAC]);;

let MOI_S4V_STD_SLAB = prove
 (`!t. &0 < t /\ t <= &1
       ==> &3 simplex (IMAGE (\x:real^3. (&1 + t) % x)
                         (convex hull {vec 0,basis 1,basis 2,basis 3})) /\
           convex hull {vec 0,basis 1,basis 2,basis 3} SUBSET
           IMAGE (\x:real^3. (&1 + t) % x) (convex hull {vec 0,basis 1,basis 2,basis 3}) /\
           relative_interior (convex hull {basis 1:real^3,basis 2,basis 3}) SUBSET
           interior (IMAGE (\x:real^3. (&1 + t) % x)
                       (convex hull {vec 0,basis 1,basis 2,basis 3})) /\
           convex hull {vec 0,basis 1,basis 2,basis 3} UNION
           {x | x IN IMAGE (\x:real^3. (&1 + t) % x)
                         (convex hull {vec 0,basis 1,basis 2,basis 3}) /\
                &1 <= x$1 + x$2 + x$3} =
           IMAGE (\x:real^3. (&1 + t) % x) (convex hull {vec 0,basis 1,basis 2,basis 3}) /\
           {x | x IN IMAGE (\x:real^3. (&1 + t) % x)
                         (convex hull {vec 0,basis 1,basis 2,basis 3}) /\
                &1 <= x$1 + x$2 + x$3} INTER convex hull {vec 0,basis 1,basis 2,basis 3} =
           convex hull {basis 1,basis 2,basis 3} /\
           compact {x | x IN IMAGE (\x:real^3. (&1 + t) % x)
                                (convex hull {vec 0,basis 1,basis 2,basis 3}) /\
                        &1 <= x$1 + x$2 + x$3} /\
           (!x. x IN IMAGE (\x:real^3. (&1 + t) % x)
                         (convex hull {vec 0,basis 1,basis 2,basis 3}) /\
                &1 <= x$1 + x$2 + x$3
                ==> ?y. y IN convex hull {basis 1,basis 2,basis 3} /\ dist(x,y) <= &2 * t) /\
           (!x. x IN IMAGE (\x:real^3. (&1 + t) % x)
                         (convex hull {vec 0,basis 1,basis 2,basis 3})
                ==> ?y. y IN convex hull {vec 0,basis 1,basis 2,basis 3} /\ dist(x,y) <= t)`,
  GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `k0 = convex hull {vec 0:real^3,basis 1,basis 2,basis 3}` THEN
  ABBREV_TAC `kt = IMAGE (\x:real^3. (&1 + t) % x) k0` THEN
  SUBGOAL_THEN `!x:real^3. x IN kt <=>
                  &0 <= x$1 /\ &0 <= x$2 /\ &0 <= x$3 /\ x$1 + x$2 + x$3 <= &1 + t`
  (LABEL_TAC "KT") THENL
   [EXPAND_TAC "kt" THEN EXPAND_TAC "k0" THEN GEN_TAC THEN
    MATCH_MP_TAC MOI_S4V_K0_DIL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN k0 <=>
                  &0 <= x$1 /\ &0 <= x$2 /\ &0 <= x$3 /\ x$1 + x$2 + x$3 <= &1`
  (LABEL_TAC "K0") THENL
   [EXPAND_TAC "k0" THEN REWRITE_TAC[MOI_SPU_K0; IN_ELIM_THM]; ALL_TAC] THEN
  REWRITE_TAC[MOI_S4V_F0_COORDS] THEN REPEAT CONJ_TAC THENL
   [(* a simplex *)
    EXPAND_TAC "kt" THEN EXPAND_TAC "k0" THEN
    MP_TAC MOI_SPU_STD_SIMPLEX THEN REWRITE_TAC[simplex] THEN
    DISCH_THEN(X_CHOOSE_THEN `cc:real^3->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `IMAGE (\x:real^3. (&1 + t) % x) cc` THEN
    SUBGOAL_THEN `linear (\x:real^3. (&1 + t) % x) /\
                  (!x y:real^3. (\x:real^3. (&1 + t) % x) x = (\x. (&1 + t) % x) y ==> x = y)`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `~(&1 + t = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[LINEAR_SCALING; VECTOR_MUL_LCANCEL];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`\x:real^3. (&1 + t) % x`; `cc:real^3->bool`]
        AFFINE_DEPENDENT_LINEAR_IMAGE_EQ) THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`\x:real^3. (&1 + t) % x`; `cc:real^3->bool`] CARD_IMAGE_INJ) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]];
        DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
      ASM_SIMP_TAC[CONVEX_HULL_LINEAR_IMAGE;
        GSYM(ASSUME `convex hull {vec 0:real^3,basis 1,basis 2,basis 3} =
                     convex hull cc`)]];
    (* k0 inside kt *)
    REWRITE_TAC[SUBSET] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    (* relint F0 interior *)
    REWRITE_TAC[MOI_SPU_RELINT_F0; SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN REWRITE_TAC[IN_INTERIOR] THEN
    EXISTS_TAC `min (min ((x:real^3)$1 / &2) (x$2 / &2)) (min (x$3 / &2) (t / &4))` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_BALL] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`x - y:real^3`; `1`] COMPONENT_LE_NORM) THEN
    MP_TAC(ISPECL [`x - y:real^3`; `2`] COMPONENT_LE_NORM) THEN
    MP_TAC(ISPECL [`x - y:real^3`; `3`] COMPONENT_LE_NORM) THEN
    REWRITE_TAC[DIMINDEX_3; ARITH; VECTOR_SUB_COMPONENT] THEN
    UNDISCH_TAC `dist(x:real^3,y) < min (min (x$1 / &2) (x$2 / &2)) (min (x$3 / &2) (t / &4))` THEN
    REWRITE_TAC[dist] THEN ASM_REAL_ARITH_TAC;
    (* kt = k0 UNION the slab *)
    REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    (* slab INTER k0 = F0 *)
    REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; MOI_S4V_F0_COORDS] THEN
    ASM_REWRITE_TAC[] THEN GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    (* compact slab *)
    REWRITE_TAC[SET_RULE `{x:real^3 | x IN s /\ P x} = s INTER {x | P x}`] THEN
    MATCH_MP_TAC COMPACT_INTER_CLOSED THEN CONJ_TAC THENL
     [EXPAND_TAC "kt" THEN MATCH_MP_TAC COMPACT_LINEAR_IMAGE THEN
      REWRITE_TAC[LINEAR_SCALING] THEN EXPAND_TAC "k0" THEN
      MATCH_MP_TAC COMPACT_CONVEX_HULL THEN
      MATCH_MP_TAC FINITE_IMP_COMPACT THEN REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
      MP_TAC(ISPECL [`vector[&1;&1;&1]:real^3`; `&1`] CLOSED_HALFSPACE_GE) THEN
      MATCH_MP_TAC(TAUT `p = q ==> p ==> q`) THEN AP_TERM_TAC THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; DOT_3; VECTOR_3; real_ge] THEN
      REAL_ARITH_TAC];
    (* slab points are near F0 *)
    X_GEN_TAC `x:real^3` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ABBREV_TAC `sx = (x:real^3)$1 + x$2 + x$3` THEN
    EXISTS_TAC `inv(sx) % x:real^3` THEN
    SUBGOAL_THEN `&0 < sx` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ];
      ALL_TAC] THEN
    REWRITE_TAC[dist; VECTOR_ARITH `x - a % x:real^3 = (&1 - a) % x`; NORM_MUL] THEN
    SUBGOAL_THEN `norm(x:real^3) <= sx` ASSUME_TAC THENL
     [MP_TAC(ISPEC `x:real^3` NORM_LE_L1) THEN
      REWRITE_TAC[DIMINDEX_3; SUM_3] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `abs(&1 - inv sx) <= t` ASSUME_TAC THENL
     [SUBGOAL_THEN `&1 - inv sx = (sx - &1) / sx` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < sx` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < sx ==> abs sx = sx`] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `t:real` THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPEC `x:real^3` NORM_POS_LE) THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `t * (&1 + t)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `t * t <= t ==> t * (&1 + t) <= &2 * t`) THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    (* kt points are near k0 *)
    X_GEN_TAC `x:real^3` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXISTS_TAC `inv(&1 + t) % x:real^3` THEN
    SUBGOAL_THEN `&0 < inv(&1 + t)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_ARITH `&0 < t ==> &0 < &1 + t`] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[dist; VECTOR_ARITH `x - a % x:real^3 = (&1 - a) % x`; NORM_MUL] THEN
    SUBGOAL_THEN `norm(x:real^3) <= &1 + t` ASSUME_TAC THENL
     [MP_TAC(ISPEC `x:real^3` NORM_LE_L1) THEN
      REWRITE_TAC[DIMINDEX_3; SUM_3] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `abs(&1 - inv(&1 + t)) = t / (&1 + t)` SUBST1_TAC THENL
     [SUBGOAL_THEN `&1 - inv(&1 + t) = t / (&1 + t)` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      REWRITE_TAC[REAL_ABS_DIV] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`;
                   REAL_ARITH `&0 < t ==> abs(&1 + t) = &1 + t`];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> &0 < &1 + t`; REAL_FIELD
      `&0 < s ==> t / s * n = t * (n / s)`] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_LDIV_EQ; REAL_ARITH `&0 < t ==> &0 < &1 + t`] THEN
    MP_TAC(ISPEC `x:real^3` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC]);;

(* A compact subset of the relative interior of a triangle lies in the      *)
(* relative interior of a homothetic copy (towards an interior point) that  *)
(* itself lies in the relative interior.                                     *)

let MOI_S4V_SHRINK_SIMPLEX = prove
 (`!t k:real^3->bool.
     &2 simplex t /\ compact k /\ k SUBSET relative_interior t
     ==> ?t2. &2 simplex t2 /\ t2 SUBSET relative_interior t /\
              k SUBSET t2 DIFF relative_frontier t2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `compact (t:real^3->bool) /\ convex t /\ ~(t = {})` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT];
      ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
      DISCH_THEN SUBST_ALL_TAC THEN
      MP_TAC(ISPECL [`{}:real^3->bool`; `&2:int`] AFF_DIM_SIMPLEX) THEN
      ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `?p:real^3. p IN relative_interior t` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `closed (affine hull t DIFF relative_interior (t:real^3->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_IN_CLOSED_TRANS THEN EXISTS_TAC `affine hull (t:real^3->bool)` THEN
    REWRITE_TAC[CLOSED_AFFINE_HULL] THEN MATCH_MP_TAC CLOSED_IN_DIFF THEN
    REWRITE_TAC[OPEN_IN_RELATIVE_INTERIOR; CLOSED_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN;
                SUBSET_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `affine hull t DIFF relative_interior (t:real^3->bool)`]
    SEPARATE_COMPACT_CLOSED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(k:real^3->bool) SUBSET relative_interior t` THEN
    SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?b. &0 < b /\ !x:real^3. x IN t ==> norm x <= b` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[BOUNDED_POS; COMPACT_IMP_BOUNDED]; ALL_TAC] THEN
  ABBREV_TAC `mu = &1 + (dl / &2) / (&2 * b)` THEN
  SUBGOAL_THEN `&0 < (dl / &2) / (&2 * b)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 < mu /\ ~(mu = &0) /\ &0 < inv mu /\ inv mu < &1`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 < mu` ASSUME_TAC THENL
     [EXPAND_TAC "mu" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_INV_LT_1] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (\x:real^3. inv mu % x + (&1 - inv mu) % p) t` THEN
  MP_TAC(ISPECL [`\x:real^3. inv mu % x`; `(&1 - inv mu) % p:real^3`; `&2:int`;
                 `t:real^3->bool`] MOI_S27_INJ_AFFINE_SIMPLEX) THEN
  REWRITE_TAC[LINEAR_SCALING] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_LCANCEL; REAL_INV_EQ_0]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [(* the copy lies in the relative interior *)
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `inv mu % x + (&1 - inv mu) % p:real^3 = x - (&1 - inv mu) % (x - p)`
    SUBST1_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SHRINK THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPEC `t:real^3->bool` CLOSURE_SUBSET) THEN
      UNDISCH_TAC `(x:real^3) IN t` THEN SET_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* k lies in the relative interior of the copy *)
  REWRITE_TAC[SUBSET; IN_DIFF] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN t` ASSUME_TAC THENL
   [MP_TAC(ISPEC `t:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
    MAP_EVERY UNDISCH_TAC [`(y:real^3) IN k`; `(k:real^3->bool) SUBSET relative_interior t`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3) IN t` ASSUME_TAC THENL
   [MP_TAC(ISPEC `t:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(p:real^3) IN relative_interior t` THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `z:real^3 = mu % y + (&1 - mu) % p` THEN
  SUBGOAL_THEN `inv mu % z + (&1 - inv mu) % p:real^3 = y` ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN
    REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC; REAL_SUB_LDISTRIB; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3) IN affine hull t` ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN
    MP_TAC(ISPEC `affine hull (t:real^3->bool)` affine) THEN
    REWRITE_TAC[AFFINE_AFFINE_HULL] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`affine:(real^3->bool)->bool`; `t:real^3->bool`] HULL_SUBSET) THEN
    MAP_EVERY UNDISCH_TAC [`(y:real^3) IN t`; `(p:real^3) IN t`] THEN
    REWRITE_TAC[REAL_ARITH `m + (&1 - m) = &1`] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `dist(y:real^3,z) <= dl / &2` ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN REWRITE_TAC[dist] THEN
    SUBGOAL_THEN `y - (mu % y + (&1 - mu) % p):real^3 = (&1 - mu) % (y - p)` SUBST1_TAC THENL
     [VECTOR_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[NORM_MUL] THEN
    SUBGOAL_THEN `abs(&1 - mu) = (dl / &2) / (&2 * b)` SUBST1_TAC THENL
     [EXPAND_TAC "mu" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `norm(y - p:real^3) <= &2 * b` ASSUME_TAC THENL
     [MATCH_MP_TAC(NORM_ARITH
       `norm(x:real^3) <= b /\ norm(y:real^3) <= b ==> norm(x - y) <= &2 * b`) THEN
      CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(dl / &2) / (&2 * b) * (&2 * b)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_ARITH `&0 < b ==> ~(&2 * b = &0)`; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3) IN relative_interior t` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `dl <= dist(y:real^3,z)` MP_TAC THENL
     [MATCH_MP_TAC(ASSUME
       `!x y. x IN k /\ y IN affine hull t DIFF relative_interior (t:real^3->bool)
              ==> dl <= dist(x,y)`) THEN
      ASM_REWRITE_TAC[IN_DIFF];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `t:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(z:real^3) IN relative_interior t` THEN SET_TAC[];
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `inv mu % w:real^3 = inv mu % z` MP_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`y:real^3 = inv mu % w + (&1 - inv mu) % p`;
                             `inv mu % z + (&1 - inv mu) % p:real^3 = y`] THEN
      VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LCANCEL; REAL_INV_EQ_0] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `(z:real^3) IN relative_frontier t` THEN
    UNDISCH_TAC `(z:real^3) IN relative_interior t` THEN
    REWRITE_TAC[relative_frontier] THEN SET_TAC[]]);;

(* A collar of the rim of a PL disk: a smaller disk e2 inside e minus j     *)
(* such that the annulus e minus (e2 minus its rim) lies in a given open o. *)

let MOI_S4V_COLLAR = prove
 (`!e j oo:real^3->bool.
     pl_cell_with_boundary 2 e j /\ open oo /\ j SUBSET oo
     ==> ?e2 j2. pl_cell_with_boundary 2 e2 j2 /\ e2 SUBSET e DIFF j /\
                 e DIFF (e2 DIFF j2) SUBSET oo`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S4L_PL_CELL2_TOPO
    (ASSUME `pl_cell_with_boundary 2 (e:real^3->bool) j`)) THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pl_cell_with_boundary]) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` (X_CHOOSE_THEN `ph:real^3->real^3`
    (X_CHOOSE_THEN `ps:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact (t:real^3->bool) /\ polytope t` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; SIMPLEX_IMP_POLYTOPE]; ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier t SUBSET (t:real^3->bool) /\
                t DIFF relative_frontier t = relative_interior t /\
                relative_interior t SUBSET t`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[relative_frontier] THEN
    ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
    MP_TAC(ISPEC `t:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  (* the part of e outside oo, pulled back into the relative interior of t *)
  MP_TAC(ISPECL [`t:real^3->bool`; `IMAGE (ps:real^3->real^3) (e DIFF oo)`]
    MOI_S4V_SHRINK_SIMPLEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `e:real^3->bool` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        SUBGOAL_THEN `e DIFF oo = e INTER ((:real^3) DIFF oo)` SUBST1_TAC THENL
         [SET_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC COMPACT_INTER_CLOSED THEN ASM_REWRITE_TAC[GSYM OPEN_CLOSED]];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF] THEN X_GEN_TAC `x:real^3` THEN
      STRIP_TAC THEN
      UNDISCH_TAC `t DIFF relative_frontier t = relative_interior (t:real^3->bool)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL
       [UNDISCH_TAC `IMAGE (ps:real^3->real^3) e = t` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
        DISCH_TAC THEN UNDISCH_TAC `~((x:real^3) IN oo)` THEN REWRITE_TAC[] THEN
        SUBGOAL_THEN `(x:real^3) IN j` MP_TAC THENL
         [REWRITE_TAC[ASSUME `j = IMAGE (ph:real^3->real^3) (relative_frontier t)`; IN_IMAGE] THEN
          EXISTS_TAC `(ps:real^3->real^3) x` THEN ASM_REWRITE_TAC[] THEN
          CONV_TAC SYM_CONV THEN
          MATCH_MP_TAC(ASSUME `!y. y IN e ==> (ph:real^3->real^3) (ps y) = y`) THEN
          FIRST_ASSUM ACCEPT_TAC;
          MP_TAC(ASSUME `(j:real^3->bool) SUBSET oo`) THEN REWRITE_TAC[SUBSET] THEN
          MESON_TAC[]]]];
    DISCH_THEN(X_CHOOSE_THEN `t2:real^3->bool` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `(t2:real^3->bool) SUBSET t /\ polytope t2 /\ relative_frontier t2 SUBSET t2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `(t2:real^3->bool) SUBSET relative_interior t` THEN
      UNDISCH_TAC `relative_interior t SUBSET (t:real^3->bool)` THEN SET_TAC[];
      ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE];
      REWRITE_TAC[relative_frontier] THEN
      SUBGOAL_THEN `closure t2 = (t2:real^3->bool)` SUBST1_TAC THENL
       [MATCH_MP_TAC CLOSURE_CLOSED THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
        ASM_MESON_TAC[SIMPLEX_IMP_COMPACT];
        SET_TAC[]]];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (ph:real^3->real^3) t2` THEN
  EXISTS_TAC `IMAGE (ph:real^3->real^3) (relative_frontier t2)` THEN
  REPEAT CONJ_TAC THENL
   [(* a PL disk *)
    REWRITE_TAC[pl_cell_with_boundary] THEN
    MAP_EVERY EXISTS_TAC [`t2:real^3->bool`; `ph:real^3->real^3`; `ps:real^3->real^3`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S4N_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`t:real^3->bool`; `e:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_POLYTOPE] THEN
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN
    ASM_SIMP_TAC[POLYTOPE_IMP_PL_POLYHEDRON] THEN
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `t:real^3->bool` THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_POLYTOPE];
    (* inside e minus j *)
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN relative_interior t /\ x IN t` STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(x:real^3) IN t2`; `(t2:real^3->bool) SUBSET relative_interior t`;
        `relative_interior t SUBSET (t:real^3->bool)`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (ph:real^3->real^3) t = e` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[ASSUME `j = IMAGE (ph:real^3->real^3) (relative_frontier t)`; IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(w:real^3) IN t` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(w:real^3) IN relative_frontier t`; `relative_frontier t SUBSET (t:real^3->bool)`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `x:real^3 = w` SUBST_ALL_TAC THENL
     [MP_TAC(ASSUME `!x. x IN t ==> (ps:real^3->real^3) (ph x) = x`) THEN
      MAP_EVERY UNDISCH_TAC [`(ph:real^3->real^3) x = ph w`; `(x:real^3) IN t`;
                             `(w:real^3) IN t`] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`(w:real^3) IN relative_frontier t`; `(w:real^3) IN relative_interior t`;
      `t DIFF relative_frontier t = relative_interior (t:real^3->bool)`] THEN
    SET_TAC[];
    (* the annulus lies in oo *)
    REWRITE_TAC[SUBSET; IN_DIFF] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(ps:real^3->real^3) x IN t2 /\ ~(ps x IN relative_frontier t2)`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ASSUME `IMAGE (ps:real^3->real^3) (e DIFF oo) SUBSET
                     t2 DIFF relative_frontier t2`) THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF] THEN DISCH_THEN MATCH_MP_TAC THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(ph:real^3->real^3) (ps x) = x` ASSUME_TAC THENL
     [MATCH_MP_TAC(ASSUME `!y. y IN e ==> (ph:real^3->real^3) (ps y) = y`) THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `~((x:real^3) IN IMAGE (ph:real^3->real^3) t2 /\
                   ~(x IN IMAGE ph (relative_frontier t2)))` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(ps:real^3->real^3) x` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(w:real^3) IN t` ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`(w:real^3) IN relative_frontier t2`; `relative_frontier t2 SUBSET (t2:real^3->bool)`;
          `(t2:real^3->bool) SUBSET t`] THEN
        SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(ps:real^3->real^3) x = w` ASSUME_TAC THENL
       [MP_TAC(MP (SPEC `w:real^3` (ASSUME `!x. x IN t ==> (ps:real^3->real^3) (ph x) = x`))
                  (ASSUME `(w:real^3) IN t`)) THEN
        UNDISCH_TAC `x:real^3 = (ph:real^3->real^3) w` THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]);
        ALL_TAC] THEN
      UNDISCH_TAC `~((ps:real^3->real^3) x IN relative_frontier t2)` THEN
      ASM_REWRITE_TAC[]]]);;

(* An affine PL homeomorphism of R^3 carrying the standard tetrahedron k0   *)
(* onto a given 3-simplex k and the facet F0 onto a facet ff of k.          *)

let MOI_S4V_SIMPLEX_STD = prove
 (`!k:real^3->bool.
     &3 simplex k
     ==> ?(aa:real^3->real^3) aa' ff.
           pl_homeomorphism ((:real^3),(:real^3)) (aa,aa') /\
           (!s. polytope s ==> polytope (IMAGE aa' s)) /\
           IMAGE aa (convex hull {vec 0,basis 1,basis 2,basis 3}) = k /\
           IMAGE aa (convex hull {basis 1,basis 2,basis 3}) = ff /\
           IMAGE aa (relative_frontier (convex hull {basis 1,basis 2,basis 3})) =
           relative_frontier ff /\
           ff face_of k /\ aff_dim ff = &2`,
  GEN_TAC THEN REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `vv:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(vv:real^3->bool) HAS_SIZE 4` MP_TAC THENL
   [ASM_SIMP_TAC[HAS_SIZE; AFFINE_INDEPENDENT_IMP_FINITE] THEN
    UNDISCH_TAC `(&(CARD (vv:real^3->bool)):int) = &3 + &1` THEN
    REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3` (X_CHOOSE_THEN `a:real^3`
    (X_CHOOSE_THEN `b:real^3` (X_CHOOSE_THEN `c:real^3`
    STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
  MP_TAC(ISPECL [`w:real^3`; `a:real^3`; `b:real^3`; `c:real^3`] MOI_SS2_AFFINE_ISO) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^3->real^3` (X_CHOOSE_THEN `l':real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!x y. (l:real^3->real^3) x = l y ==> x = y` ASSUME_TAC THENL
   [MP_TAC(ASSUME `!x. (l':real^3->real^3) ((l:real^3->real^3) x) = x`) THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (\x. w + (l:real^3->real^3) x) (convex hull {vec 0,basis 1,basis 2,basis 3}) =
    convex hull {w,a,b,c} /\
    IMAGE (\x. w + (l:real^3->real^3) x) (convex hull {basis 1,basis 2,basis 3}) =
    convex hull {a,b,c}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`l:real^3->real^3`; `w:real^3`;
                     `{vec 0:real^3,basis 1,basis 2,basis 3}`] MOI_SS2_AFFINE_IMAGES);
      MP_TAC(ISPECL [`l:real^3->real^3`; `w:real^3`;
                     `{basis 1:real^3,basis 2,basis 3}`] MOI_SS2_AFFINE_IMAGES)] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN
    AP_TERM_TAC THEN REWRITE_TAC[IMAGE_CLAUSES] THEN BETA_TAC THEN
    REWRITE_TAC[MATCH_MP LINEAR_0 (ASSUME `linear (l:real^3->real^3)`)] THEN
    ASM_REWRITE_TAC[VECTOR_ADD_RID; VECTOR_ARITH `w + (a - w):real^3 = a`];
    ALL_TAC] THEN
  EXISTS_TAC `\x:real^3. w + (l:real^3->real^3) x` THEN
  EXISTS_TAC `\y:real^3. (l':real^3->real^3) (y - w)` THEN
  EXISTS_TAC `convex hull {a:real^3,b,c}` THEN
  SUBGOAL_THEN `~affine_dependent {a:real^3,b,c}` ASSUME_TAC THENL
   [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN
    EXISTS_TAC `{w:real^3,a,b,c}` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_SS2_AFFINE_PLH THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `s:real^3->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `IMAGE (\y:real^3. (l':real^3->real^3) (y - w)) s =
                  IMAGE l' (IMAGE (\y. --w + y) s)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC POLYTOPE_LINEAR_IMAGE THEN ASM_REWRITE_TAC[POLYTOPE_TRANSLATION_EQ];
    MP_TAC(ISPECL [`l:real^3->real^3`; `w:real^3`;
                   `convex hull {basis 1:real^3,basis 2,basis 3}`] MOI_SS2_AFFINE_IMAGES) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2 th)]);
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    EXISTS_TAC `{a:real^3,b,c}` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ASM_SIMP_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_AFFINE_INDEPENDENT] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV)]);;

(* Straightening a ball with a boundary disk onto (k0, F0) on a polytope    *)
(* neighbourhood k2 of k0.                                                    *)

let MOI_S4V_STRAIGHTEN = prove
 (`!w dd jd:real^3->bool.
     PL_SCHOENFLIES_3_AMBIENT_STATEMENT /\
     pl_ball 3 w /\ pl_cell_with_boundary 2 dd jd /\ dd SUBSET frontier w
     ==> ?k2 (chi:real^3->real^3) chi'.
           polytope k2 /\
           convex hull {vec 0,basis 1,basis 2,basis 3} SUBSET interior k2 /\
           pl_homeomorphism (k2,IMAGE chi k2) (chi,chi') /\
           IMAGE chi (convex hull {vec 0,basis 1,basis 2,basis 3}) = w /\
           IMAGE chi (convex hull {basis 1,basis 2,basis 3}) = dd /\
           IMAGE chi (relative_frontier (convex hull {basis 1,basis 2,basis 3})) = jd /\
           (!u. open u /\ u SUBSET interior k2 ==> open (IMAGE chi u))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S4V_BALL_SIDES (ASSUME `pl_ball 3 (w:real^3->bool)`)) THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_SCD_COR_AMBIENT_BALL (ASSUME `PL_SCHOENFLIES_3_AMBIENT_STATEMENT`)) THEN
  DISCH_THEN(MP_TAC o SPECL [`frontier w:real^3->bool`; `(:real^3)`]) THEN
  ASM_REWRITE_TAC[CONVEX_UNIV; OPEN_UNIV; SUBSET_UNIV; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  MP_TAC(REWRITE_RULE[pl_homeomorphism; homeomorphism; IN_UNIV] (ASSUME `pl_homeomorphism ((:real^3),(:real^3)) (f:real^3->real^3,g)`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 (IMAGE (f:real^3->real^3) dd) (IMAGE f jd)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SCD_CELL_IMAGE THEN EXISTS_TAC `g:real^3->real^3` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^3->real^3) dd SUBSET relative_frontier k /\
                IMAGE f jd SUBSET IMAGE f dd` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (f:real^3->real^3) (frontier w) = relative_frontier k` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC IMAGE_SUBSET THEN
      MP_TAC(MATCH_MP MOI_S4L_PL_CELL2_TOPO
        (ASSUME `pl_cell_with_boundary 2 (dd:real^3->bool) jd`)) THEN SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `k:real^3->bool` MOI_S4V_SIMPLEX_STD) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `aa:real^3->real^3` (X_CHOOSE_THEN `aa':real^3->real^3`
    (X_CHOOSE_THEN `ff:real^3->bool` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `IMAGE (f:real^3->real^3) dd`;
                 `IMAGE (f:real^3->real^3) jd`; `ff:real^3->bool`] MOI_SPU_SPHERE_DISK_PLH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ph:real^3->real^3` (X_CHOOSE_THEN `ps:real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `ph:real^3->real^3`; `ps:real^3->real^3`]
    MOI_SPU_EXTEND_SPHERE_PLH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k2:real^3->bool` (X_CHOOSE_THEN `fh:real^3->real^3`
    (X_CHOOSE_THEN `gh:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  MP_TAC(REWRITE_RULE[pl_homeomorphism; homeomorphism] (ASSUME `pl_homeomorphism (relative_frontier k,relative_frontier k)
                   (ph:real^3->real^3,ps)`)) THEN
  STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[pl_homeomorphism; homeomorphism] (ASSUME `pl_homeomorphism (k2,k2) (fh:real^3->real^3,gh)`)) THEN
  STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[pl_homeomorphism; homeomorphism; IN_UNIV] (ASSUME `pl_homeomorphism ((:real^3),(:real^3)) (aa:real^3->real^3,aa')`)) THEN
  STRIP_TAC THEN
  (* images under the boundary homeomorphism *)
  SUBGOAL_THEN `(ff:real^3->bool) SUBSET relative_frontier k` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (ph:real^3->real^3) (IMAGE (f:real^3->real^3) dd) = ff` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `IMAGE (ph:real^3->real^3) (relative_frontier k) = relative_frontier k` THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s SUBSET relative_frontier k
                    ==> IMAGE (gh:real^3->real^3) (IMAGE ph s) = s`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real^3->bool` THEN DISCH_TAC THEN
    MAP_EVERY UNDISCH_TAC
     [`!x. x IN relative_frontier k ==> (fh:real^3->real^3) x = ph x /\ (gh:real^3->real^3) x = ps x`;
      `!x. x IN relative_frontier k ==> (ps:real^3->real^3) (ph x) = x`;
      `IMAGE (ph:real^3->real^3) (relative_frontier k) = relative_frontier k`;
      `(s:real^3->bool) SUBSET relative_frontier k`] THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; SUBSET] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (gh:real^3->real^3) ff = IMAGE (f:real^3->real^3) dd /\
                IMAGE (gh:real^3->real^3) (relative_frontier ff) = IMAGE f jd`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (ph:real^3->real^3) (IMAGE (f:real^3->real^3) dd) = ff`;
      UNDISCH_TAC `IMAGE (ph:real^3->real^3) (IMAGE (f:real^3->real^3) jd) = relative_frontier ff`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`IMAGE (f:real^3->real^3) jd SUBSET IMAGE f dd`;
      `IMAGE (f:real^3->real^3) dd SUBSET relative_frontier k`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. IMAGE (g:real^3->real^3) (IMAGE f s) = s` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN ASM_REWRITE_TAC[IMAGE_ID];
    ALL_TAC] THEN
  (* the polytope neighbourhood of k0 *)
  SUBGOAL_THEN `IMAGE (aa':real^3->real^3) k = convex hull {vec 0,basis 1,basis 2,basis 3}`
  ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (aa:real^3->real^3) (convex hull {vec 0,basis 1,basis 2,basis 3}) = k` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN ASM_REWRITE_TAC[IMAGE_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (aa:real^3->real^3) (IMAGE aa' k2) = k2` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN ASM_REWRITE_TAC[IMAGE_ID]; ALL_TAC] THEN
  SUBGOAL_THEN `polytope (IMAGE (aa':real^3->real^3) k2)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "polytope")) (concl th) &&
      is_forall (concl th))) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  (* the composite *)
  SUBGOAL_THEN
   `pl_homeomorphism (IMAGE (aa':real^3->real^3) k2,IMAGE (g:real^3->real^3) k2)
      ((g:real^3->real^3) o (gh:real^3->real^3) o (aa:real^3->real^3),
       (((aa':real^3->real^3) o (fh:real^3->real^3)) o (f:real^3->real^3)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `k2:real^3->bool` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `k2:real^3->bool` THEN
      CONJ_TAC THENL
       [MP_TAC(ISPECL [`(:real^3)`; `(:real^3)`; `aa:real^3->real^3`; `aa':real^3->real^3`;
                       `IMAGE (aa':real^3->real^3) k2`] MOI_S27_PLH_RESTRICT) THEN
        ASM_SIMP_TAC[SUBSET_UNIV; LOCALLY_POLYHEDRAL_POLYTOPE];
        ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN FIRST_ASSUM ACCEPT_TAC];
      MP_TAC(ISPECL [`(:real^3)`; `(:real^3)`; `g:real^3->real^3`; `f:real^3->real^3`;
                     `k2:real^3->bool`] MOI_S27_PLH_RESTRICT) THEN
      ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN
      ASM_SIMP_TAC[SUBSET_UNIV; LOCALLY_POLYHEDRAL_POLYTOPE]];
    ALL_TAC] THEN
  MP_TAC(REWRITE_RULE[pl_homeomorphism; homeomorphism] (ASSUME
   `pl_homeomorphism (IMAGE (aa':real^3->real^3) k2,IMAGE (g:real^3->real^3) k2)
      ((g:real^3->real^3) o (gh:real^3->real^3) o (aa:real^3->real^3),
       (((aa':real^3->real^3) o (fh:real^3->real^3)) o (f:real^3->real^3)))`)) THEN
  STRIP_TAC THEN
  EXISTS_TAC `IMAGE (aa':real^3->real^3) k2` THEN
  EXISTS_TAC `(g:real^3->real^3) o (gh:real^3->real^3) o (aa:real^3->real^3)` THEN
  EXISTS_TAC `((aa':real^3->real^3) o (fh:real^3->real^3)) o (f:real^3->real^3)` THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    (* k0 inside the interior *)
    UNDISCH_TAC `IMAGE (aa':real^3->real^3) k = convex hull {vec 0,basis 1,basis 2,basis 3}` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (aa':real^3->real^3) (interior k2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC INTERIOR_MAXIMAL THEN CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTERIOR_SUBSET];
        MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN REWRITE_TAC[OPEN_INTERIOR] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
          ASM_REWRITE_TAC[SUBSET_UNIV];
          MP_TAC(ASSUME `!y. (aa:real^3->real^3) (aa' y) = y`) THEN MESON_TAC[]]]];
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (f:real^3->real^3) w = k` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[];
    (* open images inside *)
    X_GEN_TAC `u:real^3->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `u SUBSET IMAGE (aa':real^3->real^3) k2` ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `interior (IMAGE (aa':real^3->real^3) k2)` THEN
      ASM_REWRITE_TAC[INTERIOR_SUBSET];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (aa':real^3->real^3) k2` THEN ASM_REWRITE_TAC[];
      MP_TAC(ASSUME `!x. x IN IMAGE (aa':real^3->real^3) k2
                         ==> ((((aa':real^3->real^3) o (fh:real^3->real^3)) o (f:real^3->real^3))
                              (((g:real^3->real^3) o (gh:real^3->real^3) o (aa:real^3->real^3)) x)) = x`) THEN
      UNDISCH_TAC `u SUBSET IMAGE (aa':real^3->real^3) k2` THEN
      REWRITE_TAC[SUBSET] THEN MESON_TAC[]]]);;

(* The outward push. *)

let MOI_S4V_OUTWARD_PUSH = prove
 (`!w dd jd oo:real^3->bool.
     PL_SCHOENFLIES_3_AMBIENT_STATEMENT /\
     pl_ball 3 w /\ pl_cell_with_boundary 2 dd jd /\ dd SUBSET frontier w /\
     open oo /\ dd SUBSET oo
     ==> ?w2 y. pl_ball 3 w2 /\ compact y /\ w2 = w UNION y /\ y SUBSET oo /\
                y INTER w SUBSET dd /\ dd DIFF jd SUBSET interior w2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`w:real^3->bool`; `dd:real^3->bool`; `jd:real^3->bool`]
    MOI_S4V_STRAIGHTEN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k2:real^3->bool` (X_CHOOSE_THEN `chi:real^3->real^3`
    (X_CHOOSE_THEN `chi':real^3->real^3` STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `k0 = convex hull {vec 0:real^3,basis 1,basis 2,basis 3}` THEN
  ABBREV_TAC `f0 = convex hull {basis 1:real^3,basis 2,basis 3}` THEN
  SUBGOAL_THEN `homeomorphism (k2,IMAGE chi k2) (chi:real^3->real^3,chi')` ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (k2,IMAGE chi k2) (chi:real^3->real^3,chi')` THEN
    SIMP_TAC[pl_homeomorphism];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `compact (k0:real^3->bool) /\ compact (f0:real^3->bool) /\
                f0 SUBSET k0 /\ compact (k2:real^3->bool) /\ interior k2 SUBSET k2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "k0" THEN EXPAND_TAC "f0" THEN
    REWRITE_TAC[INTERIOR_SUBSET] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONVEX_HULL THEN
      MATCH_MP_TAC FINITE_IMP_COMPACT THEN REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
      MATCH_MP_TAC COMPACT_CONVEX_HULL THEN
      MATCH_MP_TAC FINITE_IMP_COMPACT THEN REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      ASM_SIMP_TAC[POLYTOPE_IMP_COMPACT]];
    ALL_TAC] THEN
  (* room inside k2 *)
  MP_TAC(ISPECL [`k0:real^3->bool`; `interior k2:real^3->bool`] MOI_S4Q_COMPACT_IN_OPEN) THEN
  ASM_REWRITE_TAC[OPEN_INTERIOR] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
  (* the preimage of o near f0 *)
  SUBGOAL_THEN `?e2. &0 < e2 /\
                     !x y. x IN f0 /\ y IN k2 /\ dist(x,y) < e2
                           ==> (chi:real^3->real^3) y IN oo` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`chi:real^3->real^3`; `k2:real^3->bool`; `oo:real^3->bool`]
      CONTINUOUS_OPEN_IN_PREIMAGE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_OPEN]) THEN
    DISCH_THEN(X_CHOOSE_THEN `vv:real^3->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`f0:real^3->bool`; `vv:real^3->bool`] MOI_S4Q_COMPACT_IN_OPEN) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(x:real^3) IN {z | z IN k2 /\ (chi:real^3->real^3) z IN oo}` MP_TAC THENL
       [REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
         [ASM SET_TAC[];
          UNDISCH_TAC `IMAGE (chi:real^3->real^3) f0 = dd` THEN
          UNDISCH_TAC `(dd:real^3->bool) SUBSET oo` THEN ASM SET_TAC[]];
        ASM SET_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN {z | z IN k2 /\ (chi:real^3->real^3) z IN oo}` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_INTER] THEN ASM_MESON_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `t = min (&1 / &2) (min (e1 / &2) (e2 / &3))` THEN
  SUBGOAL_THEN `&0 < t /\ t <= &1 /\ t < e1 /\ &2 * t < e2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `t:real` MOI_S4V_STD_SLAB) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `kt = IMAGE (\x:real^3. (&1 + t) % x) k0` THEN
  ABBREV_TAC `y0 = {x:real^3 | x IN kt /\ &1 <= x$1 + x$2 + x$3}` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(kt:real^3->bool) SUBSET interior k2` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `t:real`)) (concl th) &&
      not (can (find_term ((=) `&1 <= (x:real^3)$1 + x$2 + x$3`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `z:real^3` THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (chi:real^3->real^3) kt`; `IMAGE (chi:real^3->real^3) y0`] THEN
  REPEAT CONJ_TAC THENL
   [(* a PL ball *)
    REWRITE_TAC[pl_ball] THEN
    MAP_EVERY EXISTS_TAC [`kt:real^3->bool`; `chi:real^3->real^3`; `chi':real^3->real^3`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_SCD_PLH_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`k2:real^3->bool`; `IMAGE (chi:real^3->real^3) k2`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `polytope (kt:real^3->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE]; ALL_TAC] THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_POLYTOPE] THEN
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN
    ASM_SIMP_TAC[POLYTOPE_IMP_PL_POLYHEDRON] THEN
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `k2:real^3->bool` THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_POLYTOPE] THEN CONJ_TAC THENL
     [UNDISCH_TAC `pl_homeomorphism (k2,IMAGE chi k2) (chi:real^3->real^3,chi')` THEN
      SIMP_TAC[pl_homeomorphism];
      ASM SET_TAC[]];
    (* compact *)
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `k2:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "y0" THEN ASM SET_TAC[];
    (* w2 = w UNION y *)
    UNDISCH_TAC `IMAGE (chi:real^3->real^3) k0 = w` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM IMAGE_UNION] THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN EXPAND_TAC "y0" THEN ASM_REWRITE_TAC[];
    (* y inside o *)
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o check (fun th ->
      is_forall (concl th) &&
      can (find_term ((=) `&1 <= (x:real^3)$1 + x$2 + x$3`)) (concl th))) THEN
    ANTS_TAC THENL [UNDISCH_TAC `(x:real^3) IN y0` THEN EXPAND_TAC "y0" THEN
                    REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN y0` THEN EXPAND_TAC "y0" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ASM SET_TAC[];
      ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC];
    (* y meets w only in dd *)
    UNDISCH_TAC `IMAGE (chi:real^3->real^3) k0 = w` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `IMAGE (chi:real^3->real^3) f0 = dd` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `y0 INTER k0 = f0:real^3->bool` THEN
    SUBGOAL_THEN `(y0:real^3->bool) SUBSET k2 /\ k0 SUBSET k2` MP_TAC THENL
     [EXPAND_TAC "y0" THEN ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `!x. x IN k2 ==> (chi':real^3->real^3) (chi x) = x` THEN
    SET_TAC[];
    (* the open disk is interior *)
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (chi:real^3->real^3) (interior kt)` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `dd DIFF jd = IMAGE (chi:real^3->real^3) (relative_interior f0)`
      SUBST1_TAC THENL
       [UNDISCH_TAC `IMAGE (chi:real^3->real^3) f0 = dd` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        UNDISCH_TAC `IMAGE (chi:real^3->real^3) (relative_frontier f0) = jd` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        REWRITE_TAC[relative_frontier] THEN
        SUBGOAL_THEN `closure f0 = f0:real^3->bool` SUBST1_TAC THENL
         [ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
        MP_TAC(ISPEC `f0:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
        SUBGOAL_THEN `(f0:real^3->bool) SUBSET k2` MP_TAC THENL
         [ASM SET_TAC[]; ALL_TAC] THEN
        UNDISCH_TAC `!x. x IN k2 ==> (chi':real^3->real^3) (chi x) = x` THEN
        SET_TAC[];
        MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC INTERIOR_MAXIMAL THEN CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTERIOR_SUBSET];
        FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[OPEN_INTERIOR] THEN
        MP_TAC(ISPEC `kt:real^3->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[]]]]);;

(* ------------------------------------------------------------------------- *)
(* The clean case.  Basic facts on d (MOI_S4V_SETUP), the open              *)
(* set O around d (MOI_S4V_O_CHOICE), the trace of the face ball on the     *)
(* pocket side is j alone (MOI_S4V_CLEAN_SIDE), and the new ball: the       *)
(* filled pocket pushed beyond d plus a collar of j (MOI_S4V_CLEAN_BALL).    *)
(* ------------------------------------------------------------------------- *)

let MOI_S4V_SETUP = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v d j.
     moi_s34_tube tt kk /\ moi_s34_emb h (UNIONS tt) /\
     moi_s34_frame tt kk h ep f1 car /\ moi_s34_fbinv tt kk h f1 car cb /\
     s IN moi_s34_simp kk (&2) /\
     moi_s34_op1w tt kk f1 cb s v d j /\ DISJOINT (d DIFF j) (cb s)
     ==> v IN s /\ {v} IN kk /\ pl_ball 3 (cb s) /\
         pl_cell_with_boundary 2 d j /\ compact d /\ compact j /\ j SUBSET d /\
         ~(j = {}) /\ connected j /\ contractible d /\
         d SUBSET IMAGE f1 (moi_s34_vb tt kk v) /\
         d SUBSET IMAGE f1 (moi_s34_bd tt kk) /\
         d SUBSET IMAGE f1 (moi_s34_ft tt kk s) /\
         d SUBSET car s /\ frontier (cb s) SUBSET car s /\
         d INTER frontier (cb s) = j /\ d INTER cb s = j /\
         j SUBSET moi_s34_trace tt kk f1 (cb s) /\
         (!w. {w} IN kk /\ ~(w IN s) ==> DISJOINT d (IMAGE f1 (moi_s34_vb tt kk w))) /\
         (!s'. s' IN moi_s34_simp kk (&2) /\ ~(s' = s) ==> DISJOINT d (cb s')) /\
         DISJOINT d (moi_s34_rims tt kk f1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_s34_op1w tt kk (f1:real^N->real^3) cb s v d j` THEN
  REWRITE_TAC[moi_s34_op1w] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`] MOI_S4L_TRACE_COMP_FACTS) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  MP_TAC(MATCH_MP MOI_S4L_PL_CELL2_TOPO
    (ASSUME `pl_cell_with_boundary 2 (d:real^3->bool) j`)) THEN STRIP_TAC THEN
  SUBGOAL_THEN `d SUBSET IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) /\
                d SUBSET IMAGE f1 (moi_s34_bd tt kk)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(j:real^3->bool) SUBSET moi_s34_trace tt kk (f1:real^N->real^3) ((cb:(real^N->bool)->real^3->bool) s)`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_s34_trace] THEN
    MAP_EVERY UNDISCH_TAC [`d INTER frontier ((cb:(real^N->bool)->real^3->bool) s) = j`;
                           `d SUBSET IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N) IN s` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `s:real^N->bool`;
                   `(cb:(real^N->bool)->real^3->bool) s`; `v:real^N`; `j:real^3->bool`]
      MOI_S4L_TRACE_AT_V) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_s34_fb1 tt kk h (f1:real^N->real^3) car s (cb s)` THEN
  REWRITE_TAC[moi_s34_fb1] THEN STRIP_TAC THEN
  (* the frame facts used *)
  SUBGOAL_THEN `(s:real^N->bool) IN kk /\ ~(s = {})` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(s:real^N->bool) IN moi_s34_simp kk (&2)` THEN
    REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `aff_dim({}:real^N->bool) = &2` THEN
    REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) SUBSET car {v} /\
                car {v:real^N} SUBSET car s /\
                IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) INTER
                interior (IMAGE f1 (moi_s34_nb tt kk)) = {}` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s34_frame tt kk (h:real^N->real^3) ep f1 car` THEN
    REWRITE_TAC[moi_s34_frame] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N` o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "pl_ball")) (concl th) &&
        is_forall (concl th))) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPECL [`{v:real^N}`; `s:real^N->bool`] o check (fun th ->
        is_forall (concl th) &&
        (let t = snd(strip_forall (concl th)) in
         is_imp t && is_comb (rand t) && fst(strip_comb(rand t)) = `(SUBSET):(real^3->bool)->(real^3->bool)->bool` &&
         can (find_term ((=) `q':real^N->bool`)) t))) THEN
      ASM_REWRITE_TAC[NOT_INSERT_EMPTY; SING_SUBSET];
      UNDISCH_TAC `IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk) DIFF
                   interior (IMAGE f1 (moi_s34_nb tt kk)) = IMAGE f1 (moi_s34_bd tt kk)` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* compact j *)
    UNDISCH_TAC `d INTER frontier ((cb:(real^N->bool)->real^3->bool) s) = j` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
    ASM_REWRITE_TAC[FRONTIER_CLOSED];
    (* contractible d *)
    UNDISCH_TAC `pl_cell_with_boundary 2 (d:real^3->bool) j` THEN
    REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `ff:real^3->real^3`
      (X_CHOOSE_THEN `gg:real^3->real^3` STRIP_ASSUME_TAC))) THEN
    MP_TAC(ISPECL [`k:real^3->bool`; `d:real^3->bool`] HOMEOMORPHIC_CONTRACTIBLE) THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[homeomorphic] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC CONVEX_IMP_CONTRACTIBLE THEN ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]];
    (* d in the face torus *)
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[moi_s34_ft] THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `z:real^N` THEN
    DISCH_TAC THEN EXISTS_TAC `moi_s34_vb tt kk (v:real^N)` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[];
    (* d in car s *)
    ASM SET_TAC[];
    (* d INTER cb s = j *)
    MAP_EVERY UNDISCH_TAC [`d INTER frontier ((cb:(real^N->bool)->real^3->bool) s) = j`;
                           `DISJOINT (d DIFF j) ((cb:(real^N->bool)->real^3->bool) s)`;
                           `frontier ((cb:(real^N->bool)->real^3->bool) s) SUBSET cb s`] THEN
    SET_TAC[];
    (* foreign vertex balls *)
    X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `v:real^N`; `w:real^N`;
                   `y:real^3`] MOI_S4L_AV_NO_OTHER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]; ASM SET_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[moi_s34_rims; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `g:real^N->bool` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s34_sd")) (concl th) &&
      can (find_term ((=) `DISJOINT:(real^3->bool)->(real^3->bool)->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`(y:real^3) IN t`; `(y:real^3) IN d`] THEN
    REWRITE_TAC[ASSUME `t = IMAGE (f1:real^N->real^3)
                              (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)`] THEN
    SET_TAC[];
    (* other face balls *)
    X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(cb:(real^N->bool)->real^3->bool) s INTER cb t SUBSET
                  interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk))` MP_TAC THENL
     [UNDISCH_TAC `moi_s34_fbinv tt kk h (f1:real^N->real^3) car cb` THEN
      REWRITE_TAC[moi_s34_fbinv; moi_s34_fb2] THEN
      DISCH_THEN(MP_TAC o SPECL [`s:real^N->bool`; `t:real^N->bool`] o CONJUNCT2) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real^N->bool` o check (fun th ->
      is_forall (concl th) &&
      can (find_term ((=) `(d:real^3->bool) DIFF j`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) INTER
       interior (IMAGE f1 (moi_s34_nb tt kk)) = {}`;
      `d SUBSET IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`;
      `(j:real^3->bool) SUBSET d`;
      `d INTER frontier ((cb:(real^N->bool)->real^3->bool) s) = j`;
      `frontier ((cb:(real^N->bool)->real^3->bool) s) SUBSET cb s`] THEN
    SET_TAC[];
    (* the rims *)
    REWRITE_TAC[moi_s34_rims; DISJOINT; INTER_UNIONS; EMPTY_UNIONS; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `g:real^N->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `g:real^N->bool` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s34_sd")) (concl th) &&
      can (find_term ((=) `DISJOINT:(real^3->bool)->(real^3->bool)->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`f1:real^N->real^3`; `moi_s34_sd tt kk (g:real^N->bool) INTER moi_s34_bd tt kk`;
                   `moi_s34_sd tt kk (g:real^N->bool)`] IMAGE_SUBSET) THEN
    ANTS_TAC THENL [SET_TAC[]; ALL_TAC] THEN SET_TAC[]]);;


let MOI_S4V_O_CHOICE = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v d j.
     moi_s34_tube tt kk /\ moi_s34_emb h (UNIONS tt) /\
     moi_s34_frame tt kk h ep f1 car /\ moi_s34_fbinv tt kk h f1 car cb /\
     s IN moi_s34_simp kk (&2) /\
     moi_s34_op1w tt kk f1 cb s v d j /\ DISJOINT (d DIFF j) (cb s)
     ==> ?oo. open oo /\ d SUBSET oo /\ oo SUBSET car s /\
             (!w. {w} IN kk /\ ~(w IN s) ==> DISJOINT oo (IMAGE f1 (moi_s34_vb tt kk w))) /\
             (!s'. s' IN moi_s34_simp kk (&2) /\ ~(s' = s) ==> DISJOINT oo (cb s')) /\
             oo INTER IMAGE f1 (moi_s34_bd tt kk) SUBSET d UNION interior (cb s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`; `v:real^N`;
                 `d:real^3->bool`; `j:real^3->bool`] MOI_S4V_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the KEY_OUT neighbourhoods *)
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`; `v:real^N`;
                 `d:real^3->bool`; `j:real^3->bool`] MOI_S4V_KEY_OUT) THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `uu:real^3->real^3->bool`) THEN
  (* points of d lie in the carriers and in no foreign vertex ball *)
  SUBGOAL_THEN `!y:real^3. y IN d ==> y IN UNIONS {(car:(real^N->bool)->real^3->bool) q | q | q IN (kk:(real^N->bool)->bool) /\ ~(q = {})}`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `(car:(real^N->bool)->real^3->bool) s` THEN CONJ_TAC THENL
     [EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(s:real^N->bool) IN moi_s34_simp kk (&2)` THEN
      REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `aff_dim({}:real^N->bool) = &2` THEN
      REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^3. y IN d
               ==> ?w. open w /\ y IN w /\
                       !v'. {v'} IN kk /\ ~(v' IN s)
                            ==> DISJOINT w (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v'))`
  MP_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                   `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `s:real^N->bool`; `y:real^3`]
      MOI_S4N_POINT_AVOID) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
    X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^N` o check (fun th ->
      is_forall (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s34_vb")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(y:real^3) IN d` THEN SET_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `ww:real^3->real^3->bool`) THEN
  (* the other face balls *)
  MP_TAC(ISPECL [`d:real^3->bool`; `{t:real^N->bool | t IN moi_s34_simp kk (&2) /\ ~(t = s)}`;
                 `cb:(real^N->bool)->real^3->bool`] MOI_S4Q_AVOID) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC MOI_S4D_PL_BALL_COMPACT THEN
        EXISTS_TAC `3` THEN
        UNDISCH_TAC `moi_s34_fbinv tt kk h (f1:real^N->real^3) car cb` THEN
        REWRITE_TAC[moi_s34_fbinv; moi_s34_fb1] THEN
        DISCH_THEN(MP_TAC o SPEC `t:real^N->bool` o CONJUNCT1) THEN ASM_SIMP_TAC[];
        ASM_SIMP_TAC[]];
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      REWRITE_TAC[GSYM CONJ_ASSOC] THEN
      MATCH_MP_TAC MOI_S4V_FB_AVOID THEN
      MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `h:real^N->real^3`; `ep:real^N->real`;
                            `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
      UNDISCH_TAC `(y:real^3) IN d` THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real^N->bool` o check (fun th ->
        is_forall (concl th) &&
        can (find_term (fun tm -> is_const tm && fst(dest_const tm) = "DISJOINT")) (concl th) &&
        can (find_term ((=) `(cb:(real^N->bool)->real^3->bool) s'`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `w3:real^3->bool` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC `UNIONS (IMAGE (uu:real^3->real^3->bool) d) INTER
              UNIONS (IMAGE (ww:real^3->real^3->bool) d) INTER w3 INTER
              (car:(real^N->bool)->real^3->bool) s` THEN
  SUBGOAL_THEN `open ((car:(real^N->bool)->real^3->bool) s)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s34_frame tt kk (h:real^N->real^3) ep f1 car` THEN
    REWRITE_TAC[moi_s34_frame] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "open")) (concl th) &&
      is_forall (concl th))) THEN
    SUBGOAL_THEN `(s:real^N->bool) IN kk /\ ~(s = {})` (fun th -> SIMP_TAC[th]) THEN
    UNDISCH_TAC `(s:real^N->bool) IN moi_s34_simp kk (&2)` THEN
    REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `aff_dim({}:real^N->bool) = &2` THEN
    REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_UNIONS THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_MESON_TAC[];
    REWRITE_TAC[SUBSET_INTER] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN ASM_MESON_TAC[];
      REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN ASM_MESON_TAC[];
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC];
    SET_TAC[];
    X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
    MATCH_MP_TAC(SET_RULE
     `!a b c e t:real^3->bool. DISJOINT b t ==> DISJOINT (a INTER b INTER c INTER e) t`) THEN
    REWRITE_TAC[SET_RULE `DISJOINT (UNIONS s) (t:real^3->bool) <=>
                          !x. x IN s ==> DISJOINT x t`; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
      is_forall (concl th) &&
      can (find_term ((=) `ww:real^3->real^3->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `w:real^N` o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real^N->bool` o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `w3:real^3->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    MATCH_MP_TAC(SET_RULE
     `!a b c e t u:real^3->bool.
        a INTER t SUBSET u ==> (a INTER b INTER c INTER e) INTER t SUBSET u`) THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    X_GEN_TAC `z:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
      is_forall (concl th) &&
      can (find_term ((=) `uu:real^3->real^3->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[SUBSET; IN_INTER] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;


(* The frontier is local. *)

let MOI_S4V_FRONTIER_LOCAL = prove
 (`!s t u:real^N->bool.
     open u /\ s INTER u = t INTER u ==> frontier s INTER u = frontier t INTER u`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!a b:real^N->bool. a INTER u = b INTER u
                  ==> closure a INTER u SUBSET closure b INTER u` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`u:real^N->bool`; `a:real^N->bool`] OPEN_INTER_CLOSURE_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[INTER_COMM] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`b:real^N->bool`; `u:real^N->bool`] CLOSURE_INTER_SUBSET) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior s INTER u = interior t INTER (u:real^N->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^N->bool`; `u:real^N->bool`] INTERIOR_INTER) THEN
    MP_TAC(ISPECL [`t:real^N->bool`; `u:real^N->bool`] INTERIOR_INTER) THEN
    ASM_SIMP_TAC[INTERIOR_OPEN];
    ALL_TAC] THEN
  REWRITE_TAC[frontier] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPECL [`s:real^N->bool`; `t:real^N->bool`] th) THEN
                          MP_TAC(SPECL [`t:real^N->bool`; `s:real^N->bool`] th)) THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `interior s INTER u = interior t INTER (u:real^N->bool)` THEN
  SET_TAC[]);;

(* Near a crossing point of frontier c and B there are points of B outside c. *)

let MOI_S4V_CROSS_OUT = prove
 (`!c b (x:real^3) u.
     closed c /\ pl_crossing_at (frontier c) b x /\ x IN frontier c /\
     open u /\ x IN u
     ==> ?y. y IN u /\ y IN b /\ ~(y IN c)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`frontier c:real^3->bool`; `b:real^3->bool`; `x:real^3`; `u:real^3->bool`]
    MOI_S4N_BALL_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:real^3->bool` (X_CHOOSE_THEN `phi:real^3->real^3`
    (X_CHOOSE_THEN `psi:real^3->real^3` (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC)))) THEN
  (* each half ball maps into c or misses c *)
  SUBGOAL_THEN
   `!sg. IMAGE (psi:real^3->real^3) {z | z IN ball(vec 0,r) /\ &0 < sg * z$1} SUBSET c \/
         IMAGE psi {z | z IN ball(vec 0,r) /\ &0 < sg * z$1} INTER c = {}`
  ASSUME_TAC THENL
   [X_GEN_TAC `sg:real` THEN
    ABBREV_TAC `hh = IMAGE (psi:real^3->real^3) {z | z IN ball(vec 0,r) /\ &0 < sg * z$1}` THEN
    SUBGOAL_THEN `connected (hh:real^3->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "hh" THEN MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:real^3,r)` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        MATCH_MP_TAC CONVEX_CONNECTED THEN
        REWRITE_TAC[SET_RULE `{z:real^3 | z IN s /\ P z} = s INTER {z | P z}`] THEN
        MATCH_MP_TAC CONVEX_INTER THEN REWRITE_TAC[CONVEX_BALL] THEN
        SUBGOAL_THEN `{z:real^3 | &0 < sg * z$1} = {z | (sg % basis 1) dot z > &0}`
        SUBST1_TAC THENL
         [SIMP_TAC[EXTENSION; IN_ELIM_THM; DOT_LMUL; DOT_BASIS; DIMINDEX_3; ARITH] THEN
          REAL_ARITH_TAC;
          REWRITE_TAC[CONVEX_HALFSPACE_GT]]];
      ALL_TAC] THEN
    SUBGOAL_THEN `DISJOINT (hh:real^3->bool) (frontier c)` ASSUME_TAC THENL
     [EXPAND_TAC "hh" THEN REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; IN_ELIM_THM;
                                        NOT_IN_EMPTY] THEN
      X_GEN_TAC `w:real^3` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) MP_TAC) THEN
      ASM_SIMP_TAC[] THEN DISCH_TAC THEN
      UNDISCH_TAC `&0 < sg * (z:real^3)$1` THEN ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_LT_REFL];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`hh:real^3->bool`; `c:real^3->bool`] CONNECTED_INTER_FRONTIER) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `DISJOINT (hh:real^3->bool) (frontier c)` THEN SET_TAC[];
    ALL_TAC] THEN
  (* not both halves inside c *)
  ASM_CASES_TAC
   `IMAGE (psi:real^3->real^3) {z | z IN ball(vec 0,r) /\ &0 < &1 * z$1} INTER c = {}` THENL
   [EXISTS_TAC `(psi:real^3->real^3) ((r / &2) % basis 1)` THEN
    SUBGOAL_THEN `(r / &2) % basis 1 IN ball(vec 0:real^3,r) /\
                  ((r / &2) % basis 1:real^3)$1 = r / &2 /\
                  ((r / &2) % basis 1:real^3)$2 = &0` STRIP_ASSUME_TAC THENL
     [SIMP_TAC[IN_BALL_0; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; VECTOR_MUL_COMPONENT;
               BASIS_COMPONENT] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[SUBSET];
      ASM_SIMP_TAC[];
      UNDISCH_TAC
       `IMAGE (psi:real^3->real^3) {z | z IN ball(vec 0,r) /\ &0 < &1 * z$1} INTER c = {}` THEN
      REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE; IN_ELIM_THM; NOT_IN_EMPTY] THEN
      DISCH_THEN(MP_TAC o SPEC `(psi:real^3->real^3) ((r / &2) % basis 1)`) THEN
      REWRITE_TAC[DE_MORGAN_THM; NOT_EXISTS_THM] THEN
      MATCH_MP_TAC(TAUT `~a ==> a \/ b ==> b`) THEN
      DISCH_THEN(MP_TAC o SPEC `(r / &2) % basis 1:real^3`) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC
   `IMAGE (psi:real^3->real^3) {z | z IN ball(vec 0,r) /\ &0 < -- &1 * z$1} INTER c = {}` THENL
   [EXISTS_TAC `(psi:real^3->real^3) (--(r / &2) % basis 1)` THEN
    SUBGOAL_THEN `--(r / &2) % basis 1 IN ball(vec 0:real^3,r) /\
                  (--(r / &2) % basis 1:real^3)$1 = --(r / &2) /\
                  (--(r / &2) % basis 1:real^3)$2 = &0` STRIP_ASSUME_TAC THENL
     [SIMP_TAC[IN_BALL_0; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; VECTOR_MUL_COMPONENT;
               BASIS_COMPONENT; REAL_ABS_NEG] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[SUBSET];
      ASM_SIMP_TAC[];
      UNDISCH_TAC
       `IMAGE (psi:real^3->real^3) {z | z IN ball(vec 0,r) /\ &0 < -- &1 * z$1} INTER c = {}` THEN
      REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE; IN_ELIM_THM; NOT_IN_EMPTY] THEN
      DISCH_THEN(MP_TAC o SPEC `(psi:real^3->real^3) (--(r / &2) % basis 1)`) THEN
      REWRITE_TAC[DE_MORGAN_THM; NOT_EXISTS_THM] THEN
      MATCH_MP_TAC(TAUT `~a ==> a \/ b ==> b`) THEN
      DISCH_THEN(MP_TAC o SPEC `--(r / &2) % basis 1:real^3`) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* both halves in c: then U SUBSET c, so x is interior *)
  SUBGOAL_THEN `(U:real^3->bool) SUBSET c` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(w:real^3) = psi((phi:real^3->real^3) w) /\ phi w IN ball(vec 0,r)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ABBREV_TAC `z = (phi:real^3->real^3) w` THEN
    ASM_CASES_TAC `(z:real^3)$1 = &0` THENL
     [SUBGOAL_THEN `(w:real^3) IN frontier c` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[FRONTIER_SUBSET_CLOSED; REWRITE_RULE[SUBSET] FRONTIER_SUBSET_CLOSED];
      ALL_TAC] THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[REAL_ARITH `~(a = &0) <=> &0 < &1 * a \/
                                                    &0 < -- &1 * a`]) THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `&1`);
      FIRST_X_ASSUM(MP_TAC o SPEC `-- &1`)] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN interior c` MP_TAC THENL
   [REWRITE_TAC[IN_INTERIOR] THEN
    UNDISCH_TAC `open (U:real^3->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC[];
    UNDISCH_TAC `(x:real^3) IN frontier c` THEN REWRITE_TAC[frontier] THEN SET_TAC[]]);;

(* In the clean case the trace of c on the pocket disk e is the rim j. *)

let MOI_S4V_CLEAN_SIDE = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v d j q e e'.
     PL_SCHOENFLIES_3_STATEMENT /\ PL_SCHOENFLIES_3_AMBIENT_STATEMENT /\
     moi_s34_tube tt kk /\ moi_s34_emb h (UNIONS tt) /\
     moi_s34_frame tt kk h ep f1 car /\ moi_s34_fbinv tt kk h f1 car cb /\
     s IN moi_s34_simp kk (&2) /\
     moi_s34_op1w tt kk f1 cb s v d j /\ DISJOINT (d DIFF j) (cb s) /\
     moi_s4v_pocket (cb s) d j q e e' /\ moi_s4v_clean tt kk f1 s q
     ==> e INTER IMAGE f1 (moi_s34_bd tt kk) = j /\
         (!s'. s' IN moi_s34_simp kk (&2) /\ ~(s' = s)
               ==> q INTER cb s' SUBSET interior (IMAGE f1 (moi_s34_nb tt kk)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`; `v:real^N`;
                 `d:real^3->bool`; `j:real^3->bool`] MOI_S4V_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`] MOI_S4L_TRACE_COMP_FACTS) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[moi_s34_fb1] THEN STRIP_TAC] THEN
  UNDISCH_TAC `moi_s4v_pocket ((cb:(real^N->bool)->real^3->bool) s) d j q e e'` THEN
  REWRITE_TAC[moi_s4v_pocket] THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_s4v_clean tt kk (f1:real^N->real^3) s q` THEN
  REWRITE_TAC[moi_s4v_clean] THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S4V_BALL_SIDES (ASSUME `pl_ball 3 (q:real^3->bool)`)) THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S4L_FRAME_F1
    (ASSUME `moi_s34_frame tt kk (h:real^N->real^3) ep f1 car`)) THEN STRIP_TAC THEN
  (* the tube is the union of the vertex balls *)
  SUBGOAL_THEN
   `!y. y IN IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)
        ==> ?w. {w} IN kk /\ y IN IMAGE f1 (moi_s34_vb tt kk w)`
  ASSUME_TAC THENL
   [MP_TAC(MATCH_MP MOI_S4J_NB_FACTS (ASSUME `moi_s34_tube tt (kk:(real^N->bool)->bool)`)) THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    REWRITE_TAC[IN_IMAGE; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) SUBSET IMAGE f1 (moi_s34_nb tt kk)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN
    MP_TAC(MATCH_MP MOI_S4J_NB_FACTS (ASSUME `moi_s34_tube tt (kk:(real^N->bool)->bool)`)) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. {w} IN kk /\ w IN s
        ==> IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w) SUBSET IMAGE f1 (moi_s34_ft tt kk s)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[moi_s34_ft] THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `z:real^N` THEN
    DISCH_TAC THEN EXISTS_TAC `moi_s34_vb tt kk (w:real^N)` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. interior (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk r)) SUBSET
        interior (IMAGE f1 (moi_s34_nb tt kk))`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SUBSET_INTERIOR THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    MP_TAC(MATCH_MP MOI_S4J_NB_FACTS (ASSUME `moi_s34_tube tt (kk:(real^N->bool)->bool)`)) THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN REWRITE_TAC[moi_s34_ft] THEN
    MATCH_MP_TAC SUBSET_UNIONS THEN SET_TAC[];
    ALL_TAC] THEN
  (* in int q the tube is the face torus T of s *)
  SUBGOAL_THEN
   `!y. y IN interior q /\ y IN IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)
        ==> y IN IMAGE f1 (moi_s34_ft tt kk s)`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    MP_TAC(MP (SPEC `y:real^3` (ASSUME
     `!y. y IN IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)
          ==> ?w. {w} IN kk /\ y IN IMAGE f1 (moi_s34_vb tt kk w)`))
      (ASSUME `(y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `(w:real^N) IN s` THENL
     [MP_TAC(MP (SPEC `w:real^N` (ASSUME
       `!w. {w} IN kk /\ w IN s
            ==> IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w) SUBSET
                IMAGE f1 (moi_s34_ft tt kk s)`))
        (CONJ (ASSUME `{w:real^N} IN kk`) (ASSUME `(w:real^N) IN s`))) THEN
      UNDISCH_TAC `(y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w)` THEN
      SET_TAC[];
      MP_TAC(MP (SPEC `w:real^N` (ASSUME
       `!w. {w} IN kk /\ ~(w IN s)
            ==> DISJOINT q (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w))`))
        (CONJ (ASSUME `{w:real^N} IN kk`) (ASSUME `~((w:real^N) IN s)`))) THEN
      MP_TAC(ISPEC `q:real^3->bool` INTERIOR_SUBSET) THEN
      MAP_EVERY UNDISCH_TAC
       [`(y:real^3) IN interior q`;
        `(y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w)`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  (* points of B in int q are impossible *)
  SUBGOAL_THEN `!y. y IN interior q ==> ~(y IN IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk))`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)` ASSUME_TAC THENL
     [MATCH_MP_TAC(ASSUME
       `!y. y IN interior q /\ y IN IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)
            ==> y IN IMAGE f1 (moi_s34_ft tt kk s)`) THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC
       [`(y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`;
        `IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) SUBSET IMAGE f1 (moi_s34_nb tt kk)`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((y:real^3) IN interior (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)))`
    ASSUME_TAC THENL
     [MP_TAC(SPEC `s:real^N->bool` (ASSUME
       `!r. interior (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk r)) SUBSET
            interior (IMAGE f1 (moi_s34_nb tt kk))`)) THEN
      MAP_EVERY UNDISCH_TAC
       [`(y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`;
        `IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) INTER
         interior (IMAGE f1 (moi_s34_nb tt kk)) = {}`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `DISJOINT (interior q)
                   (frontier (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)))` THEN
    REWRITE_TAC[frontier] THEN
    MP_TAC(ISPEC `IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)` CLOSURE_SUBSET) THEN
    MAP_EVERY UNDISCH_TAC
     [`(y:real^3) IN interior q`;
      `(y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)`;
      `~((y:real^3) IN interior (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)))`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* e INTER B = j *)
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [ALL_TAC;
      MP_TAC(MATCH_MP MOI_S4L_PL_CELL2_TOPO
        (ASSUME `pl_cell_with_boundary 2 (e:real^3->bool) j`)) THEN
      MAP_EVERY UNDISCH_TAC [`(j:real^3->bool) SUBSET d`;
                             `d SUBSET IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`] THEN
      SET_TAC[]] THEN
    REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN frontier ((cb:(real^N->bool)->real^3->bool) s) /\
                  ~(x IN d) /\ ~(x IN e')` STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(x:real^3) IN e`; `~((x:real^3) IN j)`;
        `e UNION e' = frontier ((cb:(real^N->bool)->real^3->bool) s)`;
        `e INTER e' = (j:real^3->bool)`;
        `d INTER frontier ((cb:(real^N->bool)->real^3->bool) s) = j`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^3) IN interior ((cb:(real^N->bool)->real^3->bool) s UNION q)`
    ASSUME_TAC THENL
     [MP_TAC(ISPEC `(cb:(real^N->bool)->real^3->bool) s UNION q` CLOSURE_SUBSET) THEN
      UNDISCH_TAC `frontier ((cb:(real^N->bool)->real^3->bool) s UNION q) = d UNION e'` THEN
      REWRITE_TAC[frontier] THEN
      MAP_EVERY UNDISCH_TAC
       [`(x:real^3) IN frontier ((cb:(real^N->bool)->real^3->bool) s)`;
        `frontier ((cb:(real^N->bool)->real^3->bool) s) SUBSET cb s`;
        `~((x:real^3) IN d)`; `~((x:real^3) IN e')`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `pl_crossing_at (frontier ((cb:(real^N->bool)->real^3->bool) s))
                    (IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)) x`
    ASSUME_TAC THENL
     [MATCH_MP_TAC(ASSUME
       `!x. x IN moi_s34_trace tt kk (f1:real^N->real^3) ((cb:(real^N->bool)->real^3->bool) s)
            ==> pl_crossing_at (frontier (cb s)) (IMAGE f1 (moi_s34_bd tt kk)) x`) THEN
      ASM_REWRITE_TAC[moi_s34_trace; IN_INTER];
      ALL_TAC] THEN
    SUBGOAL_THEN `open (interior ((cb:(real^N->bool)->real^3->bool) s UNION q) DIFF
                        (d UNION e'))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC OPEN_DIFF THEN REWRITE_TAC[OPEN_INTERIOR] THEN
      MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THENL
       [FIRST_ASSUM ACCEPT_TAC;
        MP_TAC(MATCH_MP MOI_S4L_PL_CELL2_TOPO
          (ASSUME `pl_cell_with_boundary 2 (e':real^3->bool) j`)) THEN SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `closed ((cb:(real^N->bool)->real^3->bool) s)` ASSUME_TAC THENL
     [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`(cb:(real^N->bool)->real^3->bool) s`;
                   `IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`; `x:real^3`;
                   `interior ((cb:(real^N->bool)->real^3->bool) s UNION q) DIFF (d UNION e')`]
      MOI_S4V_CROSS_OUT) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      ASM_REWRITE_TAC[IN_DIFF; IN_UNION];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(y:real^3) IN interior q` ASSUME_TAC THENL
     [MP_TAC(ISPEC `q:real^3->bool` CLOSURE_SUBSET) THEN
      MP_TAC(ISPEC `(cb:(real^N->bool)->real^3->bool) s UNION q` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `frontier q = (d:real^3->bool) UNION e` THEN
      REWRITE_TAC[frontier] THEN
      MAP_EVERY UNDISCH_TAC
       [`(y:real^3) IN interior ((cb:(real^N->bool)->real^3->bool) s UNION q) DIFF
                       (d UNION e')`;
        `~((y:real^3) IN (cb:(real^N->bool)->real^3->bool) s)`;
        `e UNION e' = frontier ((cb:(real^N->bool)->real^3->bool) s)`;
        `frontier ((cb:(real^N->bool)->real^3->bool) s) SUBSET cb s`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(MP (SPEC `y:real^3` (ASSUME
     `!y. y IN interior q ==> ~(y IN IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk))`))
      (ASSUME `(y:real^3) IN interior q`)) THEN
    ASM_REWRITE_TAC[];
    (* other face balls meet q only inside the tube *)
    X_GEN_TAC `s':real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `moi_s34_fb1 tt kk h (f1:real^N->real^3) car s'
                    ((cb:(real^N->bool)->real^3->bool) s')`
    MP_TAC THENL
     [UNDISCH_TAC `moi_s34_fbinv tt kk (h:real^N->real^3) f1 car cb` THEN
      REWRITE_TAC[moi_s34_fbinv] THEN
      DISCH_THEN(MP_TAC o SPEC `s':real^N->bool` o CONJUNCT1) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[moi_s34_fb1] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
    SUBGOAL_THEN `(cb:(real^N->bool)->real^3->bool) s INTER cb s' SUBSET
                  interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk))`
    ASSUME_TAC THENL
     [UNDISCH_TAC `moi_s34_fbinv tt kk (h:real^N->real^3) f1 car cb` THEN
      REWRITE_TAC[moi_s34_fbinv; moi_s34_fb2] THEN
      DISCH_THEN(MP_TAC o SPECL [`s:real^N->bool`; `s':real^N->bool`] o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ASSUME `~((s':real^N->bool) = s)`) THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `DISJOINT (d:real^3->bool) ((cb:(real^N->bool)->real^3->bool) s')`
    ASSUME_TAC THENL
     [MATCH_MP_TAC(ASSUME
       `!s'. s' IN moi_s34_simp kk (&2) /\ ~(s' = s)
             ==> DISJOINT (d:real^3->bool) ((cb:(real^N->bool)->real^3->bool) s')`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (h:real^N->real^3) (relative_frontier s') SUBSET
                  interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `interior (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s'))` THEN
      REWRITE_TAC[ASSUME
       `!r. interior (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk r)) SUBSET
            interior (IMAGE f1 (moi_s34_nb tt kk))`] THEN
      UNDISCH_TAC `moi_s34_frame tt kk (h:real^N->real^3) ep f1 car` THEN
      REWRITE_TAC[moi_s34_frame] THEN
      DISCH_THEN(MP_TAC o SPEC `s':real^N->bool` o CONJUNCT1 o funpow 9 CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `interior q SUBSET IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)` THENL
     [(* int q inside the face torus *)
      SUBGOAL_THEN `interior q SUBSET interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk))`
      ASSUME_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `interior (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s))` THEN
        REWRITE_TAC[ASSUME
         `!r. interior (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk r)) SUBSET
              interior (IMAGE f1 (moi_s34_nb tt kk))`] THEN
        MATCH_MP_TAC INTERIOR_MAXIMAL THEN ASM_REWRITE_TAC[OPEN_INTERIOR];
        ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC
       [`interior q SUBSET interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk))`;
        `frontier q UNION interior q = (q:real^3->bool)`;
        `frontier q = (d:real^3->bool) UNION e`;
        `e UNION e' = frontier ((cb:(real^N->bool)->real^3->bool) s)`;
        `frontier ((cb:(real^N->bool)->real^3->bool) s) SUBSET cb s`;
        `DISJOINT (d:real^3->bool) ((cb:(real^N->bool)->real^3->bool) s')`;
        `(cb:(real^N->bool)->real^3->bool) s INTER cb s' SUBSET
         interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk))`] THEN
      SET_TAC[];
      (* int q misses the face torus, hence the whole tube *)
      SUBGOAL_THEN `interior q INTER IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s) = {}`
      ASSUME_TAC THENL
       [MP_TAC(ISPECL [`interior q:real^3->bool`;
                       `IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)`]
          CONNECTED_INTER_FRONTIER) THEN
        MAP_EVERY UNDISCH_TAC
         [`connected (interior q:real^3->bool)`;
          `~(interior q SUBSET IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s))`;
          `DISJOINT (interior q)
             (frontier (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)))`] THEN
        SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `interior q INTER IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk) = {}`
      ASSUME_TAC THENL
       [MP_TAC(ASSUME
         `!y. y IN interior q /\ y IN IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)
              ==> y IN IMAGE f1 (moi_s34_ft tt kk s)`) THEN
        UNDISCH_TAC `interior q INTER IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s) = {}` THEN
        SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `e INTER interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)) = {}`
      ASSUME_TAC THENL
       [MP_TAC(ISPECL [`interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk))`;
                       `interior q:real^3->bool`] OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
        REWRITE_TAC[OPEN_INTERIOR] THEN
        MP_TAC(ISPEC `IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)` INTERIOR_SUBSET) THEN
        MAP_EVERY UNDISCH_TAC
         [`interior q INTER IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk) = {}`;
          `frontier q SUBSET closure (interior q:real^3->bool)`;
          `frontier q = (d:real^3->bool) UNION e`] THEN
        SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(cb:(real^N->bool)->real^3->bool) s' INTER frontier q = {}` ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`e INTER interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)) = {}`;
          `frontier q = (d:real^3->bool) UNION e`;
          `e UNION e' = frontier ((cb:(real^N->bool)->real^3->bool) s)`;
          `frontier ((cb:(real^N->bool)->real^3->bool) s) SUBSET cb s`;
          `DISJOINT (d:real^3->bool) ((cb:(real^N->bool)->real^3->bool) s')`;
          `(cb:(real^N->bool)->real^3->bool) s INTER cb s' SUBSET
           interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk))`] THEN
        SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `~(relative_frontier (s':real^N->bool) = {})` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                       `s':real^N->bool`] MOI_S4J_SIMP2) THEN
        ASM_REWRITE_TAC[] THEN SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(cb:(real^N->bool)->real^3->bool) s' INTER q = {}` MP_TAC THENL
       [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
        MP_TAC(ISPECL [`(cb:(real^N->bool)->real^3->bool) s'`; `q:real^3->bool`]
          CONNECTED_INTER_FRONTIER) THEN
        SUBGOAL_THEN `connected ((cb:(real^N->bool)->real^3->bool) s')`
          (fun th -> REWRITE_TAC[th]) THENL
         [MATCH_MP_TAC PATH_CONNECTED_IMP_CONNECTED THEN
          MATCH_MP_TAC MOI_S4L_PL_BALL_PATH_CONNECTED THEN EXISTS_TAC `3` THEN
          FIRST_ASSUM ACCEPT_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `~(IMAGE (h:real^N->real^3) (relative_frontier s') = {})` MP_TAC THENL
         [ASM_REWRITE_TAC[IMAGE_EQ_EMPTY]; ALL_TAC] THEN
        MP_TAC(ISPEC `(cb:(real^N->bool)->real^3->bool) s'` INTERIOR_SUBSET) THEN
        MP_TAC(ISPEC `IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)` INTERIOR_SUBSET) THEN
        MAP_EVERY UNDISCH_TAC
         [`IMAGE (h:real^N->real^3) (relative_frontier s') SUBSET
           interior ((cb:(real^N->bool)->real^3->bool) s')`;
          `IMAGE (h:real^N->real^3) (relative_frontier s') SUBSET
           interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk))`;
          `interior q INTER IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk) = {}`;
          `frontier q UNION interior q = (q:real^3->bool)`;
          `(cb:(real^N->bool)->real^3->bool) s' INTER frontier q = {}`;
          `~((cb:(real^N->bool)->real^3->bool) s' INTER q = {})`] THEN
        SET_TAC[];
        SET_TAC[]]]]);;

(* The new ball. *)

let MOI_S4V_CLEAN_BALL = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v d j q e e'.
     PL_SCHOENFLIES_3_STATEMENT /\ PL_SCHOENFLIES_3_AMBIENT_STATEMENT /\
     moi_s34_tube tt kk /\ moi_s34_emb h (UNIONS tt) /\
     moi_s34_frame tt kk h ep f1 car /\ moi_s34_fbinv tt kk h f1 car cb /\
     s IN moi_s34_simp kk (&2) /\
     moi_s34_op1w tt kk f1 cb s v d j /\ DISJOINT (d DIFF j) (cb s) /\
     moi_s4v_pocket (cb s) d j q e e' /\ moi_s4v_clean tt kk f1 s q
     ==> j IN components (moi_s34_trace tt kk f1 (cb s)) /\
         ?c2. pl_ball 3 c2 /\ cb s UNION q SUBSET c2 /\
              (!w. {w} IN kk /\ ~(w IN s) ==> DISJOINT c2 (IMAGE f1 (moi_s34_vb tt kk w))) /\
              (!s'. s' IN moi_s34_simp kk (&2) /\ ~(s' = s)
                    ==> c2 INTER cb s' SUBSET interior (IMAGE f1 (moi_s34_nb tt kk))) /\
              frontier c2 SUBSET car s /\
              moi_s34_trace tt kk f1 c2 = moi_s34_trace tt kk f1 (cb s) DIFF j /\
              (!x. x IN moi_s34_trace tt kk f1 c2
                   ==> ?u. open u /\ x IN u /\ frontier c2 INTER u = frontier (cb s) INTER u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`; `v:real^N`;
                 `d:real^3->bool`; `j:real^3->bool`] MOI_S4V_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`] MOI_S4L_TRACE_COMP_FACTS) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[moi_s34_fb1] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`; `v:real^N`;
                 `d:real^3->bool`; `j:real^3->bool`; `q:real^3->bool`; `e:real^3->bool`;
                 `e':real^3->bool`] MOI_S4V_CLEAN_SIDE) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`; `v:real^N`;
                 `d:real^3->bool`; `j:real^3->bool`] MOI_S4V_O_CHOICE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN(X_CHOOSE_THEN `oo:real^3->bool` STRIP_ASSUME_TAC)] THEN
  UNDISCH_TAC `moi_s4v_pocket ((cb:(real^N->bool)->real^3->bool) s) d j q e e'` THEN
  REWRITE_TAC[moi_s4v_pocket] THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_s4v_clean tt kk (f1:real^N->real^3) s q` THEN
  REWRITE_TAC[moi_s4v_clean] THEN STRIP_TAC THEN
  (* j is a component of the trace: the trace meets oo exactly in j *)
  SUBGOAL_THEN `moi_s34_trace tt kk (f1:real^N->real^3) ((cb:(real^N->bool)->real^3->bool) s)
                INTER oo = j`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_s34_trace] THEN
    MAP_EVERY UNDISCH_TAC
     [`oo INTER IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) SUBSET
       d UNION interior ((cb:(real^N->bool)->real^3->bool) s)`;
      `d INTER frontier ((cb:(real^N->bool)->real^3->bool) s) = j`;
      `(j:real^3->bool) SUBSET d`; `(d:real^3->bool) SUBSET oo`;
      `d SUBSET IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`] THEN
    REWRITE_TAC[frontier] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(j:real^3->bool) IN components (moi_s34_trace tt kk (f1:real^N->real^3)
                                                 ((cb:(real^N->bool)->real^3->bool) s))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4N_RIM_COMPONENT THEN EXISTS_TAC `oo:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  (* basic set facts *)
  SUBGOAL_THEN `d INTER e' = (j:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP MOI_S4L_PL_CELL2_TOPO
      (ASSUME `pl_cell_with_boundary 2 (e':real^3->bool) j`)) THEN
    MAP_EVERY UNDISCH_TAC
     [`d INTER frontier ((cb:(real^N->bool)->real^3->bool) s) = j`;
      `e UNION e' = frontier ((cb:(real^N->bool)->real^3->bool) s)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (q:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP MOI_S4V_BALL_SIDES (ASSUME `pl_ball 3 (q:real^3->bool)`)) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_sphere 2 (frontier ((cb:(real^N->bool)->real^3->bool) s UNION q))`
  ASSUME_TAC THENL
   [MP_TAC(MATCH_MP MOI_S4V_BALL_SIDES
      (ASSUME `pl_ball 3 ((cb:(real^N->bool)->real^3->bool) s UNION q)`)) THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the collar of j in e' and the disk to be pushed out *)
  MP_TAC(ISPECL [`e':real^3->bool`; `j:real^3->bool`; `oo:real^3->bool`] MOI_S4V_COLLAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`(j:real^3->bool) SUBSET d`; `(d:real^3->bool) SUBSET oo`] THEN
    SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `e2:real^3->bool` (X_CHOOSE_THEN `j2:real^3->bool`
      STRIP_ASSUME_TAC))] THEN
  SUBGOAL_THEN `(j2:real^3->bool) SUBSET e2` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP MOI_S4L_PL_CELL2_TOPO
      (ASSUME `pl_cell_with_boundary 2 (e2:real^3->bool) j2`)) THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`frontier ((cb:(real^N->bool)->real^3->bool) s UNION q)`;
                 `e2:real^3->bool`; `j2:real^3->bool`] DISK_COMPLEMENT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MAP_EVERY UNDISCH_TAC
     [`e2 SUBSET e' DIFF (j:real^3->bool)`;
      `frontier ((cb:(real^N->bool)->real^3->bool) s UNION q) = d UNION e'`] THEN
    SET_TAC[];
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `(frontier ((cb:(real^N->bool)->real^3->bool) s UNION q) DIFF e2) UNION j2 SUBSET
    frontier (cb s UNION q) /\
    (frontier ((cb:(real^N->bool)->real^3->bool) s UNION q) DIFF e2) UNION j2 SUBSET oo`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`e2 SUBSET e' DIFF (j:real^3->bool)`; `(j2:real^3->bool) SUBSET e2`;
      `e' DIFF (e2 DIFF j2) SUBSET (oo:real^3->bool)`; `(d:real^3->bool) SUBSET oo`;
      `frontier ((cb:(real^N->bool)->real^3->bool) s UNION q) = d UNION e'`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the outward push *)
  MP_TAC(ISPECL [`(cb:(real^N->bool)->real^3->bool) s UNION q`;
                 `(frontier ((cb:(real^N->bool)->real^3->bool) s UNION q) DIFF e2) UNION j2`;
                 `j2:real^3->bool`; `oo:real^3->bool`] MOI_S4V_OUTWARD_PUSH) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN(X_CHOOSE_THEN `c2:real^3->bool` (X_CHOOSE_THEN `y:real^3->bool`
      STRIP_ASSUME_TAC))] THEN
  (* facts about the new ball *)
  SUBGOAL_THEN `(d:real^3->bool) SUBSET interior c2` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `((frontier ((cb:(real^N->bool)->real^3->bool) s UNION q) DIFF e2) UNION j2)
                DIFF j2` THEN
    CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`frontier ((cb:(real^N->bool)->real^3->bool) s UNION q) = d UNION e'`;
        `e2 SUBSET e' DIFF (j:real^3->bool)`; `(j2:real^3->bool) SUBSET e2`;
        `d INTER e' = (j:real^3->bool)`] THEN
      SET_TAC[];
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior ((cb:(real^N->bool)->real^3->bool) s) SUBSET interior c2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_INTERIOR THEN
    UNDISCH_TAC `c2 = ((cb:(real^N->bool)->real^3->bool) s UNION q) UNION y` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier (c2:real^3->bool) INTER interior c2 = {} /\
                frontier ((cb:(real^N->bool)->real^3->bool) s) INTER interior (cb s) = {}`
  STRIP_ASSUME_TAC THENL [REWRITE_TAC[frontier] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `oo INTER IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) INTER frontier c2 = {}`
  ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`oo INTER IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) SUBSET
       d UNION interior ((cb:(real^N->bool)->real^3->bool) s)`;
      `(d:real^3->bool) SUBSET interior c2`;
      `interior ((cb:(real^N->bool)->real^3->bool) s) SUBSET interior c2`;
      `frontier (c2:real^3->bool) INTER interior c2 = {}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier c2 INTER ((:real^3) DIFF y) =
                frontier ((cb:(real^N->bool)->real^3->bool) s UNION q) INTER
                ((:real^3) DIFF y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4V_FRONTIER_LOCAL THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_DIFF THEN REWRITE_TAC[OPEN_UNIV] THEN
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `c2 = ((cb:(real^N->bool)->real^3->bool) s UNION q) UNION y` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  (* the new trace *)
  SUBGOAL_THEN `moi_s34_trace tt kk (f1:real^N->real^3) c2 =
                moi_s34_trace tt kk f1 ((cb:(real^N->bool)->real^3->bool) s) DIFF j`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_s34_trace] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`oo INTER IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) INTER frontier c2 = {}`;
        `frontier c2 INTER ((:real^3) DIFF y) =
         frontier ((cb:(real^N->bool)->real^3->bool) s UNION q) INTER ((:real^3) DIFF y)`;
        `frontier ((cb:(real^N->bool)->real^3->bool) s UNION q) = d UNION e'`;
        `(d:real^3->bool) SUBSET interior c2`; `frontier (c2:real^3->bool) INTER interior c2 = {}`;
        `e UNION e' = frontier ((cb:(real^N->bool)->real^3->bool) s)`;
        `(j:real^3->bool) SUBSET d`; `(y:real^3->bool) SUBSET oo`] THEN
      SET_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`e UNION e' = frontier ((cb:(real^N->bool)->real^3->bool) s)`;
        `e INTER IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) = j`;
        `oo INTER IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) SUBSET
         d UNION interior ((cb:(real^N->bool)->real^3->bool) s)`;
        `frontier ((cb:(real^N->bool)->real^3->bool) s) INTER interior (cb s) = {}`;
        `d INTER frontier ((cb:(real^N->bool)->real^3->bool) s) = j`;
        `(y:real^3->bool) SUBSET oo`;
        `frontier c2 INTER ((:real^3) DIFF y) =
         frontier ((cb:(real^N->bool)->real^3->bool) s UNION q) INTER ((:real^3) DIFF y)`;
        `frontier ((cb:(real^N->bool)->real^3->bool) s UNION q) = d UNION e'`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `c2:real^3->bool` THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    UNDISCH_TAC `c2 = ((cb:(real^N->bool)->real^3->bool) s UNION q) UNION y` THEN SET_TAC[];
    (* foreign vertex balls *)
    X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o C MATCH_MP
      (CONJ (ASSUME `{w:real^N} IN kk`) (ASSUME `~((w:real^N) IN s)`)))) THEN
    MAP_EVERY UNDISCH_TAC
     [`c2 = ((cb:(real^N->bool)->real^3->bool) s UNION q) UNION y`;
      `(y:real^3->bool) SUBSET oo`] THEN
    SET_TAC[];
    (* other face balls *)
    X_GEN_TAC `s':real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(cb:(real^N->bool)->real^3->bool) s INTER cb s' SUBSET
                  interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk))`
    MP_TAC THENL
     [UNDISCH_TAC `moi_s34_fbinv tt kk (h:real^N->real^3) f1 car cb` THEN
      REWRITE_TAC[moi_s34_fbinv; moi_s34_fb2] THEN
      DISCH_THEN(MP_TAC o SPECL [`s:real^N->bool`; `s':real^N->bool`] o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ASSUME `~((s':real^N->bool) = s)`) THEN MESON_TAC[];
      ALL_TAC] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o C MATCH_MP
      (CONJ (ASSUME `(s':real^N->bool) IN moi_s34_simp kk (&2)`)
            (ASSUME `~((s':real^N->bool) = s)`)))) THEN
    MAP_EVERY UNDISCH_TAC
     [`c2 = ((cb:(real^N->bool)->real^3->bool) s UNION q) UNION y`;
      `(y:real^3->bool) SUBSET oo`] THEN
    SET_TAC[];
    (* the new frontier lies in car s *)
    SUBGOAL_THEN `frontier (y:real^3->bool) SUBSET y` ASSUME_TAC THENL
     [MATCH_MP_TAC FRONTIER_SUBSET_CLOSED THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[ASSUME `c2 = ((cb:(real^N->bool)->real^3->bool) s UNION q) UNION y`] THEN
    MP_TAC(ISPECL [`(cb:(real^N->bool)->real^3->bool) s UNION q`; `y:real^3->bool`]
      FRONTIER_UNION_SUBSET) THEN
    MAP_EVERY UNDISCH_TAC
     [`frontier (y:real^3->bool) SUBSET y`;
      `frontier ((cb:(real^N->bool)->real^3->bool) s UNION q) = d UNION e'`;
      `(y:real^3->bool) SUBSET oo`; `oo SUBSET (car:(real^N->bool)->real^3->bool) s`;
      `d SUBSET (car:(real^N->bool)->real^3->bool) s`;
      `frontier ((cb:(real^N->bool)->real^3->bool) s) SUBSET car s`;
      `e UNION e' = frontier ((cb:(real^N->bool)->real^3->bool) s)`] THEN
    SET_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    (* near the new trace the new frontier is the old one *)
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    EXISTS_TAC `(:real^3) DIFF (y UNION q)` THEN
    SUBGOAL_THEN `open ((:real^3) DIFF (y UNION q))` ASSUME_TAC THENL
     [MATCH_MP_TAC OPEN_DIFF THEN REWRITE_TAC[OPEN_UNIV] THEN
      MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      MP_TAC(ASSUME `(x:real^3) IN moi_s34_trace tt kk (f1:real^N->real^3) c2`) THEN
      REWRITE_TAC[ASSUME `moi_s34_trace tt kk (f1:real^N->real^3) c2 =
                          moi_s34_trace tt kk f1 ((cb:(real^N->bool)->real^3->bool) s) DIFF j`] THEN
      MP_TAC(ASSUME `(x:real^3) IN moi_s34_trace tt kk (f1:real^N->real^3) c2`) THEN
      REWRITE_TAC[moi_s34_trace] THEN
      MAP_EVERY UNDISCH_TAC
       [`oo INTER IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) INTER frontier c2 = {}`;
        `(y:real^3->bool) SUBSET oo`;
        `e UNION e' = frontier ((cb:(real^N->bool)->real^3->bool) s)`;
        `e INTER IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) = j`;
        `frontier ((cb:(real^N->bool)->real^3->bool) s) SUBSET cb s`;
        `q INTER (cb:(real^N->bool)->real^3->bool) s = e`] THEN
      SET_TAC[];
      MATCH_MP_TAC MOI_S4V_FRONTIER_LOCAL THEN CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        UNDISCH_TAC `c2 = ((cb:(real^N->bool)->real^3->bool) s UNION q) UNION y` THEN
        SET_TAC[]]]]);;

(* ------------------------------------------------------------------------- *)
(* The face-ball invariant for the new ball (outside version                *)
(* of op1a's MOI_S4N_FB1_TRANSFER: the new ball contains the old one), the  *)
(* family update, and the main theorem OP1_OUT_FROM_UNCLEAN.                 *)
(* ------------------------------------------------------------------------- *)

let MOI_S4V_FB1_OUT = prove
 (`!(tt:(real^N->bool)->bool) kk h (f1:real^N->real^3) car s c c2 j d.
     moi_s34_fb1 tt kk h f1 car s c /\ pl_ball 3 c2 /\
     IMAGE h (relative_frontier s) SUBSET interior c2 /\
     frontier c2 SUBSET car s /\
     (!w. {w} IN kk /\ ~(w IN s) ==> DISJOINT c2 (IMAGE f1 (moi_s34_vb tt kk w))) /\
     moi_s34_trace tt kk f1 c2 = moi_s34_trace tt kk f1 c DIFF j /\
     (!x. x IN moi_s34_trace tt kk f1 c2
          ==> ?u. open u /\ x IN u /\ frontier c2 INTER u = frontier c INTER u) /\
     j IN components (moi_s34_trace tt kk f1 c) /\
     j SUBSET d /\ d SUBSET IMAGE f1 (moi_s34_ft tt kk s) /\ contractible d
     ==> moi_s34_fb1 tt kk h f1 car s c2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s34_fb1] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!g. g IN moi_s34_simp kk (&1)
                    ==> IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)
                        SUBSET IMAGE f1 (moi_s34_bd tt kk)` ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_s34_rims tt kk (f1:real^N->real^3) SUBSET IMAGE f1 (moi_s34_bd tt kk)`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_s34_rims; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s34_trace tt kk (f1:real^N->real^3) c2 SUBSET moi_s34_trace tt kk f1 c`
  ASSUME_TAC THENL
   [REWRITE_TAC[ASSUME `moi_s34_trace tt kk (f1:real^N->real^3) c2 =
                        moi_s34_trace tt kk f1 c DIFF j`] THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [(* crossings at trace points *)
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MP_TAC(MP (SPEC `x:real^3` (ASSUME
      `!x. x IN moi_s34_trace tt kk (f1:real^N->real^3) c2
           ==> ?u. open u /\ x IN u /\ frontier c2 INTER u = frontier c INTER u`))
      (ASSUME `(x:real^3) IN moi_s34_trace tt kk (f1:real^N->real^3) c2`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC MOI_FGB_CROSSING_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`frontier c:real^3->bool`;
                          `IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`;
                          `u:real^3->bool`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [MATCH_MP_TAC(ASSUME
       `!x. x IN moi_s34_trace tt kk (f1:real^N->real^3) c
            ==> pl_crossing_at (frontier c) (IMAGE f1 (moi_s34_bd tt kk)) x`) THEN
      UNDISCH_TAC `(x:real^3) IN moi_s34_trace tt kk (f1:real^N->real^3) c2` THEN
      UNDISCH_TAC `moi_s34_trace tt kk (f1:real^N->real^3) c2 SUBSET
                   moi_s34_trace tt kk f1 c` THEN
      SET_TAC[];
      UNDISCH_TAC `frontier c2 INTER u = frontier c INTER (u:real^3->bool)` THEN
      SET_TAC[];
      REWRITE_TAC[]];
    (* crossings with the rims *)
    MAP_EVERY X_GEN_TAC [`g:real^N->bool`; `x:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN moi_s34_trace tt kk (f1:real^N->real^3) c2 /\
                  x IN moi_s34_trace tt kk f1 c`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(MP (SPEC `g:real^N->bool` (ASSUME
        `!g. g IN moi_s34_simp kk (&1)
             ==> IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)
                 SUBSET IMAGE f1 (moi_s34_bd tt kk)`))
        (ASSUME `(g:real^N->bool) IN moi_s34_simp kk (&1)`)) THEN
      MAP_EVERY UNDISCH_TAC
       [`(x:real^3) IN frontier c2 INTER
         IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)`;
        `moi_s34_trace tt kk (f1:real^N->real^3) c2 SUBSET moi_s34_trace tt kk f1 c`] THEN
      REWRITE_TAC[moi_s34_trace] THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(MP (SPEC `x:real^3` (ASSUME
      `!x. x IN moi_s34_trace tt kk (f1:real^N->real^3) c2
           ==> ?u. open u /\ x IN u /\ frontier c2 INTER u = frontier c INTER u`))
      (ASSUME `(x:real^3) IN moi_s34_trace tt kk (f1:real^N->real^3) c2`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC MOI_FGB_CURVE_CROSSING_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`moi_s34_trace tt kk (f1:real^N->real^3) c`;
                          `IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) INTER u`] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(SPECL [`g:real^N->bool`; `x:real^3`] (ASSUME
        `!g x. g IN moi_s34_simp kk (&1) /\
               x IN frontier c INTER
                    IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)
               ==> pl_curve_crossing_at (IMAGE f1 (moi_s34_bd tt kk))
                     (moi_s34_trace tt kk f1 c)
                     (IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)) x`)) THEN
      DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[ASSUME `(g:real^N->bool) IN moi_s34_simp kk (&1)`] THEN
      MAP_EVERY UNDISCH_TAC
       [`(x:real^3) IN frontier c2 INTER
         IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)`;
        `(x:real^3) IN moi_s34_trace tt kk (f1:real^N->real^3) c`] THEN
      REWRITE_TAC[moi_s34_trace] THEN SET_TAC[];
      MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
      UNDISCH_TAC `(x:real^3) IN moi_s34_trace tt kk (f1:real^N->real^3) c2` THEN
      REWRITE_TAC[moi_s34_trace] THEN SET_TAC[];
      REWRITE_TAC[moi_s34_trace] THEN
      UNDISCH_TAC `frontier c2 INTER u = frontier c INTER (u:real^3->bool)` THEN
      SET_TAC[]];
    (* finitely many components: j is dropped *)
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `components (moi_s34_trace tt kk (f1:real^N->real^3) c)` THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `moi_s34_trace tt kk (f1:real^N->real^3) c2 =
                        moi_s34_trace tt kk f1 c DIFF j`] THEN
    MP_TAC(ISPECL [`moi_s34_trace tt kk (f1:real^N->real^3) c`; `(:real^3)`;
                   `{}:real^3->bool`; `j:real^3->bool`] MOI_S4N_COMPONENTS_SIDE) THEN
    ASM_REWRITE_TAC[CLOSED_UNIV; CLOSED_EMPTY; INTER_EMPTY; EMPTY_SUBSET; UNION_EMPTY;
                    SUBSET_UNIV; INTER_UNIV] THEN
    SET_TAC[];
    (* finitely many rim crossings *)
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `frontier c INTER moi_s34_rims tt kk (f1:real^N->real^3)` THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`moi_s34_rims tt kk (f1:real^N->real^3) SUBSET IMAGE f1 (moi_s34_bd tt kk)`;
      `moi_s34_trace tt kk (f1:real^N->real^3) c2 SUBSET moi_s34_trace tt kk f1 c`] THEN
    REWRITE_TAC[moi_s34_trace] THEN SET_TAC[];
    (* the carrying property survives dropping the clopen piece j *)
    SUBGOAL_THEN `(j:real^3->bool) SUBSET moi_s34_trace tt kk (f1:real^N->real^3) c`
    ASSUME_TAC THENL
     [MATCH_MP_TAC IN_COMPONENTS_SUBSET THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `open_in (subtopology euclidean (moi_s34_trace tt kk (f1:real^N->real^3) c)) j /\
      closed_in (subtopology euclidean (moi_s34_trace tt kk f1 c)) j`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC(ISPECL [`subtopology euclidean (moi_s34_trace tt kk (f1:real^N->real^3) c)`;
                       `j:real^3->bool`] OPEN_IN_FINITE_CONNECTED_COMPONENTS) THEN
        REWRITE_TAC[EUCLIDEAN_CONNECTED_COMPONENTS_OF] THEN
        DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC CLOSED_IN_COMPONENT THEN FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `open_in (subtopology euclidean (moi_s34_trace tt kk (f1:real^N->real^3) c))
              (moi_s34_trace tt kk f1 c DIFF j)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC OPEN_IN_DIFF THEN
      ASM_REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN; SUBSET_UNIV];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `moi_s34_trace tt kk (f1:real^N->real^3) c2 INTER IMAGE f1 (moi_s34_ft tt kk s) =
      (moi_s34_trace tt kk f1 c INTER IMAGE f1 (moi_s34_ft tt kk s)) DIFF j`
    SUBST1_TAC THENL
     [REWRITE_TAC[ASSUME `moi_s34_trace tt kk (f1:real^N->real^3) c2 =
                          moi_s34_trace tt kk f1 c DIFF j`] THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_S4V_CARRIES_DROP THEN EXISTS_TAC `d:real^3->bool` THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [SET_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`(j:real^3->bool) SUBSET moi_s34_trace tt kk (f1:real^N->real^3) c`;
        `(j:real^3->bool) SUBSET d`;
        `d SUBSET IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)`] THEN
      SET_TAC[];
      MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN
      EXISTS_TAC `moi_s34_trace tt kk (f1:real^N->real^3) c` THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC
       [`(j:real^3->bool) SUBSET moi_s34_trace tt kk (f1:real^N->real^3) c`;
        `(j:real^3->bool) SUBSET d`;
        `d SUBSET IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)`] THEN
      SET_TAC[];
      SUBGOAL_THEN
       `(moi_s34_trace tt kk (f1:real^N->real^3) c INTER IMAGE f1 (moi_s34_ft tt kk s)) DIFF j =
        (moi_s34_trace tt kk f1 c INTER IMAGE f1 (moi_s34_ft tt kk s)) INTER
        (moi_s34_trace tt kk f1 c DIFF j)`
      SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC OPEN_IN_SUBTOPOLOGY_INTER_SUBSET THEN
      EXISTS_TAC `moi_s34_trace tt kk (f1:real^N->real^3) c` THEN
      REWRITE_TAC[INTER_SUBSET] THEN
      SUBGOAL_THEN
       `moi_s34_trace tt kk (f1:real^N->real^3) c INTER (moi_s34_trace tt kk f1 c DIFF j) =
        moi_s34_trace tt kk f1 c DIFF j`
      SUBST1_TAC THENL [SET_TAC[]; FIRST_ASSUM ACCEPT_TAC]]]);;

let MOI_S4V_FBINV_OUT = prove
 (`!(tt:(real^N->bool)->bool) kk h (f1:real^N->real^3) car cb s c2.
     moi_s34_fbinv tt kk h f1 car cb /\ s IN moi_s34_simp kk (&2) /\
     moi_s34_fb1 tt kk h f1 car s c2 /\
     (!s'. s' IN moi_s34_simp kk (&2) /\ ~(s' = s)
           ==> c2 INTER cb s' SUBSET interior (IMAGE f1 (moi_s34_nb tt kk)))
     ==> moi_s34_fbinv tt kk h f1 car (\s'. if s' = s then c2 else cb s')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s34_fbinv] THEN STRIP_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `t:real^N->bool` THEN DISCH_TAC THEN
    ASM_CASES_TAC `t:real^N->bool = s` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `t':real^N->bool`] THEN STRIP_TAC THEN
    REWRITE_TAC[moi_s34_fb2] THEN DISCH_TAC THEN
    ASM_CASES_TAC `t:real^N->bool = s` THEN ASM_CASES_TAC `t':real^N->bool = s` THEN
    ASM_REWRITE_TAC[] THENL
     [ASM_MESON_TAC[];
      UNDISCH_TAC `t:real^N->bool = s` THEN DISCH_THEN SUBST_ALL_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      UNDISCH_TAC `t':real^N->bool = s` THEN DISCH_THEN SUBST_ALL_TAC THEN
      ONCE_REWRITE_TAC[INTER_COMM] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPECL [`t:real^N->bool`; `t':real^N->bool`] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s34_fb2")) (concl th))) THEN
      ASM_REWRITE_TAC[moi_s34_fb2]]]);;

let OP1_OUT_FROM_UNCLEAN = prove
 (mk_imp(MOI_S4V_UNCLEAN,MOI_S34_OP1_OUT),
  DISCH_THEN(LABEL_TAC "U") THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`; `v:real^N`;
                 `d:real^3->bool`; `j:real^3->bool`] MOI_S4V_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the pocket *)
  MP_TAC(ISPECL [`(cb:(real^N->bool)->real^3->bool) s`; `d:real^3->bool`; `j:real^3->bool`]
    MOI_S4V_THETA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^3->bool` (X_CHOOSE_THEN `e:real^3->bool`
    (X_CHOOSE_THEN `e':real^3->bool` ASSUME_TAC))) THEN
  ASM_CASES_TAC `moi_s4v_clean tt kk (f1:real^N->real^3) s q` THENL
   [ALL_TAC;
    REMOVE_THEN "U" (MP_TAC o SPECL
      [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
       `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
       `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`; `v:real^N`;
       `d:real^3->bool`; `j:real^3->bool`; `q:real^3->bool`; `e:real^3->bool`;
       `e':real^3->bool`] o
      C MP (ASSUME `PL_SCHOENFLIES_3_STATEMENT /\ PL_SCHOENFLIES_3_AMBIENT_STATEMENT`)) THEN
    ASM_REWRITE_TAC[]] THEN
  (* the clean case *)
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`; `v:real^N`;
                 `d:real^3->bool`; `j:real^3->bool`; `q:real^3->bool`; `e:real^3->bool`;
                 `e':real^3->bool`] MOI_S4V_CLEAN_BALL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `c2:real^3->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`]
    MOI_S4L_TRACE_COMP_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_s34_fb1 tt kk h (f1:real^N->real^3) car s c2` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4V_FB1_OUT THEN
    MAP_EVERY EXISTS_TAC [`(cb:(real^N->bool)->real^3->bool) s`; `j:real^3->bool`;
                          `d:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `interior ((cb:(real^N->bool)->real^3->bool) s)` THEN CONJ_TAC THENL
     [UNDISCH_TAC `moi_s34_fb1 tt kk h (f1:real^N->real^3) car s (cb s)` THEN
      SIMP_TAC[moi_s34_fb1];
      MATCH_MP_TAC SUBSET_INTERIOR THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `\s':real^N->bool. if s' = s then c2 else (cb:(real^N->bool)->real^3->bool) s'` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S4V_FBINV_OUT THEN ASM_REWRITE_TAC[];
    SIMP_TAC[];
    REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S4N_RANK_DROP THEN
    EXISTS_TAC `j:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_s34_fb1 tt kk h (f1:real^N->real^3) car s (cb s)` THEN
    REWRITE_TAC[moi_s34_fb1] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
    MP_TAC(ISPECL [`moi_s34_trace tt kk (f1:real^N->real^3) ((cb:(real^N->bool)->real^3->bool) s)`; `(:real^3)`;
                   `{}:real^3->bool`; `j:real^3->bool`] MOI_S4N_COMPONENTS_SIDE) THEN
    ASM_REWRITE_TAC[CLOSED_UNIV; CLOSED_EMPTY; INTER_EMPTY; EMPTY_SUBSET; UNION_EMPTY;
                    SUBSET_UNIV; INTER_UNIV]]);;


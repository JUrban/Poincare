(* ========================================================================= *)
(* pc_moi_lt_gpb1h: the boundary homotopy of the chart step of the loop      *)
(* theorem (pc_moi_lt_gpb1).  Main theorem MOI_LGB1H_HTPY: the boundary loop *)
(* of g is homotopic in w to that of the map equal to h' o A on M and to g   *)
(* elsewhere.                                                                *)
(* Route: the explicit homotopy K(t,s) = h'((1 - t) h(g(loop s)) +          *)
(* t A(loop s)) when loop s IN M and g(loop s) otherwise, loop =            *)
(* std_triangle_loop, through HOMOTOPIC_LOOPS; continuity by                *)
(* CONTINUOUS_ON_CASES on the closed preimages of M and M' (they cover the  *)
(* square since the loop image is relative_frontier std_triangle).          *)
(* ========================================================================= *)

needs "src/pc_moi_loop_stmt.ml";;

prioritize_real();;
type_invention_error := true;;


(* ------------------------------------------------------------------------- *)
(* Facts about std_triangle_loop on the unit square: the loop               *)
(* in the second coordinate is continuous, the preimages of closed sets are *)
(* closed, and continuity of maps composed with it.                         *)
(* ------------------------------------------------------------------------- *)

let MOI_LGB1H_LOOP_FACTS = prove
 (`std_triangle_loop continuous_on interval[vec 0,vec 1] /\
   (!s. s IN interval[vec 0,vec 1]
        ==> std_triangle_loop s IN relative_frontier std_triangle) /\
   relative_frontier std_triangle SUBSET std_triangle /\
   std_triangle_loop (vec 1) = std_triangle_loop (vec 0)`,
  MP_TAC MOI_LTD_STD_TRIANGLE_LOOP THEN
  REWRITE_TAC[path; pathstart; pathfinish; path_image] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[MOI_LTD_FRONTIER_SUBSET_TRIANGLE] THEN
  UNDISCH_TAC `IMAGE std_triangle_loop (interval[vec 0:real^1,vec 1]) =
               relative_frontier std_triangle` THEN
  SET_TAC[]);;

let MOI_LGB1H_LOOP_SND_CONT = prove
 (`(\z:real^(1,1)finite_sum. std_triangle_loop(sndcart z)) continuous_on
   (interval[vec 0:real^1,vec 1] PCROSS interval[vec 0:real^1,vec 1])`,
  MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_COMPOSE) THEN
  SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART; ETA_AX] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
  REWRITE_TAC[MOI_LGB1H_LOOP_FACTS] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; SNDCART_PASTECART] THEN
  SIMP_TAC[]);;

let MOI_LGB1H_CLOSED_PRE = prove
 (`!M:real^2->bool.
     closed M
     ==> closed {z | z IN interval[vec 0:real^1,vec 1] PCROSS
                          interval[vec 0:real^1,vec 1] /\
                     std_triangle_loop(sndcart z) IN M}`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\z:real^(1,1)finite_sum. std_triangle_loop(sndcart z)`;
                 `interval[vec 0:real^1,vec 1] PCROSS interval[vec 0:real^1,vec 1]`;
                 `M:real^2->bool`] CONTINUOUS_CLOSED_PREIMAGE) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[MOI_LGB1H_LOOP_SND_CONT; CLOSED_PCROSS; CLOSED_INTERVAL]);;

let MOI_LGB1H_PRE_CONT = prove
 (`!(f:real^2->real^K) (M:real^2->bool).
     f continuous_on M
     ==> (\z:real^(1,1)finite_sum. f(std_triangle_loop(sndcart z))) continuous_on
         {z | z IN interval[vec 0:real^1,vec 1] PCROSS interval[vec 0:real^1,vec 1] /\
              std_triangle_loop(sndcart z) IN M}`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_COMPOSE) THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `interval[vec 0:real^1,vec 1] PCROSS interval[vec 0:real^1,vec 1]` THEN
    REWRITE_TAC[MOI_LGB1H_LOOP_SND_CONT] THEN SET_TAC[];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `M:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

let MOI_LGB1H_LIN_CONT = prove
 (`!(a:real^(1,1)finite_sum->real^3) b s.
     a continuous_on s /\ b continuous_on s
     ==> (\z. (&1 - drop(fstcart z)) % a z + drop(fstcart z) % b z) continuous_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN ASM_REWRITE_TAC[o_DEF; LIFT_DROP; LIFT_SUB] THEN
  SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; LINEAR_CONTINUOUS_ON;
           LINEAR_FSTCART; ETA_AX]);;


(* ------------------------------------------------------------------------- *)
(* Continuity of the pasted homotopy on the unit square.                    *)
(* ------------------------------------------------------------------------- *)

let MOI_LGB1H_CONT = prove
 (`!(g:real^2->real^N) (h:real^N->real^3) (h':real^3->real^N) (u:real^N->bool)
    (A:real^2->real^3) (M:real^2->bool) (M':real^2->bool).
     g continuous_on std_triangle /\
     h continuous_on u /\ h' continuous_on IMAGE h u /\
     (!x. x IN u ==> h' (h x) = x) /\ convex (IMAGE h u) /\
     closed M /\ closed M' /\ M UNION M' = std_triangle /\
     A continuous_on M /\
     (!x. x IN M ==> g x IN u /\ A x IN IMAGE h u) /\
     (!x. x IN M INTER M' ==> A x = h (g x))
     ==> (\z:real^(1,1)finite_sum.
            if std_triangle_loop(sndcart z) IN M
            then h' ((&1 - drop(fstcart z)) % h(g(std_triangle_loop(sndcart z))) +
                     drop(fstcart z) % A(std_triangle_loop(sndcart z)))
            else g(std_triangle_loop(sndcart z)))
         continuous_on (interval[vec 0,vec 1] PCROSS interval[vec 0,vec 1])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  STRIP_ASSUME_TAC MOI_LGB1H_LOOP_FACTS THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC
   `{z | z IN interval[vec 0:real^1,vec 1] PCROSS interval[vec 0:real^1,vec 1] /\
         std_triangle_loop(sndcart z) IN (M:real^2->bool)} UNION
    {z | z IN interval[vec 0:real^1,vec 1] PCROSS interval[vec 0:real^1,vec 1] /\
         std_triangle_loop(sndcart z) IN (M':real^2->bool)}` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_PCROSS; IN_UNION; IN_ELIM_THM; PASTECART_IN_PCROSS;
                SNDCART_PASTECART] THEN
    MAP_EVERY X_GEN_TAC [`t:real^1`; `s:real^1`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `std_triangle_loop s IN (std_triangle:real^2->bool)` MP_TAC THENL
     [ASM_MESON_TAC[SUBSET];
      UNDISCH_TAC `(M:real^2->bool) UNION M' = std_triangle` THEN SET_TAC[]]] THEN
  MATCH_MP_TAC CONTINUOUS_ON_CASES THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_LGB1H_CLOSED_PRE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_LGB1H_CLOSED_PRE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_COMPOSE) THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_LGB1H_LIN_CONT THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`\y:real^2. (h:real^N->real^3)((g:real^2->real^N) y)`;
                       `M:real^2->bool`] MOI_LGB1H_PRE_CONT) THEN
        REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
        MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_COMPOSE) THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
          EXISTS_TAC `std_triangle:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `(M:real^2->bool) UNION M' = std_triangle` THEN SET_TAC[];
          MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `u:real^N->bool` THEN
          ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[]];
        MATCH_MP_TAC MOI_LGB1H_PRE_CONT THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (h:real^N->real^3) u` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IMP_CONJ; FORALL_IN_PCROSS;
                  FSTCART_PASTECART; SNDCART_PASTECART] THEN
      MAP_EVERY X_GEN_TAC [`t:real^1`; `s:real^1`] THEN REPEAT DISCH_TAC THEN
      SUBGOAL_THEN `&0 <= drop t /\ drop t <= &1` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(t:real^1) IN interval[vec 0,vec 1]` THEN
        REWRITE_TAC[IN_INTERVAL_1; DROP_VEC];
        ALL_TAC] THEN
      UNDISCH_TAC `convex (IMAGE (h:real^N->real^3) u)` THEN REWRITE_TAC[convex] THEN
      DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_MESON_TAC[];
        ASM_MESON_TAC[];
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC]];
    MATCH_MP_TAC MOI_LGB1H_PRE_CONT THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `std_triangle:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(M:real^2->bool) UNION M' = std_triangle` THEN SET_TAC[];
    X_GEN_TAC `z:real^(1,1)finite_sum` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(A:real^2->real^3)(std_triangle_loop(sndcart(z:real^(1,1)finite_sum))) =
      (h:real^N->real^3)((g:real^2->real^N)(std_triangle_loop(sndcart z)))`
    SUBST1_TAC THENL [ASM_MESON_TAC[IN_INTER]; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_ARITH `(&1 - t) % a + t % a:real^3 = a`] THEN
    ASM_MESON_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* The main theorem MOI_LGB1H_HTPY.                                          *)
(* ------------------------------------------------------------------------- *)

let MOI_LGB1H_HTPY = prove
 (`!(g:real^2->real^N) (h:real^N->real^3) (h':real^3->real^N) (u:real^N->bool)
    (A:real^2->real^3) (M:real^2->bool) (M':real^2->bool) (w:real^N->bool).
     g continuous_on std_triangle /\
     h continuous_on u /\ h' continuous_on IMAGE h u /\
     (!x. x IN u ==> h' (h x) = x) /\ convex (IMAGE h u) /\
     closed M /\ closed M' /\ M UNION M' = std_triangle /\
     A continuous_on M /\
     (!x. x IN M ==> g x IN u /\ A x IN IMAGE h u) /\
     (!x. x IN M INTER M' ==> A x = h (g x)) /\
     IMAGE g (relative_frontier std_triangle) SUBSET w /\
     (!t x. t IN interval[vec 0,vec 1] /\ x IN M /\ x IN relative_frontier std_triangle
            ==> h' ((&1 - drop t) % h (g x) + drop t % A x) IN w)
     ==> homotopic_loops w (g o std_triangle_loop)
                         ((\x. if x IN M then h' (A x) else g x) o std_triangle_loop)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  STRIP_ASSUME_TAC MOI_LGB1H_LOOP_FACTS THEN
  SUBGOAL_THEN `!x. x IN relative_frontier std_triangle ==> (g:real^2->real^N) x IN w`
  ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (g:real^2->real^N) (relative_frontier std_triangle) SUBSET w` THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[HOMOTOPIC_LOOPS] THEN
  EXISTS_TAC
   `\z:real^(1,1)finite_sum.
      if std_triangle_loop(sndcart z) IN (M:real^2->bool)
      then (h':real^3->real^N)
             ((&1 - drop(fstcart z)) %
              (h:real^N->real^3)((g:real^2->real^N)(std_triangle_loop(sndcart z))) +
              drop(fstcart z) % (A:real^2->real^3)(std_triangle_loop(sndcart z)))
      else g(std_triangle_loop(sndcart z))` THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`g:real^2->real^N`; `h:real^N->real^3`; `h':real^3->real^N`;
                   `u:real^N->bool`; `A:real^2->real^3`; `M:real^2->bool`;
                   `M':real^2->bool`] MOI_LGB1H_CONT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; FSTCART_PASTECART;
                SNDCART_PASTECART] THEN
    MAP_EVERY X_GEN_TAC [`t:real^1`; `s:real^1`] THEN STRIP_TAC THEN
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `drop:real^1->real`)) (concl th))) THEN
      ASM_SIMP_TAC[];
      ASM_SIMP_TAC[]];
    X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; o_THM; DROP_VEC] THEN
    REWRITE_TAC[REAL_SUB_RZERO; VECTOR_MUL_LID; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    COND_CASES_TAC THEN ASM_MESON_TAC[];
    X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; o_THM; DROP_VEC] THEN
    REWRITE_TAC[REAL_SUB_REFL; VECTOR_MUL_LID; VECTOR_MUL_LZERO; VECTOR_ADD_LID];
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    REWRITE_TAC[pathstart; pathfinish; o_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    ASM_REWRITE_TAC[]]);;


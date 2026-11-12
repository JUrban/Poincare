(* ========================================================================= *)
(* pc_moi_s35_mark: the Sec 35 unit s35_mark (pc_moi_s35_stmt.ml), main      *)
(* theorems FILL = MOI_S35_FILL (sets close to a compact set with connected  *)
(* complement have their insides in a given neighbourhood of it), MARKER =   *)
(* MOI_S35_MARKER (an embedding of a PL 3-cell close to h on the boundary    *)
(* covers h of the far interior part; Jordan-Brouwer and Borsuk maps) and    *)
(* CELL_341 = MOI_S35_CELL_341 (Moise 34.1 for PL 3-cells in real^N).        *)
(* Moise GTM 47, p.248 (1), p.249 (4), (6).                                  *)
(* ========================================================================= *)

needs "src/pc_moi_s35_stmt.ml";;
needs "src/pc_moi_plmap.ml";;
needs "src/pc_moi_fnd_m3a.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* FILL: compactness of the region outside w and paths to infinity.         *)
(* ------------------------------------------------------------------------- *)

let MOI_S5M_PATH_AWAY = prove
 (`!(k:real^3->bool) x z.
     compact k /\ connected ((:real^3) DIFF k) /\ ~(x IN k) /\ ~(z IN k)
     ==> ?r g. &0 < r /\ path g /\ pathstart g = x /\ pathfinish g = z /\
               (!y. y IN path_image g ==> !u. u IN k ==> &2 * r <= dist(y,u))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `(:real^3) DIFF k` CONNECTED_OPEN_PATH_CONNECTED) THEN
  ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED; path_connected] THEN
  DISCH_THEN(MP_TAC o SPECL [`x:real^3`; `z:real^3`]) THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`path_image (g:real^1->real^3)`; `k:real^3->bool`]
    SEPARATE_COMPACT_CLOSED) THEN
  ASM_SIMP_TAC[COMPACT_PATH_IMAGE; COMPACT_IMP_CLOSED] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`d / &2`; `g:real^1->real^3`] THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  REWRITE_TAC[REAL_ARITH `&2 * d / &2 = d`] THEN ASM_MESON_TAC[]);;

let MOI_S5M_FAR = prove
 (`!R. connected {x:real^3 | R < norm x} /\ ~bounded {x:real^3 | R < norm x}`,
  GEN_TAC THEN CONJ_TAC THENL
   [SUBGOAL_THEN `{x:real^3 | R < norm x} = (:real^3) DIFF cball(vec 0,R)`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_CBALL; DIST_0] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC CONNECTED_COMPLEMENT_BOUNDED_CONVEX THEN
      REWRITE_TAC[BOUNDED_CBALL; CONVEX_CBALL; DIMINDEX_3] THEN ARITH_TAC];
    REWRITE_TAC[BOUNDED_POS; IN_ELIM_THM; NOT_EXISTS_THM] THEN
    X_GEN_TAC `b:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(abs R + b + &1) % basis 1:real^3`) THEN
    SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
    ASM_REAL_ARITH_TAC]);;

let MOI_S5M_SETDIST_WITNESS = prove
 (`!(x:real^N) k e.
     compact k /\ ~(k = {}) /\ setdist({x},k) < e ==> ?u. u IN k /\ dist(x,u) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{x:real^N}`; `k:real^N->bool`] SETDIST_COMPACT_CLOSED) THEN
  ASM_SIMP_TAC[COMPACT_SING; COMPACT_IMP_CLOSED; NOT_INSERT_EMPTY] THEN
  REWRITE_TAC[IN_SING] THEN ASM_MESON_TAC[]);;

let FILL = prove
 (MOI_S35_FILL,
  MAP_EVERY X_GEN_TAC [`k:real^3->bool`; `w:real^3->bool`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `(:real^3) DIFF w`] SEPARATE_COMPACT_CLOSED) THEN
  ASM_REWRITE_TAC[GSYM OPEN_CLOSED] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d0"))) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN REWRITE_TAC[BOUNDED_POS] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "R"))) THEN
  ABBREV_TAC `z0 = (R + &2) % basis 1:real^3` THEN
  SUBGOAL_THEN `norm(z0:real^3) = R + &2` ASSUME_TAC THENL
   [EXPAND_TAC "z0" THEN SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
    UNDISCH_TAC `&0 < R` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~((z0:real^3) IN k)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    USE_THEN "R" (MP_TAC o C MATCH_MP (ASSUME `(z0:real^3) IN k`)) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < R` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `cc = ((:real^3) DIFF w) INTER cball(vec 0,R + &1)` THEN
  SUBGOAL_THEN `compact (cc:real^3->bool) /\ (!x. x IN cc ==> ~(x IN k))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "cc" THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_INTER_COMPACT THEN
      ASM_REWRITE_TAC[GSYM OPEN_CLOSED; COMPACT_CBALL];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN cc
        ==> ?r g. &0 < r /\ path g /\ pathstart g = x /\ pathfinish g = z0 /\
                  (!y. y IN path_image g ==> !u. u IN k ==> &2 * r <= dist(y:real^3,u))`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S5M_PATH_AWAY THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^3->real` (X_CHOOSE_THEN `g:real^3->real^1->real^3`
    (LABEL_TAC "pa"))) THEN
  MP_TAC(ISPEC `cc:real^3->bool` COMPACT_IMP_HEINE_BOREL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (\x:real^3. ball(x,(r:real^3->real) x)) cc`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; OPEN_BALL; SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN EXISTS_TAC `x:real^3` THEN
    ASM_SIMP_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ff:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`\x:real^3. ball(x,(r:real^3->real) x)`; `cc:real^3->bool`;
                 `ff:(real^3->bool)->bool`] FINITE_SUBSET_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `fs:real^3->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `?dl. &0 < dl /\ !x. x IN fs ==> dl <= (r:real^3->real) x`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `inf ((&1) INSERT IMAGE (r:real^3->real) fs)` THEN
    MP_TAC(ISPEC `(&1) INSERT IMAGE (r:real^3->real) fs` INF_FINITE) THEN
    ASM_SIMP_TAC[FINITE_INSERT; FINITE_IMAGE; NOT_INSERT_EMPTY] THEN
    REWRITE_TAC[IN_INSERT; FORALL_IN_INSERT; FORALL_IN_IMAGE; IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[REAL_LT_01] THEN
    USE_THEN "pa" (MP_TAC o SPEC `x:real^3`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `min d0 (min dl (&1)) / &2` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `k':real^3->bool` THEN STRIP_TAC THEN
  ABBREV_TAC `e = min d0 (min dl (&1)) / &2` THEN
  SUBGOAL_THEN `&0 < e /\ e < d0 /\ e < dl /\ e < &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!q. q IN k' ==> ?u. u IN k /\ dist(q:real^3,u) < e` (LABEL_TAC "wit")
  THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S5M_SETDIST_WITNESS THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p:real^3. (!u. u IN k ==> e <= dist(p,u)) ==> ~(p IN k')`
  (LABEL_TAC "far") THENL
   [X_GEN_TAC `p:real^3` THEN REPEAT STRIP_TAC THEN
    USE_THEN "wit" (MP_TAC o C MATCH_MP (ASSUME `(p:real^3) IN k'`)) THEN
    ASM_MESON_TAC[REAL_NOT_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!q:real^3. q IN k' ==> norm q < R + &1` (LABEL_TAC "kb") THENL
   [X_GEN_TAC `q:real^3` THEN DISCH_TAC THEN
    USE_THEN "wit" (MP_TAC o C MATCH_MP (ASSUME `(q:real^3) IN k'`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC) THEN
    USE_THEN "R" (MP_TAC o C MATCH_MP (ASSUME `(u:real^3) IN k`)) THEN
    MP_TAC(NORM_ARITH `norm(q:real^3) <= norm(u:real^3) + dist(q,u)`) THEN
    UNDISCH_TAC `dist(q:real^3,u) < e` THEN UNDISCH_TAC `e < &1` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `R + &1` MOI_S5M_FAR) THEN STRIP_TAC THEN
  SUBGOAL_THEN `{x:real^3 | R + &1 < norm x} SUBSET (:real^3) DIFF k'` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DIFF; IN_UNIV] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN DISCH_TAC THEN
    USE_THEN "kb" (MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN k'`)) THEN
    UNDISCH_TAC `R + &1 < norm(x:real^3)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `q:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    USE_THEN "wit" (MP_TAC o C MATCH_MP (ASSUME `(q:real^3) IN k'`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC) THEN
    USE_THEN "d0" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(u:real^3) IN k`)
      (ASSUME `~((q:real^3) IN w)`))) THEN
    MP_TAC(ISPECL [`q:real^3`; `u:real^3`] DIST_SYM) THEN
    UNDISCH_TAC `dist(q:real^3,u) < e` THEN UNDISCH_TAC `e < d0` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; inside; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?t. connected t /\ (y:real^3) IN t /\ t SUBSET (:real^3) DIFF k' /\
        {x:real^3 | R + &1 < norm x} SUBSET t`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `R + &1 < norm(y:real^3)` THENL
     [EXISTS_TAC `{x:real^3 | R + &1 < norm x}` THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; SUBSET_REFL];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^3) IN cc` ASSUME_TAC THENL
     [EXPAND_TAC "cc" THEN REWRITE_TAC[IN_INTER; IN_DIFF; IN_UNIV; IN_CBALL_0] THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(R + &1 < norm(y:real^3))` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `?x:real^3. x IN fs /\ y IN ball(x,(r:real^3->real) x)`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `cc SUBSET UNIONS (IMAGE (\x:real^3. ball(x,(r:real^3->real) x)) fs)` THEN
      REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^3) IN cc` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "pa" (MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN cc`)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gx"))))) THEN
    SUBGOAL_THEN `(x:real^3) IN path_image ((g:real^3->real^1->real^3) x) /\
                  (z0:real^3) IN path_image (g x)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE]; ALL_TAC] THEN
    SUBGOAL_THEN `dl <= (r:real^3->real) x` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `(segment[x,y] UNION path_image ((g:real^3->real^1->real^3) x)) UNION
                {x:real^3 | R + &1 < norm x}` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_UNION THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONNECTED_UNION THEN
        ASM_SIMP_TAC[CONNECTED_SEGMENT; CONNECTED_PATH_IMAGE] THEN
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `x:real^3` THEN
        ASM_REWRITE_TAC[ENDS_IN_SEGMENT];
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_UNION; IN_ELIM_THM] THEN
        EXISTS_TAC `z0:real^3` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `&0 < R` THEN REAL_ARITH_TAC];
      REWRITE_TAC[IN_UNION; ENDS_IN_SEGMENT];
      REWRITE_TAC[UNION_SUBSET] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIV] THEN X_GEN_TAC `p:real^3` THEN
        DISCH_TAC THEN USE_THEN "far" MATCH_MP_TAC THEN
        X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN
        USE_THEN "gx" (MP_TAC o C MATCH_MP
          (ASSUME `(x:real^3) IN path_image ((g:real^3->real^1->real^3) x)`)) THEN
        DISCH_THEN(MP_TAC o C MATCH_MP (ASSUME `(u:real^3) IN k`)) THEN
        MP_TAC(ISPECL [`x:real^3`; `y:real^3`; `p:real^3`] DIST_IN_CLOSED_SEGMENT) THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(y:real^3) IN ball(x,(r:real^3->real) x)` THEN
        REWRITE_TAC[IN_BALL] THEN
        MP_TAC(NORM_ARITH `dist(x:real^3,u) <= dist(p,x) + dist(p,u)`) THEN
        UNDISCH_TAC `dl <= (r:real^3->real) x` THEN UNDISCH_TAC `e < dl` THEN
        REAL_ARITH_TAC;
        REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIV] THEN X_GEN_TAC `p:real^3` THEN
        DISCH_TAC THEN USE_THEN "far" MATCH_MP_TAC THEN
        X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN
        USE_THEN "gx" (MP_TAC o C MATCH_MP
          (ASSUME `(p:real^3) IN path_image ((g:real^3->real^1->real^3) x)`)) THEN
        DISCH_THEN(MP_TAC o C MATCH_MP (ASSUME `(u:real^3) IN k`)) THEN
        UNDISCH_TAC `dl <= (r:real^3->real) x` THEN UNDISCH_TAC `e < dl` THEN
        UNDISCH_TAC `&0 < dl` THEN REAL_ARITH_TAC];
      REWRITE_TAC[SUBSET; IN_UNION] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `bounded {x:real^3 | R + &1 < norm x}` MP_TAC THENL
   [MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `connected_component ((:real^3) DIFF k') y` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* CELL_341: Moise 34.1 transported to PL 3-cells in real^N.                 *)
(* ------------------------------------------------------------------------- *)

let MOI_S5M_STD3 = prove
 (`&3 simplex (convex hull {vec 0:real^3,basis 1,basis 2,basis 3})`,
  REWRITE_TAC[simplex] THEN EXISTS_TAC `{vec 0:real^3,basis 1,basis 2,basis 3}` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(INST_TYPE [`:3`,`:N`] AFFINE_INDEPENDENT_STDBASIS) THEN
    SUBGOAL_THEN `{basis i:real^3 | 1 <= i /\ i <= dimindex(:3)} =
                  {basis 1,basis 2,basis 3}` (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM; NOT_IN_EMPTY; DIMINDEX_3] THEN
    REWRITE_TAC[ARITH_RULE `1 <= i /\ i <= 3 <=> i = 1 \/ i = 2 \/ i = 3`] THEN
    REWRITE_TAC[RIGHT_OR_DISTRIB; EXISTS_OR_THM; UNWIND_THM2];
    SUBGOAL_THEN `~(vec 0:real^3 = basis 1) /\ ~(vec 0:real^3 = basis 2) /\
                  ~(vec 0:real^3 = basis 3) /\ ~(basis 1:real^3 = basis 2) /\
                  ~(basis 1:real^3 = basis 3) /\ ~(basis 2:real^3 = basis 3)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN
      TRY(MATCH_MP_TAC(MESON[] `~(b:real^3 = a) ==> ~(a = b)`) THEN
          MATCH_MP_TAC BASIS_NONZERO THEN REWRITE_TAC[DIMINDEX_3] THEN ARITH_TAC) THEN
      SIMP_TAC[BASIS_INJ_EQ; DIMINDEX_3; ARITH];
      ALL_TAC] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV)]);;

let CELL_341 = prove
 (MOI_S35_CELL_341,
  DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `bs:real^N->bool`; `h:real^N->real^3`;
                       `e:real`] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `pl_cell_with_boundary 3 (s:real^N->bool) bs` THEN
  REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `phi:real^N->real^N`
    (X_CHOOSE_THEN `psi:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`convex hull {vec 0:real^3,basis 1,basis 2,basis 3}`;
                 `k:real^N->bool`; `&3:int`] MOI_FM3_SIMPLEX_PLH) THEN
  ASM_REWRITE_TAC[MOI_S5M_STD3] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^3->real^N` (X_CHOOSE_THEN `q:real^N->real^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`3`; `convex hull {vec 0:real^3,basis 1,basis 2,basis 3}`]
    PL_BALL_SIMPLEX) THEN
  REWRITE_TAC[MOI_S5M_STD3] THEN DISCH_TAC THEN
  ABBREV_TAC `k0 = convex hull {vec 0:real^3,basis 1,basis 2,basis 3}` THEN
  SUBGOAL_THEN
   `pl_homeomorphism (k0,s:real^N->bool)
      ((phi:real^N->real^N) o (p:real^3->real^N),(q:real^N->real^3) o
       (psi:real^N->real^N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `k:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `ff = (phi:real^N->real^N) o (p:real^3->real^N)` THEN
  ABBREV_TAC `gg = (q:real^N->real^3) o (psi:real^N->real^N)` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism; homeomorphism] o
    check (fun th -> concl th = `pl_homeomorphism (k0,s:real^N->bool)
                                   ((ff:real^3->real^N),(gg:real^N->real^3))`)) THEN
  UNDISCH_TAC `MOISE_341_STATEMENT` THEN REWRITE_TAC[MOISE_341_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`k0:real^3->bool`;
    `(h:real^N->real^3) o (ff:real^3->real^N)`; `e:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(ff:real^3->real^N) x = ff y` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term ((=) `h:real^N->real^3`)) (concl th) &&
          is_forall (concl th))) THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f0:real^3->real^3` (X_CHOOSE_THEN `g0:real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism; homeomorphism] o
    check (fun th -> can (find_term ((=) `f0:real^3->real^3`)) (concl th) &&
                     can (find_term ((=) `g0:real^3->real^3`)) (concl th))) THEN
  EXISTS_TAC `(f0:real^3->real^3) o (gg:real^N->real^3)` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `k0:real^3->bool` THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN REWRITE_TAC[o_THM] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(gg:real^N->real^3) x IN k0 /\ gg y IN k0` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(gg:real^N->real^3) x = gg y` MP_TAC THENL
     [ASM_MESON_TAC[]; ASM_MESON_TAC[]];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(gg:real^N->real^3) x IN k0` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(MATCH_MP (ASSUME `!x. x IN k0 ==> dist ((f0:real^3->real^3) x,
                ((h:real^N->real^3) o (ff:real^3->real^N)) x) < e`)
      (ASSUME `(gg:real^N->real^3) x IN k0`)) THEN
    REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(ff:real^3->real^N) ((gg:real^N->real^3) x) = x`
      (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `(x:real^N) IN s` THEN
    UNDISCH_TAC `!y. y IN s ==> (ff:real^3->real^N) ((gg:real^N->real^3) y) = y` THEN
    MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* MARKER: Jordan-Brouwer components of images of a 3-cell boundary and     *)
(* Borsuk maps transported along close embeddings.                           *)
(* ------------------------------------------------------------------------- *)

let MOI_S5M_PLH_FACTS = prove
 (`!(s:real^M->bool) (t:real^N->bool) f g.
     pl_homeomorphism (s,t) (f,g)
     ==> IMAGE f s = t /\ IMAGE g t = s /\ (!x. x IN s ==> g (f x) = x) /\
         (!y. y IN t ==> f (g y) = y) /\ f continuous_on s /\ g continuous_on t /\
         pl_map_on s f /\ pl_map_on t g`,
  SIMP_TAC[pl_homeomorphism; homeomorphism]);;

let MOI_S5M_CELL_STD = prove
 (`!(s:real^N->bool) bs.
     pl_cell_with_boundary 3 s bs
     ==> ?ff gg. pl_homeomorphism
                   (convex hull {vec 0:real^3,basis 1,basis 2,basis 3},s) (ff,gg) /\
                 IMAGE ff (frontier (convex hull {vec 0:real^3,basis 1,basis 2,basis 3})) =
                 bs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `phi:real^N->real^N`
    (X_CHOOSE_THEN `psi:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`convex hull {vec 0:real^3,basis 1,basis 2,basis 3}`;
                 `k:real^N->bool`; `&3:int`] MOI_FM3_SIMPLEX_PLH) THEN
  ASM_REWRITE_TAC[MOI_S5M_STD3] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^3->real^N` (X_CHOOSE_THEN `q:real^N->real^3`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`(phi:real^N->real^N) o (p:real^3->real^N)`;
                        `(q:real^N->real^3) o (psi:real^N->real^N)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `k:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frontier (convex hull {vec 0:real^3,basis 1,basis 2,basis 3}) =
    relative_frontier (convex hull {vec 0:real^3,basis 1,basis 2,basis 3})`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RELATIVE_FRONTIER_NONEMPTY_INTERIOR THEN
    MP_TAC(MATCH_MP MOI_FN1_SIMPLEX_3_INTERIOR MOI_S5M_STD3) THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IMAGE_o] THEN AP_TERM_TAC THEN
  MP_TAC(CONJUNCT1(MATCH_MP MOI_S5M_PLH_FACTS (ASSUME
   `pl_homeomorphism
      (relative_frontier (convex hull {vec 0:real^3,basis 1,basis 2,basis 3}),
       relative_frontier k) ((p:real^3->real^N),(q:real^N->real^3))`))) THEN
  SIMP_TAC[]);;

let MOI_S5M_OPEN_IMAGE = prove
 (`!(f:real^3->real^3) k0.
     f continuous_on k0 /\ (!x y. x IN k0 /\ y IN k0 /\ f x = f y ==> x = y)
     ==> open (IMAGE f (interior k0))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN
  REWRITE_TAC[OPEN_INTERIOR] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; INTERIOR_SUBSET];
    ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET]]);;

let MOI_S5M_FRONTIER_SPLIT = prove
 (`!k0:real^3->bool.
     compact k0 ==> frontier k0 = k0 DIFF interior k0 /\ interior k0 SUBSET k0`,
  SIMP_TAC[frontier; CLOSURE_CLOSED; COMPACT_IMP_CLOSED; INTERIOR_SUBSET]);;

let MOI_S5M_BOUNDED_COMP = prove
 (`!(h:real^3->real^3) k0 x0.
     convex k0 /\ compact k0 /\ h continuous_on k0 /\
     (!x y. x IN k0 /\ y IN k0 /\ h x = h y ==> x = y) /\ x0 IN interior k0
     ==> ~(h x0 IN IMAGE h (frontier k0)) /\
         bounded (connected_component ((:real^3) DIFF IMAGE h (frontier k0)) (h x0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5M_FRONTIER_SPLIT) THEN
  ABBREV_TAC `u = IMAGE (h:real^3->real^3) (interior k0)` THEN
  SUBGOAL_THEN
   `open (u:real^3->bool) /\ connected u /\ (h:real^3->real^3) x0 IN u /\
    u INTER IMAGE h (frontier k0) = {} /\ closure u SUBSET IMAGE h k0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S5M_OPEN_IMAGE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
      ASM_SIMP_TAC[CONVEX_CONNECTED; CONVEX_INTERIOR] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ASM SET_TAC[];
      MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THENL
       [ASM SET_TAC[];
        MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `IMAGE (h:real^3->real^3) k0` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `u:real^3->bool` THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  ABBREV_TAC `cc = connected_component ((:real^3) DIFF IMAGE h (frontier k0))
                     ((h:real^3->real^3) x0)` THEN
  SUBGOAL_THEN
   `connected (cc:real^3->bool) /\ (h:real^3->real^3) x0 IN cc /\
    cc SUBSET (:real^3) DIFF IMAGE h (frontier k0)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "cc" THEN
    REWRITE_TAC[CONNECTED_CONNECTED_COMPONENT; CONNECTED_COMPONENT_SUBSET] THEN
    REWRITE_TAC[IN] THEN MATCH_MP_TAC CONNECTED_COMPONENT_REFL THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`cc:real^3->bool`; `u:real^3->bool`] CONNECTED_INTER_FRONTIER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `frontier u SUBSET IMAGE (h:real^3->real^3) (frontier k0)` MP_TAC THENL
   [ASM_SIMP_TAC[frontier; INTERIOR_OPEN] THEN ASM SET_TAC[];
    ASM SET_TAC[]]);;

let MOI_S5M_BOUNDED_IN = prove
 (`!(f:real^3->real^3) k0 y.
     convex k0 /\ compact k0 /\ f continuous_on k0 /\
     (!x y. x IN k0 /\ y IN k0 /\ f x = f y ==> x = y) /\
     ~(y IN IMAGE f (frontier k0)) /\
     bounded (connected_component ((:real^3) DIFF IMAGE f (frontier k0)) y)
     ==> y IN IMAGE f (interior k0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5M_FRONTIER_SPLIT) THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `~((y:real^3) IN IMAGE (f:real^3->real^3) k0)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `connected ((:real^3) DIFF IMAGE (f:real^3->real^3) k0)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`IMAGE (f:real^3->real^3) k0`; `k0:real^3->bool`]
      CONNECTED_COMPLEMENT_HOMEOMORPHIC_CONVEX_COMPACT) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN
    ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
    EXISTS_TAC `f:real^3->real^3` THEN MATCH_MP_TAC HOMEOMORPHISM_COMPACT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(:real^3) DIFF IMAGE (f:real^3->real^3) k0 SUBSET
    connected_component ((:real^3) DIFF IMAGE f (frontier k0)) y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `bounded ((:real^3) DIFF IMAGE (f:real^3->real^3) k0)` MP_TAC THENL
   [ASM_MESON_TAC[BOUNDED_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `bounded (IMAGE (f:real^3->real^3) k0)` MP_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IMP_IMP; GSYM BOUNDED_UNION] THEN
  REWRITE_TAC[SET_RULE `(s:real^3->bool) UNION ((:real^3) DIFF s) = (:real^3)`;
              NOT_BOUNDED_UNIV]);;

let MOI_S5M_BORSUK_TRANSFER = prove
 (`!(phi:real^3->real^3) s0 y.
     phi continuous_on s0 /\ compact s0 /\
     (!x x'. x IN s0 /\ x' IN s0 /\ phi x = phi x' ==> x = x') /\
     ~(y IN IMAGE phi s0)
     ==> ((?c. homotopic_with (\x. T)
                 (subtopology euclidean (IMAGE phi s0),
                  subtopology euclidean (sphere(vec 0:real^3,&1)))
                 (\x. inv(norm(x - y)) % (x - y)) (\x. c)) <=>
          (?c. homotopic_with (\x. T)
                 (subtopology euclidean s0,
                  subtopology euclidean (sphere(vec 0:real^3,&1)))
                 (\z. inv(norm(phi z - y)) % (phi z - y)) (\x. c)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s0:real^3->bool`; `phi:real^3->real^3`;
                 `IMAGE (phi:real^3->real^3) s0`] HOMEOMORPHISM_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:real^3->real^3` MP_TAC) THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_TAC `c:real^3`) THEN EXISTS_TAC `c:real^3` THENL
   [MP_TAC(ISPECL [`\x:real^3. inv(norm(x - y)) % (x - y)`; `(\x. c):real^3->real^3`;
                   `phi:real^3->real^3`; `s0:real^3->bool`;
                   `IMAGE (phi:real^3->real^3) s0`; `sphere(vec 0:real^3,&1)`]
      HOMOTOPIC_COMPOSE_CONTINUOUS_RIGHT) THEN
    ASM_REWRITE_TAC[SUBSET_REFL; o_DEF] THEN DISCH_THEN MATCH_ACCEPT_TAC;
    MP_TAC(ISPECL [`\z:real^3. inv(norm((phi:real^3->real^3) z - y)) % (phi z - y)`;
                   `(\x. c):real^3->real^3`; `psi:real^3->real^3`;
                   `IMAGE (phi:real^3->real^3) s0`; `s0:real^3->bool`;
                   `sphere(vec 0:real^3,&1)`] HOMOTOPIC_COMPOSE_CONTINUOUS_RIGHT) THEN
    ASM_REWRITE_TAC[SUBSET_REFL; o_DEF] THEN DISCH_TAC THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_EQ THEN
    MAP_EVERY EXISTS_TAC
     [`\x:real^3. inv(norm((phi:real^3->real^3) (psi x) - y)) % (phi (psi x) - y)`;
      `(\x. c):real^3->real^3`] THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN ASM_SIMP_TAC[]]);;

let MOI_S5M_NOT_ANTIPODAL = prove
 (`!a b:real^3 e. e <= norm a /\ norm(a - b) < e
                  ==> ~(inv(norm a) % a = --(inv(norm b) % b))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(a:real^3) /\ &0 < norm(b:real^3)` STRIP_ASSUME_TAC THENL
   [MP_TAC(NORM_ARITH `norm(a:real^3) <= norm(a - b) + norm b`) THEN
    MP_TAC(ISPEC `a - b:real^3` NORM_POS_LE) THEN
    UNDISCH_TAC `e <= norm(a:real^3)` THEN UNDISCH_TAC `norm(a - b:real^3) < e` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(b:real^3) % a = --(norm(a:real^3) % b)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `\v:real^3. (norm(a:real^3) * norm(b:real^3)) % v` o
      check (fun th -> is_eq(concl th) && can (find_term ((=) `inv`)) (concl th))) THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC; VECTOR_MUL_RNEG] THEN
    SUBGOAL_THEN `norm(a:real^3) * norm(b:real^3) * inv(norm a) = norm b /\
                  norm(a:real^3) * norm(b:real^3) * inv(norm b) = norm a`
      (fun th -> REWRITE_TAC[REAL_MUL_ASSOC; th] THEN
                 REWRITE_TAC[GSYM REAL_MUL_ASSOC; th]) THEN
    UNDISCH_TAC `&0 < norm(a:real^3)` THEN UNDISCH_TAC `&0 < norm(b:real^3)` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(b:real^3) * norm(a - b:real^3) = (norm a + norm b) * norm b`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `norm(b:real^3) % (a - b:real^3) = --((norm a + norm b) % b)`
    MP_TAC THENL
     [REWRITE_TAC[VECTOR_SUB_LDISTRIB] THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `norm:real^3->real`) THEN
    REWRITE_TAC[NORM_MUL; NORM_NEG; REAL_ABS_NORM] THEN
    SUBGOAL_THEN `abs(norm(a:real^3) + norm(b:real^3)) = norm a + norm b`
      (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `&0 < norm(a:real^3)` THEN UNDISCH_TAC `&0 < norm(b:real^3)` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(a - b:real^3) = norm a + norm b` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_EQ_LCANCEL_IMP THEN EXISTS_TAC `norm(b:real^3)` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `norm(a - b:real^3) = norm a + norm b` THEN
  UNDISCH_TAC `e <= norm(a:real^3)` THEN UNDISCH_TAC `norm(a - b:real^3) < e` THEN
  UNDISCH_TAC `&0 < norm(b:real^3)` THEN REAL_ARITH_TAC);;

let MOI_S5M_SPHERE_MAP = prove
 (`!(g:real^3->real^3) s0 y.
     g continuous_on s0 /\ (!z. z IN s0 ==> ~(g z = y))
     ==> (\z. inv(norm(g z - y)) % (g z - y)) continuous_on s0 /\
         IMAGE (\z. inv(norm(g z - y)) % (g z - y)) s0 SUBSET sphere(vec 0,&1)`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(lift o (\z. inv(norm((g:real^3->real^3) z - y)))) =
                    (lift o inv o (\z. norm(g z - y)))` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_INV THEN CONJ_TAC THENL
       [REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[CONTINUOUS_ON_CONST; ETA_AX];
        ASM_SIMP_TAC[NORM_EQ_0; VECTOR_SUB_EQ]];
      MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[CONTINUOUS_ON_CONST; ETA_AX]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0] THEN
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~((g:real^3->real^3) z - y = vec 0)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[VECTOR_SUB_EQ]; ALL_TAC] THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0]]);;

let MOI_S5M_HOMOTOPIC_CLOSE = prove
 (`!(f:real^3->real^3) h s0 y e.
     f continuous_on s0 /\ h continuous_on s0 /\
     (!z. z IN s0 ==> dist(f z,h z) < e) /\ (!z. z IN s0 ==> e <= dist(h z,y))
     ==> (!z. z IN s0 ==> ~(f z = y)) /\
         homotopic_with (\x. T)
           (subtopology euclidean s0,subtopology euclidean (sphere(vec 0:real^3,&1)))
           (\z. inv(norm(h z - y)) % (h z - y)) (\z. inv(norm(f z - y)) % (f z - y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z. z IN s0 ==> &0 < dist((h:real^3->real^3) z,y) /\
                                &0 < dist((f:real^3->real^3) z,y)` ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    UNDISCH_TAC `!z:real^3. z IN s0 ==> dist((f:real^3->real^3) z,h z) < e` THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN
    UNDISCH_TAC `!z:real^3. z IN s0 ==> e <= dist((h:real^3->real^3) z,y)` THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(NORM_ARITH
      `dist((h:real^3->real^3) z,y) <= dist((f:real^3->real^3) z,h z) + dist(f z,y)`) THEN
    MP_TAC(ISPECL [`(f:real^3->real^3) z`; `(h:real^3->real^3) z`] DIST_POS_LE) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(!z. z IN s0 ==> ~((h:real^3->real^3) z = y)) /\
                (!z. z IN s0 ==> ~((f:real^3->real^3) z = y))` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[DIST_REFL; REAL_LT_REFL]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMOTOPIC_NON_ANTIPODAL_SPHEREMAPS THEN
  ASM_SIMP_TAC[MOI_S5M_SPHERE_MAP] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  MATCH_MP_TAC MOI_S5M_NOT_ANTIPODAL THEN EXISTS_TAC `e:real` THEN
  REWRITE_TAC[VECTOR_ARITH `((h:real^3) - y) - (f - y) = h - f`] THEN
  REWRITE_TAC[GSYM dist] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[];
    GEN_REWRITE_TAC LAND_CONV [DIST_SYM] THEN ASM_SIMP_TAC[]]);;

let MARKER = prove
 (MOI_S35_MARKER,
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `bs:real^N->bool`; `k:real^N->bool`;
                       `f:real^N->real^3`; `h:real^N->real^3`; `e:real`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S5M_CELL_STD) THEN
  DISCH_THEN(X_CHOOSE_THEN `ff:real^3->real^N` (X_CHOOSE_THEN `gg:real^N->real^3`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `k0 = convex hull {vec 0:real^3,basis 1,basis 2,basis 3}` THEN
  SUBGOAL_THEN `convex (k0:real^3->bool) /\ compact k0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "k0" THEN
    SIMP_TAC[CONVEX_CONVEX_HULL; COMPACT_CONVEX_HULL; FINITE_IMP_COMPACT;
             FINITE_INSERT; FINITE_EMPTY];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5M_PLH_FACTS o check (fun th ->
    concl th = `pl_homeomorphism (k0,s:real^N->bool)
                  ((ff:real^3->real^N),(gg:real^N->real^3))`)) THEN
  SUBGOAL_THEN
   `((f:real^N->real^3) o (ff:real^3->real^N)) continuous_on k0 /\
    ((h:real^N->real^3) o ff) continuous_on k0 /\
    (!x y. x IN k0 /\ y IN k0 /\ (f o ff) x = (f o ff) y ==> x = y) /\
    (!x y. x IN k0 /\ y IN k0 /\ (h o ff) x = (h o ff) y ==> x = y)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[o_THM] THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `(ff:real^3->real^N) x = ff y` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term ((=) `f:real^N->real^3`)) (concl th) && is_forall (concl th) &&
          not (can (find_term ((=) `h:real^N->real^3`)) (concl th)))) THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        ASM_MESON_TAC[]];
      REWRITE_TAC[o_THM] THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `(ff:real^3->real^N) x = ff y` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term ((=) `h:real^N->real^3`)) (concl th) && is_forall (concl th) &&
          not (can (find_term ((=) `f:real^N->real^3`)) (concl th)) &&
          not (can (find_term ((=) `e:real`)) (concl th)))) THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^N->real^3) s = IMAGE (f o (ff:real^3->real^N)) k0` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[IMAGE_o]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^N) IN s /\ ~(x IN bs)` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(gg:real^N->real^3) x IN interior k0` ASSUME_TAC THENL
   [SUBGOAL_THEN `(gg:real^N->real^3) x IN k0` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(MATCH_MP MOI_S5M_FRONTIER_SPLIT (ASSUME `compact (k0:real^3->bool)`)) THEN
    STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    UNDISCH_TAC `~((x:real^N) IN bs)` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rand(concl th) = `bs:real^N->bool`)) THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(gg:real^N->real^3) x` THEN
    ASM_SIMP_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `x0 = (gg:real^N->real^3) x` THEN
  SUBGOAL_THEN `(ff:real^3->real^N) x0 = x` ASSUME_TAC THENL
   [EXPAND_TAC "x0" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^N->real^3) x = (h o (ff:real^3->real^N)) x0` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[o_THM]; ALL_TAC] THEN
  ABBREV_TAC `y0 = ((h:real^N->real^3) o (ff:real^3->real^N)) x0` THEN
  (* the h side: essential Borsuk map *)
  MP_TAC(ISPECL [`(h:real^N->real^3) o (ff:real^3->real^N)`; `k0:real^3->bool`;
                 `x0:real^3`] MOI_S5M_BOUNDED_COMP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact (frontier (k0:real^3->bool)) /\ frontier k0 SUBSET k0`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_FRONTIER_BOUNDED; COMPACT_IMP_BOUNDED] THEN
    MP_TAC(MATCH_MP MOI_S5M_FRONTIER_SPLIT (ASSUME `compact (k0:real^3->bool)`)) THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE ((h:real^N->real^3) o (ff:real^3->real^N)) (frontier k0)`;
                 `y0:real^3`] BORSUK_MAP_ESSENTIAL_BOUNDED_COMPONENT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`(h:real^N->real^3) o (ff:real^3->real^N)`; `frontier k0:real^3->bool`;
                 `y0:real^3`] MOI_S5M_BORSUK_TRANSFER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ASM_MESON_TAC[SUBSET]];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  (* the close homotopy on the frontier *)
  MP_TAC(ISPECL [`(f:real^N->real^3) o (ff:real^3->real^N)`;
                 `(h:real^N->real^3) o (ff:real^3->real^N)`; `frontier k0:real^3->bool`;
                 `y0:real^3`; `e:real`] MOI_S5M_HOMOTOPIC_CLOSE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `f:real^N->real^3`)) (concl th) && is_forall (concl th) &&
        can (find_term ((=) `bs:real^N->bool`)) (concl th))) THEN
      ASM SET_TAC[];
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
      EXPAND_TAC "y0" THEN EXPAND_TAC "x0" THEN REWRITE_TAC[o_THM] THEN
      ASM_SIMP_TAC[] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `k:real^N->bool`)) (concl th) && is_forall (concl th) &&
        can (find_term ((=) `bs:real^N->bool`)) (concl th))) THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `~(?c. homotopic_with (\x. T)
           (subtopology euclidean (frontier k0),
            subtopology euclidean (sphere(vec 0:real^3,&1)))
           (\z. inv(norm(((f:real^N->real^3) o (ff:real^3->real^N)) z - y0)) %
                (((f:real^N->real^3) o ff) z - y0)) (\x. c))`
  ASSUME_TAC THENL
   [DISCH_THEN(X_CHOOSE_TAC `c:real^3`) THEN
    UNDISCH_TAC
     `~(?c. homotopic_with (\x. T)
            (subtopology euclidean (frontier k0),
             subtopology euclidean (sphere(vec 0:real^3,&1)))
            (\z. inv(norm(((h:real^N->real^3) o (ff:real^3->real^N)) z - y0)) %
                 (((h:real^N->real^3) o ff) z - y0)) (\x. c))` THEN
    REWRITE_TAC[] THEN EXISTS_TAC `c:real^3` THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_TRANS THEN
    EXISTS_TAC `\z. inv(norm(((f:real^N->real^3) o (ff:real^3->real^N)) z - y0)) %
                    (((f:real^N->real^3) o ff) z - y0)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the f side *)
  MP_TAC(ISPECL [`(f:real^N->real^3) o (ff:real^3->real^N)`; `frontier k0:real^3->bool`;
                 `y0:real^3`] MOI_S5M_BORSUK_TRANSFER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      ASM_MESON_TAC[SUBSET];
      REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`IMAGE ((f:real^N->real^3) o (ff:real^3->real^N)) (frontier k0)`;
                 `y0:real^3`] BORSUK_MAP_ESSENTIAL_BOUNDED_COMPONENT) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~((y0:real^3) IN IMAGE ((f:real^N->real^3) o (ff:real^3->real^N))
                                      (frontier k0))` ASSUME_TAC THENL
   [REWRITE_TAC[IN_IMAGE; NOT_EXISTS_THM] THEN X_GEN_TAC `z:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN
    UNDISCH_TAC `!z. z IN frontier k0
                     ==> ~(((f:real^N->real^3) o (ff:real^3->real^N)) z = y0)` THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(f:real^N->real^3) o (ff:real^3->real^N)`; `k0:real^3->bool`;
                 `y0:real^3`] MOI_S5M_BOUNDED_IN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`(f:real^N->real^3) o (ff:real^3->real^N)`; `k0:real^3->bool`]
    MOI_S5M_OPEN_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`IMAGE ((f:real^N->real^3) o (ff:real^3->real^N)) k0`;
                 `IMAGE ((f:real^N->real^3) o (ff:real^3->real^N)) (interior k0)`]
    INTERIOR_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTERIOR_SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;


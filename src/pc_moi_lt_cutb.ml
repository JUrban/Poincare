needs "src/pc_moi_lt_cutbstmt.ml";;
needs "src/pc_moi_lt_cutb0.ml";;
needs "src/pc_moi_lt_model2d.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* pc_moi_lt_cutb: the arc case of the cut step of the loop theorem, Moise   *)
(* GTM 47 p.185-187 Cases 3-4.  Main theorem ARC_FROM_SEAM :                 *)
(* |- MOI_LCUS_ARC_FROM_SEAM, i.e. MOI_LCUS_SEAM ==> MOI_LT4_CUT_ARC_SPLIT   *)
(* (statements in pc_moi_lt_cutbstmt.ml).                                    *)
(*   M  the model: the preimage of a double arc k meeting the boundary is   *)
(*      two disjoint spanning PL arcs (vertex walks in the source complex);  *)
(*      the 2D model LT_MODEL_2D (pc_moi_lt_model2d.ml)                      *)
(*      gives a PL homeomorphism g of the rectangle [0,3] x [0,1] onto      *)
(*      std_triangle carrying the chords x = 1 and x = 2 onto them, with    *)
(*      f(g(1,t)) = f(g(2,t)) or f(g(2,1-t)), and the boundary loop in the  *)
(*      standard orientation.                                               *)
(*   D1 the disk R1 + R2 reglued along the two chords: a normal2 disk       *)
(*      without k, whose boundary loop is s1 s3 or s1 s3^-1.                *)
(*   L  the four boundary arcs s1..s4 and the words; SEAM gives D_2.        *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* M1, combinatorics: a longest injective path from a vertex of degree     *)
(* 1 in a graph of degree <= 2 ends at a vertex of degree 1 and its vertex *)
(* set is closed under adjacency.                                           *)
(* ------------------------------------------------------------------------- *)

(* A longest injective path from a vertex of degree 1 in a graph of degree *)
(* at most 2 ends at a vertex of degree 1, and its vertex set is closed    *)
(* under adjacency.                                                          *)

let MOI_LCU_GPATH = prove
 (`!(V:A->bool) R x0.
     FINITE V /\ x0 IN V /\ (!x y. R x y ==> R y x) /\ (!x. x IN V ==> ~R x x) /\
     (!x a b c. x IN V /\ a IN V /\ b IN V /\ c IN V /\ R x a /\ R x b /\ R x c
                ==> a = b \/ a = c \/ b = c) /\
     (?y. y IN V /\ R x0 y) /\ (!a b. a IN V /\ b IN V /\ R x0 a /\ R x0 b ==> a = b)
     ==> ?k W. moi_scf_path V R x0 k W /\ 1 <= k /\
               (!u. u IN V /\ R (W k) u ==> u = W(k - 1)) /\
               (!j v. j <= k /\ v IN V /\ R (W j) v ==> ?i. i <= k /\ v = W i)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "sym") (CONJUNCTS_THEN2 (LABEL_TAC "irr")
      (CONJUNCTS_THEN2 (LABEL_TAC "deg") (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `y0:A` STRIP_ASSUME_TAC) (LABEL_TAC "one"))))))) THEN
  MP_TAC(ISPEC `\k. ?W:num->A. moi_scf_path V R x0 k W` num_MAX) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `a /\ (b ==> c) ==> (a <=> b) ==> c`) THEN CONJ_TAC THENL
   [CONJ_TAC THENL
     [EXISTS_TAC `0` THEN EXISTS_TAC `\i:num. (x0:A)` THEN
      REWRITE_TAC[moi_scf_path; LE; LT] THEN ASM_MESON_TAC[];
      EXISTS_TAC `CARD(V:A->bool)` THEN X_GEN_TAC `k:num` THEN
      DISCH_THEN(X_CHOOSE_TAC `W:num->A`) THEN
      MATCH_MP_TAC LT_IMP_LE THEN MATCH_MP_TAC MOI_SCF_PATH_BOUND THEN
      MAP_EVERY EXISTS_TAC [`R:A->A->bool`; `x0:A`; `W:num->A`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (CONJUNCTS_THEN2
    (X_CHOOSE_TAC `W:num->A`) (LABEL_TAC "max"))) THEN
  EXISTS_TAC `k:num` THEN EXISTS_TAC `W:num->A` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_scf_path]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "W0") (CONJUNCTS_THEN2
    (LABEL_TAC "WV") (CONJUNCTS_THEN2 (LABEL_TAC "WR") (LABEL_TAC "Winj")))) THEN
  SUBGOAL_THEN `!u:A. u IN V /\ R ((W:num->A) k) u ==> ?i. i <= k /\ W i = u`
  (LABEL_TAC "onpath") THENL
   [X_GEN_TAC `u:A` THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(ASSUME_TAC o
      REWRITE_RULE[NOT_EXISTS_THM; TAUT `~(a /\ b) <=> a ==> ~b`]) THEN
    USE_THEN "max" (MP_TAC o SPEC `SUC k`) THEN
    REWRITE_TAC[ARITH_RULE `~(SUC k <= k)`; NOT_CLAUSES; IMP_CLAUSES] THEN
    EXISTS_TAC `\i. if i <= k then (W:num->A) i else u` THEN
    MATCH_MP_TAC MOI_SCF_PATH_EXTEND THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i <= k ==> (W:num->A) i IN V` ASSUME_TAC THENL
   [USE_THEN "WV" ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `1 <= k` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `~(k = 0) ==> 1 <= k`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(R:A->A->bool) ((W:num->A) k) (y0:A)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "onpath" (MP_TAC o C MATCH_MP
      (CONJ (ASSUME `(y0:A) IN V`) (ASSUME `(R:A->A->bool) ((W:num->A) k) (y0:A)`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `i = 0` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(y0:A) = x0` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `(W:num->A) 0 = y0` THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
      ALL_TAC] THEN
    USE_THEN "irr" (MP_TAC o C MATCH_MP (ASSUME `(x0:A) IN V`)) THEN
    UNDISCH_TAC `(R:A->A->bool) x0 x0` THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!i. 0 < i /\ i <= k ==> R ((W:num->A) i) (W(i - 1))`
  (LABEL_TAC "Wback") THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    USE_THEN "sym" MATCH_MP_TAC THEN
    SUBGOAL_THEN `(W:num->A) i = W(SUC(i - 1))` SUBST1_TAC THENL
     [AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "WR" MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!i j. i <= k /\ j <= k /\ (W:num->A) i = W j ==> i = j`
  (LABEL_TAC "inj") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    USE_THEN "Winj" (MP_TAC o SPECL [`i:num`; `j:num`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u:A. u IN V /\ R ((W:num->A) k) u ==> u = W(k - 1)`
  (LABEL_TAC "end") THENL
   [X_GEN_TAC `u:A` THEN STRIP_TAC THEN
    USE_THEN "onpath" (MP_TAC o C MATCH_MP
      (CONJ (ASSUME `(u:A) IN V`) (ASSUME `(R:A->A->bool) ((W:num->A) k) (u:A)`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` (CONJUNCTS_THEN2 ASSUME_TAC (SUBST_ALL_TAC o SYM))) THEN
    ASM_CASES_TAC `i = k - 1` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `i:num = k` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      USE_THEN "irr" (MP_TAC o SPEC `(W:num->A) k`) THEN
      ASM_SIMP_TAC[LE_REFL];
      ALL_TAC] THEN
    ASM_CASES_TAC `i = 0` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      SUBGOAL_THEN `(R:A->A->bool) x0 ((W:num->A) k) /\ R x0 (W 1)`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [USE_THEN "sym" MATCH_MP_TAC THEN
          UNDISCH_TAC `(R:A->A->bool) ((W:num->A) k) (W 0)` THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[ARITH_RULE `1 = SUC 0`] THEN
          SUBGOAL_THEN `(x0:A) = W 0` SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
          USE_THEN "WR" MATCH_MP_TAC THEN ASM_ARITH_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `(W:num->A) k IN V /\ W 1 IN V` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN USE_THEN "WV" MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(W:num->A) k = W 1` ASSUME_TAC THENL
       [USE_THEN "one" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `k = 1` MP_TAC THENL
       [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[LE_REFL]; ASM_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `0 < i /\ i + 1 < k` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "deg" (MP_TAC o SPECL [`(W:num->A) i`; `(W:num->A)(i - 1)`;
                                    `(W:num->A)(SUC i)`; `(W:num->A) k`]) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [USE_THEN "WV" MATCH_MP_TAC THEN ASM_ARITH_TAC;
        USE_THEN "WV" MATCH_MP_TAC THEN ASM_ARITH_TAC;
        USE_THEN "WV" MATCH_MP_TAC THEN ASM_ARITH_TAC;
        USE_THEN "WV" MATCH_MP_TAC THEN ASM_ARITH_TAC;
        USE_THEN "Wback" MATCH_MP_TAC THEN ASM_ARITH_TAC;
        USE_THEN "WR" MATCH_MP_TAC THEN ASM_ARITH_TAC;
        USE_THEN "sym" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    STRIP_TAC THENL
     [SUBGOAL_THEN `i - 1 = SUC i` MP_TAC THENL
       [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        ASM_ARITH_TAC];
      SUBGOAL_THEN `i - 1 = k` MP_TAC THENL
       [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        ASM_ARITH_TAC];
      SUBGOAL_THEN `SUC i = k` MP_TAC THENL
       [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        ASM_ARITH_TAC]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`j:num`; `v:A`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `j:num = k` THENL
   [EXISTS_TAC `k - 1` THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    USE_THEN "end" MATCH_MP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `j = 0` THENL
   [EXISTS_TAC `1` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "one" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "WV" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `(R:A->A->bool) ((W:num->A) j) (v:A)` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[ARITH_RULE `1 = SUC 0`] THEN
      SUBGOAL_THEN `(x0:A) = W 0` SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "WR" MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "deg" (MP_TAC o SPECL [`(W:num->A) j`; `(W:num->A)(j - 1)`;
                                  `(W:num->A)(SUC j)`; `v:A`]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "WV" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      USE_THEN "WV" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      USE_THEN "WV" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC[];
      USE_THEN "Wback" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      USE_THEN "WR" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [SUBGOAL_THEN `j - 1 = SUC j` MP_TAC THENL
     [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ASM_ARITH_TAC];
    EXISTS_TAC `j - 1` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    EXISTS_TAC `SUC j` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* Reindexing a finite union of segments of a walk. *)

let MOI_LCU_GSPEC_SUC = prove
 (`!(f:num->A) n. {f i | i < SUC n} = f 0 INSERT {f (SUC i) | i < n}`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_INSERT; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `i = 0` THENL
     [DISJ1_TAC THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN EXISTS_TAC `i - 1` THEN
      SUBGOAL_THEN `SUC(i - 1) = i` SUBST1_TAC THENL
       [ASM_ARITH_TAC; ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]];
    STRIP_TAC THENL
     [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      EXISTS_TAC `SUC i` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]]);;

let MOI_LCU_UNIONS_SUC = prove
 (`!(W:num->real^N) n.
     UNIONS {segment[W i,W(SUC i)] | i < SUC n} =
     segment[W 0,W 1] UNION UNIONS {segment[W(SUC i),W(SUC(SUC i))] | i < n}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOI_LCU_GSPEC_SUC; UNIONS_INSERT] THEN
  REWRITE_TAC[ARITH_RULE `SUC 0 = 1`]);;

(* A PL arc through an injective vertex walk whose edges meet only in     *)
(* common ends.                                                             *)

let MOI_LCU_WALK_ARC = prove
 (`!n (W:num->real^N).
     1 <= n /\ (!i m. i <= n /\ m <= n /\ W i = W m ==> i = m) /\
     (!i m. i < n /\ m < n /\ ~(i = m)
            ==> segment[W i,W(SUC i)] INTER segment[W m,W(SUC m)] SUBSET
                {W i,W(SUC i)} INTER {W m,W(SUC m)})
     ==> ?gam. arc gam /\ pl_map_on (interval[vec 0,vec 1]) gam /\
               pathstart gam = W 0 /\ pathfinish gam = W n /\
               path_image gam = UNIONS {segment[W i,W(SUC i)] | i < n}`,
  INDUCT_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `W:num->real^N` THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((W:num->real^N) 0 = W 1)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `0 = 1` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        not (can (find_term (fun t -> is_const t && fst(dest_const t) = "closed_segment"))
          (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    EXISTS_TAC `linepath((W:num->real^N) 0,W 1)` THEN
    ASM_REWRITE_TAC[ARC_LINEPATH_EQ; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                    PATH_IMAGE_LINEPATH; ARITH_RULE `SUC 0 = 1`] THEN
    SIMP_TAC[MOI_PL2_PL_LINEPATH; MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL] THEN
    REWRITE_TAC[ARITH_RULE `i < 1 <=> i = 0`] THEN
    REWRITE_TAC[SET_RULE `!f:num->real^N->bool. {f i | i = 0} = {f 0}`; UNIONS_1;
                ARITH_RULE `SUC 0 = 1`];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `\i. (W:num->real^N)(SUC i)` o check (fun th ->
    is_forall(concl th) && is_imp(snd(strip_forall(concl th))))) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `SUC i = SUC m` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          not (can (find_term (fun t -> is_const t && fst(dest_const t) = "closed_segment"))
            (concl th)))) THEN
        ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        ARITH_TAC];
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "closed_segment"))
          (concl th))) THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g1:real^1->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `linepath((W:num->real^N) 0,W 1) ++ g1` THEN
  SUBGOAL_THEN `pathfinish(linepath((W:num->real^N) 0,W 1)) = pathstart g1`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[PATHFINISH_LINEPATH; ARITH_RULE `SUC 0 = 1`]; ALL_TAC] THEN
  ASM_SIMP_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATH_IMAGE_JOIN; PATHSTART_LINEPATH;
               PATH_IMAGE_LINEPATH; MOI_LCU_UNIONS_SUC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ARC_JOIN THEN ASM_REWRITE_TAC[ARC_LINEPATH_EQ; PATH_IMAGE_LINEPATH] THEN
    ASM_REWRITE_TAC[ARITH_RULE `SUC 0 = 1`] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS; IN_ELIM_THM; IN_SING] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t:real^N->bool`
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) ASSUME_TAC))) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `SUC i`] o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "closed_segment"))
        (concl th))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `SUC 0 = 1`; SUBSET; IN_INTER; IN_INSERT; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~((W:num->real^N) 0 = W(SUC i)) /\ ~(W 0 = W(SUC(SUC i)))`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN DISCH_TAC THENL
       [SUBGOAL_THEN `0 = SUC i` MP_TAC;
        SUBGOAL_THEN `0 = SUC(SUC i)` MP_TAC] THEN
      (CONJ_TAC ORELSE ALL_TAC) THEN
      TRY(FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        not (can (find_term (fun t -> is_const t && fst(dest_const t) = "closed_segment"))
          (concl th)))) THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC) THEN
      ARITH_TAC;
      ALL_TAC] THEN
    ASM_MESON_TAC[];
    MATCH_MP_TAC MOI_PL2_PL_JOINPATHS THEN
    ASM_SIMP_TAC[MOI_PL2_PL_LINEPATH; MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL]]);;

(* ------------------------------------------------------------------------- *)
(* M1, complexes: edges of a 1-dimensional simplicial complex; the         *)
(* vertex graph of a component is connected; a component with a vertex of *)
(* degree 1 is the union of the edges of an injective vertex walk.          *)
(* ------------------------------------------------------------------------- *)

(* Edges of a 1-dimensional simplicial complex: their ends are vertices,   *)
(* and two different edges meet only in common ends.                      *)

let MOI_LCU_K1_SEG_VERTICES = prove
 (`!(K:(real^N->bool)->bool) a b.
     simplicial_complex K /\ (!s. s IN K ==> aff_dim s <= &1) /\
     segment[a,b] IN K /\ ~(a = b)
     ==> {a} IN K /\ {b} IN K`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `segment[a:real^N,b]`] MOI_S4L_K1_CASES) THEN
  ASM_REWRITE_TAC[SEGMENT_EQ_EMPTY] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
   [UNDISCH_TAC `segment[a:real^N,b] = {a'}` THEN REWRITE_TAC[SEGMENT_EQ_SING] THEN
    ASM_MESON_TAC[];
    UNDISCH_TAC `segment[a:real^N,b] = segment[a',b']` THEN REWRITE_TAC[SEGMENT_EQ] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(a:real^N = a' \/ a = b') /\ (b = a' \/ b = b')` MP_TAC THENL
     [UNDISCH_TAC `{a:real^N,b} = {a',b'}` THEN SET_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

let MOI_LCU_K1_SEG_INTER = prove
 (`!(K:(real^N->bool)->bool) a b c d.
     simplicial_complex K /\ segment[a,b] IN K /\ segment[c,d] IN K /\
     ~(a = b) /\ ~(c = d) /\ ~(segment[a,b] = segment[c,d])
     ==> segment[a,b] INTER segment[c,d] SUBSET {a,b} INTER {c,d}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(segment[a,b] INTER segment[c,d]) face_of segment[a:real^N,b] /\
                (segment[a,b] INTER segment[c,d]) face_of segment[c:real^N,d]`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_complex (K:(real^N->bool)->bool)` THEN
    REWRITE_TAC[simplicial_complex] THEN
    DISCH_THEN(MP_TAC o SPECL [`segment[a:real^N,b]`; `segment[c:real^N,d]`] o
      last o CONJUNCTS) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `segment[a,b] INTER segment[c,d] = {x:real^N}` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [ALL_TAC; ASM_REWRITE_TAC[SING_SUBSET]] THEN
    REWRITE_TAC[SUBSET; IN_SING] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `segment[a,b] INTER segment[c,d] = segment[a:real^N,b] /\
                  segment[a,b] INTER segment[c,d] = segment[c:real^N,d]`
    MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC MOI_LCC_FACE_SEGMENT_TWO THEN
      MAP_EVERY EXISTS_TAC [`x:real^N`; `y:real^N`] THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `x extreme_point_of segment[a:real^N,b] /\ x extreme_point_of segment[c,d]`
  MP_TAC THENL
   [REWRITE_TAC[GSYM FACE_OF_SING] THEN ASM_MESON_TAC[];
    REWRITE_TAC[EXTREME_POINT_OF_SEGMENT; IN_INTER; IN_INSERT; NOT_IN_EMPTY] THEN
    MESON_TAC[]]);;

(* Three elements of a set of size at most 2 are not pairwise distinct. *)

let MOI_LCU_SIZE_LE2 = prove
 (`!(s:A->bool). s HAS_SIZE 1 \/ s HAS_SIZE 2
                 ==> !a b c. a IN s /\ b IN s /\ c IN s ==> a = b \/ a = c \/ b = c`,
  GEN_TAC THEN CONV_TAC(LAND_CONV(BINOP_CONV HAS_SIZE_CONV)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[]);;

(* The vertex graph of a component of a 1-dimensional complex is connected. *)

let MOI_LCU_K1_CONN = prove
 (`!(K:(real^N->bool)->bool) j U.
     simplicial_complex K /\ (!s. s IN K ==> aff_dim s <= &1) /\
     j IN components (UNIONS K) /\
     U SUBSET {a | {a} IN K /\ a IN j} /\ ~(U = {}) /\
     (!x y. x IN U /\ {y} IN K /\ y IN j /\ ~(x = y) /\ segment[x,y] IN K ==> y IN U)
     ==> U = {a | {a} IN K /\ a IN j}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN K ==> connected s /\ closed s /\ s SUBSET UNIONS K`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX; CONVEX_CONNECTED];
      ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_COMPACT; COMPACT_IMP_CLOSED];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN K /\ ~(s INTER j = {}) ==> s SUBSET j`
  (LABEL_TAC "insj") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
    EXISTS_TAC `UNIONS K:real^N->bool` THEN ASM_MESON_TAC[INTER_COMM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(j:real^N->bool) SUBSET UNIONS K` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
  ABBREV_TAC `V = {a:real^N | {a} IN K /\ a IN j}` THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `?a0:real^N. a0 IN V /\ ~(a0 IN U)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(U:real^N->bool = V)` THEN
    UNDISCH_TAC `(U:real^N->bool) SUBSET V` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s a b:real^N. s IN K /\ s SUBSET j /\ {a} IN K /\ a IN s /\ {b} IN K /\ b IN s
                   ==> (a IN U <=> b IN U)`
  (LABEL_TAC "allin") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `s:real^N->bool`] MOI_S4L_K1_CASES) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
     [ASM_MESON_TAC[NOT_IN_EMPTY];
      ASM_MESON_TAC[IN_SING];
      ALL_TAC] THEN
    SUBGOAL_THEN `(a = a' \/ a = b') /\ (b = a' \/ b = (b':real^N))` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC MOI_S4L_K1_ENDPOINT THEN
      EXISTS_TAC `K:(real^N->bool)->bool` THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(a':real^N) IN j /\ b' IN j` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET; ENDS_IN_SEGMENT]; ALL_TAC] THEN
    SUBGOAL_THEN `segment[a':real^N,b'] IN K /\ segment[b',a'] IN K` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[SEGMENT_SYM]; ALL_TAC] THEN
    SUBGOAL_THEN `((a':real^N) IN U ==> b' IN U) /\ (b' IN U ==> a' IN U)` MP_TAC THENL
     [CONJ_TAC THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        length(fst(strip_forall(concl th))) = 2 &&
        can (find_term (fun t -> t = `U:real^N->bool`)) (concl th))) THENL
       [EXISTS_TAC `a':real^N`; EXISTS_TAC `b':real^N`] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `X = UNIONS {s | s IN K /\ s SUBSET j /\
                             ?a:real^N. a IN U /\ {a} IN K /\ a IN s}` THEN
  ABBREV_TAC `Y = UNIONS {s | s IN K /\ s SUBSET j /\
                             ?a:real^N. a IN V DIFF U /\ {a} IN K /\ a IN s}` THEN
  SUBGOAL_THEN `closed(X:real^N->bool) /\ closed(Y:real^N->bool)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["X"; "Y"] THEN CONJ_TAC THEN
    MATCH_MP_TAC CLOSED_UNIONS THEN REWRITE_TAC[IN_ELIM_THM] THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_MESON_TAC[simplicial_complex];
       ASM_MESON_TAC[]]);
    ALL_TAC] THEN
  SUBGOAL_THEN `(j:real^N->bool) SUBSET X UNION Y` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_UNION] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?s:real^N->bool. s IN K /\ x IN s` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^N) IN j` THEN
      UNDISCH_TAC `(j:real^N->bool) SUBSET UNIONS K` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(s:real^N->bool) SUBSET j` ASSUME_TAC THENL
     [USE_THEN "insj" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `s:real^N->bool`] MOI_S4L_K1_VERTEX_IN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[NOT_IN_EMPTY]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(a:real^N) IN V` ASSUME_TAC THENL
     [EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[SUBSET];
      ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["X"; "Y"] THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    ASM_CASES_TAC `(a:real^N) IN U` THENL
     [DISJ1_TAC; DISJ2_TAC] THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[IN_DIFF];
    ALL_TAC] THEN
  SUBGOAL_THEN `X INTER Y INTER (j:real^N->bool) = {}` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["X"; "Y"] THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_UNIONS; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `s1:real^N->bool` (CONJUNCTS_THEN2
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
          (X_CHOOSE_THEN `a1:real^N` STRIP_ASSUME_TAC))) ASSUME_TAC))
      (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `s2:real^N->bool` (CONJUNCTS_THEN2
          (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
            (X_CHOOSE_THEN `a2:real^N` STRIP_ASSUME_TAC))) ASSUME_TAC))
        ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `s1:real^N->bool`; `s2:real^N->bool`]
      MOI_S4L_K1_COMMON_VERTEX) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `((a1:real^N) IN U <=> c IN U) /\ ((a2:real^N) IN U <=> c IN U)`
    MP_TAC THENL
     [CONJ_TAC THEN USE_THEN "allin" MATCH_MP_TAC THENL
       [EXISTS_TAC `s1:real^N->bool`; EXISTS_TAC `s2:real^N->bool`] THEN
      ASM_REWRITE_TAC[];
      RULE_ASSUM_TAC(REWRITE_RULE[IN_DIFF]) THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `j IN components(UNIONS K:real^N->bool)` THEN
  DISCH_THEN(MP_TAC o MATCH_MP IN_COMPONENTS_CONNECTED) THEN
  REWRITE_TAC[CONNECTED_CLOSED] THEN
  MAP_EVERY EXISTS_TAC [`X:real^N->bool`; `Y:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `?a:real^N. a IN U` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `a:real^N` THEN
    SUBGOAL_THEN `{a:real^N} IN K /\ a IN j` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(U:real^N->bool) SUBSET V` THEN EXPAND_TAC "V" THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "X" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `{a:real^N}` THEN ASM_REWRITE_TAC[IN_SING; SING_SUBSET] THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `a0:real^N` THEN
    SUBGOAL_THEN `{a0:real^N} IN K /\ a0 IN j` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(a0:real^N) IN V` THEN EXPAND_TAC "V" THEN
      REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "Y" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `{a0:real^N}` THEN ASM_REWRITE_TAC[IN_SING; SING_SUBSET] THEN
    EXISTS_TAC `a0:real^N` THEN ASM_REWRITE_TAC[IN_DIFF; IN_SING]]);;

(* A component of a 1-dimensional complex with vertex degrees 1 or 2 that  *)
(* contains a vertex of degree 1 is the union of the edges of an injective  *)
(* vertex walk from it to another vertex of degree 1, through vertices of  *)
(* degree 2.                                                                *)

let MOI_LCU_K1_PATH = prove
 (`!(K:(real^N->bool)->bool) j v0.
     simplicial_complex K /\ (!s. s IN K ==> aff_dim s <= &1) /\
     (!v. {v} IN K ==> {u | ~(u = v) /\ segment[v,u] IN K} HAS_SIZE 1 \/
                       {u | ~(u = v) /\ segment[v,u] IN K} HAS_SIZE 2) /\
     j IN components (UNIONS K) /\ {v0} IN K /\ v0 IN j /\
     {u | ~(u = v0) /\ segment[v0,u] IN K} HAS_SIZE 1
     ==> ?n W. 1 <= n /\ W 0 = v0 /\
               (!i m. i <= n /\ m <= n /\ W i = W m ==> i = m) /\
               (!i. i <= n ==> {W i} IN K /\ W i IN j) /\
               (!i. i < n ==> segment[W i,W(SUC i)] IN K) /\
               j = UNIONS {segment[W i,W(SUC i)] | i < n} /\
               (!v. {v} IN K /\ v IN j ==> ?i. i <= n /\ v = W i) /\
               {u | ~(u = W n) /\ segment[W n,u] IN K} HAS_SIZE 1 /\
               (!i. 0 < i /\ i < n
                    ==> {u | ~(u = W i) /\ segment[W i,u] IN K} HAS_SIZE 2)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "degs") STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN K /\ ~(s INTER j = {}) ==> s SUBSET j`
  (LABEL_TAC "insj") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
    EXISTS_TAC `UNIONS K:real^N->bool` THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX; CONVEX_CONNECTED];
      ASM SET_TAC[];
      ASM_MESON_TAC[INTER_COMM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(j:real^N->bool) SUBSET UNIONS K` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
  ABBREV_TAC `V = {a:real^N | {a} IN K /\ a IN j}` THEN
  SUBGOAL_THEN `!a u:real^N. a IN V /\ ~(u = a) /\ segment[a,u] IN K ==> u IN V`
  (LABEL_TAC "nbr") THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `a:real^N`; `u:real^N`]
        MOI_LCU_K1_SEG_VERTICES) THEN ASM_MESON_TAC[];
      SUBGOAL_THEN `segment[a:real^N,u] SUBSET j` MP_TAC THENL
       [USE_THEN "insj" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
        EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[ENDS_IN_SEGMENT];
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
        REWRITE_TAC[ENDS_IN_SEGMENT]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v0:real^N) IN V` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `?y:real^N. {u | ~(u = v0) /\ segment[v0,u] IN K} = {y}`
  (X_CHOOSE_TAC `y0:real^N`) THENL
   [UNDISCH_TAC `{u:real^N | ~(u = v0) /\ segment[v0,u] IN K} HAS_SIZE 1` THEN
    CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(y0:real^N = v0) /\ segment[v0,y0] IN K` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `{u:real^N | ~(u = v0) /\ segment[v0,u] IN K} = {y0}` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN
    DISCH_THEN(MP_TAC o SPEC `y0:real^N`) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `\a b:real^N. ~(a = b) /\ segment[a,b] IN K`;
                 `v0:real^N`] MOI_LCU_GPATH) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "V" THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `IMAGE (CHOICE:(real^N->bool)->real^N) K` THEN CONJ_TAC THENL
       [ASM_MESON_TAC[FINITE_IMAGE; simplicial_complex];
        REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE] THEN
        MESON_TAC[CHOICE_DEF; IN_SING; NOT_INSERT_EMPTY]];
      ASM_REWRITE_TAC[];
      MESON_TAC[SEGMENT_SYM];
      MESON_TAC[];
      MAP_EVERY X_GEN_TAC [`x:real^N`; `a:real^N`; `b:real^N`; `c:real^N`] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `{x:real^N} IN K` ASSUME_TAC THENL
       [UNDISCH_TAC `(x:real^N) IN V` THEN EXPAND_TAC "V" THEN SIMP_TAC[IN_ELIM_THM];
        ALL_TAC] THEN
      USE_THEN "degs" (MP_TAC o C MATCH_MP (ASSUME `{x:real^N} IN K`)) THEN
      DISCH_THEN(MP_TAC o SPECL [`a:real^N`; `b:real^N`; `c:real^N`] o
        MATCH_MP MOI_LCU_SIZE_LE2) THEN
      DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `y0:real^N` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "nbr" MATCH_MP_TAC THEN EXISTS_TAC `v0:real^N` THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN STRIP_TAC THEN
      UNDISCH_TAC `{u:real^N | ~(u = v0) /\ segment[v0,u] IN K} = {y0}` THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN
      DISCH_THEN(fun th -> MP_TAC(SPEC `a:real^N` th) THEN MP_TAC(SPEC `b:real^N` th)) THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `W:num->real^N`
    (CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "end") (LABEL_TAC "clos")))))) THEN
  REWRITE_TAC[moi_scf_path] THEN BETA_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "WV")
    (CONJUNCTS_THEN2 (LABEL_TAC "WR") (LABEL_TAC "Winj")))) THEN
  SUBGOAL_THEN `!i m. i <= k /\ m <= k /\ (W:num->real^N) i = W m ==> i = m`
  (LABEL_TAC "inj") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    USE_THEN "Winj" (MP_TAC o SPECL [`i:num`; `m:num`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i <= k ==> {(W:num->real^N) i} IN K /\ W i IN j`
  (LABEL_TAC "Wj") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "WV" (MP_TAC o C MATCH_MP (ASSUME `i:num <= k`)) THEN
    EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `{(W:num->real^N) i | i <= k} = V` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN MATCH_MP_TAC MOI_LCU_K1_CONN THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN GEN_TAC THEN
      DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      EXISTS_TAC `(W:num->real^N) 0` THEN EXISTS_TAC `0` THEN REWRITE_TAC[LE_0];
      MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN REWRITE_TAC[IN_ELIM_THM] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC)
        STRIP_ASSUME_TAC) THEN
      REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `x:real^N`))) THEN
      USE_THEN "clos" (MP_TAC o SPECL [`i:num`; `y:real^N`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN EXPAND_TAC "V" THEN ASM_REWRITE_TAC[IN_ELIM_THM];
        MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[]]];
    ALL_TAC] THEN
  FIRST_X_ASSUM((fun th -> LABEL_TAC "Veq"
    (MESON[REWRITE_RULE[EXTENSION; IN_ELIM_THM] th]
      `!v:real^N. v IN V ==> ?i. i <= k /\ v = (W:num->real^N) i`)) o
    check (fun th -> aconv (concl th) `{(W:num->real^N) i | i <= k} = V`)) THEN
  SUBGOAL_THEN
   `!i m. i <= k /\ m <= k /\ ~((W:num->real^N) i = W m) /\ segment[W i,W m] IN K
          ==> ?p. p < k /\ segment[W i,W m] = segment[W p,W(SUC p)]`
  (LABEL_TAC "edge") THENL
   [REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `i:num = k` THENL
     [EXISTS_TAC `k - 1` THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(W:num->real^N) m = W(k - 1)` SUBST1_TAC THENL
       [USE_THEN "end" MATCH_MP_TAC THEN
        UNDISCH_TAC `~((W:num->real^N) i = W m)` THEN
        UNDISCH_TAC `segment[(W:num->real^N) i,W m] IN K` THEN
        ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "WV" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `SUC(k - 1) = k` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[SEGMENT_SYM];
      ALL_TAC] THEN
    ASM_CASES_TAC `i = 0` THENL
     [EXISTS_TAC `0` THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      SUBGOAL_THEN `(W:num->real^N) m = y0 /\ W(SUC 0) = y0` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `{u:real^N | ~(u = v0) /\ segment[v0,u] IN K} = {y0}` THEN
        REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN
        DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
        USE_THEN "WR" (MP_TAC o SPEC `0`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `~((W:num->real^N) 0 = W m)` THEN
        UNDISCH_TAC `segment[(W:num->real^N) 0,W m] IN K` THEN
        UNDISCH_TAC `(W:num->real^N) 0 = v0` THEN DISCH_THEN SUBST1_TAC THEN
        MESON_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(W:num->real^N) m = W(i - 1) \/ W m = W(SUC i)` MP_TAC THENL
     [SUBGOAL_THEN `{(W:num->real^N) i} IN K` ASSUME_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `~((W:num->real^N)(i - 1) = W i) /\ segment[W i,W(i - 1)] IN K /\
                    ~((W:num->real^N)(SUC i) = W i) /\ segment[W i,W(SUC i)] IN K /\
                    ~((W:num->real^N) m = W i) /\ ~(W(i - 1) = W(SUC i))`
      STRIP_ASSUME_TAC THENL
       [REPEAT CONJ_TAC THENL
         [DISCH_TAC THEN SUBGOAL_THEN `i - 1 = i` MP_TAC THENL
           [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
            ASM_ARITH_TAC];
          ONCE_REWRITE_TAC[SEGMENT_SYM] THEN
          USE_THEN "WR" (MP_TAC o SPEC `i - 1`) THEN
          SUBGOAL_THEN `SUC(i - 1) = i` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
          ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
          DISCH_TAC THEN SUBGOAL_THEN `SUC i = i` MP_TAC THENL
           [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
            ARITH_TAC];
          USE_THEN "WR" (MP_TAC o SPEC `i:num`) THEN
          ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
          UNDISCH_TAC `~((W:num->real^N) i = W m)` THEN MESON_TAC[];
          DISCH_TAC THEN SUBGOAL_THEN `i - 1 = SUC i` MP_TAC THENL
           [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
            ARITH_TAC]];
        ALL_TAC] THEN
      USE_THEN "degs" (MP_TAC o C MATCH_MP (ASSUME `{(W:num->real^N) i} IN K`)) THEN
      DISCH_THEN(MP_TAC o SPECL [`(W:num->real^N)(i - 1)`; `(W:num->real^N)(SUC i)`;
                                 `(W:num->real^N) m`] o MATCH_MP MOI_LCU_SIZE_LE2) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THENL
     [EXISTS_TAC `i - 1` THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `SUC(i - 1) = i` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[SEGMENT_SYM];
      EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i < k ==> ~((W:num->real^N) i = W(SUC i)) /\
                              segment[W i,W(SUC i)] IN K /\ segment[W(SUC i),W i] IN K`
  (LABEL_TAC "WR2") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "WR" (MP_TAC o C MATCH_MP (ASSUME `i:num < k`)) THEN
    MESON_TAC[SEGMENT_SYM];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`k:num`; `W:num->real^N`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "WR2" (MP_TAC o C MATCH_MP (ASSUME `i:num < k`)) THEN SIMP_TAC[];
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN `?s:real^N->bool. s IN K /\ x IN s` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(x:real^N) IN j` THEN
        UNDISCH_TAC `(j:real^N->bool) SUBSET UNIONS K` THEN SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(s:real^N->bool) SUBSET j` ASSUME_TAC THENL
       [USE_THEN "insj" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
        EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `!a:real^N. {a} IN K /\ a IN j ==> ?i. i <= k /\ a = (W:num->real^N) i`
      (LABEL_TAC "onW") THENL
       [GEN_TAC THEN STRIP_TAC THEN USE_THEN "Veq" MATCH_MP_TAC THEN
        EXPAND_TAC "V" THEN ASM_REWRITE_TAC[IN_ELIM_THM];
        ALL_TAC] THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `s:real^N->bool`] MOI_S4L_K1_CASES) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
       [UNDISCH_TAC `(x:real^N) IN s` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY];
        SUBGOAL_THEN `(x:real^N) = a` SUBST_ALL_TAC THENL
         [UNDISCH_TAC `(x:real^N) IN s` THEN ASM_REWRITE_TAC[IN_SING]; ALL_TAC] THEN
        USE_THEN "onW" (MP_TAC o SPEC `a:real^N`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
        ASM_CASES_TAC `i:num < k` THENL
         [EXISTS_TAC `segment[(W:num->real^N) i,W(SUC i)]` THEN
          ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN EXISTS_TAC `i:num` THEN
          ASM_REWRITE_TAC[];
          EXISTS_TAC `segment[(W:num->real^N)(k - 1),W(SUC(k - 1))]` THEN
          CONJ_TAC THENL
           [EXISTS_TAC `k - 1` THEN REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `SUC(k - 1) = i` SUBST1_TAC THENL
           [ASM_ARITH_TAC; ASM_REWRITE_TAC[ENDS_IN_SEGMENT]]];
        SUBGOAL_THEN `(a:real^N) IN j /\ b IN j` STRIP_ASSUME_TAC THENL
         [UNDISCH_TAC `(s:real^N->bool) SUBSET j` THEN ASM_REWRITE_TAC[] THEN
          MESON_TAC[SUBSET; ENDS_IN_SEGMENT];
          ALL_TAC] THEN
        USE_THEN "onW" (MP_TAC o SPEC `a:real^N`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
        USE_THEN "onW" (MP_TAC o SPEC `b:real^N`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
        USE_THEN "edge" (MP_TAC o SPECL [`i:num`; `m:num`]) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
           [UNDISCH_TAC `~(a:real^N = b)` THEN ASM_REWRITE_TAC[];
            UNDISCH_TAC `(s:real^N->bool) IN K` THEN ASM_REWRITE_TAC[]];
          ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `segment[(W:num->real^N) p,W(SUC p)]` THEN
        CONJ_TAC THENL [EXISTS_TAC `p:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        UNDISCH_TAC `(x:real^N) IN s` THEN
        UNDISCH_TAC `segment[(W:num->real^N) i,W m] = segment[W p,W(SUC p)]` THEN
        UNDISCH_TAC `(s:real^N->bool) = segment[a,b]` THEN
        UNDISCH_TAC `(a:real^N) = W(i:num)` THEN UNDISCH_TAC `(b:real^N) = W(m:num)` THEN
        REPEAT(DISCH_THEN SUBST1_TAC) THEN SIMP_TAC[]];
      REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN X_GEN_TAC `i:num` THEN
      DISCH_TAC THEN USE_THEN "insj" MATCH_MP_TAC THEN
      USE_THEN "WR2" (MP_TAC o C MATCH_MP (ASSUME `i:num < k`)) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `(W:num->real^N) i` THEN REWRITE_TAC[ENDS_IN_SEGMENT] THEN
      USE_THEN "Wj" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]];
    X_GEN_TAC `v:real^N` THEN STRIP_TAC THEN USE_THEN "Veq" MATCH_MP_TAC THEN
    EXPAND_TAC "V" THEN ASM_REWRITE_TAC[IN_ELIM_THM];
    SUBGOAL_THEN `{u | ~(u = (W:num->real^N) k) /\ segment[W k,u] IN K} = {W(k - 1)}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN X_GEN_TAC `u:real^N` THEN
      EQ_TAC THENL
       [STRIP_TAC THEN USE_THEN "end" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "nbr" MATCH_MP_TAC THEN EXISTS_TAC `(W:num->real^N) k` THEN
        ASM_REWRITE_TAC[] THEN USE_THEN "WV" MATCH_MP_TAC THEN REWRITE_TAC[LE_REFL];
        DISCH_THEN SUBST1_TAC THEN
        USE_THEN "WR2" (MP_TAC o SPEC `k - 1`) THEN
        SUBGOAL_THEN `SUC(k - 1) = k` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]];
      CONV_TAC HAS_SIZE_CONV THEN MESON_TAC[]];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `{(W:num->real^N) i} IN K` ASSUME_TAC THENL
     [USE_THEN "Wj" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    USE_THEN "degs" (MP_TAC o C MATCH_MP (ASSUME `{(W:num->real^N) i} IN K`)) THEN
    MATCH_MP_TAC(TAUT `~a ==> a \/ b ==> b`) THEN
    CONV_TAC(RAND_CONV HAS_SIZE_CONV) THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^N` MP_TAC) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `(W:num->real^N)(i - 1)` th) THEN
                         MP_TAC(SPEC `(W:num->real^N)(SUC i)` th)) THEN
    USE_THEN "WR2" (MP_TAC o SPEC `i:num`) THEN
    USE_THEN "WR2" (MP_TAC o SPEC `i - 1`) THEN
    SUBGOAL_THEN `SUC(i - 1) = i` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `~((W:num->real^N)(i - 1) = W(SUC i))` MP_TAC THENL
     [DISCH_TAC THEN SUBGOAL_THEN `i - 1 = SUC i` MP_TAC THENL
       [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* M1, the source arcs: boundary points are vertices; a source            *)
(* component meeting the frontier of std_triangle is a PL arc with exactly *)
(* its two ends on the frontier.                                            *)
(* ------------------------------------------------------------------------- *)

(* Points of the source double set on the frontier of std_triangle are    *)
(* vertices of the source complex; points of the double image on the       *)
(* boundary of c are vertices of its 1-manifold complex.                    *)

let MOI_LCU_SRC_BD_VERTEX = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) s0 x.
     moi_lt_normal_disk c f /\ simplicial_complex s0 /\
     UNIONS s0 = {x | x IN std_triangle /\ f x IN moi_lt_double_image f} /\
     (!t. t IN s0 ==> aff_dim t <= &1 /\ t SUBSET std_triangle /\
                      ?l y. linear l /\ !z. z IN t ==> f z = l z + y) /\
     x IN UNIONS s0 /\ x IN relative_frontier std_triangle
     ==> {x} IN s0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s0:(real^2->bool)->bool`; `x:real^2`] MOI_LCC_POINT_CASES) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `~b ==> a \/ b ==> a`) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^2` (X_CHOOSE_THEN `b:real^2` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `moi_lt_singular_disk c (f:real^2->real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_lt_normal_disk]; ALL_TAC] THEN
  SUBGOAL_THEN `segment[a:real^2,b] SUBSET std_triangle /\
                ?l y. linear l /\ !z. z IN segment[a,b] ==> (f:real^2->real^N) z = l z + y`
  (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `l:real^2->real^N`
    (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC))) THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~((f:real^2->real^N) a = f b)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(a:real^2 = b)` THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`f:real^2->real^N`; `std_triangle`; `segment[a:real^2,b]`;
                   `l:real^2->real^N`; `y:real^N`] MOI_LCC_AFFINE_INJ) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[CONVEX_SEGMENT] THEN
      UNDISCH_TAC `moi_lt_singular_disk c (f:real^2->real^N)` THEN
      REWRITE_TAC[moi_lt_singular_disk] THEN MESON_TAC[];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[ENDS_IN_SEGMENT]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^2->real^N`; `l:real^2->real^N`; `y:real^N`; `a:real^2`; `b:real^2`]
    MOI_LCC_AFFINE_SEG) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `(x:real^2) IN segment(a,b)` THEN REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(x:real^2) = a + u % (b - a)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^2->real^N) x = f a + u % (f b - f a)` ASSUME_TAC THENL
   [SUBST1_TAC(ASSUME `(x:real^2) = a + u % (b - a)`) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `l:real^2->real^N`)) (concl th) = false &&
      can (find_term (fun t -> t = `(f:real^2->real^N) b - f a`)) (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `(f:real^2->real^N) x`;
                 `(f:real^2->real^N) a`; `(f:real^2->real^N) b`] MOI_LCC_BD_NOT_INTERIOR) THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `(x:real^2) IN std_triangle` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_LTD_FRONTIER_SUBSET_TRIANGLE; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `segment[(f:real^2->real^N) a,f b] SUBSET moi_lt_double_image f`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_SEGMENT] THEN X_GEN_TAC `w:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(w:real^N) = f(a + t % (b - a:real^2))` SUBST1_TAC THENL
     [ASM_SIMP_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `a + t % (b - a:real^2) IN UNIONS s0` MP_TAC THENL
     [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `segment[a:real^2,b]` THEN
      ASM_REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `t:real` THEN
      ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[moi_lt_singular_disk];
    UNDISCH_TAC `moi_lt_normal_disk c (f:real^2->real^N)` THEN
    REWRITE_TAC[moi_lt_normal_disk] THEN DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN
    UNDISCH_TAC `segment[(f:real^2->real^N) a,f b] SUBSET moi_lt_double_image f` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `u:real` THEN
    REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC];
    UNDISCH_TAC `moi_lt_singular_disk c (f:real^2->real^N)` THEN
    REWRITE_TAC[moi_lt_singular_disk] THEN
    DISCH_THEN(MP_TAC o el 2 o CONJUNCTS) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    REWRITE_TAC[IN_SEGMENT] THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `u:real` THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC]);;

let MOI_LCU_TGT_BD_VERTEX = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) s y.
     moi_lt_normal_disk c f /\ FINITE s /\ combinatorial_manifold_with_boundary 1 s /\
     UNIONS s = moi_lt_double_image f /\ y IN moi_lt_double_image f /\
     y IN complex_boundary c
     ==> {y} IN s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (s:(real^N->bool)->bool) /\
                (!t. t IN s ==> aff_dim t <= &1)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MOI_LCC_LF_SC THEN
      ASM_MESON_TAC[combinatorial_manifold_with_boundary];
      MATCH_MP_TAC MOI_LCC_CMWB1_DIM THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:(real^N->bool)->bool`; `y:real^N`] MOI_LCC_POINT_CASES) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `~b ==> a \/ b ==> a`) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `y:real^N`;
                 `a:real^N`; `b:real^N`] MOI_LCC_BD_NOT_INTERIOR) THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[moi_lt_normal_disk; moi_lt_singular_disk];
    UNDISCH_TAC `moi_lt_normal_disk c (f:real^2->real^N)` THEN
    REWRITE_TAC[moi_lt_normal_disk] THEN DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `UNIONS (s:(real^N->bool)->bool)`)) THEN
    ASM SET_TAC[]]);;

(* A source component meeting the frontier of std_triangle is a PL arc     *)
(* whose points on the frontier are exactly its two ends.                  *)

let MOI_LCU_SRC_ARC = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) C.
     moi_lt_normal_disk c f /\
     C IN components {x | x IN std_triangle /\ f x IN moi_lt_double_image f} /\
     ~(C INTER relative_frontier std_triangle = {})
     ==> ?p. arc p /\ pl_map_on (interval[vec 0,vec 1]) p /\ path_image p = C /\
             C INTER relative_frontier std_triangle = {pathstart p,pathfinish p}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `s0:(real^2->bool)->bool` STRIP_ASSUME_TAC o
    MATCH_MP MOI_LA1_SRC) THEN
  SUBGOAL_THEN `!t:real^2->bool. t IN s0 ==> aff_dim t <= &1` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!v:real^2. {v} IN s0
               ==> ({u | ~(u = v) /\ segment[v,u] IN s0} HAS_SIZE 1 /\
                    v IN relative_frontier std_triangle) \/
                   ({u | ~(u = v) /\ segment[v,u] IN s0} HAS_SIZE 2 /\
                    ~(v IN relative_frontier std_triangle))`
  (LABEL_TAC "deg") THENL
   [X_GEN_TAC `v:real^2` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`s0:(real^2->bool)->bool`; `v:real^2`] MOI_LCC_LINK_1) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^2->bool. ~(s HAS_SIZE 1 /\ s HAS_SIZE 2)` ASSUME_TAC THENL
   [REWRITE_TAC[HAS_SIZE] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(C:real^2->bool) SUBSET UNIONS s0` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^2. z IN C /\ z IN relative_frontier std_triangle ==> {z} IN s0`
  (LABEL_TAC "bdv") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_LCU_SRC_BD_VERTEX THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `f:real^2->real^N`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY] o check (fun th ->
    concl th = `~((C:real^2->bool) INTER relative_frontier std_triangle = {})`)) THEN
  REWRITE_TAC[IN_INTER] THEN DISCH_THEN(X_CHOOSE_THEN `x0:real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `{x0:real^2} IN s0` ASSUME_TAC THENL
   [USE_THEN "bdv" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(!v:real^2. {v} IN s0 ==> {u | ~(u = v) /\ segment[v,u] IN s0} HAS_SIZE 1 \/
                              {u | ~(u = v) /\ segment[v,u] IN s0} HAS_SIZE 2) /\
    C IN components (UNIONS s0) /\
    {u | ~(u = x0) /\ segment[x0,u] IN s0} HAS_SIZE 1`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `v:real^2` THEN DISCH_TAC THEN
      USE_THEN "deg" (MP_TAC o C MATCH_MP (ASSUME `{v:real^2} IN s0`)) THEN
      MESON_TAC[];
      ASM_REWRITE_TAC[];
      USE_THEN "deg" (MP_TAC o C MATCH_MP (ASSUME `{x0:real^2} IN s0`)) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s0:(real^2->bool)->bool`; `C:real^2->bool`; `x0:real^2`]
    MOI_LCU_K1_PATH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `W:num->real^2` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`n:num`; `W:num->real^2`] MOI_LCU_WALK_ARC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MOI_LCU_K1_SEG_INTER THEN
    EXISTS_TAC `s0:(real^2->bool)->bool` THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `!p q. p <= n /\ q <= n /\ ~(p = q) ==> ~((W:num->real^2) p = W q)`
    (LABEL_TAC "dis") THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC [`i:num < n`; `m:num < n`; `~(i:num = m)`] THEN
    REPEAT DISCH_TAC THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "dis" MATCH_MP_TAC THEN
      UNDISCH_TAC `i:num < n` THEN ARITH_TAC;
      USE_THEN "dis" MATCH_MP_TAC THEN
      UNDISCH_TAC `m:num < n` THEN ARITH_TAC;
      REWRITE_TAC[SEGMENT_EQ] THEN
      SUBGOAL_THEN `~((W:num->real^2) i = W m) /\ ~(W i = W(SUC m)) \/
                    ~(W(SUC i) = W m) /\ ~(W(SUC i) = W(SUC m))`
      MP_TAC THENL
       [ASM_CASES_TAC `i = SUC m` THENL
         [DISJ2_TAC THEN CONJ_TAC THEN USE_THEN "dis" MATCH_MP_TAC THEN
          MAP_EVERY UNDISCH_TAC [`i:num < n`; `m:num < n`; `~(i:num = m)`;
                                 `i = SUC m`] THEN ARITH_TAC;
          DISJ1_TAC THEN CONJ_TAC THEN USE_THEN "dis" MATCH_MP_TAC THEN
          MAP_EVERY UNDISCH_TAC [`i:num < n`; `m:num < n`; `~(i:num = m)`;
                                 `~(i = SUC m)`] THEN ARITH_TAC];
        SET_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^1->real^2` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `C:real^2->bool`)) THEN
  EXISTS_TAC `p:real^1->real^2` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER; IN_INSERT; NOT_IN_EMPTY] THEN
    X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
    SUBGOAL_THEN `{z:real^2} IN s0` ASSUME_TAC THENL
     [USE_THEN "bdv" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `?i. i <= n /\ z = (W:num->real^2) i` STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `C:real^2->bool`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "INSERT")) (concl th) &&
        not (can (find_term (fun t -> is_const t && fst(dest_const t) = "closed_segment"))
               (concl th)))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ASM_CASES_TAC `0 < i /\ i < n` THENL
     [SUBGOAL_THEN `{u | ~(u = (W:num->real^2) i) /\ segment[W i,u] IN s0} HAS_SIZE 2`
      ASSUME_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> t = `2`)) (concl th))) THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      USE_THEN "deg" (MP_TAC o C MATCH_MP (ASSUME `{(W:num->real^2) i} IN s0`)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `{u | ~(u = (W:num->real^2) i) /\ segment[W i,u] IN s0}`
        o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> t = `2`)) (concl th) &&
          not (can (find_term (fun t -> t = `s0:(real^2->bool)->bool`)) (concl th)))) THEN
      ASM_REWRITE_TAC[];
      ASM_CASES_TAC `i = 0` THENL
       [DISJ1_TAC THEN ASM_REWRITE_TAC[];
        DISJ2_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC]];
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_INTER] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(W:num->real^2) n IN C /\ {W n} IN s0` STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `C:real^2->bool`)) (concl th) &&
        not (can (find_term (fun t -> t = `relative_frontier std_triangle`)) (concl th)) &&
        not (can (find_term (fun t -> t = `2`)) (concl th)) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "INSERT")) (concl th) &&
        not (can (find_term (fun t -> t = `v:real^2`)) (concl th)))) THEN
      REWRITE_TAC[LE_REFL] THEN SIMP_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "deg" (MP_TAC o C MATCH_MP (ASSUME `{(W:num->real^2) n} IN s0`)) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `{u | ~(u = (W:num->real^2) n) /\ segment[W n,u] IN s0}`
      o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `2`)) (concl th) &&
        not (can (find_term (fun t -> t = `s0:(real^2->bool)->bool`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC TAUT]);;

(* ------------------------------------------------------------------------- *)
(* M1 result: k meets the boundary of c in two points; its preimage is      *)
(* two disjoint spanning PL arcs p, q with f o q = f o p.                   *)
(* ------------------------------------------------------------------------- *)

(* A component of the double image meeting the boundary of c meets it in at *)
(* least two points (the two ends of the arc).                              *)

let MOI_LCU_TWO_ENDS = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) k.
     moi_lt_normal_disk c f /\ k IN components (moi_lt_double_image f) /\
     ~(k INTER complex_boundary c = {})
     ==> ?y1 y2. ~(y1 = y2) /\ y1 IN k /\ y2 IN k /\
                 y1 IN complex_boundary c /\ y2 IN complex_boundary c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_lt_normal_disk]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `s:(real^N->bool)->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  SUBGOAL_THEN `simplicial_complex (s:(real^N->bool)->bool) /\
                (!t. t IN s ==> aff_dim t <= &1)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MOI_LCC_LF_SC THEN
      ASM_MESON_TAC[combinatorial_manifold_with_boundary];
      MATCH_MP_TAC MOI_LCC_CMWB1_DIM THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v:real^N. {v} IN s
               ==> UNIONS (simplicial_link s v) = {u | ~(u = v) /\ segment[v,u] IN s}`
  (LABEL_TAC "lk") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_LCC_LINK_1 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v:real^N. {v} IN s
               ==> ({u | ~(u = v) /\ segment[v,u] IN s} HAS_SIZE 1 <=>
                    v IN complex_boundary c) /\
                   ({u | ~(u = v) /\ segment[v,u] IN s} HAS_SIZE 1 \/
                    {u | ~(u = v) /\ segment[v,u] IN s} HAS_SIZE 2)`
  (LABEL_TAC "deg") THENL
   [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    USE_THEN "lk" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th (ASSUME `{v:real^N} IN s`))]) THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `{v:real^N} IN s`) o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> t = `complex_boundary (c:(real^N->bool)->bool)`))
        (concl th))) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `combinatorial_manifold_with_boundary 1 (s:(real^N->bool)->bool)` THEN
    REWRITE_TAC[combinatorial_manifold_with_boundary] THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^N` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
    REWRITE_TAC[MOI_LCC_PL_BALL_0; MOI_LCC_PL_SPHERE_0] THEN
    CONV_TAC(ONCE_DEPTH_CONV HAS_SIZE_CONV) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY] o check (fun th ->
    concl th = `~((k:real^N->bool) INTER complex_boundary c = {})`)) THEN
  REWRITE_TAC[IN_INTER] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:real^N) IN moi_lt_double_image f` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `{y:real^N} IN s` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LCU_TGT_BD_VERTEX THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `f:real^2->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:(real^N->bool)->bool`; `k:real^N->bool`; `y:real^N`]
    MOI_LCU_K1_PATH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
      USE_THEN "deg" (MP_TAC o C MATCH_MP (ASSUME `{v:real^N} IN s`)) THEN
      SIMP_TAC[];
      USE_THEN "deg" (MP_TAC o C MATCH_MP (ASSUME `{y:real^N} IN s`)) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `W:num->real^N` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `k:real^N->bool`)) THEN
  MAP_EVERY EXISTS_TAC [`y:real^N`; `(W:num->real^N) n`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN SUBGOAL_THEN `0 = n` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        length(fst(strip_forall(concl th))) = 2 &&
        not (can (find_term (fun t -> is_const t && fst(dest_const t) = "closed_segment"))
          (concl th)))) THEN
      ASM_REWRITE_TAC[LE_0; LE_REFL];
      UNDISCH_TAC `1 <= n` THEN ARITH_TAC];
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `k:real^N->bool`)) (concl th) &&
      not (can (find_term (fun t -> t = `2`)) (concl th)) &&
      length(fst(strip_forall(concl th))) = 1)) THEN
    SIMP_TAC[LE_REFL];
    SUBGOAL_THEN `{(W:num->real^N) n} IN s` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `k:real^N->bool`)) (concl th) &&
        not (can (find_term (fun t -> t = `2`)) (concl th)) &&
        length(fst(strip_forall(concl th))) = 1)) THEN
      SIMP_TAC[LE_REFL];
      ALL_TAC] THEN
    USE_THEN "deg" (MP_TAC o C MATCH_MP (ASSUME `{(W:num->real^N) n} IN s`)) THEN
    ASM_SIMP_TAC[]]);;

(* The preimage of a double arc meeting the boundary of c is two disjoint  *)
(* spanning PL arcs, parametrized compatibly through f.                    *)

let MOI_LCU_SOURCE_ARCS = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) k.
     moi_lt_normal_disk c f /\ k IN components (moi_lt_double_image f) /\
     ~(k INTER complex_boundary c = {})
     ==> ?p q. arc p /\ pl_map_on (interval[vec 0,vec 1]) p /\
               arc q /\ pl_map_on (interval[vec 0,vec 1]) q /\
               path_image p SUBSET std_triangle /\ path_image q SUBSET std_triangle /\
               path_image p INTER relative_frontier std_triangle =
               {pathstart p,pathfinish p} /\
               path_image q INTER relative_frontier std_triangle =
               {pathstart q,pathfinish q} /\
               path_image p INTER path_image q = {} /\
               {x | x IN std_triangle /\ f x IN k} = path_image p UNION path_image q /\
               (!t. t IN interval[vec 0,vec 1] ==> f(q t) = f(p t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_lt_singular_disk c (f:real^2->real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_lt_normal_disk]; ALL_TAC] THEN
  SUBGOAL_THEN `pl_map_on std_triangle (f:real^2->real^N) /\
                f continuous_on std_triangle` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[moi_lt_singular_disk]; ALL_TAC] THEN
    MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN ASM_MESON_TAC[moi_lt_singular_disk];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^2. x IN std_triangle
                           ==> ((f:real^2->real^N) x IN complex_boundary c <=>
                                x IN relative_frontier std_triangle)`
  (LABEL_TAC "bd") THENL
   [UNDISCH_TAC `moi_lt_singular_disk c (f:real^2->real^N)` THEN
    REWRITE_TAC[moi_lt_singular_disk] THEN
    DISCH_THEN(MP_TAC o el 2 o CONJUNCTS) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier std_triangle SUBSET std_triangle` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_LTD_FRONTIER_SUBSET_TRIANGLE]; ALL_TAC] THEN
  ABBREV_TAC `S = {x | x IN std_triangle /\ (f:real^2->real^N) x IN moi_lt_double_image f}` THEN
  ABBREV_TAC `J = {x | x IN std_triangle /\ (f:real^2->real^N) x IN k}` THEN
  SUBGOAL_THEN `(k:real^N->bool) SUBSET moi_lt_double_image f` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(J:real^2->bool) SUBSET S` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["J"; "S"] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^N. y IN k ==> ?x:real^2. x IN J /\ (f:real^2->real^N) x = y`
  (LABEL_TAC "kJ") THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN moi_lt_double_image f` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[moi_lt_double_image; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `x:real^2` THEN EXPAND_TAC "J" THEN ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `k:real^N->bool`]
    MOI_LCU_TWO_ENDS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y1:real^N` (X_CHOOSE_THEN `y2:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `~connected (J:real^2->bool)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    USE_THEN "kJ" (MP_TAC o C MATCH_MP (ASSUME `(y1:real^N) IN k`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `x1:real^2` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `C = connected_component S (x1:real^2)` THEN
    SUBGOAL_THEN `C IN components (S:real^2->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "C" THEN REWRITE_TAC[IN_COMPONENTS] THEN EXISTS_TAC `x1:real^2` THEN
      REWRITE_TAC[] THEN UNDISCH_TAC `(J:real^2->bool) SUBSET S` THEN
      UNDISCH_TAC `(x1:real^2) IN J` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(J:real^2->bool) = C` ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [EXPAND_TAC "C" THEN MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN
        ASM_REWRITE_TAC[];
        SUBGOAL_THEN `IMAGE (f:real^2->real^N) C = k` ASSUME_TAC THENL
         [MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `C:real^2->bool`]
            MOI_LA1_COMPONENT_IMAGE) THEN
          ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
          MP_TAC(ISPECL [`moi_lt_double_image (f:real^2->real^N)`;
                         `IMAGE (f:real^2->real^N) C`; `k:real^N->bool`]
            COMPONENTS_NONOVERLAP) THEN
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `~a ==> (a <=> ~b) ==> b`) THEN
          REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `y1:real^N` THEN
          ASM_REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x1:real^2` THEN
          ASM_REWRITE_TAC[] THEN EXPAND_TAC "C" THEN REWRITE_TAC[IN] THEN
          REWRITE_TAC[CONNECTED_COMPONENT_REFL_EQ] THEN
          UNDISCH_TAC `(J:real^2->bool) SUBSET S` THEN
          UNDISCH_TAC `(x1:real^2) IN J` THEN SET_TAC[];
          ALL_TAC] THEN
        SUBGOAL_THEN `(C:real^2->bool) SUBSET S` ASSUME_TAC THENL
         [EXPAND_TAC "C" THEN REWRITE_TAC[CONNECTED_COMPONENT_SUBSET]; ALL_TAC] THEN
        EXPAND_TAC "J" THEN
        UNDISCH_TAC `IMAGE (f:real^2->real^N) C = k` THEN
        UNDISCH_TAC `(C:real^2->bool) SUBSET S` THEN EXPAND_TAC "S" THEN SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((C:real^2->bool) INTER relative_frontier std_triangle = {})`
    ASSUME_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `x1:real^2` THEN
      SUBGOAL_THEN `(x1:real^2) IN std_triangle` ASSUME_TAC THENL
       [UNDISCH_TAC `(x1:real^2) IN J` THEN EXPAND_TAC "J" THEN SIMP_TAC[IN_ELIM_THM];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `(J:real^2->bool) = C` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      USE_THEN "bd" (MP_TAC o C MATCH_MP (ASSUME `(x1:real^2) IN std_triangle`)) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `C:real^2->bool`]
      MOI_LCU_SRC_ARC) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `g0:real^1->real^2` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `!y:real^N x. y IN k /\ y IN complex_boundary c /\ x IN std_triangle /\
                               f x = y
                               ==> x = pathstart g0 \/ x = pathfinish (g0:real^1->real^2)`
    (LABEL_TAC "ends") THENL
     [REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `(x:real^2) IN C INTER relative_frontier std_triangle` MP_TAC THENL
       [REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
         [UNDISCH_TAC `(J:real^2->bool) = C` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
          EXPAND_TAC "J" THEN ASM_REWRITE_TAC[IN_ELIM_THM];
          USE_THEN "bd" (MP_TAC o C MATCH_MP (ASSUME `(x:real^2) IN std_triangle`)) THEN
          ASM_REWRITE_TAC[]];
        ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y1:real^N) IN moi_lt_double_image f` ASSUME_TAC THENL
     [UNDISCH_TAC `(k:real^N->bool) SUBSET moi_lt_double_image f` THEN
      UNDISCH_TAC `(y1:real^N) IN k` THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(y1:real^N) IN moi_lt_double_image f` THEN
    REWRITE_TAC[moi_lt_double_image; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^2` (X_CHOOSE_THEN `u':real^2` STRIP_ASSUME_TAC)) THEN
    USE_THEN "kJ" (MP_TAC o C MATCH_MP (ASSUME `(y2:real^N) IN k`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `x2:real^2` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(x2:real^2) IN std_triangle` ASSUME_TAC THENL
     [UNDISCH_TAC `(x2:real^2) IN J` THEN EXPAND_TAC "J" THEN SIMP_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    USE_THEN "ends" (MP_TAC o SPECL [`y1:real^N`; `u:real^2`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    USE_THEN "ends" (MP_TAC o SPECL [`y1:real^N`; `u':real^2`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    USE_THEN "ends" (MP_TAC o SPECL [`y2:real^N`; `x2:real^2`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    UNDISCH_TAC `(x2:real^2) = pathstart g0 \/ x2 = pathfinish (g0:real^1->real^2)` THEN
    UNDISCH_TAC `(u':real^2) = pathstart g0 \/ u' = pathfinish (g0:real^1->real^2)` THEN
    UNDISCH_TAC `(u:real^2) = pathstart g0 \/ u = pathfinish (g0:real^1->real^2)` THEN
    UNDISCH_TAC `~(y1:real^N = y2)` THEN UNDISCH_TAC `~(u:real^2 = u')` THEN
    UNDISCH_TAC `(f:real^2->real^N) u = y1` THEN UNDISCH_TAC `(f:real^2->real^N) u' = y1` THEN
    UNDISCH_TAC `(f:real^2->real^N) x2 = y2` THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `k:real^N->bool`]
    MOI_LA1_CLOSED_TWO) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `j1:real^2->bool` (X_CHOOSE_THEN `j2:real^2->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`] MOI_LA1_SOURCE_COMPONENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `DISJOINT (j1:real^2->bool) j2 /\ compact j1 /\ compact j2 /\
                connected j1 /\ connected j2 /\ ~(j1 = {}) /\ ~(j2 = {}) /\
                j1 SUBSET S /\ j2 SUBSET S`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[COMPONENTS_NONOVERLAP];
      ASM_MESON_TAC[COMPACT_COMPONENTS];
      ASM_MESON_TAC[COMPACT_COMPONENTS];
      ASM_MESON_TAC[IN_COMPONENTS_CONNECTED];
      ASM_MESON_TAC[IN_COMPONENTS_CONNECTED];
      ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY];
      ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY];
      ASM_MESON_TAC[IN_COMPONENTS_SUBSET];
      ASM_MESON_TAC[IN_COMPONENTS_SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(S:real^2->bool) SUBSET std_triangle` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN SET_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `k:real^N->bool`;
                `j1:real^2->bool`; `j2:real^2->bool`] MOI_LA1_CASE2_BIJ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `!j:real^2->bool. j SUBSET S /\ IMAGE (f:real^2->real^N) j = k
                                 ==> ~(j INTER relative_frontier std_triangle = {})`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y1:real^N) IN IMAGE f (j:real^2->bool)` MP_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `z:real^2` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(z:real^2) IN std_triangle` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "bd" (MP_TAC o C MATCH_MP (ASSUME `(z:real^2) IN std_triangle`)) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `j1:real^2->bool`]
    MOI_LCU_SRC_ARC) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^1->real^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `j2:real^2->bool`]
    MOI_LCU_SRC_ARC) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q0:real^1->real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `pl_polyhedron (j2:real^2->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `path_image (q0:real^1->real^2)`)) THEN
    REWRITE_TAC[path_image] THEN MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN
    ASM_REWRITE_TAC[pl_polyhedron] THEN
    EXISTS_TAC `{interval[vec 0:real^1,vec 1]}` THEN
    REWRITE_TAC[FINITE_SING; IN_SING; UNIONS_1] THEN MESON_TAC[POLYTOPE_INTERVAL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`j2:real^2->bool`; `f:real^2->real^N`] PL_INJECTIVE_INVERSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_MAP_ON_SUBSET THEN
    EXISTS_TAC `std_triangle` THEN ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:real^N->real^2` ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism; homeomorphism] o
    check (fun th -> is_comb(concl th) &&
      can (find_term (fun t -> t = `r2:real^N->real^2`)) (concl th))) THEN
  SUBGOAL_THEN `!t. t IN interval[vec 0,vec 1] ==> (p:real^1->real^2) t IN j1`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `path_image (p:real^1->real^2)`)) THEN
    REWRITE_TAC[path_image] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^2->real^N) (path_image (p:real^1->real^2)) = k`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `arc ((f:real^2->real^N) o (p:real^1->real^2)) /\
                pl_map_on (interval[vec 0,vec 1]) (f o p) /\
                path_image (f o p) = k`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC ARC_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `std_triangle` THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `path_image (p:real^1->real^2)`)) THEN
      REWRITE_TAC[path_image] THEN DISCH_THEN SUBST1_TAC THEN ASM SET_TAC[];
      ASM_REWRITE_TAC[PATH_IMAGE_COMPOSE]];
    ALL_TAC] THEN
  ABBREV_TAC `q = (r2:real^N->real^2) o (f:real^2->real^N) o (p:real^1->real^2)` THEN
  SUBGOAL_THEN `arc (q:real^1->real^2) /\ pl_map_on (interval[vec 0,vec 1]) q /\
                path_image q = j2 /\
                (!t. t IN interval[vec 0,vec 1] ==> (f:real^2->real^N)(q t) = f(p t))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC ARC_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[];
      MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `k:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `path_image ((f:real^2->real^N) o (p:real^1->real^2))`)) THEN
      REWRITE_TAC[path_image] THEN SIMP_TAC[SUBSET_REFL];
      ASM_REWRITE_TAC[PATH_IMAGE_COMPOSE];
      X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `r2:real^N->real^2`)) (concl th) &&
        can (find_term (fun t -> t = `k:real^N->bool`)) (concl th))) THEN
      UNDISCH_TAC `IMAGE (f:real^2->real^N) j1 = k` THEN
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `t IN interval[vec 0:real^1,vec 1]`) o
        check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> t = `j1:real^2->bool`)) (concl th) &&
          can (find_term (fun t -> t = `p:real^1->real^2`)) (concl th))) THEN
      SET_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `(j2:real^2->bool) INTER relative_frontier std_triangle`)) THEN
  MAP_EVERY EXISTS_TAC [`p:real^1->real^2`; `q:real^1->real^2`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    ASM SET_TAC[];
    ALL_TAC;
    ASM_MESON_TAC[DISJOINT]] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER; IN_INSERT; NOT_IN_EMPTY] THEN
    X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
    SUBGOAL_THEN `?t. t IN interval[vec 0,vec 1] /\ (q:real^1->real^2) t = z`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^2) IN j2` THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `path_image (q:real^1->real^2)`)) THEN
      REWRITE_TAC[path_image; IN_IMAGE] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(p:real^1->real^2) t IN relative_frontier std_triangle` ASSUME_TAC THENL
     [SUBGOAL_THEN `(p:real^1->real^2) t IN std_triangle /\ z IN std_triangle`
      STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      USE_THEN "bd" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th
        (ASSUME `(p:real^1->real^2) t IN std_triangle`))]) THEN
      SUBGOAL_THEN `(f:real^2->real^N)(p(t:real^1)) = f z` SUBST1_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      USE_THEN "bd" (fun th -> REWRITE_TAC[MATCH_MP th
        (ASSUME `(z:real^2) IN std_triangle`)]) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(p:real^1->real^2) t IN j1 INTER relative_frontier std_triangle`
    MP_TAC THENL [ASM_SIMP_TAC[IN_INTER]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    REWRITE_TAC[pathstart; pathfinish] THEN
    SUBGOAL_THEN `!u. u IN interval[vec 0,vec 1] /\ (p:real^1->real^2) t = p u ==> t = u`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      UNDISCH_TAC `arc (p:real^1->real^2)` THEN REWRITE_TAC[arc] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THENL
     [DISJ1_TAC THEN
      SUBGOAL_THEN `t:real^1 = vec 0` (fun th -> ASM_MESON_TAC[th]) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL];
      DISJ2_TAC THEN
      SUBGOAL_THEN `t:real^1 = vec 1` (fun th -> ASM_MESON_TAC[th]) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL]];
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_INTER] THEN
    SUBGOAL_THEN `pathstart (q:real^1->real^2) IN j2 /\ pathfinish q IN j2`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `path_image (q:real^1->real^2)`)) THEN
      REWRITE_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `pathstart (p:real^1->real^2) IN relative_frontier std_triangle /\
                  pathfinish p IN relative_frontier std_triangle`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `pathstart (q:real^1->real^2) IN std_triangle /\
                  pathfinish q IN std_triangle /\
                  pathstart (p:real^1->real^2) IN std_triangle /\
                  pathfinish p IN std_triangle`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(f:real^2->real^N)(pathstart q) = f(pathstart p) /\
                  f(pathfinish q) = f(pathfinish p)` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[pathstart; pathfinish] THEN CONJ_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[ENDS_IN_UNIT_INTERVAL];
      ALL_TAC] THEN
    USE_THEN "bd" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th
      (ASSUME `pathstart (q:real^1->real^2) IN std_triangle`));
      GSYM(MATCH_MP th (ASSUME `pathfinish (q:real^1->real^2) IN std_triangle`))]) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "bd" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `pathstart (p:real^1->real^2) IN std_triangle`);
      MATCH_MP th (ASSUME `pathfinish (p:real^1->real^2) IN std_triangle`)]) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* MODEL: from the source arcs and the 2D model (LT_MODEL_2D of              *)
(* pc_moi_lt_model2d), the PL homeomorphism g of the rectangle onto          *)
(* std_triangle with the relation e.  The 2D model enters as antecedent.    *)
(* ------------------------------------------------------------------------- *)

(* The 2D model statement, proved as LT_MODEL_2D in pc_moi_lt_model2d.ml.    *)
(* It enters here only as an antecedent.                                     *)

let MOI_LCU_MODEL2D =
 `!(p:real^1->real^2) (q:real^1->real^2).
     arc p /\ pl_map_on (interval[vec 0,vec 1]) p /\
     arc q /\ pl_map_on (interval[vec 0,vec 1]) q /\
     path_image p SUBSET std_triangle /\ path_image q SUBSET std_triangle /\
     path_image p INTER relative_frontier std_triangle = {pathstart p,pathfinish p} /\
     path_image q INTER relative_frontier std_triangle = {pathstart q,pathfinish q} /\
     path_image p INTER path_image q = {}
     ==> ?g g' e1 e2.
           pl_homeomorphism (moi_lcus_mr,std_triangle) (g,g') /\
           IMAGE g (relative_frontier moi_lcus_mr) = relative_frontier std_triangle /\
           (!t. &0 <= t /\ t <= &1
                ==> g(vector[&1; t]) = p(lift(if e1 then &1 - t else t)) /\
                    g(vector[&2; t]) = q(lift(if e2 then &1 - t else t))) /\
           homotopic_loops (relative_frontier std_triangle) std_triangle_loop
             (g o (moi_lcus_as ++ moi_lcus_at ++ moi_lcus_au ++ moi_lcus_av))`;;

(* The image of a chord under a map that runs along an arc, possibly        *)
(* reversed.                                                                 *)

let MOI_LCU_CHORD_IMAGE = prove
 (`!(g:real^2->real^2) (p:real^1->real^2) a e.
     (!t. &0 <= t /\ t <= &1 ==> g(vector[a; t]) = p(lift(if e then &1 - t else t)))
     ==> IMAGE g (segment[vector[a; &0],vector[a; &1]]) = path_image p`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SIMP_TAC[MOI_LC0_VSEG; REAL_POS] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; path_image] THEN
  X_GEN_TAC `z:real^2` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(g:real^2->real^2) x = p(lift(if e then &1 - (x:real^2)$2 else x$2))`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `x = vector[a; (x:real^2)$2]:real^2`
       (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
       [ASM_REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2]; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `lift(if e then &1 - (x:real^2)$2 else x$2)` THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
    COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `s:real^1` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `vector[a; if e then &1 - drop s else drop s]:real^2` THEN
    UNDISCH_TAC `s IN interval[vec 0:real^1,vec 1]` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[VECTOR_2] THEN
    SUBGOAL_THEN `&0 <= (if e then &1 - drop s else drop s) /\
                  (if e then &1 - drop s else drop s) <= &1`
    STRIP_ASSUME_TAC THENL [COND_CASES_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP] THEN
    BOOL_CASES_TAC `e:bool` THEN REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* MODEL from the source arcs and the 2D model. *)

let MOI_LCU_MODEL = prove
 (mk_imp(MOI_LCU_MODEL2D,
  `!(c:(real^N->bool)->bool) (f:real^2->real^N) k.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\ moi_lt_normal2_disk c f /\
     k IN components (moi_lt_double_image f) /\ ~(k INTER complex_boundary c = {})
     ==> ?g e. moi_lcus_model c f g e /\
               homotopic_loops (relative_frontier std_triangle) std_triangle_loop
                 (g o (moi_lcus_as ++ moi_lcus_at ++ moi_lcus_au ++ moi_lcus_av))`),
  DISCH_THEN(LABEL_TAC "m2d") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_lt_normal_disk c (f:real^2->real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_lt_normal2_disk]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `k:real^N->bool`]
    MOI_LCU_SOURCE_ARCS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^1->real^2` (X_CHOOSE_THEN `q:real^1->real^2`
    STRIP_ASSUME_TAC)) THEN
  USE_THEN "m2d" (MP_TAC o SPECL [`p:real^1->real^2`; `q:real^1->real^2`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^2->real^2` (X_CHOOSE_THEN `g':real^2->real^2`
    (X_CHOOSE_THEN `e1:bool` (X_CHOOSE_THEN `e2:bool` STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`g:real^2->real^2`; `~(e1 <=> e2)`] THEN
  ASM_REWRITE_TAC[moi_lcus_model] THEN CONJ_TAC THENL
   [EXISTS_TAC `g':real^2->real^2` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [EXISTS_TAC `k:real^N->bool` THEN ASM_REWRITE_TAC[IMAGE_UNION] THEN
    BINOP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_LCU_CHORD_IMAGE THENL
     [EXISTS_TAC `e1:bool`; EXISTS_TAC `e2:bool`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  ABBREV_TAC `v = if ~(e1 <=> e2) then &1 - t else t` THEN
  SUBGOAL_THEN `&0 <= v /\ v <= &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(if e2 then &1 - v else v) = (if e1 then &1 - t else t)` ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN MAP_EVERY BOOL_CASES_TAC [`e1:bool`; `e2:bool`] THEN
    REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM((fun th -> REWRITE_TAC[CONJUNCT1(MP (SPEC `t:real` th)
    (CONJ (ASSUME `&0 <= t`) (ASSUME `t <= &1`)))]) o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `q:real^1->real^2`)) (concl th) &&
      can (find_term (fun t -> t = `g:real^2->real^2`)) (concl th))) THEN
  FIRST_ASSUM((fun th -> REWRITE_TAC[CONJUNCT2(MP (SPEC `v:real` th)
    (CONJ (ASSUME `&0 <= v`) (ASSUME `v <= &1`)))]) o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `q:real^1->real^2`)) (concl th) &&
      can (find_term (fun t -> t = `g:real^2->real^2`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
  COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* D1, the reglued map: psi = id on [0,1] x [0,1] and the shift            *)
(* rho_e on (1,2] x [0,1]; F1 = f o g o psi on [0,2] x [0,1] is PL and      *)
(* locally injective (across the chord a double point would lie near k    *)
(* but off the chords).                                                     *)
(* ------------------------------------------------------------------------- *)

let moi_lcu_rho = new_definition
 `moi_lcu_rho e (x:real^2) = vector[x$1 + &1; if e then &1 - x$2 else x$2]:real^2`;;

let moi_lcu_psi = new_definition
 `moi_lcu_psi e (x:real^2) = if x$1 <= &1 then x else moi_lcu_rho e x`;;

let MOI_LCU_RHO = prove
 (`!e. (!x:real^2. (moi_lcu_rho e x)$1 = x$1 + &1) /\
       (!x:real^2. (moi_lcu_rho e x)$2 = if e then &1 - x$2 else x$2) /\
       (!x y:real^2. moi_lcu_rho e x = moi_lcu_rho e y <=> x = y) /\
       (!s:real^2->bool. locally_polyhedral s ==> pl_map_on s (moi_lcu_rho e)) /\
       moi_lcu_rho e continuous_on (:real^2) /\
       (!a b:real^2. moi_lcu_rho e o linepath(a,b) =
                     linepath(moi_lcu_rho e a,moi_lcu_rho e b))`,
  GEN_TAC THEN
  SUBGOAL_THEN `moi_lcu_rho e =
                (\x:real^2. (\x:real^2. vector[x$1; if e then --(x$2) else x$2]:real^2) x +
                            vector[&1; if e then &1 else &0])`
  ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; moi_lcu_rho; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2;
                VECTOR_ADD_COMPONENT] THEN
    GEN_TAC THEN BOOL_CASES_TAC `e:bool` THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `linear (\x:real^2. vector[x$1; if e then --(x$2) else x$2]:real^2)`
  ASSUME_TAC THENL
   [REWRITE_TAC[linear; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT] THEN
    BOOL_CASES_TAC `e:bool` THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[moi_lcu_rho; VECTOR_2];
    REWRITE_TAC[moi_lcu_rho; VECTOR_2];
    REWRITE_TAC[moi_lcu_rho; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
    REPEAT GEN_TAC THEN BOOL_CASES_TAC `e:bool` THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
    GEN_TAC THEN DISCH_TAC THEN ONCE_ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_MAP_ON_AFFINE THEN ASM_REWRITE_TAC[];
    ONCE_ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_PLM_AFFINE_CONTINUOUS_ON THEN
    MAP_EVERY EXISTS_TAC
     [`\x:real^2. vector[x$1; if e then --(x$2) else x$2]:real^2`;
      `vector[&1; if e then &1 else &0]:real^2`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[FUN_EQ_THM; o_THM; linepath; moi_lcu_rho; CART_EQ; DIMINDEX_2; FORALL_2;
                VECTOR_2; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    REPEAT GEN_TAC THEN BOOL_CASES_TAC `e:bool` THEN REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* The source map psi of the disk R1 + R2: the identity on [0,1] x [0,1], *)
(* and (x,y) |-> (x+1, y or 1-y) on (1,2] x [0,1].                        *)

let MOI_LCU_PSI = prove
 (`!e. (!z:real^2. z IN interval[vector[&0; &0],vector[&2; &1]]
                   ==> moi_lcu_psi e z IN moi_lcus_mr) /\
       (!z z':real^2. z IN interval[vector[&0; &0],vector[&2; &1]] /\
                      z' IN interval[vector[&0; &0],vector[&2; &1]] /\
                      moi_lcu_psi e z = moi_lcu_psi e z' ==> z = z') /\
       (!z:real^2. z IN interval[vector[&0; &0],vector[&2; &1]]
                   ==> (moi_lcu_psi e z IN relative_frontier moi_lcus_mr <=>
                        z IN frontier(interval[vector[&0; &0],vector[&2; &1]]))) /\
       (!m:real^2. m IN moi_lcus_mr /\ (m$1 <= &1 \/ &2 < m$1)
                   ==> ?z. z IN interval[vector[&0; &0],vector[&2; &1]] /\
                           moi_lcu_psi e z = m) /\
       (!z:real^2. z IN interval[vector[&0; &0],vector[&2; &1]]
                   ==> (moi_lcu_psi e z)$1 <= &1 \/ &2 < (moi_lcu_psi e z)$1) /\
       (!z:real^2. z$1 <= &1 ==> moi_lcu_psi e z = z) /\
       (!z:real^2. &1 < z$1 ==> moi_lcu_psi e z = moi_lcu_rho e z)`,
  GEN_TAC THEN
  MP_TAC(SPECL [`&0`; `&2`] MOI_LC0_RECT_FACTS) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  DISCH_THEN(ASSUME_TAC o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[MOI_LM2_MR_ARCS] THEN
  MP_TAC(SPECL [`&0`; `&3`] MOI_LC0_RECT_FACTS) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[last(CONJUNCTS th)] THEN
    ASSUME_TAC(el 5 (CONJUNCTS th))) THEN
  ASM_REWRITE_TAC[GSYM(CONJUNCT1(CONJUNCT2(CONJUNCT2 MOI_LM2_MR_ARCS)))] THEN
  REWRITE_TAC[MOI_LM2_MR_ARCS; IN_INTERVAL; IN_ELIM_THM; DIMINDEX_2; FORALL_2; VECTOR_2;
              moi_lcu_psi; moi_lcu_rho] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[VECTOR_2] THEN ASM_REAL_ARITH_TAC;
    REPEAT GEN_TAC THEN REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2] THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[VECTOR_2] THEN ASM_REAL_ARITH_TAC;
    GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[VECTOR_2] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `m:real^2` THEN STRIP_TAC THENL
     [EXISTS_TAC `m:real^2` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      EXISTS_TAC `vector[(m:real^2)$1 - &1; if e then &1 - m$2 else m$2]:real^2` THEN
      REWRITE_TAC[VECTOR_2; CART_EQ; DIMINDEX_2; FORALL_2] THEN
      REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[VECTOR_2] THEN ASM_REAL_ARITH_TAC];
    GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[VECTOR_2] THEN ASM_REAL_ARITH_TAC;
    SIMP_TAC[];
    SIMP_TAC[REAL_ARITH `&1 < x ==> ~(x <= &1)`]]);;

(* Unpacking the model. *)

let MOI_LCU_MODEL_FACTS = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) g e.
     moi_lt_singular_disk c f /\ moi_lcus_model c f g e
     ==> ?g' k. pl_homeomorphism (moi_lcus_mr,std_triangle) (g,g') /\
                g continuous_on moi_lcus_mr /\ pl_map_on moi_lcus_mr g /\
                IMAGE g moi_lcus_mr = std_triangle /\
                (!x. x IN moi_lcus_mr ==> g x IN std_triangle) /\
                (!x y. x IN moi_lcus_mr /\ y IN moi_lcus_mr /\ g x = g y ==> x = y) /\
                (!y. y IN std_triangle ==> g' y IN moi_lcus_mr /\ g(g' y) = y) /\
                g' continuous_on std_triangle /\
                (!x. x IN moi_lcus_mr
                     ==> (g x IN relative_frontier std_triangle <=>
                          x IN relative_frontier moi_lcus_mr)) /\
                f continuous_on std_triangle /\ pl_map_on std_triangle f /\
                k IN components (moi_lt_double_image f) /\
                ~(k INTER complex_boundary c = {}) /\
                {x | x IN std_triangle /\ f x IN k} =
                IMAGE g (segment[vector[&1; &0],vector[&1; &1]] UNION
                         segment[vector[&2; &0],vector[&2; &1]]) /\
                (!x. x IN moi_lcus_mr ==> (f(g x) IN k <=> x$1 = &1 \/ x$1 = &2)) /\
                (!t. &0 <= t /\ t <= &1
                     ==> f(g(vector[&1; t])) = f(g(moi_lcu_rho e (vector[&1; t]))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lcus_model] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_TAC `g':real^2->real^2`) (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC)
        (LABEL_TAC "rel"))))) THEN
  SUBGOAL_THEN `!t. &0 <= t /\ t <= &1
                    ==> (f:real^2->real^N)(g(vector[&1; t])) =
                        f(g(moi_lcu_rho e (vector[&1; t])))`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "rel" (fun th -> REWRITE_TAC[MP (SPEC `t:real` th)
      (CONJ (ASSUME `&0 <= t`) (ASSUME `t <= &1`))]) THEN
    REPEAT AP_TERM_TAC THEN
    REWRITE_TAC[moi_lcu_rho; VECTOR_2; CART_EQ; DIMINDEX_2; FORALL_2] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "rel" (K ALL_TAC) THEN
  MAP_EVERY EXISTS_TAC [`g':real^2->real^2`; `k:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `pl_homeomorphism (moi_lcus_mr,std_triangle) (g:real^2->real^2,g')` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[pl_homeomorphism; homeomorphism] th)) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `pl_map_on std_triangle (f:real^2->real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_lt_singular_disk]; ALL_TAC] THEN
  ASM_SIMP_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON] THEN
  SUBGOAL_THEN `relative_frontier moi_lcus_mr SUBSET moi_lcus_mr` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_LM2_MR_ARCS] THEN
    SIMP_TAC[frontier; CLOSURE_CLOSED; CLOSED_INTERVAL] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[vector[&1; &0],vector[&1; &1]] UNION
                segment[vector[&2; &0],vector[&2; &1]] =
                {x:real^2 | x IN moi_lcus_mr /\ (x$1 = &1 \/ x$1 = &2)}`
  ASSUME_TAC THENL
   [SIMP_TAC[MOI_LC0_VSEG; REAL_POS] THEN
    REWRITE_TAC[MOI_LM2_MR_ARCS; EXTENSION; IN_UNION; IN_ELIM_THM; IN_INTERVAL;
                DIMINDEX_2; FORALL_2; VECTOR_2] THEN
    GEN_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^2. x IN moi_lcus_mr ==> (g:real^2->real^2) x IN std_triangle`
  ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (g:real^2->real^2) moi_lcus_mr = std_triangle` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `!x:real^2. x IN moi_lcus_mr ==> (g':real^2->real^2)(g x) = x` THEN
    MESON_TAC[];
    UNDISCH_TAC `IMAGE (g':real^2->real^2) std_triangle = moi_lcus_mr` THEN
    UNDISCH_TAC `!y:real^2. y IN std_triangle ==> (g:real^2->real^2)(g' y) = y` THEN
    SET_TAC[];
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) o
      check (fun th -> is_eq(concl th) &&
                       rhs(concl th) = `relative_frontier std_triangle`)) THEN
    REWRITE_TAC[IN_IMAGE] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(x:real^2) = y` (fun th -> ASM_REWRITE_TAC[th]) THEN
      SUBGOAL_THEN `(y:real^2) IN moi_lcus_mr` ASSUME_TAC THENL
       [UNDISCH_TAC `relative_frontier moi_lcus_mr SUBSET moi_lcus_mr` THEN
        UNDISCH_TAC `(y:real^2) IN relative_frontier moi_lcus_mr` THEN SET_TAC[];
        ALL_TAC] THEN
      ASM_MESON_TAC[];
      DISCH_TAC THEN EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(f:real^2->real^N)(g(x:real^2)) IN k <=>
                  g x IN {x | x IN std_triangle /\ f x IN k}` SUBST1_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^2) IN moi_lcus_mr` THEN
    UNDISCH_TAC `!x:real^2. x IN moi_lcus_mr ==> (g':real^2->real^2)(g x) = x` THEN
    SET_TAC[]]);;

(* Local injectivity is preserved by composing with a continuous injection. *)

let MOI_LCU_LOCINJ_COMPOSE = prove
 (`!(f:real^2->real^N) (h:real^2->real^2) s t.
     h continuous_on s /\ IMAGE h s SUBSET t /\
     (!x y. x IN s /\ y IN s /\ h x = h y ==> x = y) /\
     (!y. y IN t ==> ?n. open n /\ y IN n /\
                         !y1 y2. y1 IN n INTER t /\ y2 IN n INTER t /\ f y1 = f y2
                                 ==> y1 = y2)
     ==> !x. x IN s ==> ?m. open m /\ x IN m /\
                            !x1 x2. x1 IN m INTER s /\ x2 IN m INTER s /\
                                    f(h x1) = f(h x2) ==> x1 = x2`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "li")))) THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  USE_THEN "li" (MP_TAC o SPEC `(h:real^2->real^2) x`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:real^2->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`h:real^2->real^2`; `s:real^2->bool`; `n:real^2->bool`]
    CONTINUOUS_OPEN_IN_PREIMAGE) THEN
  ASM_REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real^2->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `m:real^2->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `{x | x IN s /\ (h:real^2->real^2) x IN n} = s INTER m` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x1:real^2`; `x2:real^2`] THEN REWRITE_TAC[IN_INTER] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(h:real^2->real^2) x1 IN n /\ h x2 IN n /\ h x1 IN t /\ h x2 IN t`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `{x | x IN s /\ (h:real^2->real^2) x IN n} = s INTER m` THEN
    UNDISCH_TAC `IMAGE (h:real^2->real^2) s SUBSET t` THEN
    UNDISCH_TAC `(x1:real^2) IN s` THEN UNDISCH_TAC `(x2:real^2) IN s` THEN
    UNDISCH_TAC `(x1:real^2) IN m` THEN UNDISCH_TAC `(x2:real^2) IN m` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^2->real^2) x1 = h x2` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `n:real^2->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
    length(fst(strip_forall(concl th))) = 2 &&
    can (find_term (fun t -> t = `s:real^2->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[]);;

(* A component of the double image of a normal disk is cut out of it by an *)
(* open set.                                                                 *)

let MOI_LCU_COMPONENT_OPEN = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) k.
     moi_lt_normal_disk c f /\ k IN components (moi_lt_double_image f)
     ==> ?u. open u /\ moi_lt_double_image f INTER u = k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`] MOI_LA1_SOURCE_COMPONENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`moi_lt_double_image (f:real^2->real^N)`; `k:real^N->bool`]
    MOI_LA1_COMPONENT_CLOPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[]);;

(* The reglued map F1 = f o g o psi on [0,2] x [0,1] is PL. *)

let MOI_LCU_F1_PL = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) g e.
     moi_lt_singular_disk c f /\ moi_lcus_model c f g e
     ==> pl_map_on (interval[vector[&0; &0],vector[&2; &1]]) (f o g o moi_lcu_psi e)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_LCU_MODEL_FACTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `g':real^2->real^2` (X_CHOOSE_THEN `k:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `pl_map_on moi_lcus_mr ((f:real^2->real^N) o (g:real^2->real^2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `std_triangle` THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_LC0_RECT_PASTE THEN EXISTS_TAC `&1` THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN CONJ_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `(f:real^2->real^N) o (g:real^2->real^2)` THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2; o_THM] THEN
      SIMP_TAC[MOI_LCU_PSI];
      MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `moi_lcus_mr` THEN
      ASM_REWRITE_TAC[MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL] THEN
      REWRITE_TAC[MOI_LM2_MR_ARCS; SUBSET; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
      REAL_ARITH_TAC];
    MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `((f:real^2->real^N) o (g:real^2->real^2)) o moi_lcu_rho e` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2; o_THM] THEN
      X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
      ASM_CASES_TAC `(z:real^2)$1 = &1` THENL
       [SUBGOAL_THEN `z = vector[&1; (z:real^2)$2]:real^2` SUBST1_TAC THENL
         [ASM_REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2]; ALL_TAC] THEN
        SIMP_TAC[MOI_LCU_PSI; VECTOR_2; REAL_LE_REFL] THEN
        CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        SUBGOAL_THEN `&1 < (z:real^2)$1` ASSUME_TAC THENL
         [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[MOI_LCU_PSI]]];
      MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `moi_lcus_mr` THEN
      ASM_REWRITE_TAC[] THEN
      SIMP_TAC[MOI_LCU_RHO; MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL] THEN
      REWRITE_TAC[MOI_LM2_MR_ARCS; SUBSET; FORALL_IN_IMAGE; IN_INTERVAL; DIMINDEX_2;
                  FORALL_2; VECTOR_2; MOI_LCU_RHO] THEN
      GEN_TAC THEN COND_CASES_TAC THEN REAL_ARITH_TAC]]);;

(* The two descriptions of F1 near the chord x = 1. *)

let MOI_LCU_F1_SIDES = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) g e.
     moi_lt_singular_disk c f /\ moi_lcus_model c f g e
     ==> (!z. z IN interval[vector[&0; &0],vector[&2; &1]] /\ z$1 <= &1
              ==> (f o g o moi_lcu_psi e) z = f(g z)) /\
         (!z. z IN interval[vector[&0; &0],vector[&2; &1]] /\ &1 <= z$1
              ==> (f o g o moi_lcu_psi e) z = f(g(moi_lcu_rho e z)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_LCU_MODEL_FACTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `g':real^2->real^2` (X_CHOOSE_THEN `k:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2; o_THM] THEN
  CONJ_TAC THENL [SIMP_TAC[MOI_LCU_PSI]; ALL_TAC] THEN
  X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
  ASM_CASES_TAC `(z:real^2)$1 = &1` THENL
   [SUBGOAL_THEN `z = vector[&1; (z:real^2)$2]:real^2` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2]; ALL_TAC] THEN
    SIMP_TAC[MOI_LCU_PSI; VECTOR_2; REAL_LE_REFL] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `&1 < (z:real^2)$1` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[MOI_LCU_PSI]]]);;

(* F1 is locally injective on [0,2] x [0,1]: across the chord, two points  *)
(* with the same image would give a double point near k off the chords.   *)

let MOI_LCU_F1_LOCINJ = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) g e.
     moi_lt_normal_disk c f /\ moi_lcus_model c f g e
     ==> !z. z IN interval[vector[&0; &0],vector[&2; &1]]
             ==> ?n. open n /\ z IN n /\
                     !z1 z2. z1 IN n INTER interval[vector[&0; &0],vector[&2; &1]] /\
                             z2 IN n INTER interval[vector[&0; &0],vector[&2; &1]] /\
                             (f o g o moi_lcu_psi e) z1 = (f o g o moi_lcu_psi e) z2
                             ==> z1 = z2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_lt_singular_disk c (f:real^2->real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_lt_normal_disk]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`; `e:bool`]
    MOI_LCU_F1_SIDES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "H1") (LABEL_TAC "H2")) THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`; `e:bool`]
    MOI_LCU_MODEL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g':real^2->real^2` (X_CHOOSE_THEN `k:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `!y. y IN std_triangle
        ==> ?n. open n /\ y IN n /\
                !y1 y2. y1 IN n INTER std_triangle /\ y2 IN n INTER std_triangle /\
                        (f:real^2->real^N) y1 = f y2 ==> y1 = y2`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_lt_singular_disk c (f:real^2->real^N)` THEN
    REWRITE_TAC[moi_lt_singular_disk] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^2->real^N`; `g:real^2->real^2`; `moi_lcus_mr`; `std_triangle`]
    MOI_LCU_LOCINJ_COMPOSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_REFL]; DISCH_THEN(LABEL_TAC "LL")] THEN
  MP_TAC(ISPECL [`f:real^2->real^N`; `(g:real^2->real^2) o moi_lcu_rho e`;
                 `interval[vector[&1; &0]:real^2,vector[&2; &1]]`; `std_triangle`]
    MOI_LCU_LOCINJ_COMPOSE) THEN
  SUBGOAL_THEN `!z:real^2. z IN interval[vector[&1; &0],vector[&2; &1]]
                           ==> moi_lcu_rho e z IN moi_lcus_mr`
  ASSUME_TAC THENL
   [REWRITE_TAC[MOI_LM2_MR_ARCS; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2;
                MOI_LCU_RHO] THEN
    GEN_TAC THEN COND_CASES_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
        REWRITE_TAC[MOI_LCU_RHO; SUBSET_UNIV];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_lcus_mr` THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN ASM_MESON_TAC[];
      REWRITE_TAC[o_THM] THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `moi_lcu_rho e x = moi_lcu_rho e (y:real^2)` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          length(fst(strip_forall(concl th))) = 2 &&
          can (find_term (fun t -> t = `moi_lcus_mr`)) (concl th))) THEN
        ASM_SIMP_TAC[];
        REWRITE_TAC[MOI_LCU_RHO]];
      ASM_REWRITE_TAC[]];
    DISCH_THEN(LABEL_TAC "RR")] THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `k:real^N->bool`]
    MOI_LCU_COMPONENT_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `interval[vector[&0; &0],vector[&2; &1]] SUBSET moi_lcus_mr`
  ASSUME_TAC THENL
   [REWRITE_TAC[MOI_LM2_MR_ARCS; SUBSET; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `((f:real^2->real^N) o (g:real^2->real^2) o moi_lcu_psi e) continuous_on
                interval[vector[&0; &0],vector[&2; &1]]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN MATCH_MP_TAC MOI_LCU_F1_PL THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(f:real^2->real^N) o (g:real^2->real^2) o moi_lcu_psi e`;
                 `interval[vector[&0; &0]:real^2,vector[&2; &1]]`; `u:real^N->bool`]
    CONTINUOUS_OPEN_IN_PREIMAGE) THEN
  ASM_REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `mu:real^2->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!a b. a IN interval[vector[&0; &0],vector[&2; &1]] /\
          b IN interval[vector[&0; &0],vector[&2; &1]] /\
          a$1 < &1 /\ &1 < b$1 /\ a IN mu /\
          ((f:real^2->real^N) o (g:real^2->real^2) o moi_lcu_psi e) a =
          (f o g o moi_lcu_psi e) b
          ==> F`
  (LABEL_TAC "KC") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `(a:real^2) IN moi_lcus_mr /\ moi_lcu_rho e (b:real^2) IN moi_lcus_mr`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC(ASSUME `interval[vector[&0; &0],vector[&2; &1]] SUBSET moi_lcus_mr`) THEN
        MP_TAC(ASSUME `(a:real^2) IN interval[vector[&0; &0],vector[&2; &1]]`) THEN
        SET_TAC[];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `moi_lcu_rho e`)) (concl th) &&
        can (find_term (fun t -> t = `moi_lcus_mr`)) (concl th) &&
        not (can (find_term (fun t -> t = `g:real^2->real^2`)) (concl th)))) THEN
      UNDISCH_TAC `(b:real^2) IN interval[vector[&0; &0],vector[&2; &1]]` THEN
      UNDISCH_TAC `&1 < (b:real^2)$1` THEN
      REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(f:real^2->real^N)((g:real^2->real^2) a) IN k` MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        rhs(concl th) = `k:real^N->bool`)) THEN
      REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
       [REWRITE_TAC[moi_lt_double_image; IN_ELIM_THM] THEN
        MAP_EVERY EXISTS_TAC [`(g:real^2->real^2) a`; `(g:real^2->real^2)(moi_lcu_rho e b)`] THEN
        ASM_SIMP_TAC[] THEN CONJ_TAC THENL
         [DISCH_TAC THEN
          SUBGOAL_THEN `(a:real^2) = moi_lcu_rho e b` MP_TAC THENL
           [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
              length(fst(strip_forall(concl th))) = 2 &&
              can (find_term (fun t -> t = `moi_lcus_mr`)) (concl th))) THEN
            ASM_REWRITE_TAC[];
            DISCH_THEN(MP_TAC o AP_TERM `\x:real^2. x$1`) THEN
            REWRITE_TAC[MOI_LCU_RHO] THEN ASM_REAL_ARITH_TAC];
          USE_THEN "H1" (MP_TAC o SPEC `a:real^2`) THEN
          USE_THEN "H2" (MP_TAC o SPEC `b:real^2`) THEN
          ASM_SIMP_TAC[REAL_LT_IMP_LE]];
        UNDISCH_TAC `{x | x IN interval[vector[&0; &0],vector[&2; &1]] /\
                         ((f:real^2->real^N) o (g:real^2->real^2) o moi_lcu_psi e) x IN u} =
                     interval[vector[&0; &0],vector[&2; &1]] INTER mu` THEN
        REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN
        DISCH_THEN(MP_TAC o SPEC `a:real^2`) THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "H1" (MP_TAC o SPEC `a:real^2`) THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE]];
      ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:real^2) IN moi_lcus_mr` ASSUME_TAC THENL
   [MP_TAC(ASSUME `interval[vector[&0; &0],vector[&2; &1]] SUBSET moi_lcus_mr`) THEN
    MP_TAC(ASSUME `(z:real^2) IN interval[vector[&0; &0],vector[&2; &1]]`) THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(z:real^2)$1 < &1` THENL
   [USE_THEN "LL" (MP_TAC o C MATCH_MP (ASSUME `(z:real^2) IN moi_lcus_mr`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `m:real^2->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `m INTER {x:real^2 | x$1 < &1}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT];
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM]; ALL_TAC] THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`z1:real^2`; `z2:real^2`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z1:real^2) IN moi_lcus_mr /\ (z2:real^2) IN moi_lcus_mr`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `interval[vector[&0; &0],vector[&2; &1]] SUBSET moi_lcus_mr` THEN
      UNDISCH_TAC `(z1:real^2) IN interval[vector[&0; &0],vector[&2; &1]]` THEN
      UNDISCH_TAC `(z2:real^2) IN interval[vector[&0; &0],vector[&2; &1]]` THEN
      SET_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER] THEN
    USE_THEN "H1" (MP_TAC o SPEC `z1:real^2`) THEN
    USE_THEN "H1" (MP_TAC o SPEC `z2:real^2`) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; o_THM];
    ALL_TAC] THEN
  ASM_CASES_TAC `&1 < (z:real^2)$1` THENL
   [SUBGOAL_THEN `(z:real^2) IN interval[vector[&1; &0],vector[&2; &1]]` ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^2) IN interval[vector[&0; &0],vector[&2; &1]]` THEN
      UNDISCH_TAC `&1 < (z:real^2)$1` THEN
      REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "RR" (MP_TAC o C MATCH_MP
      (ASSUME `(z:real^2) IN interval[vector[&1; &0],vector[&2; &1]]`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `m:real^2->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `m INTER {x:real^2 | x$1 > &1}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT];
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; real_gt]; ALL_TAC] THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM; real_gt] THEN
    MAP_EVERY X_GEN_TAC [`z1:real^2`; `z2:real^2`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z1:real^2) IN interval[vector[&1; &0],vector[&2; &1]] /\
                  (z2:real^2) IN interval[vector[&1; &0],vector[&2; &1]]`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(z1:real^2) IN interval[vector[&0; &0],vector[&2; &1]]` THEN
      UNDISCH_TAC `(z2:real^2) IN interval[vector[&0; &0],vector[&2; &1]]` THEN
      UNDISCH_TAC `&1 < (z1:real^2)$1` THEN UNDISCH_TAC `&1 < (z2:real^2)$1` THEN
      REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER; o_THM] THEN
    USE_THEN "H2" (MP_TAC o SPEC `z1:real^2`) THEN
    USE_THEN "H2" (MP_TAC o SPEC `z2:real^2`) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^2)$1 = &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^2) IN interval[vector[&1; &0],vector[&2; &1]]` ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^2) IN interval[vector[&0; &0],vector[&2; &1]]` THEN
    UNDISCH_TAC `(z:real^2)$1 = &1` THEN
    REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "LL" (MP_TAC o C MATCH_MP (ASSUME `(z:real^2) IN moi_lcus_mr`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `mL:real^2->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "mL")))) THEN
  USE_THEN "RR" (MP_TAC o C MATCH_MP
      (ASSUME `(z:real^2) IN interval[vector[&1; &0],vector[&2; &1]]`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `mR:real^2->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "mR")))) THEN
  SUBGOAL_THEN `((f:real^2->real^N) o (g:real^2->real^2) o moi_lcu_psi e) z IN u`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `((f:real^2->real^N) o (g:real^2->real^2) o moi_lcu_psi e) z = f(g z)`
    SUBST1_TAC THENL
     [USE_THEN "H1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    SUBGOAL_THEN `(f:real^2->real^N)((g:real^2->real^2) z) IN k` MP_TAC THENL
     [UNDISCH_TAC `!x:real^2. x IN moi_lcus_mr
                              ==> ((f:real^2->real^N)(g x) IN k <=> x$1 = &1 \/ x$1 = &2)` THEN
      DISCH_THEN(MP_TAC o SPEC `z:real^2`) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `moi_lt_double_image (f:real^2->real^N) INTER u = k` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^2) IN mu` ASSUME_TAC THENL
   [UNDISCH_TAC `{x | x IN interval[vector[&0; &0],vector[&2; &1]] /\
                     ((f:real^2->real^N) o (g:real^2->real^2) o moi_lcu_psi e) x IN u} =
                 interval[vector[&0; &0],vector[&2; &1]] INTER mu` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^2`) THEN
    UNDISCH_TAC `((f:real^2->real^N) o (g:real^2->real^2) o moi_lcu_psi e) z IN u` THEN
    UNDISCH_TAC `(z:real^2) IN interval[vector[&0; &0],vector[&2; &1]]` THEN
    MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `mL INTER mR INTER (mu:real^2->bool)` THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`z1:real^2`; `z2:real^2`] THEN REWRITE_TAC[IN_INTER] THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `(z1:real^2)$1 <= &1 /\ (z2:real^2)$1 <= &1` THENL
   [USE_THEN "mL" MATCH_MP_TAC THEN
    SUBGOAL_THEN `(z1:real^2) IN moi_lcus_mr /\ (z2:real^2) IN moi_lcus_mr`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `interval[vector[&0; &0],vector[&2; &1]] SUBSET moi_lcus_mr` THEN
      UNDISCH_TAC `(z1:real^2) IN interval[vector[&0; &0],vector[&2; &1]]` THEN
      UNDISCH_TAC `(z2:real^2) IN interval[vector[&0; &0],vector[&2; &1]]` THEN
      SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_INTER] THEN
    SUBGOAL_THEN
     `((f:real^2->real^N) o (g:real^2->real^2) o moi_lcu_psi e) z1 = f(g z1) /\
      ((f:real^2->real^N) o (g:real^2->real^2) o moi_lcu_psi e) z2 = f(g z2)`
    MP_TAC THENL
     [CONJ_TAC THEN USE_THEN "H1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `((f:real^2->real^N) o (g:real^2->real^2) o moi_lcu_psi e) z1 =
                   (f o g o moi_lcu_psi e) z2` THEN
      MESON_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `&1 <= (z1:real^2)$1 /\ &1 <= (z2:real^2)$1` THENL
   [SUBGOAL_THEN `(z1:real^2) IN interval[vector[&1; &0],vector[&2; &1]] /\
                  (z2:real^2) IN interval[vector[&1; &0],vector[&2; &1]]`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(z1:real^2) IN interval[vector[&0; &0],vector[&2; &1]]` THEN
      UNDISCH_TAC `(z2:real^2) IN interval[vector[&0; &0],vector[&2; &1]]` THEN
      UNDISCH_TAC `&1 <= (z1:real^2)$1 /\ &1 <= (z2:real^2)$1` THEN
      REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "mR" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER; o_THM] THEN
    SUBGOAL_THEN
     `((f:real^2->real^N) o (g:real^2->real^2) o moi_lcu_psi e) z1 = f(g(moi_lcu_rho e z1)) /\
      ((f:real^2->real^N) o (g:real^2->real^2) o moi_lcu_psi e) z2 = f(g(moi_lcu_rho e z2))`
    MP_TAC THENL
     [CONJ_TAC THEN USE_THEN "H2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `((f:real^2->real^N) o (g:real^2->real^2) o moi_lcu_psi e) z1 =
                   (f o g o moi_lcu_psi e) z2` THEN
      MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN
  ASM_CASES_TAC `(z1:real^2)$1 < &1` THENL
   [USE_THEN "KC" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`z1:real^2`; `z2:real^2`] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((z1:real^2)$1 <= &1 /\ (z2:real^2)$1 <= &1)` THEN
    UNDISCH_TAC `(z1:real^2)$1 < &1` THEN REAL_ARITH_TAC;
    USE_THEN "KC" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`z2:real^2`; `z1:real^2`] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((z1:real^2)$1 <= &1 /\ (z2:real^2)$1 <= &1)` THEN
    UNDISCH_TAC `~(&1 <= (z1:real^2)$1 /\ &1 <= (z2:real^2)$1)` THEN
    UNDISCH_TAC `~((z1:real^2)$1 < &1)` THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* D1: the boundary, the fibres and the double points of F1.  Its          *)
(* double points are those of f with no preimage in the middle part        *)
(* g([1,2] x [0,1]).                                                        *)
(* ------------------------------------------------------------------------- *)

(* F1 meets the boundary of c exactly on the frontier of [0,2] x [0,1], *)
(* and its fibres have at most two points.                               *)

let MOI_LCU_F1_BD = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) g e.
     moi_lt_singular_disk c f /\ moi_lcus_model c f g e
     ==> !z. z IN interval[vector[&0; &0],vector[&2; &1]]
             ==> ((f o g o moi_lcu_psi e) z IN complex_boundary c <=>
                  z IN frontier(interval[vector[&0; &0],vector[&2; &1]]))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`; `e:bool`]
    MOI_LCU_MODEL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g':real^2->real^2` (X_CHOOSE_THEN `k:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
  MP_TAC(SPEC `e:bool` MOI_LCU_PSI) THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `z:real^2` (CONJUNCT1 th)) THEN
                       MP_TAC(SPEC `z:real^2` (CONJUNCT1(CONJUNCT2(CONJUNCT2 th))))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_TAC THEN
  REWRITE_TAC[o_THM] THEN
  FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC RAND_CONV [SYM(MATCH_MP th
    (ASSUME `moi_lcu_psi e (z:real^2) IN moi_lcus_mr`))]) o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `relative_frontier std_triangle`)) (concl th))) THEN
  UNDISCH_TAC `moi_lt_singular_disk c (f:real^2->real^N)` THEN
  REWRITE_TAC[moi_lt_singular_disk] THEN
  DISCH_THEN(MP_TAC o el 2 o CONJUNCTS) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `(g:real^2->real^2)(moi_lcu_psi e z)`) THEN
  ASM_SIMP_TAC[]);;

let MOI_LCU_F1_FIBRE = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) g e.
     moi_lt_singular_disk c f /\ moi_lcus_model c f g e
     ==> !y. FINITE {z | z IN interval[vector[&0; &0],vector[&2; &1]] /\
                         (f o g o moi_lcu_psi e) z = y} /\
             CARD {z | z IN interval[vector[&0; &0],vector[&2; &1]] /\
                       (f o g o moi_lcu_psi e) z = y} <= 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`; `e:bool`]
    MOI_LCU_MODEL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g':real^2->real^2` (X_CHOOSE_THEN `k:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  X_GEN_TAC `y:real^N` THEN
  ABBREV_TAC `S = {z | z IN interval[vector[&0; &0],vector[&2; &1]] /\
                       ((f:real^2->real^N) o (g:real^2->real^2) o moi_lcu_psi e) z = y}` THEN
  SUBGOAL_THEN `!z z':real^2. z IN S /\ z' IN S /\
                  (g:real^2->real^2)(moi_lcu_psi e z) = g(moi_lcu_psi e z') ==> z = z'`
  ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MP_TAC(SPEC `e:bool` MOI_LCU_PSI) THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 2 &&
      can (find_term (fun t -> t = `moi_lcu_psi e`)) (concl th) &&
      not (can (find_term (fun t -> t = `relative_frontier moi_lcus_mr`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 2 &&
      can (find_term (fun t -> t = `g:real^2->real^2`)) (concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (\z. (g:real^2->real^2)(moi_lcu_psi e z)) S SUBSET
                {x | x IN std_triangle /\ (f:real^2->real^N) x = y}`
  ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; o_THM] THEN
    MP_TAC(SPEC `e:bool` MOI_LCU_PSI) THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {x | x IN std_triangle /\ (f:real^2->real^N) x = y} /\
                CARD {x | x IN std_triangle /\ (f:real^2->real^N) x = y} <= 2`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_lt_singular_disk c (f:real^2->real^N)` THEN
    REWRITE_TAC[moi_lt_singular_disk] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (IMAGE (\z. (g:real^2->real^2)(moi_lcu_psi e z)) S)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (S:real^2->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\z. (g:real^2->real^2)(moi_lcu_psi e z)`; `S:real^2->bool`]
      FINITE_IMAGE_INJ_EQ) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\z. (g:real^2->real^2)(moi_lcu_psi e z)`; `S:real^2->bool`]
    CARD_IMAGE_INJ) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD {x | x IN std_triangle /\ (f:real^2->real^N) x = y}` THEN
  ASM_SIMP_TAC[CARD_SUBSET]);;

(* Two points of [0,2] x [0,1] with the same F1 image never lie on the    *)
(* chord: a point of k has exactly its two preimages on the two chords.  *)

let MOI_LCU_F1_CHORD = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) g e.
     moi_lt_singular_disk c f /\ moi_lcus_model c f g e
     ==> !z z'. z IN interval[vector[&0; &0],vector[&2; &1]] /\
                z' IN interval[vector[&0; &0],vector[&2; &1]] /\ ~(z = z') /\
                (f o g o moi_lcu_psi e) z = (f o g o moi_lcu_psi e) z'
                ==> ~((moi_lcu_psi e z)$1 = &1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`; `e:bool`]
    MOI_LCU_MODEL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g':real^2->real^2` (X_CHOOSE_THEN `k:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPEC `e:bool` MOI_LCU_PSI) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "Pin") (CONJUNCTS_THEN2 (LABEL_TAC "Pinj")
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
      (CONJUNCTS_THEN2 (LABEL_TAC "Pcoord") (CONJUNCTS_THEN2 (LABEL_TAC "Pid")
        (LABEL_TAC "Prho"))))))) THEN
  MAP_EVERY X_GEN_TAC [`z:real^2`; `z':real^2`] THEN STRIP_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:real^2)$1 <= &1` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `~(&1 < x) ==> x <= &1`) THEN DISCH_TAC THEN
    UNDISCH_TAC `(moi_lcu_psi e z)$1 = &1` THEN
    USE_THEN "Prho" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `&1 < (z:real^2)$1`)]) THEN
    REWRITE_TAC[MOI_LCU_RHO] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_lcu_psi e z = z:real^2` ASSUME_TAC THENL
   [USE_THEN "Pid" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^2)$1 = &1` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^2) IN moi_lcus_mr /\ moi_lcu_psi e (z':real^2) IN moi_lcus_mr`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[];
      USE_THEN "Pin" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (z:real^2)$2 /\ (z:real^2)$2 <= &1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^2) IN interval[vector[&0; &0],vector[&2; &1]]` THEN
    REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^2->real^N)((g:real^2->real^2) z) = f(g(moi_lcu_rho e z))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `z = vector[&1; (z:real^2)$2]:real^2` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2]; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `moi_lcu_rho e`)) (concl th) &&
      can (find_term (fun t -> t = `f:real^2->real^N`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_lcu_rho e (z:real^2) IN moi_lcus_mr /\
                ~(moi_lcu_rho e z = z)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOI_LM2_MR_ARCS; IN_INTERVAL; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2;
                MOI_LCU_RHO] THEN
    COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^2->real^2) z IN std_triangle /\
                (g:real^2->real^2)(moi_lcu_rho e z) IN std_triangle /\
                (g:real^2->real^2)(moi_lcu_psi e z') IN std_triangle`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      concl th = `!x:real^2. x IN moi_lcus_mr ==> (g:real^2->real^2) x IN std_triangle`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^2->real^N)((g:real^2->real^2) z) IN moi_lt_double_image f`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_lt_double_image; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`(g:real^2->real^2) z`; `(g:real^2->real^2)(moi_lcu_rho e z)`] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(moi_lcu_rho e z = z:real^2)` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 2 &&
      can (find_term (fun t -> t = `moi_lcus_mr`)) (concl th) &&
      can (find_term (fun t -> t = `g:real^2->real^2`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `(g:real^2->real^2) z`]
    MOI_LCC_FIBER_TWO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^2` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fib"))))) THEN
  SUBGOAL_THEN `(g:real^2->real^2)(moi_lcu_rho e z) = v` ASSUME_TAC THENL
   [USE_THEN "fib" (MP_TAC o SPEC `(g:real^2->real^2)(moi_lcu_rho e z)`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `~a ==> a \/ b ==> b`) THEN DISCH_TAC THEN
    UNDISCH_TAC `~(moi_lcu_rho e z = z:real^2)` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 2 &&
      can (find_term (fun t -> t = `moi_lcus_mr`)) (concl th) &&
      can (find_term (fun t -> t = `g:real^2->real^2`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^2->real^2)(moi_lcu_psi e z') = v` ASSUME_TAC THENL
   [USE_THEN "fib" (MP_TAC o SPEC `(g:real^2->real^2)(moi_lcu_psi e z')`) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      UNDISCH_TAC `((f:real^2->real^N) o (g:real^2->real^2) o moi_lcu_psi e) z =
                   (f o g o moi_lcu_psi e) z'` THEN
      REWRITE_TAC[o_THM; ASSUME `moi_lcu_psi e z = z:real^2`] THEN MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `~a ==> a \/ b ==> b`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `moi_lcu_psi e z' = z:real^2` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        length(fst(strip_forall(concl th))) = 2 &&
        can (find_term (fun t -> t = `moi_lcus_mr`)) (concl th) &&
        can (find_term (fun t -> t = `g:real^2->real^2`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `~(z:real^2 = z')` THEN REWRITE_TAC[] THEN
    USE_THEN "Pinj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_lcu_psi e z' = moi_lcu_rho e (z:real^2)` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 2 &&
      can (find_term (fun t -> t = `moi_lcus_mr`)) (concl th) &&
      can (find_term (fun t -> t = `g:real^2->real^2`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `\x:real^2. x$1`) THEN REWRITE_TAC[MOI_LCU_RHO] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  DISCH_TAC THEN
  USE_THEN "Pcoord" (MP_TAC o SPEC `z':real^2`) THEN
  REWRITE_TAC[ASSUME `(z':real^2) IN interval[vector[&0; &0],vector[&2; &1]]`;
              ASSUME `(moi_lcu_psi e z')$1 = &2`] THEN
  REAL_ARITH_TAC);;

(* The double points of F1: the double points of f whose preimages all lie *)
(* outside the middle part g([1,2] x [0,1]).                              *)

(* One inclusion: a double point of F1 is a double point of f with no      *)
(* preimage in the middle part.                                            *)

let MOI_LCU_F1_DOUBLE_SUB = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) g e.
     moi_lt_singular_disk c f /\ moi_lcus_model c f g e
     ==> !y z z'. z IN interval[vector[&0; &0],vector[&2; &1]] /\
                  z' IN interval[vector[&0; &0],vector[&2; &1]] /\ ~(z = z') /\
                  (f o g o moi_lcu_psi e) z = y /\ (f o g o moi_lcu_psi e) z' = y
                  ==> y IN moi_lt_double_image f /\
                      ~(y IN IMAGE f (IMAGE g (interval[vector[&1; &0],vector[&2; &1]])))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`; `e:bool`]
    MOI_LCU_F1_CHORD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "CH") THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`; `e:bool`]
    MOI_LCU_MODEL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g':real^2->real^2` (X_CHOOSE_THEN `k:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPEC `e:bool` MOI_LCU_PSI) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "Pin") (CONJUNCTS_THEN2 (LABEL_TAC "Pinj")
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "Ponto")
      (CONJUNCTS_THEN2 (LABEL_TAC "Pcoord") (K ALL_TAC)))))) THEN
  SUBGOAL_THEN `interval[vector[&1; &0],vector[&2; &1]] SUBSET moi_lcus_mr`
  ASSUME_TAC THENL
   [REWRITE_TAC[MOI_LM2_MR_ARCS; SUBSET; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`y:real^N`; `z:real^2`; `z':real^2`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_lcu_psi e (z:real^2) IN moi_lcus_mr /\
                moi_lcu_psi e (z':real^2) IN moi_lcus_mr`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "Pin" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~((g:real^2->real^2)(moi_lcu_psi e z) = g(moi_lcu_psi e z'))`
  ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(z:real^2 = z')` THEN REWRITE_TAC[] THEN
    USE_THEN "Pinj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 2 &&
      can (find_term (fun t -> t = `moi_lcus_mr`)) (concl th) &&
      can (find_term (fun t -> t = `g:real^2->real^2`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^2->real^2)(moi_lcu_psi e z) IN std_triangle /\
                (g:real^2->real^2)(moi_lcu_psi e z') IN std_triangle`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      concl th = `!x:real^2. x IN moi_lcus_mr ==> (g:real^2->real^2) x IN std_triangle`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN moi_lt_double_image f` ASSUME_TAC THENL
   [REWRITE_TAC[moi_lt_double_image; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`(g:real^2->real^2)(moi_lcu_psi e z)`;
                          `(g:real^2->real^2)(moi_lcu_psi e z')`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `((f:real^2->real^N) o (g:real^2->real^2) o moi_lcu_psi e) z = y` THEN
    UNDISCH_TAC `((f:real^2->real^N) o (g:real^2->real^2) o moi_lcu_psi e) z' = y` THEN
    REWRITE_TAC[o_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^2` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `m:real^2` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `(m:real^2) IN moi_lcus_mr` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`;
                `(g:real^2->real^2)(moi_lcu_psi e z)`] MOI_LCC_FIBER_TWO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `((f:real^2->real^N) o (g:real^2->real^2) o moi_lcu_psi e) z = y` THEN
    REWRITE_TAC[o_THM] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^2` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fib"))))) THEN
  SUBGOAL_THEN `(g:real^2->real^2) m = g(moi_lcu_psi e z) \/
                (g:real^2->real^2) m = g(moi_lcu_psi e z')`
  MP_TAC THENL
   [SUBGOAL_THEN `(g:real^2->real^2) m IN std_triangle /\
                  (f:real^2->real^N)(g m) = f(g(moi_lcu_psi e z)) /\
                  (f:real^2->real^N)(g(moi_lcu_psi e z')) = f(g(moi_lcu_psi e z))`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          concl th = `!x:real^2. x IN moi_lcus_mr ==> (g:real^2->real^2) x IN std_triangle`)) THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `((f:real^2->real^N) o (g:real^2->real^2) o moi_lcu_psi e) z = y` THEN
        REWRITE_TAC[o_THM] THEN DISCH_THEN SUBST1_TAC THEN
        UNDISCH_TAC `(y:real^N) = f(x:real^2)` THEN
        UNDISCH_TAC `(x:real^2) = g(m:real^2)` THEN
        DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC;
        UNDISCH_TAC `((f:real^2->real^N) o (g:real^2->real^2) o moi_lcu_psi e) z = y` THEN
        UNDISCH_TAC `((f:real^2->real^N) o (g:real^2->real^2) o moi_lcu_psi e) z' = y` THEN
        REWRITE_TAC[o_THM] THEN MESON_TAC[]];
      ALL_TAC] THEN
    USE_THEN "fib" (fun th ->
      MP_TAC(MP (SPEC `(g:real^2->real^2) m` th)
        (CONJ (ASSUME `(g:real^2->real^2) m IN std_triangle`)
              (ASSUME `(f:real^2->real^N)((g:real^2->real^2) m) =
                       f(g(moi_lcu_psi e z))`))) THEN
      MP_TAC(MP (SPEC `(g:real^2->real^2)(moi_lcu_psi e z')` th)
        (CONJ (ASSUME `(g:real^2->real^2)(moi_lcu_psi e z') IN std_triangle`)
              (ASSUME `(f:real^2->real^N)((g:real^2->real^2)(moi_lcu_psi e z')) =
                       f(g(moi_lcu_psi e z))`)))) THEN
    UNDISCH_TAC `~((g:real^2->real^2)(moi_lcu_psi e z) = g(moi_lcu_psi e z'))` THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^2. w IN moi_lcus_mr /\ (g:real^2->real^2) m = g w ==> m = w`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 2 &&
      can (find_term (fun t -> t = `moi_lcus_mr`)) (concl th) &&
      can (find_term (fun t -> t = `g:real^2->real^2`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= (m:real^2)$1 /\ (m:real^2)$1 <= &2` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(m:real^2) IN interval[vector[&1; &0],vector[&2; &1]]` THEN
    REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THENL
   [SUBGOAL_THEN `m = moi_lcu_psi e (z:real^2)` SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "CH" (MP_TAC o SPECL [`z:real^2`; `z':real^2`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    USE_THEN "Pcoord" (MP_TAC o C MATCH_MP
      (ASSUME `(z:real^2) IN interval[vector[&0; &0],vector[&2; &1]]`)) THEN
    UNDISCH_TAC `~((moi_lcu_psi e (z:real^2))$1 = &1)` THEN
    UNDISCH_TAC `&1 <= (moi_lcu_psi e (z:real^2))$1` THEN
    UNDISCH_TAC `(moi_lcu_psi e (z:real^2))$1 <= &2` THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `m = moi_lcu_psi e (z':real^2)` SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "CH" (MP_TAC o SPECL [`z':real^2`; `z:real^2`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    USE_THEN "Pcoord" (MP_TAC o C MATCH_MP
      (ASSUME `(z':real^2) IN interval[vector[&0; &0],vector[&2; &1]]`)) THEN
    UNDISCH_TAC `~((moi_lcu_psi e (z':real^2))$1 = &1)` THEN
    UNDISCH_TAC `&1 <= (moi_lcu_psi e (z':real^2))$1` THEN
    UNDISCH_TAC `(moi_lcu_psi e (z':real^2))$1 <= &2` THEN REAL_ARITH_TAC]);;

let MOI_LCU_F1_DOUBLE = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) g e.
     moi_lt_singular_disk c f /\ moi_lcus_model c f g e
     ==> {y | ?z z'. z IN interval[vector[&0; &0],vector[&2; &1]] /\
                     z' IN interval[vector[&0; &0],vector[&2; &1]] /\ ~(z = z') /\
                     (f o g o moi_lcu_psi e) z = y /\ (f o g o moi_lcu_psi e) z' = y} =
         moi_lt_double_image f DIFF
         IMAGE f (IMAGE g (interval[vector[&1; &0],vector[&2; &1]]))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`; `e:bool`]
    MOI_LCU_F1_DOUBLE_SUB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "SUB") THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`; `e:bool`]
    MOI_LCU_MODEL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g':real^2->real^2` (X_CHOOSE_THEN `k:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPEC `e:bool` MOI_LCU_PSI) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "Pin") (CONJUNCTS_THEN2 (LABEL_TAC "Pinj")
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "Ponto")
      (CONJUNCTS_THEN2 (LABEL_TAC "Pcoord") (K ALL_TAC)))))) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF] THEN X_GEN_TAC `y:real^N` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `z:real^2` (X_CHOOSE_THEN `z':real^2` STRIP_ASSUME_TAC)) THEN
    USE_THEN "SUB" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`z:real^2`; `z':real^2`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `(y:real^N) IN moi_lt_double_image f` THEN
  REWRITE_TAC[moi_lt_double_image; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^2` (X_CHOOSE_THEN `x':real^2` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `!w:real^2. w IN std_triangle /\ (f:real^2->real^N) w = y
               ==> ?z. z IN interval[vector[&0; &0],vector[&2; &1]] /\
                       (g:real^2->real^2)(moi_lcu_psi e z) = w`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^2` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(g':real^2->real^2) w IN moi_lcus_mr /\ (g:real^2->real^2)(g' w) = w`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    USE_THEN "Ponto" (MP_TAC o SPEC `(g':real^2->real^2) w`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `~(&1 <= x /\ x <= &2) ==> x <= &1 \/ &2 < x`) THEN
      STRIP_TAC THEN
      UNDISCH_TAC `~((y:real^N) IN IMAGE (f:real^2->real^N)
        (IMAGE (g:real^2->real^2) (interval[vector[&1; &0],vector[&2; &1]])))` THEN
      REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `w:real^2` THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      EXISTS_TAC `(g':real^2->real^2) w` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(g':real^2->real^2) w IN moi_lcus_mr` THEN
      UNDISCH_TAC `&1 <= ((g':real^2->real^2) w)$1` THEN
      UNDISCH_TAC `((g':real^2->real^2) w)$1 <= &2` THEN
      REWRITE_TAC[MOI_LM2_MR_ARCS; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `x:real^2` th) THEN MP_TAC(SPEC `x':real^2` th)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z':real^2` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`z:real^2`; `z':real^2`] THEN
  ASM_REWRITE_TAC[o_THM] THEN DISCH_TAC THEN
  UNDISCH_TAC `~(x:real^2 = x')` THEN REWRITE_TAC[] THEN
  UNDISCH_TAC `(g:real^2->real^2)(moi_lcu_psi e z) = x` THEN
  UNDISCH_TAC `(g:real^2->real^2)(moi_lcu_psi e z') = x'` THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* D1: components of the double image lie over the middle part or          *)
(* miss it; psi is continuous off the chord; reparametrization by a PL     *)
(* homeomorphism from std_triangle.                                         *)
(* ------------------------------------------------------------------------- *)

(* A connected planar set that avoids the lines x = a and x = b and meets *)
(* the band between them lies in the band.                               *)

let MOI_LCU_CONNECTED_BAND = prove
 (`!(D:real^2->bool) a b m.
     connected D /\ m IN D /\ a < m$1 /\ m$1 < b /\
     (!d. d IN D ==> ~(d$1 = a) /\ ~(d$1 = b))
     ==> !d. d IN D ==> a < d$1 /\ d$1 < b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `d:real^2` THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  UNDISCH_TAC `connected (D:real^2->bool)` THEN REWRITE_TAC[connected] THEN
  MAP_EVERY EXISTS_TAC [`{x:real^2 | a < x$1} INTER {x:real^2 | x$1 < b}`;
                        `{x:real^2 | x$1 < a} UNION {x:real^2 | b < x$1}`] THEN
  SIMP_TAC[OPEN_INTER; OPEN_UNION; OPEN_HALFSPACE_COMPONENT_LT;
           REWRITE_RULE[real_gt] OPEN_HALFSPACE_COMPONENT_GT] THEN
  REWRITE_TAC[SUBSET; EXTENSION; IN_INTER; IN_UNION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2` o check (fun th -> is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    X_GEN_TAC `x:real^2` THEN REAL_ARITH_TAC;
    REWRITE_TAC[NOT_FORALL_THM] THEN EXISTS_TAC `m:real^2` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[NOT_FORALL_THM] THEN EXISTS_TAC `d:real^2` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `d:real^2` o check (fun th -> is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(a < (d:real^2)$1 /\ d$1 < b)` THEN REAL_ARITH_TAC]);;

(* Every component of the double image lies in f(g([1,2] x [0,1])) or     *)
(* misses it: a source component off the chords lies in one of the three  *)
(* parts of the model.                                                    *)

let MOI_LCU_DICHOTOMY = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) g e k'.
     moi_lt_normal_disk c f /\ moi_lcus_model c f g e /\
     k' IN components (moi_lt_double_image f)
     ==> k' SUBSET IMAGE f (IMAGE g (interval[vector[&1; &0],vector[&2; &1]])) \/
         DISJOINT k' (IMAGE f (IMAGE g (interval[vector[&1; &0],vector[&2; &1]])))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_lt_singular_disk c (f:real^2->real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_lt_normal_disk]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`; `e:bool`]
    MOI_LCU_MODEL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g':real^2->real^2` (X_CHOOSE_THEN `k:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `MID = IMAGE (f:real^2->real^N)
                      (IMAGE (g:real^2->real^2) (interval[vector[&1; &0],vector[&2; &1]]))` THEN
  SUBGOAL_THEN `interval[vector[&1; &0],vector[&2; &1]] SUBSET moi_lcus_mr`
  ASSUME_TAC THENL
   [REWRITE_TAC[MOI_LM2_MR_ARCS; SUBSET; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^2. x IN std_triangle /\ (f:real^2->real^N) x IN k
                           ==> ?m. m IN moi_lcus_mr /\ (m$1 = &1 \/ m$1 = &2) /\ g m = x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^2) IN {x | x IN std_triangle /\ (f:real^2->real^N) x IN k}`
    MP_TAC THENL [ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
    FIRST_X_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_eq(concl th) &&
      can (find_term (fun t -> t = `segment[vector[&1; &0],vector[&1; &1]]:real^2->bool`))
        (concl th))) THEN
    SIMP_TAC[MOI_LC0_VSEG; REAL_POS] THEN
    REWRITE_TAC[IN_IMAGE; IN_UNION; IN_ELIM_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `m:real^2` THEN
    REWRITE_TAC[MOI_LM2_MR_ARCS; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(k:real^N->bool) SUBSET MID` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN IMAGE f std_triangle` MP_TAC THENL
     [MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`] MOI_LA2_NORMAL_BASIC) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^N` o last o CONJUNCTS) THEN
      SUBGOAL_THEN `(y:real^N) IN moi_lt_double_image f` (fun th -> SIMP_TAC[th]) THEN
      ASM_MESON_TAC[IN_COMPONENTS_SUBSET; SUBSET];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^2` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `k:real^N->bool`)) (concl th) &&
      can (find_term (fun t -> t = `std_triangle`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `m:real^2` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
    EXPAND_TAC "MID" THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `x:real^2` THEN REWRITE_TAC[] THEN EXISTS_TAC `m:real^2` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(m:real^2) IN moi_lcus_mr` THEN
    UNDISCH_TAC `(m:real^2)$1 = &1 \/ m$1 = &2` THEN
    REWRITE_TAC[MOI_LM2_MR_ARCS; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `k':real^N->bool = k` THENL
   [DISJ1_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `DISJOINT (k':real^N->bool) MID` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[DISJOINT] o check (fun th ->
    concl th = `~DISJOINT (k':real^N->bool) MID`)) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `y1:real^N` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(y1:real^N) IN MID` THEN EXPAND_TAC "MID" THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `x1:real^2` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `m1:real^2` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `(k':real^N->bool) INTER k = {}` ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPONENTS_NONOVERLAP]; ALL_TAC] THEN
  SUBGOAL_THEN `(m1:real^2) IN moi_lcus_mr` ASSUME_TAC THENL
   [UNDISCH_TAC `interval[vector[&1; &0],vector[&2; &1]] SUBSET moi_lcus_mr` THEN
    UNDISCH_TAC `(m1:real^2) IN interval[vector[&1; &0],vector[&2; &1]]` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x1:real^2) IN std_triangle` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      concl th = `!x:real^2. x IN moi_lcus_mr ==> (g:real^2->real^2) x IN std_triangle`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 < (m1:real^2)$1 /\ (m1:real^2)$1 < &2` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `~((m1:real^2)$1 = &1) /\ ~((m1:real^2)$1 = &2)` MP_TAC THENL
     [SUBGOAL_THEN `~((f:real^2->real^N)((g:real^2->real^2) m1) IN k)` MP_TAC THENL
       [UNDISCH_TAC `(k':real^N->bool) INTER k = {}` THEN
        UNDISCH_TAC `(y1:real^N) IN k'` THEN
        UNDISCH_TAC `(y1:real^N) = f(x1:real^2)` THEN
        UNDISCH_TAC `(x1:real^2) = g(m1:real^2)` THEN SET_TAC[];
        ASM_SIMP_TAC[DE_MORGAN_THM]];
      UNDISCH_TAC `(m1:real^2) IN interval[vector[&1; &0],vector[&2; &1]]` THEN
      REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `S = {x | x IN std_triangle /\
                       (f:real^2->real^N) x IN moi_lt_double_image f}` THEN
  SUBGOAL_THEN `(x1:real^2) IN S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_MESON_TAC[IN_COMPONENTS_SUBSET; SUBSET];
    ALL_TAC] THEN
  ABBREV_TAC `C = connected_component S (x1:real^2)` THEN
  SUBGOAL_THEN `C IN components (S:real^2->bool) /\ (x1:real^2) IN C /\
                connected C /\ C SUBSET S` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN
    REWRITE_TAC[CONNECTED_CONNECTED_COMPONENT; CONNECTED_COMPONENT_SUBSET] THEN
    CONJ_TAC THENL [REWRITE_TAC[IN_COMPONENTS] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN] THEN ASM_REWRITE_TAC[CONNECTED_COMPONENT_REFL_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^2->real^N) C = k'` ASSUME_TAC THENL
   [MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `C:real^2->bool`]
      MOI_LA1_COMPONENT_IMAGE) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
    MP_TAC(ISPECL [`moi_lt_double_image (f:real^2->real^N)`; `IMAGE (f:real^2->real^N) C`;
                   `k':real^N->bool`] COMPONENTS_NONOVERLAP) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `~a ==> (a <=> ~b) ==> b`) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `y1:real^N` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x1:real^2` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^2. x IN C ==> x IN std_triangle /\ ~((f:real^2->real^N) x IN k)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN CONJ_TAC THENL
     [UNDISCH_TAC `(C:real^2->bool) SUBSET S` THEN EXPAND_TAC "S" THEN
      UNDISCH_TAC `(x:real^2) IN C` THEN SET_TAC[];
      UNDISCH_TAC `(k':real^N->bool) INTER k = {}` THEN
      UNDISCH_TAC `IMAGE (f:real^2->real^N) C = k'` THEN
      UNDISCH_TAC `(x:real^2) IN C` THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (g':real^2->real^2) C`; `&1`; `&2`; `m1:real^2`]
    MOI_LCU_CONNECTED_BAND) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x1:real^2` THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC SYM_CONV THEN
      UNDISCH_TAC `pl_homeomorphism (moi_lcus_mr,std_triangle) (g:real^2->real^2,g')` THEN
      SIMP_TAC[pl_homeomorphism; homeomorphism] THEN ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(x:real^2) IN std_triangle /\ ~((f:real^2->real^N) x IN k)`
      STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(g':real^2->real^2) x IN moi_lcus_mr /\ (g:real^2->real^2)(g' x) = x`
      STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `~((f:real^2->real^N) x IN k)` THEN
      FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(g':real^2->real^2) x IN moi_lcus_mr`) o
        check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun t -> t = `k:real^N->bool`)) (concl th) &&
        can (find_term (fun t -> t = `moi_lcus_mr`)) (concl th) &&
        not (can (find_term (fun t -> t = `std_triangle`)) (concl th)))) THEN
      REWRITE_TAC[ASSUME `(g:real^2->real^2)(g' x) = x`] THEN CONV_TAC TAUT];
    DISCH_TAC] THEN
  EXPAND_TAC "MID" THEN
  FIRST_X_ASSUM((fun th -> REWRITE_TAC[SYM th]) o check (fun th ->
    concl th = `IMAGE (f:real^2->real^N) C = k'`)) THEN
  MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; IN_IMAGE] THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN EXISTS_TAC `(g':real^2->real^2) x` THEN
  SUBGOAL_THEN `(x:real^2) IN std_triangle` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(g':real^2->real^2) x` o check (fun th ->
    is_forall(concl th) && can (find_term (fun t -> t = `&2`)) (concl th))) THEN
  REWRITE_TAC[IN_IMAGE] THEN
  ANTS_TAC THENL [EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(g':real^2->real^2) x IN moi_lcus_mr` MP_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MOI_LM2_MR_ARCS; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
  REAL_ARITH_TAC);;

(* The double arc k itself lies over the middle part. *)

let MOI_LCU_K_MID = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) g e.
     moi_lt_normal_disk c f /\ moi_lcus_model c f g e
     ==> ?k. k IN components (moi_lt_double_image f) /\
             k SUBSET IMAGE f (IMAGE g (interval[vector[&1; &0],vector[&2; &1]]))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_lt_singular_disk c (f:real^2->real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_lt_normal_disk]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`; `e:bool`]
    MOI_LCU_MODEL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g':real^2->real^2` (X_CHOOSE_THEN `k:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `k:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN IMAGE f std_triangle` MP_TAC THENL
   [MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`] MOI_LA2_NORMAL_BASIC) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N` o last o CONJUNCTS) THEN
    SUBGOAL_THEN `(y:real^N) IN moi_lt_double_image f` (fun th -> SIMP_TAC[th]) THEN
    ASM_MESON_TAC[IN_COMPONENTS_SUBSET; SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^2` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `(x:real^2) IN {x | x IN std_triangle /\ (f:real^2->real^N) x IN k}`
  MP_TAC THENL [ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  FIRST_X_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_eq(concl th) &&
    can (find_term (fun t -> t = `segment[vector[&1; &0],vector[&1; &1]]:real^2->bool`))
      (concl th))) THEN
  SIMP_TAC[MOI_LC0_VSEG; REAL_POS] THEN
  REWRITE_TAC[IN_IMAGE; IN_UNION; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real^2` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `x:real^2` THEN REWRITE_TAC[] THEN EXISTS_TAC `m:real^2` THEN
  ASM_REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2] THEN ASM_REAL_ARITH_TAC);;

(* psi is continuous off the chord x = 1. *)

let MOI_LCU_PSI_CONT = prove
 (`!e. moi_lcu_psi e continuous_on {z:real^2 | ~(z$1 = &1)}`,
  GEN_TAC THEN
  SUBGOAL_THEN `{z:real^2 | ~(z$1 = &1)} = {z | z$1 < &1} UNION {z | z$1 > &1}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNION] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_UNION_LOCAL_OPEN THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_OPEN_IN_TRANS THEN
    SIMP_TAC[OPEN_HALFSPACE_COMPONENT_LT; OPEN_HALFSPACE_COMPONENT_GT; OPEN_UNION;
             SUBSET_UNION];
    MATCH_MP_TAC OPEN_OPEN_IN_TRANS THEN
    SIMP_TAC[OPEN_HALFSPACE_COMPONENT_LT; OPEN_HALFSPACE_COMPONENT_GT; OPEN_UNION;
             SUBSET_UNION];
    MATCH_MP_TAC CONTINUOUS_ON_EQ THEN EXISTS_TAC `\z:real^2. z` THEN
    REWRITE_TAC[CONTINUOUS_ON_ID; IN_ELIM_THM] THEN
    SIMP_TAC[MOI_LCU_PSI; REAL_LT_IMP_LE];
    MATCH_MP_TAC CONTINUOUS_ON_EQ THEN EXISTS_TAC `moi_lcu_rho e` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM; real_gt] THEN SIMP_TAC[MOI_LCU_PSI];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      REWRITE_TAC[MOI_LCU_RHO; SUBSET_UNIV]]]);;

(* Reparametrizing a map on a planar disk by a PL homeomorphism from     *)
(* std_triangle: the singular disk conditions and the double image.       *)

let MOI_LCU_REPARAM = prove
 (`!(c:(real^N->bool)->bool) (h:real^2->real^N) (p:real^2->real^2) p' q.
     pl_homeomorphism (std_triangle,q) (p,p') /\
     IMAGE p (relative_frontier std_triangle) = frontier q /\
     pl_map_on q h /\ IMAGE h q SUBSET UNIONS c /\
     (!z. z IN q ==> (h z IN complex_boundary c <=> z IN frontier q)) /\
     (!z. z IN q
          ==> ?n. open n /\ z IN n /\
                  !z1 z2. z1 IN n INTER q /\ z2 IN n INTER q /\ h z1 = h z2 ==> z1 = z2) /\
     (!y. FINITE {z | z IN q /\ h z = y} /\ CARD {z | z IN q /\ h z = y} <= 2)
     ==> moi_lt_singular_disk c (h o p) /\
         moi_lt_double_image (h o p) =
         {y | ?z z'. z IN q /\ z' IN q /\ ~(z = z') /\ h z = y /\ h z' = y}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `pl_homeomorphism (std_triangle,q) (p:real^2->real^2,p')` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[pl_homeomorphism; homeomorphism] th)) THEN
  SUBGOAL_THEN `!x:real^2. x IN std_triangle ==> (p:real^2->real^2) x IN q`
  ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (p:real^2->real^2) std_triangle = q` THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x y:real^2. x IN std_triangle /\ y IN std_triangle /\
                             (p:real^2->real^2) x = p y ==> x = y`
  ASSUME_TAC THENL
   [UNDISCH_TAC `!x:real^2. x IN std_triangle ==> (p':real^2->real^2)(p x) = x` THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier std_triangle SUBSET std_triangle` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_LTD_FRONTIER_SUBSET_TRIANGLE]; ALL_TAC] THEN
  REWRITE_TAC[moi_lt_singular_disk] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `q:real^2->bool` THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; o_THM] THEN X_GEN_TAC `x:real^2` THEN
    ASM_CASES_TAC `(x:real^2) IN std_triangle` THENL
     [ASM_SIMP_TAC[] THEN
      UNDISCH_TAC `IMAGE (p:real^2->real^2) (relative_frontier std_triangle) = frontier q` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE] THEN EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `w:real^2` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `(x:real^2) = w` (fun th -> ASM_REWRITE_TAC[th]) THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          length(fst(strip_forall(concl th))) = 2 &&
          can (find_term (fun t -> t = `p:real^2->real^2`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        DISCH_TAC THEN EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[]];
      ASM SET_TAC[]];
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`h:real^2->real^N`; `p:real^2->real^2`; `std_triangle`; `q:real^2->bool`]
      MOI_LCU_LOCINJ_COMPOSE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[SUBSET_REFL] THEN ASM_MESON_TAC[];
      DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[o_THM]];
    X_GEN_TAC `y:real^N` THEN
    SUBGOAL_THEN `IMAGE (p:real^2->real^2) {x | x IN std_triangle /\
                    ((h:real^2->real^N) o p) x = y} =
                  {z | z IN q /\ (h:real^2->real^N) z = y}`
    (fun th -> SUBST1_TAC(SYM th) THEN ASSUME_TAC th) THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; o_THM] THEN
      X_GEN_TAC `z:real^2` THEN EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC[];
        STRIP_TAC THEN EXISTS_TAC `(p':real^2->real^2) z` THEN ASM_SIMP_TAC[] THEN
        UNDISCH_TAC `IMAGE (p':real^2->real^2) q = std_triangle` THEN
        UNDISCH_TAC `(z:real^2) IN q` THEN SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `!x1 x2:real^2.
                    x1 IN {x | x IN std_triangle /\ ((h:real^2->real^N) o p) x = y} /\
                    x2 IN {x | x IN std_triangle /\ ((h:real^2->real^N) o p) x = y} /\
                    (p:real^2->real^2) x1 = p x2 ==> x1 = x2`
    ASSUME_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        length(fst(strip_forall(concl th))) = 2 &&
        can (find_term (fun t -> t = `std_triangle`)) (concl th) &&
        can (find_term (fun t -> t = `p:real^2->real^2`)) (concl th) &&
        not (can (find_term (fun t -> t = `h:real^2->real^N`)) (concl th)))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`p:real^2->real^2`; `{x | x IN std_triangle /\
                                         ((h:real^2->real^N) o (p:real^2->real^2)) x = y}`]
      FINITE_IMAGE_INJ_EQ) THEN
    MP_TAC(ISPECL [`p:real^2->real^2`; `{x | x IN std_triangle /\
                                         ((h:real^2->real^N) o (p:real^2->real^2)) x = y}`]
      CARD_IMAGE_INJ) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `CARD:(real^2->bool)->num`)) (concl th))) THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[moi_lt_double_image; EXTENSION; IN_ELIM_THM; o_THM] THEN
    X_GEN_TAC `y:real^N` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real^2` (X_CHOOSE_THEN `x':real^2` STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`(p:real^2->real^2) x`; `(p:real^2->real^2) x'`] THEN
      ASM_SIMP_TAC[] THEN ASM_MESON_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `z:real^2` (X_CHOOSE_THEN `z':real^2` STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`(p':real^2->real^2) z`; `(p':real^2->real^2) z'`] THEN
      SUBGOAL_THEN `(p':real^2->real^2) z IN std_triangle /\ p' z' IN std_triangle`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `IMAGE (p':real^2->real^2) q = std_triangle` THEN
        UNDISCH_TAC `(z:real^2) IN q` THEN UNDISCH_TAC `(z':real^2) IN q` THEN SET_TAC[];
        ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN ASM_MESON_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* D1: the rectangle loop, the crossing2 charts and normality of the        *)
(* reglued disk, and its smaller complexity.                                *)
(* ------------------------------------------------------------------------- *)

(* The rectangle [0,2] x [0,1] of D1 and its boundary loop from (1,1)     *)
(* through the left side to (1,0) and back through the right side.       *)

let MOI_LCU_Q_LOOP = prove
 (`polytope (interval[vector[&0; &0],vector[&2; &1]]:real^2->bool) /\
   ~(interior (interval[vector[&0; &0],vector[&2; &1]]:real^2->bool) = {}) /\
   compact (interval[vector[&0; &0],vector[&2; &1]]:real^2->bool) /\
   frontier (interval[vector[&0; &0],vector[&2; &1]]:real^2->bool) SUBSET
   interval[vector[&0; &0],vector[&2; &1]] /\
   simple_path (moi_lc0_larc (&0) (&1) ++ moi_lc0_rarc (&1) (&2)) /\
   pathfinish (moi_lc0_larc (&0) (&1) ++ moi_lc0_rarc (&1) (&2)) =
   pathstart (moi_lc0_larc (&0) (&1) ++ moi_lc0_rarc (&1) (&2)) /\
   path_image (moi_lc0_larc (&0) (&1) ++ moi_lc0_rarc (&1) (&2)) =
   frontier (interval[vector[&0; &0],vector[&2; &1]]) /\
   path_image (moi_lc0_larc (&0) (&1)) SUBSET {x:real^2 | x$1 <= &1} /\
   path_image (moi_lc0_rarc (&1) (&2)) SUBSET {x:real^2 | &1 <= x$1} /\
   pl_map_on (interval[vec 0,vec 1]) (moi_lc0_larc (&0) (&1)) /\
   pl_map_on (interval[vec 0,vec 1]) (moi_lc0_rarc (&1) (&2))`,
  MP_TAC(SPECL [`&0`; `&2`] MOI_LC0_RECT_FACTS) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (butlast (CONJUNCTS th)) THEN
                       LABEL_TAC "fr" (last (CONJUNCTS th))) THEN
  MP_TAC(SPECL [`&0`; `&1`] MOI_LC0_LARC) THEN
  MP_TAC(SPECL [`&1`; `&2`] MOI_LC0_RARC) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REPEAT(DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))) THEN
  SUBGOAL_THEN `frontier (interval[vector[&0; &0],vector[&2; &1]]:real^2->bool) SUBSET
                interval[vector[&0; &0],vector[&2; &1]]` ASSUME_TAC THENL
   [SIMP_TAC[frontier; CLOSURE_CLOSED; CLOSED_INTERVAL] THEN SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATH_IMAGE_JOIN] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_PATH_JOIN_LOOP THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY;
                MOI_LC0_VECTOR2_EQ] THEN
    REAL_ARITH_TAC;
    REMOVE_THEN "fr" SUBST1_TAC THEN
    REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC]);;

(* The middle part's image is compact. *)

let MOI_LCU_MID_COMPACT = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) g e.
     moi_lt_singular_disk c f /\ moi_lcus_model c f g e
     ==> compact (IMAGE f (IMAGE g (interval[vector[&1; &0],vector[&2; &1]])))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`; `e:bool`]
    MOI_LCU_MODEL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g':real^2->real^2` (X_CHOOSE_THEN `k:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `interval[vector[&1; &0],vector[&2; &1]] SUBSET moi_lcus_mr`
  ASSUME_TAC THENL
   [REWRITE_TAC[MOI_LM2_MR_ARCS; SUBSET; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (g:real^2->real^2) moi_lcus_mr = std_triangle` THEN
    UNDISCH_TAC `interval[vector[&1; &0],vector[&2; &1]] SUBSET moi_lcus_mr` THEN
    SET_TAC[];
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN REWRITE_TAC[COMPACT_INTERVAL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_lcus_mr` THEN
    ASM_REWRITE_TAC[]]);;

(* crossing2 charts of f pass to the reglued disk off the middle part. *)

let MOI_LCU_D1_CROSSING = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) g e (p:real^2->real^2) p'.
     moi_lt_normal2_disk c f /\ moi_lcus_model c f g e /\
     pl_homeomorphism (std_triangle,interval[vector[&0; &0],vector[&2; &1]]) (p,p') /\
     moi_lt_double_image ((f o g o moi_lcu_psi e) o p) =
     moi_lt_double_image f DIFF
     IMAGE f (IMAGE g (interval[vector[&1; &0],vector[&2; &1]]))
     ==> !y. y IN moi_lt_double_image ((f o g o moi_lcu_psi e) o p)
             ==> moi_lt_crossing2_at c ((f o g o moi_lcu_psi e) o p) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_lt_normal_disk c (f:real^2->real^N) /\ moi_lt_singular_disk c f`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_lt_normal2_disk; moi_lt_normal_disk]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`; `e:bool`]
    MOI_LCU_MID_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`; `e:bool`]
    MOI_LCU_MODEL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g':real^2->real^2` (X_CHOOSE_THEN `k:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `MID = IMAGE (f:real^2->real^N)
                      (IMAGE (g:real^2->real^2) (interval[vector[&1; &0],vector[&2; &1]]))` THEN
  UNDISCH_TAC `pl_homeomorphism (std_triangle,interval[vector[&0; &0],vector[&2; &1]])
                 (p:real^2->real^2,p')` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[pl_homeomorphism; homeomorphism] th)) THEN
  MP_TAC(SPEC `e:bool` MOI_LCU_PSI) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "Pin") (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "Ponto")
      (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "Pid") (K ALL_TAC))))))) THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  MATCH_MP_TAC MOI_LC0_CROSSING2_TRANSFER THEN
  MAP_EVERY EXISTS_TAC [`f:real^2->real^N`;
                        `(g:real^2->real^2) o moi_lcu_psi e o (p:real^2->real^2)`;
                        `(:real^N) DIFF MID`] THEN
  SUBGOAL_THEN `(y:real^N) IN moi_lt_double_image f /\ ~(y IN MID)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^N) IN moi_lt_double_image f DIFF MID` THEN
    REWRITE_TAC[IN_DIFF];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^2. x IN std_triangle
                           ==> (p:real^2->real^2) x IN interval[vector[&0; &0],vector[&2; &1]]`
  ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (p:real^2->real^2) std_triangle =
                 interval[vector[&0; &0],vector[&2; &1]]` THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `moi_lt_normal2_disk c (f:real^2->real^N)` THEN
    REWRITE_TAC[moi_lt_normal2_disk] THEN ASM_MESON_TAC[];
    REWRITE_TAC[GSYM closed] THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    ASM_REWRITE_TAC[IN_DIFF; IN_UNIV];
    X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      concl th = `!x:real^2. x IN moi_lcus_mr ==> (g:real^2->real^2) x IN std_triangle`)) THEN
    USE_THEN "Pin" MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `{z:real^2 | ~(z$1 = &1)}` THEN
        REWRITE_TAC[MOI_LCU_PSI_CONT] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_DIFF; IN_UNIV; o_THM] THEN
        X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN DISCH_TAC THEN
        UNDISCH_TAC `~((f:real^2->real^N)
                        ((g:real^2->real^2)(moi_lcu_psi e ((p:real^2->real^2) x))) IN MID)` THEN
        REWRITE_TAC[] THEN
        SUBGOAL_THEN `moi_lcu_psi e ((p:real^2->real^2) x) = p x` SUBST1_TAC THENL
         [USE_THEN "Pid" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
        EXPAND_TAC "MID" THEN REWRITE_TAC[IN_IMAGE] THEN
        EXISTS_TAC `(g:real^2->real^2)((p:real^2->real^2) x)` THEN REWRITE_TAC[] THEN
        EXISTS_TAC `(p:real^2->real^2) x` THEN REWRITE_TAC[] THEN
        SUBGOAL_THEN `(p:real^2->real^2) x IN interval[vector[&0; &0],vector[&2; &1]]`
        MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
        UNDISCH_TAC `((p:real^2->real^2) x)$1 = &1` THEN
        REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2] THEN REAL_ARITH_TAC];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_lcus_mr` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; o_THM] THEN
      X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
      USE_THEN "Pin" MATCH_MP_TAC THEN ASM_SIMP_TAC[]];
    X_GEN_TAC `z:real^2` THEN REWRITE_TAC[IN_DIFF; IN_UNIV] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(g':real^2->real^2) z IN moi_lcus_mr /\ (g:real^2->real^2)(g' z) = z`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    USE_THEN "Ponto" (MP_TAC o SPEC `(g':real^2->real^2) z`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `~(&1 <= x /\ x <= &2) ==> x <= &1 \/ &2 < x`) THEN
      STRIP_TAC THEN UNDISCH_TAC `~((f:real^2->real^N) z IN MID)` THEN REWRITE_TAC[] THEN
      EXPAND_TAC "MID" THEN REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `z:real^2` THEN REWRITE_TAC[] THEN
      EXISTS_TAC `(g':real^2->real^2) z` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(g':real^2->real^2) z IN moi_lcus_mr` THEN
      UNDISCH_TAC `&1 <= ((g':real^2->real^2) z)$1` THEN
      UNDISCH_TAC `((g':real^2->real^2) z)$1 <= &2` THEN
      REWRITE_TAC[MOI_LM2_MR_ARCS; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^2` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(p':real^2->real^2) q` THEN
    SUBGOAL_THEN `(p':real^2->real^2) q IN std_triangle /\ (p:real^2->real^2)(p' q) = q`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `IMAGE (p':real^2->real^2) (interval[vector[&0; &0],vector[&2; &1]]) =
                     std_triangle` THEN
        UNDISCH_TAC `(q:real^2) IN interval[vector[&0; &0],vector[&2; &1]]` THEN SET_TAC[];
        ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[o_THM; IN_DIFF; IN_UNIV];
    ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

(* The reglued disk is a normal2 disk of smaller complexity. *)

let MOI_LCU_D1_NORMAL = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) g e (p:real^2->real^2) p'.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     moi_lt_normal2_disk c f /\ moi_lcus_model c f g e /\
     pl_homeomorphism (std_triangle,interval[vector[&0; &0],vector[&2; &1]]) (p,p') /\
     IMAGE p (relative_frontier std_triangle) =
     frontier (interval[vector[&0; &0],vector[&2; &1]])
     ==> moi_lt_normal2_disk c ((f o g o moi_lcu_psi e) o p) /\
         moi_lt_disk_complexity ((f o g o moi_lcu_psi e) o p) <
         moi_lt_disk_complexity f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_lt_normal_disk c (f:real^2->real^N) /\ moi_lt_singular_disk c f`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_lt_normal2_disk; moi_lt_normal_disk]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`; `e:bool`]
    MOI_LCU_MODEL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g':real^2->real^2` (X_CHOOSE_THEN `k:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`;
                 `(f:real^2->real^N) o (g:real^2->real^2) o moi_lcu_psi e`;
                 `p:real^2->real^2`; `p':real^2->real^2`;
                 `interval[vector[&0; &0],vector[&2; &1]]:real^2->bool`] MOI_LCU_REPARAM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_LCU_F1_PL THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN X_GEN_TAC `z:real^2` THEN
      DISCH_TAC THEN
      UNDISCH_TAC `moi_lt_singular_disk c (f:real^2->real^N)` THEN
      REWRITE_TAC[moi_lt_singular_disk] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        concl th = `!x:real^2. x IN moi_lcus_mr ==> (g:real^2->real^2) x IN std_triangle`)) THEN
      MP_TAC(SPEC `e:bool` MOI_LCU_PSI) THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC MOI_LCU_F1_BD THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_LCU_F1_LOCINJ THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_LCU_F1_FIBRE THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`; `e:bool`]
    MOI_LCU_F1_DOUBLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `MID = IMAGE (f:real^2->real^N)
                      (IMAGE (g:real^2->real^2) (interval[vector[&1; &0],vector[&2; &1]]))` THEN
  SUBGOAL_THEN
   `!k'. k' IN components (moi_lt_double_image (f:real^2->real^N))
         ==> k' SUBSET moi_lt_double_image f DIFF MID \/
             DISJOINT k' (moi_lt_double_image f DIFF MID)`
  (LABEL_TAC "dich") THENL
   [X_GEN_TAC `k':real^N->bool` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`; `e:bool`;
                  `k':real^N->bool`] MOI_LCU_DICHOTOMY) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(k':real^N->bool) SUBSET moi_lt_double_image f` MP_TAC THENL
     [ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN moi_lt_double_image
          (((f:real^2->real^N) o (g:real^2->real^2) o moi_lcu_psi e) o (p:real^2->real^2))
        ==> moi_lt_crossing2_at c ((f o g o moi_lcu_psi e) o p) y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LCU_D1_CROSSING THEN EXISTS_TAC `p':real^2->real^2` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `components (moi_lt_double_image f DIFF MID) SUBSET
                components (moi_lt_double_image (f:real^2->real^N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LA2_UNION_COMPONENTS THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[moi_lt_normal2_disk; moi_lt_normal_disk] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `moi_lt_normal_disk c (f:real^2->real^N)` THEN
      REWRITE_TAC[moi_lt_normal_disk] THEN
      DISCH_THEN(X_CHOOSE_THEN `s:(real^N->bool)->bool` STRIP_ASSUME_TAC o
        CONJUNCT1 o CONJUNCT2) THEN
      MATCH_MP_TAC MOI_LA2_SUBCOMPLEX_MANIFOLD THEN
      EXISTS_TAC `s:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[SUBSET_DIFF] THEN
      ASM_MESON_TAC[];
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      MATCH_MP_TAC MOI_LT2D_CROSSING2_IMP THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[moi_lt_disk_complexity] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CARD_PSUBSET THEN CONJ_TAC THENL
   [ALL_TAC;
    MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`]
      MOI_LA1_SOURCE_COMPONENTS) THEN
    ASM_SIMP_TAC[]] THEN
  ASM_REWRITE_TAC[PSUBSET] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`; `e:bool`]
    MOI_LCU_K_MID) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(k0:real^N->bool) IN components (moi_lt_double_image f DIFF MID)`
  MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP IN_COMPONENTS_NONEMPTY th) THEN
                       MP_TAC(MATCH_MP IN_COMPONENTS_SUBSET th)) THEN
  UNDISCH_TAC `(k0:real^N->bool) SUBSET MID` THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* D1: the boundary loop of the reglued disk (the left half is s1, the      *)
(* right half s3 or its reverse) and the theorem MOI_LCU_D1.                *)
(* ------------------------------------------------------------------------- *)

(* The right arc of [0,2] x [0,1] shifted by rho_e, and the reverse of A_u. *)

let MOI_LCU_RHO_RARC = prove
 (`!e. moi_lcu_rho e o moi_lc0_rarc (&1) (&2) =
       (if e then linepath(vector[&2; &1]:real^2,vector[&3; &1]) ++
                  linepath(vector[&3; &1],vector[&3; &0]) ++
                  linepath(vector[&3; &0],vector[&2; &0])
        else moi_lcus_au) /\
       reversepath moi_lcus_au =
       (linepath(vector[&2; &1]:real^2,vector[&3; &1]) ++
        linepath(vector[&3; &1],vector[&3; &0])) ++
       linepath(vector[&3; &0],vector[&2; &0])`,
  GEN_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[moi_lc0_rarc; moi_lcus_au; PATH_COMPOSE_JOIN; MOI_LCU_RHO] THEN
    REWRITE_TAC[moi_lcu_rho; VECTOR_2] THEN
    BOOL_CASES_TAC `e:bool` THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    REWRITE_TAC[];
    REWRITE_TAC[moi_lcus_au] THEN
    SIMP_TAC[REVERSEPATH_JOINPATHS; PATHSTART_JOIN; PATHFINISH_JOIN;
             PATHSTART_LINEPATH; PATHFINISH_LINEPATH; REVERSEPATH_LINEPATH]]);;

(* Paths of the model boundary carried to f(Bd T). *)

let MOI_LCU_FG_PATH = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) g e (q:real^1->real^2).
     moi_lt_singular_disk c f /\ moi_lcus_model c f g e /\
     path q /\ path_image q SUBSET relative_frontier moi_lcus_mr
     ==> path (f o g o q) /\
         path_image (f o g o q) SUBSET IMAGE f (relative_frontier std_triangle)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`; `e:bool`]
    MOI_LCU_MODEL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g':real^2->real^2` (X_CHOOSE_THEN `k:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `relative_frontier moi_lcus_mr SUBSET moi_lcus_mr` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_LM2_MR_ARCS] THEN
    SIMP_TAC[frontier; CLOSURE_CLOSED; CLOSED_INTERVAL] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[o_ASSOC] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_lcus_mr` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    REWRITE_TAC[PATH_IMAGE_COMPOSE; IMAGE_o; SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    SUBGOAL_THEN `(x:real^2) IN relative_frontier moi_lcus_mr /\ x IN moi_lcus_mr`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[]]);;

(* The right half of the D1 boundary loop is s3 or its reverse. *)

let MOI_LCU_D1_RIGHT = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) g e.
     moi_lt_singular_disk c f /\ moi_lcus_model c f g e
     ==> homotopic_paths (IMAGE f (relative_frontier std_triangle))
           ((f o g o moi_lcu_psi e) o moi_lc0_rarc (&1) (&2))
           (if e then reversepath (f o g o moi_lcus_au) else f o g o moi_lcus_au)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`; `e:bool`]
    MOI_LCU_F1_SIDES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "H2" o CONJUNCT2) THEN
  ABBREV_TAC `t = IMAGE (f:real^2->real^N) (relative_frontier std_triangle)` THEN
  SUBGOAL_THEN
   `!q:real^1->real^2. path q /\ path_image q SUBSET relative_frontier moi_lcus_mr
                       ==> path ((f:real^2->real^N) o (g:real^2->real^2) o q) /\
                           path_image (f o g o q) SUBSET t`
  (LABEL_TAC "FG") THENL
   [EXPAND_TAC "t" THEN GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_LCU_FG_PATH THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `e:bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC MOI_LCU_Q_LOOP THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN
   `!s. s IN interval[vec 0,vec 1]
        ==> ((f:real^2->real^N) o (g:real^2->real^2) o moi_lcu_psi e)
              (moi_lc0_rarc (&1) (&2) s) =
            (f o g o (moi_lcu_rho e o moi_lc0_rarc (&1) (&2))) s`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `moi_lc0_rarc (&1) (&2) s IN
                  path_image (moi_lc0_rarc (&1) (&2))` ASSUME_TAC THENL
     [REWRITE_TAC[path_image] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "H2" (MP_TAC o SPEC `moi_lc0_rarc (&1) (&2) s`) THEN
    REWRITE_TAC[o_THM] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [SUBGOAL_THEN `pathfinish (moi_lc0_larc (&0) (&1)) =
                    pathstart (moi_lc0_rarc (&1) (&2):real^1->real^2)` ASSUME_TAC THENL
       [MP_TAC(SPECL [`&0`; `&1`] MOI_LC0_LARC) THEN
        MP_TAC(SPECL [`&1`; `&2`] MOI_LC0_RARC) THEN
        CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN SIMP_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `frontier (interval[vector[&0; &0],vector[&2; &1]]:real^2->bool) SUBSET
                   interval[vector[&0; &0],vector[&2; &1]]` THEN
      UNDISCH_TAC `path_image (moi_lc0_larc (&0) (&1) ++ moi_lc0_rarc (&1) (&2)) =
                   frontier (interval[vector[&0; &0],vector[&2; &1]])` THEN
      ASM_SIMP_TAC[PATH_IMAGE_JOIN] THEN
      UNDISCH_TAC `moi_lc0_rarc (&1) (&2) s IN path_image (moi_lc0_rarc (&1) (&2))` THEN
      SET_TAC[];
      UNDISCH_TAC `path_image (moi_lc0_rarc (&1) (&2)) SUBSET {x:real^2 | &1 <= x$1}` THEN
      UNDISCH_TAC `moi_lc0_rarc (&1) (&2) s IN path_image (moi_lc0_rarc (&1) (&2))` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPEC `e:bool` MOI_LCU_RHO_RARC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  MP_TAC MOI_LM2_MR_ARCS THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (snd(chop_list 4 (CONJUNCTS th)))) THEN
  SUBGOAL_THEN `path_image (linepath(vector[&2; &1]:real^2,vector[&3; &1])) SUBSET
                relative_frontier moi_lcus_mr /\
                path_image (linepath(vector[&3; &1]:real^2,vector[&3; &0])) SUBSET
                relative_frontier moi_lcus_mr /\
                path_image (linepath(vector[&3; &0]:real^2,vector[&2; &0])) SUBSET
                relative_frontier moi_lcus_mr`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `path_image moi_lcus_au SUBSET relative_frontier moi_lcus_mr` THEN
    ONCE_REWRITE_TAC[GSYM PATH_IMAGE_REVERSEPATH] THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `reversepath moi_lcus_au`)) THEN
    SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH;
             PATHFINISH_LINEPATH; PATH_IMAGE_REVERSEPATH] THEN
    SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `la = linepath(vector[&2; &1]:real^2,vector[&3; &1])` THEN
  ABBREV_TAC `lb = linepath(vector[&3; &1]:real^2,vector[&3; &0])` THEN
  ABBREV_TAC `lc = linepath(vector[&3; &0]:real^2,vector[&2; &0])` THEN
  SUBGOAL_THEN `path (la:real^1->real^2) /\ path (lb:real^1->real^2) /\
                path (lc:real^1->real^2) /\
                pathfinish la = pathstart lb /\ pathfinish lb = pathstart lc`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["la"; "lb"; "lc"] THEN
    REWRITE_TAC[PATH_LINEPATH; PATHSTART_LINEPATH; PATHFINISH_LINEPATH];
    ALL_TAC] THEN
  SUBGOAL_THEN `path (moi_lcus_au) /\ path_image moi_lcus_au SUBSET relative_frontier moi_lcus_mr`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[ARC_IMP_PATH]; ALL_TAC] THEN
  SUBGOAL_THEN `path ((la:real^1->real^2) ++ lb ++ lc) /\
                path_image (la ++ lb ++ lc) SUBSET relative_frontier moi_lcus_mr`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN] THEN
    ASM_REWRITE_TAC[UNION_SUBSET];
    ALL_TAC] THEN
  ASM_CASES_TAC `e:bool` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o EQT_INTRO) THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
    EXISTS_TAC `(f:real^2->real^N) o (g:real^2->real^2) o (la ++ lb ++ lc)` THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN MATCH_MP_TAC HOMOTOPIC_PATHS_EQ THEN
      USE_THEN "FG" (fun th -> SIMP_TAC[MATCH_MP th
        (CONJ (ASSUME `path ((la:real^1->real^2) ++ lb ++ lc)`)
              (ASSUME `path_image ((la:real^1->real^2) ++ lb ++ lc) SUBSET
                       relative_frontier moi_lcus_mr`))]) THEN
      X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real^1` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `moi_lcu_rho T o moi_lc0_rarc (&1) (&2)`))
          (concl th))) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[o_THM] THEN MESON_TAC[];
      REWRITE_TAC[GSYM PATH_COMPOSE_REVERSEPATH] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[PATH_COMPOSE_JOIN] THEN
      MATCH_MP_TAC HOMOTOPIC_PATHS_ASSOC THEN
      REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "FG" (fun th ->
        MP_TAC(MATCH_MP th (CONJ (ASSUME `path (la:real^1->real^2)`)
          (ASSUME `path_image (la:real^1->real^2) SUBSET relative_frontier moi_lcus_mr`))) THEN
        MP_TAC(MATCH_MP th (CONJ (ASSUME `path (lb:real^1->real^2)`)
          (ASSUME `path_image (lb:real^1->real^2) SUBSET relative_frontier moi_lcus_mr`))) THEN
        MP_TAC(MATCH_MP th (CONJ (ASSUME `path (lc:real^1->real^2)`)
          (ASSUME `path_image (lc:real^1->real^2) SUBSET relative_frontier moi_lcus_mr`)))) THEN
      SIMP_TAC[]];
    FIRST_X_ASSUM(SUBST_ALL_TAC o EQF_INTRO) THEN REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN MATCH_MP_TAC HOMOTOPIC_PATHS_EQ THEN
    USE_THEN "FG" (fun th -> SIMP_TAC[MATCH_MP th
      (CONJ (ASSUME `path moi_lcus_au`)
            (ASSUME `path_image moi_lcus_au SUBSET relative_frontier moi_lcus_mr`))]) THEN
    X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real^1` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `moi_lcu_rho F o moi_lc0_rarc (&1) (&2)`))
        (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[o_THM] THEN MESON_TAC[]]);;

(* The left half of the D1 boundary loop is s1. *)

let MOI_LCU_D1_LEFT = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) g e.
     moi_lt_singular_disk c f /\ moi_lcus_model c f g e
     ==> homotopic_paths (IMAGE f (relative_frontier std_triangle))
           ((f o g o moi_lcu_psi e) o moi_lc0_larc (&0) (&1))
           (f o g o moi_lcus_as)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`; `e:bool`]
    MOI_LCU_F1_SIDES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "H1" o CONJUNCT1) THEN
  MP_TAC MOI_LCU_Q_LOOP THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN MATCH_MP_TAC HOMOTOPIC_PATHS_EQ THEN
  REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_LCU_FG_PATH THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `e:bool`] THEN
    ASM_REWRITE_TAC[] THEN
    SIMP_TAC[MOI_LM2_MR_ARCS; ARC_IMP_PATH];
    ALL_TAC] THEN
  X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
  REWRITE_TAC[CONJUNCT1 MOI_LM2_MR_ARCS; o_THM] THEN
  SUBGOAL_THEN `moi_lc0_larc (&0) (&1) s IN path_image (moi_lc0_larc (&0) (&1))`
  ASSUME_TAC THENL
   [REWRITE_TAC[path_image] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN
  USE_THEN "H1" (MP_TAC o SPEC `moi_lc0_larc (&0) (&1) s`) THEN
  REWRITE_TAC[o_THM] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [SUBGOAL_THEN `pathfinish (moi_lc0_larc (&0) (&1)) =
                  pathstart (moi_lc0_rarc (&1) (&2):real^1->real^2)` ASSUME_TAC THENL
     [MP_TAC(SPECL [`&0`; `&1`] MOI_LC0_LARC) THEN
      MP_TAC(SPECL [`&1`; `&2`] MOI_LC0_RARC) THEN
      CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN SIMP_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `frontier (interval[vector[&0; &0],vector[&2; &1]]:real^2->bool) SUBSET
                 interval[vector[&0; &0],vector[&2; &1]]` THEN
    UNDISCH_TAC `path_image (moi_lc0_larc (&0) (&1) ++ moi_lc0_rarc (&1) (&2)) =
                 frontier (interval[vector[&0; &0],vector[&2; &1]])` THEN
    ASM_SIMP_TAC[PATH_IMAGE_JOIN] THEN
    UNDISCH_TAC `moi_lc0_larc (&0) (&1) s IN path_image (moi_lc0_larc (&0) (&1))` THEN
    SET_TAC[];
    UNDISCH_TAC `path_image (moi_lc0_larc (&0) (&1)) SUBSET {x:real^2 | x$1 <= &1}` THEN
    UNDISCH_TAC `moi_lc0_larc (&0) (&1) s IN path_image (moi_lc0_larc (&0) (&1))` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]]);;

let MOI_LCU_D1 = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) g e.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\ moi_lt_normal2_disk c f /\
     moi_lcus_model c f g e
     ==> ?f1. moi_lt_normal2_disk c f1 /\
              moi_lt_disk_complexity f1 < moi_lt_disk_complexity f /\
              homotopic_loops (IMAGE f (relative_frontier std_triangle))
                (f1 o std_triangle_loop)
                (if e then (f o g o moi_lcus_as) ++ reversepath (f o g o moi_lcus_au)
                 else (f o g o moi_lcus_as) ++ (f o g o moi_lcus_au))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_lt_singular_disk c (f:real^2->real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_lt_normal2_disk; moi_lt_normal_disk]; ALL_TAC] THEN
  MP_TAC MOI_LCU_Q_LOOP THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MP_TAC(ISPECL [`interval[vector[&0; &0],vector[&2; &1]]:real^2->bool`;
                 `moi_lc0_larc (&0) (&1) ++ moi_lc0_rarc (&1) (&2)`] MOI_LC0_DISK_LOOP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^2->real^2` (X_CHOOSE_THEN `p':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `((f:real^2->real^N) o (g:real^2->real^2) o moi_lcu_psi e) o
              (p:real^2->real^2)` THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`; `e:bool`;
                `p:real^2->real^2`; `p':real^2->real^2`] MOI_LCU_D1_NORMAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`; `e:bool`]
    MOI_LCU_D1_LEFT) THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`; `e:bool`]
    MOI_LCU_D1_RIGHT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `((f:real^2->real^N) o (g:real^2->real^2) o moi_lcu_psi e) continuous_on
                interval[vector[&0; &0],vector[&2; &1]]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN MATCH_MP_TAC MOI_LCU_F1_PL THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE ((f:real^2->real^N) o (g:real^2->real^2) o moi_lcu_psi e)
      (frontier(interval[vector[&0; &0],vector[&2; &1]])) SUBSET
    IMAGE f (relative_frontier std_triangle)`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`; `e:bool`]
      MOI_LCU_MODEL_FACTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `g':real^2->real^2` (X_CHOOSE_THEN `k:real^N->bool`
      STRIP_ASSUME_TAC)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN X_GEN_TAC `z:real^2` THEN
    DISCH_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    SUBGOAL_THEN `(z:real^2) IN interval[vector[&0; &0],vector[&2; &1]]` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(SPEC `e:bool` MOI_LCU_PSI) THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `z:real^2` (CONJUNCT1 th)) THEN
                         MP_TAC(SPEC `z:real^2` (CONJUNCT1(CONJUNCT2(CONJUNCT2 th))))) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `homotopic_loops (IMAGE (f:real^2->real^N) (relative_frontier std_triangle))
      ((f o (g:real^2->real^2) o moi_lcu_psi e) o (p:real^2->real^2) o std_triangle_loop)
      ((f o g o moi_lcu_psi e) o (moi_lc0_larc (&0) (&1) ++ moi_lc0_rarc (&1) (&2)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE THEN
    EXISTS_TAC `frontier(interval[vector[&0; &0],vector[&2; &1]]:real^2->bool)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `interval[vector[&0; &0],vector[&2; &1]]:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pathfinish ((f o (g:real^2->real^2) o moi_lcu_psi e) o moi_lc0_larc (&0) (&1)) =
    pathstart (((f:real^2->real^N) o g o moi_lcu_psi e) o moi_lc0_rarc (&1) (&2)) /\
    pathfinish (((f:real^2->real^N) o g o moi_lcu_psi e) o
                (moi_lc0_larc (&0) (&1) ++ moi_lc0_rarc (&1) (&2))) =
    pathstart (((f:real^2->real^N) o g o moi_lcu_psi e) o
                (moi_lc0_larc (&0) (&1) ++ moi_lc0_rarc (&1) (&2)))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`&0`; `&1`] MOI_LC0_LARC) THEN
    MP_TAC(SPECL [`&1`; `&2`] MOI_LC0_RARC) THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `homotopic_paths (IMAGE (f:real^2->real^N) (relative_frontier std_triangle))
      ((f o (g:real^2->real^2) o moi_lcu_psi e) o
       (moi_lc0_larc (&0) (&1) ++ moi_lc0_rarc (&1) (&2)))
      ((f o g o moi_lcus_as) ++
       (if e then reversepath (f o g o moi_lcus_au) else f o g o moi_lcus_au))`
  ASSUME_TAC THENL
   [REWRITE_TAC[PATH_COMPOSE_JOIN] THEN MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `homotopic_loops (IMAGE (f:real^2->real^N) (relative_frontier std_triangle))
      ((f o (g:real^2->real^2) o moi_lcu_psi e) o
       (moi_lc0_larc (&0) (&1) ++ moi_lc0_rarc (&1) (&2)))
      ((f o g o moi_lcus_as) ++
       (if e then reversepath (f o g o moi_lcus_au) else f o g o moi_lcus_au))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_PATHS_IMP_HOMOTOPIC_LOOPS THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[GSYM(MATCH_MP HOMOTOPIC_PATHS_IMP_PATHFINISH th)]) o
      check (fun th -> is_comb(concl th) &&
        fst(dest_const(fst(strip_comb(concl th)))) = "homotopic_paths")) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM o_ASSOC] THEN
  MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
  EXISTS_TAC `((f:real^2->real^N) o (g:real^2->real^2) o moi_lcu_psi e) o
              (moi_lc0_larc (&0) (&1) ++ moi_lc0_rarc (&1) (&2))` THEN
  CONJ_TAC THENL
   [UNDISCH_TAC
     `homotopic_loops (IMAGE (f:real^2->real^N) (relative_frontier std_triangle))
        ((f o (g:real^2->real^2) o moi_lcu_psi e) o (p:real^2->real^2) o std_triangle_loop)
        ((f o g o moi_lcu_psi e) o (moi_lc0_larc (&0) (&1) ++ moi_lc0_rarc (&1) (&2)))` THEN
    REWRITE_TAC[o_ASSOC];
    ASM_CASES_TAC `e:bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC
     `homotopic_loops (IMAGE (f:real^2->real^N) (relative_frontier std_triangle))
        ((f o (g:real^2->real^2) o moi_lcu_psi e) o
         (moi_lc0_larc (&0) (&1) ++ moi_lc0_rarc (&1) (&2)))
        ((f o g o moi_lcus_as) ++
         (if e then reversepath (f o g o moi_lcus_au) else f o g o moi_lcus_au))` THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The paths s1..s4, the words and the main theorem ARC_FROM_SEAM.         *)
(* ------------------------------------------------------------------------- *)

(* The four boundary paths s1..s4 of the model: paths in f(Bd T), their     *)
(* joints, and the boundary loop of f as their product.                     *)

let MOI_LCU_PATHS = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) g e.
     moi_lt_singular_disk c f /\ moi_lcus_model c f g e /\
     homotopic_loops (relative_frontier std_triangle) std_triangle_loop
       (g o (moi_lcus_as ++ moi_lcus_at ++ moi_lcus_au ++ moi_lcus_av))
     ==> path (f o g o moi_lcus_as) /\ path (f o g o moi_lcus_at) /\
         path (f o g o moi_lcus_au) /\ path (f o g o moi_lcus_av) /\
         path_image (f o g o moi_lcus_as) SUBSET IMAGE f (relative_frontier std_triangle) /\
         path_image (f o g o moi_lcus_at) SUBSET IMAGE f (relative_frontier std_triangle) /\
         path_image (f o g o moi_lcus_au) SUBSET IMAGE f (relative_frontier std_triangle) /\
         path_image (f o g o moi_lcus_av) SUBSET IMAGE f (relative_frontier std_triangle) /\
         pathfinish (f o g o moi_lcus_as) = pathstart (f o g o moi_lcus_at) /\
         pathfinish (f o g o moi_lcus_at) = pathstart (f o g o moi_lcus_au) /\
         pathfinish (f o g o moi_lcus_au) = pathstart (f o g o moi_lcus_av) /\
         pathfinish (f o g o moi_lcus_av) = pathstart (f o g o moi_lcus_as) /\
         homotopic_loops (IMAGE f (relative_frontier std_triangle)) (f o std_triangle_loop)
           ((f o g o moi_lcus_as) ++ (f o g o moi_lcus_at) ++
            (f o g o moi_lcus_au) ++ (f o g o moi_lcus_av))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  REWRITE_TAC[moi_lcus_model] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `g':real^2->real^2`)
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  SUBGOAL_THEN `(f:real^2->real^N) continuous_on std_triangle` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN
    ASM_MESON_TAC[moi_lt_singular_disk];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^2->real^2) continuous_on moi_lcus_mr /\
                IMAGE g moi_lcus_mr = std_triangle`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (moi_lcus_mr,std_triangle) (g:real^2->real^2,g')` THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^2->real^N) o (g:real^2->real^2) continuous_on moi_lcus_mr`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier moi_lcus_mr SUBSET moi_lcus_mr` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_LM2_MR_ARCS] THEN
    SIMP_TAC[frontier; CLOSURE_CLOSED; CLOSED_INTERVAL] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p:real^1->real^2.
      arc p /\ path_image p SUBSET relative_frontier moi_lcus_mr
      ==> path ((f:real^2->real^N) o (g:real^2->real^2) o p) /\
          path_image (f o g o p) SUBSET IMAGE f (relative_frontier std_triangle)`
  ASSUME_TAC THENL
   [X_GEN_TAC `p:real^1->real^2` THEN STRIP_TAC THEN
    REWRITE_TAC[o_ASSOC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_SIMP_TAC[ARC_IMP_PATH] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_lcus_mr` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      REWRITE_TAC[PATH_IMAGE_COMPOSE; IMAGE_o] THEN
      UNDISCH_TAC `IMAGE (g:real^2->real^2) (relative_frontier moi_lcus_mr) =
                   relative_frontier std_triangle` THEN
      UNDISCH_TAC `path_image (p:real^1->real^2) SUBSET relative_frontier moi_lcus_mr` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC MOI_LM2_MR_ARCS THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (snd(chop_list 3 (CONJUNCTS th)))) THEN
  ASM_SIMP_TAC[] THEN
  REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; MOI_LCUS_SAN_ENDS] THEN
  REWRITE_TAC[GSYM PATH_COMPOSE_JOIN] THEN
  REWRITE_TAC[GSYM o_ASSOC] THEN
  MATCH_MP_TAC HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE THEN
  EXISTS_TAC `relative_frontier std_triangle` THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
  ASM_REWRITE_TAC[MOI_LTD_FRONTIER_SUBSET_TRIANGLE]);;

(* The two disjuncts of MOI_LT4_CUT_ARC_SPLIT from the model relation e. *)

let MOI_LCU_GLUE = prove
 (`!e (s1:real^1->real^N) s2 s3 s4 l1 l2 w.
     (if e
      then pathfinish s1 = pathstart s4 /\ pathfinish s4 = pathstart s3 /\
           pathfinish s3 = pathstart s2 /\ pathfinish s2 = pathstart s1 /\
           pathstart s3 = pathstart s1 /\ pathfinish s3 = pathfinish s1
      else pathfinish s1 = pathstart (reversepath s2) /\
           pathfinish (reversepath s2) = pathstart s3 /\
           pathfinish s3 = pathstart (reversepath s4) /\
           pathfinish (reversepath s4) = pathstart s1 /\
           pathfinish s2 = pathstart s2 /\ pathfinish s4 = pathstart s4) /\
     homotopic_loops w l2
       (if e then s1 ++ s4 ++ s3 ++ s2
        else s1 ++ reversepath s2 ++ s3 ++ reversepath s4) /\
     homotopic_loops w l1 (if e then s1 ++ reversepath s3 else s1 ++ s3)
     ==> (pathstart s3 = pathstart s1 /\ pathfinish s3 = pathfinish s1 /\
          homotopic_loops w l1 (s1 ++ reversepath s3) /\
          homotopic_loops w l2 (s1 ++ s4 ++ s3 ++ s2)) \/
         (pathfinish s2 = pathstart s2 /\ pathfinish s4 = pathstart s4 /\
          homotopic_loops w l1 (s1 ++ s3) /\
          homotopic_loops w l2 (s1 ++ reversepath s2 ++ s3 ++ reversepath s4))`,
  GEN_TAC THEN BOOL_CASES_TAC `e:bool` THEN REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THENL [DISJ1_TAC; DISJ2_TAC] THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* The main theorem conditional on the 2D model; ARC_FROM_SEAM below is one  *)
(* MP with LT_MODEL_2D of pc_moi_lt_model2d.ml.                              *)

let MOI_LCU_ARC_FROM_SEAM_M = prove
 (mk_imp(MOI_LCU_MODEL2D,MOI_LCUS_ARC_FROM_SEAM),
  DISCH_THEN(LABEL_TAC "m2d") THEN
  DISCH_THEN(LABEL_TAC "seam") THEN
  MAP_EVERY X_GEN_TAC [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `w:real^N->bool`] THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC o
    check (is_exists o concl)) THEN
  USE_THEN "m2d" (fun th -> MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`;
    `k:real^N->bool`] (MP MOI_LCU_MODEL th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^2->real^2` (X_CHOOSE_THEN `e:bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`; `e:bool`]
    MOI_LCU_D1) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f1:real^2->real^N` STRIP_ASSUME_TAC) THEN
  USE_THEN "seam" (MP_TAC o SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`;
    `w:real^N->bool`; `g:real^2->real^2`; `e:bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f2:real^2->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_lt_singular_disk c (f:real^2->real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_lt_normal2_disk; moi_lt_normal_disk]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`; `e:bool`]
    MOI_LCU_PATHS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^2`; `e:bool`]
    MOI_LCUS_SAN_WORDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ABBREV_TAC `s1 = (f:real^2->real^N) o (g:real^2->real^2) o moi_lcus_as` THEN
  ABBREV_TAC `s2 = (f:real^2->real^N) o (g:real^2->real^2) o moi_lcus_at` THEN
  ABBREV_TAC `s3 = (f:real^2->real^N) o (g:real^2->real^2) o moi_lcus_au` THEN
  ABBREV_TAC `s4 = (f:real^2->real^N) o (g:real^2->real^2) o moi_lcus_av` THEN
  MAP_EVERY EXISTS_TAC
   [`f1:real^2->real^N`; `f2:real^2->real^N`; `s1:real^1->real^N`; `s2:real^1->real^N`;
    `s3:real^1->real^N`; `s4:real^1->real^N`] THEN
  SUBGOAL_THEN `!p:real^1->real^N. path_image p SUBSET IMAGE f (relative_frontier std_triangle)
                                  ==> path_image p SUBSET w`
  ASSUME_TAC THENL
   [GEN_TAC THEN UNDISCH_TAC `IMAGE (f:real^2->real^N) (relative_frontier std_triangle)
                               SUBSET w` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `path_image (s1:real^1->real^N) SUBSET w /\ path_image (s2:real^1->real^N) SUBSET w /\
                path_image (s3:real^1->real^N) SUBSET w /\ path_image (s4:real^1->real^N) SUBSET w`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `homotopic_loops w ((f:real^2->real^N) o std_triangle_loop)
                  ((s1:real^1->real^N) ++ s2 ++ s3 ++ s4)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_LOOPS_SUBSET THEN
    EXISTS_TAC `IMAGE (f:real^2->real^N) (relative_frontier std_triangle)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `homotopic_loops w ((f1:real^2->real^N) o std_triangle_loop)
      (if e then (s1:real^1->real^N) ++ reversepath s3 else s1 ++ s3)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_LOOPS_SUBSET THEN
    EXISTS_TAC `IMAGE (f:real^2->real^N) (relative_frontier std_triangle)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(pathstart s3 = pathstart s1 /\ pathfinish s3 = pathfinish s1 /\
     homotopic_loops w ((f1:real^2->real^N) o std_triangle_loop) (s1 ++ reversepath s3) /\
     homotopic_loops w ((f2:real^2->real^N) o std_triangle_loop) (s1 ++ s4 ++ s3 ++ s2)) \/
    (pathfinish s2 = pathstart s2 /\ pathfinish (s4:real^1->real^N) = pathstart s4 /\
     homotopic_loops w (f1 o std_triangle_loop) (s1 ++ s3) /\
     homotopic_loops w (f2 o std_triangle_loop)
       (s1 ++ reversepath s2 ++ s3 ++ reversepath s4))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LCU_GLUE THEN EXISTS_TAC `e:bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* ------------------------------------------------------------------------- *)
(* ARC_FROM_SEAM: discharge the 2D model antecedent with LT_MODEL_2D.       *)
(* ------------------------------------------------------------------------- *)

let ARC_FROM_SEAM = MP MOI_LCU_ARC_FROM_SEAM_M LT_MODEL_2D;;


(* ========================================================================= *)
(* pc_moi_s32_iter3: Moise Sec 32 Step 1 at all levels with the member      *)
(* invariant of pc_moi_s3032_stmt6.  Main theorem                           *)
(* ITERATE_3 |- MOI_S32_ITERATE_3.  The proof of ITERATE_2                  *)
(* (pc_moi_s32_iter) with moi_s32_state3: the stages are states3 (LEVEL_3), *)
(* so states (the bridge MOI_S3S6_STATE3), and the limit lemmas of s32_iter *)
(* apply; a member of the limit family takes its member clause, with the    *)
(* history witness, from a stage where both its levels are processed.       *)
(* ========================================================================= *)

needs "src/pc_moi_s32_iter.ml";;
needs "src/pc_moi_s3032_stmt6.ml";;

prioritize_real();;
type_invention_error := true;;


(* ------------------------------------------------------------------------- *)
(* Sequences of states3, the members of the limit family, the limit state3  *)
(* and ITERATE_3.                                                           *)
(* ------------------------------------------------------------------------- *)

let moi_s3t3_seq = new_definition
 `moi_s3t3_seq (g:real^3->real^3) v pp dd s2 (e:num->int)
               (f:num->(real^3->bool)->bool) <=>
    moi_s3it_seq g v pp dd s2 e f /\
    (!n. moi_s32_state3 g dd s2 (IMAGE e {k | k < n}) (f n))`;;

let MOI_S3T3_FF_MEMBER = prove
 (`!(g:real^3->real^3) v pp dd s2 e f c.
     moi_s3t3_seq g v pp dd s2 e f /\ c IN {c | ?n0. !n. n0 <= n ==> c IN f n}
     ==> ?i cc. (c SUBSET moi_s32_lvl g dd i /\
                 FINITE cc /\ combinatorial_manifold_with_boundary 2 cc /\
                 UNIONS cc = c /\ connected c /\ ~(c = {}) /\
                 surface_boundary cc = c INTER moi_s32_evens s2 /\
                 c INTER moi_s32_evens s2 SUBSET
                   frontier (s2 (&2 * i)) UNION frontier (s2 (&2 * i + &2)) /\
                 (i IN (:int)
                  ==> !jj. jj IN components (c INTER frontier (s2 (&2 * i)))
                           ==> moi_s32_ess s2 (&2 * i) jj) /\
                 ((i + &1) IN (:int)
                  ==> !jj. jj IN components (c INTER frontier (s2 (&2 * i + &2)))
                           ==> moi_s32_ess s2 (&2 * i + &2) jj)) /\
                moi_s32_hist s2 i cc c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o GEN_REWRITE_RULE I [moi_s3t3_seq])
    (X_CHOOSE_TAC `n0:num`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "seq") (LABEL_TAC "st3")) THEN
  USE_THEN "seq" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s3it_seq]) THEN
  SUBGOAL_THEN `?y:real^3. y IN c /\ y IN IMAGE (g:real^3->real^3) v` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                   `dd:int->real^3->bool`; `s2:int->real^3->bool`;
                   `IMAGE (e:num->int) {k | k < n0}`; `(f:num->(real^3->bool)->bool) n0`;
                   `c:real^3->bool`] MOI_S3IT_MEMBER_FACTS) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[LE_REFL]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `i0:int` STRIP_ASSUME_TAC) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `e:num->int`;
                 `f:num->(real^3->bool)->bool`; `y:real^3`] MOI_S3IT_POINT_STAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN
  ABBREV_TAC `n = n0 + N:num` THEN
  SUBGOAL_THEN `(c:real^3->bool) IN f (n:num)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN EXPAND_TAC "n" THEN ARITH_TAC; ALL_TAC] THEN
  USE_THEN "st3" (MP_TAC o SPEC `n:num`) THEN
  REWRITE_TAC[moi_s32_state3] THEN
  DISCH_THEN(MP_TAC o SPEC `c:real^3->bool` o CONJUNCT1 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `i:int` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `cc:(real^3->bool)->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[IN_UNIV] THEN
  SUBGOAL_THEN `(y:real^3) IN moi_s32_lvl g dd i` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!j. (!m. N <= m ==> ~((e:num->int) m = j)) ==> j IN IMAGE e {k | k < n}`
  (LABEL_TAC "proc") THENL
   [X_GEN_TAC `j:int` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                   `dd:int->real^3->bool`; `s2:int->real^3->bool`; `e:num->int`;
                   `f:num->(real^3->bool)->bool`; `N:num`; `j:int`] MOI_S3IT_SEQ_PROCESSED) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN EXPAND_TAC "n" THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `i IN IMAGE (e:num->int) {k | k < n} /\ (i + &1) IN IMAGE e {k | k < n}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "proc" MATCH_MP_TAC THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    USE_THEN "N" (MP_TAC o SPECL [`m:num`; `i:int`]) THEN ASM_SIMP_TAC[];
    ASM_MESON_TAC[]]);;

let MOI_S3T3_FF_STATE = prove
 (`!(g:real^3->real^3) v pp dd s2 e f.
     moi_s3t3_seq g v pp dd s2 e f
     ==> moi_s32_state3 g dd s2 (:int) {c | ?n0. !n. n0 <= n ==> c IN f n}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3IT_FF_STATE o CONJUNCT1 o
              GEN_REWRITE_RULE I [moi_s3t3_seq]) THEN
  REWRITE_TAC[moi_s32_state; moi_s32_state3] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `c:real^3->bool` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_S3T3_FF_MEMBER THEN
  MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`; `e:num->int`;
                        `f:num->(real^3->bool)->bool`] THEN
  ASM_REWRITE_TAC[]);;

let ITERATE_3 = prove
 (MOI_S32_ITERATE_3,
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lev3") (K ALL_TAC)) THEN
  MAP_EVERY X_GEN_TAC [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                       `dd:int->real^3->bool`; `s2:int->real^3->bool`;
                       `fam:(real^3->bool)->bool`] THEN
  STRIP_TAC THEN
  X_CHOOSE_THEN `e:num->int` STRIP_ASSUME_TAC MOI_S3IT_INT_ENUM THEN
  MP_TAC(ISPECL
   [`moi_s32_state3 (g:real^3->real^3) dd s2`;
    `\(fam:(real^3->bool)->bool) (fam':(real^3->bool)->bool) (i:int).
        moi_s32_set (g:real^3->real^3) s2 fam' DIFF
          interior (IMAGE g (revolution ((dd:int->real^3->bool) (&2 * i)))) =
        moi_s32_set g s2 fam DIFF interior (IMAGE g (revolution (dd (&2 * i)))) /\
        {c | c IN fam' /\ DISJOINT c (interior (IMAGE g (revolution (dd (&2 * i)))))} =
        {c | c IN fam /\ DISJOINT c (interior (IMAGE g (revolution (dd (&2 * i)))))}`;
    `e:num->int`; `fam:(real^3->bool)->bool`] MOI_S3IT_ITERATE_SEQ) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`lev:int->bool`; `a:(real^3->bool)->bool`; `i:int`] THEN
    STRIP_TAC THEN
    REMOVE_THEN "lev3" (MP_TAC o SPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
      `dd:int->real^3->bool`; `s2:int->real^3->bool`; `lev:int->bool`;
      `a:(real^3->bool)->bool`; `i:int`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `{c | ?n0. !n. n0 <= n ==> c IN (f:num->(real^3->bool)->bool) n}` THEN
  MATCH_MP_TAC MOI_S3T3_FF_STATE THEN
  MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`; `e:num->int`] THEN
  ASM_REWRITE_TAC[moi_s3t3_seq; moi_s3it_seq] THEN ASM_SIMP_TAC[MOI_S3S6_STATE3]);;


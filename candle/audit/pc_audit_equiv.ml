(* ========================================================================= *)
(* pc_audit_equiv: our headline statements (poincare_statement.ml) are       *)
(* equivalent to those of the blind independent formalization                *)
(* audit/poincare_blind.ml (POINCARE_TOP_BLIND_EQUIV,                        *)
(* POINCARE_SMOOTH_BLIND_EQUIV).  First the topological form.                *)
(*                                                                           *)
(* Bridges: (1) neighbourhoods homeomorphic to real^3 versus to open subsets *)
(* of real^3; (2) second countability, automatic for compact locally         *)
(* Euclidean spaces; (3) simple connectivity: any two loops freely homotopic *)
(* as loops (plus nonempty) versus nonempty, path connected and every loop   *)
(* null-homotopic with its base point fixed.  The hard half of (3) turns a   *)
(* free homotopy of a loop p to the constant loop into a based one, by an    *)
(* explicit reparametrization of the square in two stages.                   *)
(* ========================================================================= *)

needs "src/poincare_statement_sanity.ml";;
needs "src/ns_smooth_elem.ml";;
needs "src/pc_mfd_examples.ml";;
loads "audit/poincare_blind.ml";;  (* Candle: no loadt *)

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The two 3-spheres are literally the same space.                           *)
(* ------------------------------------------------------------------------- *)

let AUDEQ_SPHERE3_TOPOLOGY = prove
 (`blind_sphere3_topology = subtopology euclidean (sphere(vec 0:real^4,&1))`,
  REWRITE_TAC[blind_sphere3_topology; blind_sphere3]);;

(* ------------------------------------------------------------------------- *)
(* Locally Euclidean: real^3 versus open subsets of real^3.                  *)
(* ------------------------------------------------------------------------- *)

let AUDEQ_LOCALLY_EUCLIDEAN_EQ = prove
 (`!top:A topology.
        locally_euclidean_space (:3) top <=> blind_locally_euclidean_3 top`,
  GEN_TAC THEN
  REWRITE_TAC[locally_euclidean_space; blind_locally_euclidean_3] THEN
  EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THENL
   [DISCH_THEN(X_CHOOSE_THEN `U:A->bool` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`U:A->bool`; `(:real^3)`] THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:A->bool`; `v:real^3->bool`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HOMEOMORPHIC_SPACE]) THEN
  DISCH_THEN(X_CHOOSE_TAC `f:A->real^3`) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HOMEOMORPHIC_IMP_SURJECTIVE_MAP) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HOMEOMORPHIC_IMP_CONTINUOUS_MAP) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TOPSPACE_SUBTOPOLOGY;
                              TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]) THEN
  SUBGOAL_THEN `(f:A->real^3) x IN v` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `(f:A->real^3) x`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `{y:A | y IN topspace top INTER u /\
                     (f:A->real^3) y IN ball(f x,r)}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `u:A->bool` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `{y:A | y IN topspace top INTER u /\ (f:A->real^3) y IN ball(f x,r)} =
      {y | y IN topspace (subtopology top u) /\ f y IN ball(f x,r)}`
    SUBST1_TAC THENL
     [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
    EXISTS_TAC `subtopology euclidean (v:real^3->bool)` THEN
    ASM_SIMP_TAC[OPEN_SUBSET; OPEN_BALL];
    ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER; CENTRE_IN_BALL] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  TRANS_TAC HOMEOMORPHIC_SPACE_TRANS
   `subtopology euclidean (ball((f:A->real^3) x,r))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    GEN_REWRITE_TAC RAND_CONV [GSYM SUBTOPOLOGY_UNIV] THEN
    ASM_SIMP_TAC[HOMEOMORPHIC_SPACE_EUCLIDEAN; HOMEOMORPHIC_BALL_UNIV]] THEN
  MATCH_MP_TAC HOMEOMORPHIC_MAP_IMP_HOMEOMORPHIC_SPACE THEN
  EXISTS_TAC `f:A->real^3` THEN
  MP_TAC(ISPECL [`subtopology top (u:A->bool)`;
                 `subtopology euclidean (v:real^3->bool)`; `f:A->real^3`;
                 `{y:A | y IN topspace top INTER u /\
                         (f:A->real^3) y IN ball(f x,r)}`;
                 `ball((f:A->real^3) x,r)`] HOMEOMORPHIC_MAP_SUBTOPOLOGIES) THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY;
                  TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(u:A->bool) INTER {y:A | y IN topspace top INTER u /\
                             (f:A->real^3) y IN ball(f x,r)} =
    {y:A | y IN topspace top INTER u /\ (f:A->real^3) y IN ball(f x,r)} /\
    v INTER ball((f:A->real^3) x,r) = ball(f x,r)`
   (fun th -> REWRITE_TAC[th]) THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Second countability of compact locally Euclidean spaces.                  *)
(* ------------------------------------------------------------------------- *)

let AUDEQ_SECOND_COUNTABLE_EUCLIDEAN = prove
 (`second_countable (euclidean:(real^N)topology)`,
  REWRITE_TAC[second_countable; GSYM OPEN_IN] THEN
  MP_TAC UNIV_SECOND_COUNTABLE THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:(real^N->bool)->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `x:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `u:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  ASM SET_TAC[]);;

let AUDEQ_COMPACT_LOCALLY_SECOND_COUNTABLE = prove
 (`!top:A topology.
        compact_space top /\
        (!x. x IN topspace top
             ==> ?u. open_in top u /\ x IN u /\
                     second_countable (subtopology top u))
        ==> second_countable top`,
  GEN_TAC THEN REWRITE_TAC[COMPACT_SPACE_ALT] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `{u:A->bool | open_in top u /\ second_countable (subtopology top u)}`) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL
   [SIMP_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?B:(A->bool)->(A->bool)->bool.
        !v. v IN V
            ==> COUNTABLE (B v) /\
                (!w. w IN B v ==> open_in (subtopology top v) w) /\
                (!u x. open_in (subtopology top v) u /\ x IN u
                       ==> ?w. w IN B v /\ x IN w /\ w SUBSET u)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
    X_GEN_TAC `v:A->bool` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM second_countable] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[second_countable] THEN
  EXISTS_TAC `UNIONS (IMAGE (B:(A->bool)->(A->bool)->bool) V)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COUNTABLE_UNIONS THEN
    ASM_SIMP_TAC[COUNTABLE_IMAGE; FINITE_IMP_COUNTABLE; FORALL_IN_IMAGE];
    REWRITE_TAC[FORALL_IN_UNIONS; FORALL_IN_IMAGE; IMP_CONJ;
                RIGHT_FORALL_IMP_THM] THEN
    X_GEN_TAC `v:A->bool` THEN DISCH_TAC THEN
    X_GEN_TAC `w:A->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `v:A->bool` THEN
    ASM SET_TAC[];
    MAP_EVERY X_GEN_TAC [`u:A->bool`; `x:A`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `?v:A->bool. v IN V /\ x IN v` STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `v:A->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`v INTER u:A->bool`; `x:A`] o
               last o CONJUNCTS) THEN
    ASM_SIMP_TAC[OPEN_IN_SUBTOPOLOGY_INTER_OPEN; IN_INTER] THEN
    REWRITE_TAC[UNIONS_IMAGE; IN_ELIM_THM] THEN ASM SET_TAC[]]);;

let AUDEQ_BLIND_LOCALLY_EUCLIDEAN_SECOND_COUNTABLE = prove
 (`!top:A topology.
        compact_space top /\ blind_locally_euclidean_3 top
        ==> second_countable top`,
  GEN_TAC THEN REWRITE_TAC[blind_locally_euclidean_3] THEN STRIP_TAC THEN
  MATCH_MP_TAC AUDEQ_COMPACT_LOCALLY_SECOND_COUNTABLE THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:A->bool`; `v:real^3->bool`] THEN STRIP_TAC THEN
  EXISTS_TAC `u:A->bool` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP HOMEOMORPHIC_SPACE_SECOND_COUNTABILITY) THEN
  MATCH_MP_TAC SECOND_COUNTABLE_SUBTOPOLOGY THEN
  REWRITE_TAC[AUDEQ_SECOND_COUNTABLE_EUCLIDEAN]);;

(* ------------------------------------------------------------------------- *)
(* Continuity on the unit square [0,1] x [0,1].                              *)
(* ------------------------------------------------------------------------- *)

let AUDEQ_CONTINUOUS_MAP_II_FST_SND = prove
 (`continuous_map
    (prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                   (subtopology euclideanreal (real_interval[&0,&1])),
     euclideanreal) FST /\
   continuous_map
    (prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                   (subtopology euclideanreal (real_interval[&0,&1])),
     euclideanreal) SND`,
  REWRITE_TAC[PROD_TOPOLOGY_SUBTOPOLOGY] THEN
  SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY; CONTINUOUS_MAP_FST;
           CONTINUOUS_MAP_SND]);;

(* Continuity of real expressions in FST z and SND z built from constants,   *)
(* min, max, +, - and multiplication by constants (SIMP_TAC gives up on      *)
(* deeper nestings of these conditional rules).                              *)

let AUDEQ_REAL_CONTINUITY_TAC =
  REPEAT((MATCH_MP_TAC CONTINUOUS_MAP_REAL_MIN ORELSE
          MATCH_MP_TAC CONTINUOUS_MAP_REAL_MAX ORELSE
          MATCH_MP_TAC CONTINUOUS_MAP_REAL_ADD ORELSE
          MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB ORELSE
          MATCH_MP_TAC CONTINUOUS_MAP_REAL_LMUL) THEN TRY CONJ_TAC) THEN
  REWRITE_TAC[GEN_ALL CONTINUOUS_MAP_REAL_CONST;
              AUDEQ_CONTINUOUS_MAP_II_FST_SND];;

let AUDEQ_CONTINUOUS_MAP_SQUARE_REPARAM = prove
 (`!top (h:real#real->A) (f:real#real->real) (g:real#real->real).
        continuous_map
         (prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                        (subtopology euclideanreal (real_interval[&0,&1])),
          top) h /\
        continuous_map
         (prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                        (subtopology euclideanreal (real_interval[&0,&1])),
          euclideanreal) f /\
        continuous_map
         (prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                        (subtopology euclideanreal (real_interval[&0,&1])),
          euclideanreal) g /\
        (!s t. s IN real_interval[&0,&1] /\ t IN real_interval[&0,&1]
               ==> f(s,t) IN real_interval[&0,&1] /\
                   g(s,t) IN real_interval[&0,&1])
        ==> continuous_map
             (prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                            (subtopology euclideanreal (real_interval[&0,&1])),
              top)
             (\z. h(f z,g z))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z. (h:real#real->A)((f:real#real->real) z,(g:real#real->real) z)) =
    h o (\z. f z,g z)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC
   `prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                  (subtopology euclideanreal (real_interval[&0,&1]))` THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_PAIRED; CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_PROD_TOPOLOGY;
              TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; FORALL_PAIR_THM;
              IN_CROSS] THEN
  ASM_SIMP_TAC[]);;

let AUDEQ_UNIT_INTERVAL_ENDS = prove
 (`&0 IN real_interval[&0,&1] /\ &1 IN real_interval[&0,&1]`,
  REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC);;

let AUDEQ_LOOP_PROP_TOPSPACE = prove
 (`!a:A. !h k. (!x. x IN topspace
                     (subtopology euclideanreal (real_interval[&0,&1]))
                     ==> h x = k x)
               ==> ((\q:real->A. q(&0) = a /\ q(&1) = a) h <=>
                    (\q:real->A. q(&0) = a /\ q(&1) = a) k)`,
  REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
  MESON_TAC[AUDEQ_UNIT_INTERVAL_ENDS]);;

let AUDEQ_HOMOTOPIC_WITH_MONO = prove
 (`!P Q X Y (f:A->B) g.
        homotopic_with P (X,Y) f g /\ (!h. P h ==> Q h)
        ==> homotopic_with Q (X,Y) f g`,
  REWRITE_TAC[homotopic_with] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* From a free homotopy h of a loop p to the constant loop at p(0) (through  *)
(* loops: h(s,1) = h(s,0)) to a homotopy with the base point fixed.  Stage   *)
(* 1: K = h o phi with phi(s,t) = (min(3t,s,3-3t), clamp((3t-s)/(3-2s))),    *)
(* from p to the loop m(t) = h(min(3t,1,3-3t),0), which runs along the base *)
(* point path s -> h(s,0) and back.  Stage 2: m retracts along that path.    *)
(* ------------------------------------------------------------------------- *)

let AUDEQ_LOOP_STAGE1 = prove
 (`!top (p:real->A) (h:real#real->A).
        continuous_map
         (prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                        (subtopology euclideanreal (real_interval[&0,&1])),
          top) h /\
        (!t. h(&0,t) = p t) /\ (!t. h(&1,t) = p(&0)) /\
        (!s. s IN real_interval[&0,&1] ==> h(s,&1) = h(s,&0)) /\
        p(&1) = p(&0)
        ==> homotopic_with (\q. q(&0) = p(&0) /\ q(&1) = p(&0))
              (subtopology euclideanreal (real_interval[&0,&1]),top)
              p (\t. h(min (&3 * t) (min (&1) (&3 - &3 * t)),&0))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\q:real->A. q(&0) = p(&0) /\ q(&1) = p(&0)`;
    `subtopology euclideanreal (real_interval[&0,&1])`;
    `top:A topology`; `p:real->A`;
    `\t. (h:real#real->A)(min (&3 * t) (min (&1) (&3 - &3 * t)),&0)`]
   HOMOTOPIC_WITH) THEN
  REWRITE_TAC[AUDEQ_LOOP_PROP_TOPSPACE] THEN DISCH_THEN SUBST1_TAC THEN
  EXISTS_TAC
   `\z. (h:real#real->A)
         (min (&3 * SND z) (min (FST z) (&3 - &3 * SND z)),
          max (&0) (min (&1) ((&3 * SND z - FST z) / (&3 - &2 * FST z))))` THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; IN_REAL_INTERVAL] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC AUDEQ_CONTINUOUS_MAP_SQUARE_REPARAM THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT CONJ_TAC THENL
     [AUDEQ_REAL_CONTINUITY_TAC;
      MATCH_MP_TAC CONTINUOUS_MAP_REAL_MAX THEN
      REWRITE_TAC[GEN_ALL CONTINUOUS_MAP_REAL_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_REAL_MIN THEN
      REWRITE_TAC[GEN_ALL CONTINUOUS_MAP_REAL_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_REAL_DIV THEN
      CONJ_TAC THENL [AUDEQ_REAL_CONTINUITY_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [AUDEQ_REAL_CONTINUITY_TAC; ALL_TAC] THEN
      REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; FORALL_PAIR_THM; IN_CROSS;
                  TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; IN_REAL_INTERVAL] THEN
      REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    X_GEN_TAC `x:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `min (&3 * x) (min (&0) (&3 - &3 * x)) = &0 /\
      max (&0) (min (&1) ((&3 * x - &0) / (&3 - &2 * &0))) = x`
     (fun th -> ASM_REWRITE_TAC[th]) THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `(&3 * x - &0) / (&3 - &2 * &0) = x`] THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `x:real` THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ARITH `&3 - &2 * &1 = &1`; REAL_DIV_1] THEN
    ASM_CASES_TAC `&3 * x - &1 <= &0` THENL
     [AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `x <= &2 / &3` THENL
     [SUBGOAL_THEN `min (&3 * x) (min (&1) (&3 - &3 * x)) = &1`
       (fun th -> ASM_REWRITE_TAC[th]) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `min (&3 * x) (min (&1) (&3 - &3 * x)) = &3 - &3 * x /\
      max (&0) (min (&1) (&3 * x - &1)) = &1`
     (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < &3 - &2 * s` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `min (&3 * &0) (min s (&3 - &3 * &0)) = &0 /\
      max (&0) (min (&1) ((&3 * &0 - s) / (&3 - &2 * s))) = &0 /\
      min (&3 * &1) (min s (&3 - &3 * &1)) = &0 /\
      max (&0) (min (&1) ((&3 * &1 - s) / (&3 - &2 * s))) = &1`
     (fun th -> ASM_REWRITE_TAC[th]) THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `(&3 * &0 - s) / (&3 - &2 * s) <= &0` MP_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `&1 <= (&3 * &1 - s) / (&3 - &2 * s)` MP_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC]]]);;

let AUDEQ_LOOP_STAGE2 = prove
 (`!top (p:real->A) (h:real#real->A).
        continuous_map
         (prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                        (subtopology euclideanreal (real_interval[&0,&1])),
          top) h /\
        (!t. h(&0,t) = p t)
        ==> homotopic_with (\q. q(&0) = p(&0) /\ q(&1) = p(&0))
              (subtopology euclideanreal (real_interval[&0,&1]),top)
              (\t. h(min (&3 * t) (min (&1) (&3 - &3 * t)),&0))
              (\t. p(&0))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[homotopic_with] THEN
  EXISTS_TAC
   `\z. (h:real#real->A)
         ((&1 - FST z) * min (&3 * SND z) (min (&1) (&3 - &3 * SND z)),&0)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC AUDEQ_CONTINUOUS_MAP_SQUARE_REPARAM THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_REAL_MUL THEN CONJ_TAC THEN
      AUDEQ_REAL_CONTINUITY_TAC;
      AUDEQ_REAL_CONTINUITY_TAC;
      MAP_EVERY X_GEN_TAC [`s:real`; `t:real`] THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `&0 <= min (&3 * t) (min (&1) (&3 - &3 * t)) /\
        min (&3 * t) (min (&1) (&3 - &3 * t)) <= &1`
      STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_LE_REFL; REAL_POS] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC]];
    REWRITE_TAC[REAL_SUB_RZERO; REAL_MUL_LID];
    ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_LZERO];
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_RID; REAL_SUB_RZERO;
                REAL_SUB_REFL] THEN
    REWRITE_TAC[REAL_ARITH `min (&0) (min (&1) (&3)) = &0 /\
                            min (&3) (min (&1) (&0)) = &0`] THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO]]);;

(* ------------------------------------------------------------------------- *)
(* Simple connectivity: the two definitions agree.                           *)
(* ------------------------------------------------------------------------- *)

let AUDEQ_SIMPLY_CONNECTED_IMP_PATH_CONNECTED = prove
 (`!top:A topology. simply_connected_space top ==> path_connected_space top`,
  GEN_TAC THEN REWRITE_TAC[simply_connected_space] THEN DISCH_TAC THEN
  REWRITE_TAC[PATH_CONNECTED_SPACE_IFF_PATH_COMPONENT] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology euclideanreal (real_interval[&0,&1])`;
                 `top:A topology`; `x:A`; `y:A`] HOMOTOPIC_CONSTANT_MAPS) THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; REAL_INTERVAL_EQ_EMPTY] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC AUDEQ_HOMOTOPIC_WITH_MONO THEN
  EXISTS_TAC `\r:real->A. r(&1) = r(&0)` THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[PATH_IN_CONST]);;

let AUDEQ_PATH_IN_START = prove
 (`!top (p:real->A). path_in top p ==> p(&0) IN topspace top`,
  REWRITE_TAC[path_in] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
  MP_TAC AUDEQ_UNIT_INTERVAL_ENDS THEN SET_TAC[]);;

let AUDEQ_SIMPLY_CONNECTED_IMP_BLIND = prove
 (`!top:A topology.
        ~(topspace top = {}) /\ simply_connected_space top
        ==> blind_simply_connected_space top`,
  GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[blind_simply_connected_space;
               AUDEQ_SIMPLY_CONNECTED_IMP_PATH_CONNECTED] THEN
  X_GEN_TAC `p:real->A` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p:real->A`; `\t:real. (p:real->A)(&0)`] o
    REWRITE_RULE[simply_connected_space]) THEN
  ASM_SIMP_TAC[PATH_IN_CONST; AUDEQ_PATH_IN_START] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real#real->A` STRIP_ASSUME_TAC o
             REWRITE_RULE[homotopic_with]) THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_TRANS THEN
  EXISTS_TAC
   `\t. (h:real#real->A)(min (&3 * t) (min (&1) (&3 - &3 * t)),&0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC AUDEQ_LOOP_STAGE1 THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    MATCH_MP_TAC AUDEQ_LOOP_STAGE2 THEN ASM_REWRITE_TAC[]]);;

let AUDEQ_BLIND_IMP_SIMPLY_CONNECTED = prove
 (`!top:A topology.
        blind_simply_connected_space top
        ==> ~(topspace top = {}) /\ simply_connected_space top`,
  GEN_TAC THEN REWRITE_TAC[blind_simply_connected_space] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[simply_connected_space] THEN
  MAP_EVERY X_GEN_TAC [`p:real->A`; `q:real->A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `homotopic_with (\r:real->A. r(&1) = r(&0))
      (subtopology euclideanreal (real_interval[&0,&1]),top)
      (\t. p(&0)) (\t. q(&0))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`(p:real->A)(&0)`; `(q:real->A)(&0)`] o
      GEN_REWRITE_RULE I [path_connected_space]) THEN
    ASM_SIMP_TAC[AUDEQ_PATH_IN_START] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real->A` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[homotopic_with] THEN
    EXISTS_TAC `\z:real#real. (g:real->A)(FST z)` THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_OF_FST] THEN
    DISJ2_TAC THEN ASM_REWRITE_TAC[GSYM path_in];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_TRANS THEN
  EXISTS_TAC `\t:real. (p:real->A)(&0)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC AUDEQ_HOMOTOPIC_WITH_MONO THEN
    EXISTS_TAC `\r:real->A. r(&0) = p(&0) /\ r(&1) = p(&0)` THEN
    ASM_SIMP_TAC[] THEN MESON_TAC[];
    MATCH_MP_TAC HOMOTOPIC_WITH_TRANS THEN
    EXISTS_TAC `\t:real. (q:real->A)(&0)` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[HOMOTOPIC_WITH_SYM] THEN
    MATCH_MP_TAC AUDEQ_HOMOTOPIC_WITH_MONO THEN
    EXISTS_TAC `\r:real->A. r(&0) = q(&0) /\ r(&1) = q(&0)` THEN
    ASM_SIMP_TAC[] THEN MESON_TAC[]]);;

let AUDEQ_SIMPLY_CONNECTED_EQ = prove
 (`!top:A topology.
        ~(topspace top = {}) /\ simply_connected_space top <=>
        blind_simply_connected_space top`,
  MESON_TAC[AUDEQ_SIMPLY_CONNECTED_IMP_BLIND;
            AUDEQ_BLIND_IMP_SIMPLY_CONNECTED]);;

(* ------------------------------------------------------------------------- *)
(* The topological headline statements are equivalent.                      *)
(* ------------------------------------------------------------------------- *)

let AUDEQ_TOP_HYPOTHESES_EQ = prove
 (`!top:A topology.
        (hausdorff_space top /\ locally_euclidean_space (:3) top /\
         compact_space top /\ ~(topspace top = {}) /\
         simply_connected_space top) <=>
        blind_closed_topological_3_manifold top /\
        blind_simply_connected_space top`,
  GEN_TAC THEN
  REWRITE_TAC[blind_closed_topological_3_manifold;
              blind_topological_3_manifold] THEN
  REWRITE_TAC[GSYM AUDEQ_SIMPLY_CONNECTED_EQ;
              GSYM AUDEQ_LOCALLY_EUCLIDEAN_EQ] THEN
  MP_TAC(SPEC `top:A topology`
    AUDEQ_BLIND_LOCALLY_EUCLIDEAN_SECOND_COUNTABLE) THEN
  REWRITE_TAC[GSYM AUDEQ_LOCALLY_EUCLIDEAN_EQ] THEN
  CONV_TAC TAUT);;

let POINCARE_TOP_BLIND_EQUIV = prove
 (`!u:A->bool. POINCARE_STATEMENT u <=> BLIND_POINCARE_TOP u`,
  REWRITE_TAC[POINCARE_STATEMENT; BLIND_POINCARE_TOP;
              AUDEQ_TOP_HYPOTHESES_EQ; AUDEQ_SPHERE3_TOPOLOGY]);;

(* ------------------------------------------------------------------------- *)
(* Smooth maps.  On open sets the blind class blind_ck (partial              *)
(* derivatives at points) agrees with continuously_differentiable (Frechet   *)
(* derivatives within the set).  Generic lemmas: smoothness is local, one-   *)
(* sided inverses force injective derivatives, a smooth map with injective   *)
(* derivative and a left inverse has open image and smooth inverse there     *)
(* (inverse function theorem SMOOTH_INVERSE_FUNCTION_THEOREM of the vendored *)
(* Navier-Stokes library), and the two notions of smooth atlas agree.        *)
(* ------------------------------------------------------------------------- *)

let AUDEQ_BLIND_CK_EQ = prove
 (`!n s (f:real^M->real^N).
        open s ==> (blind_ck n s f <=> continuously_differentiable n s f)`,
  INDUCT_TAC THEN REWRITE_TAC[blind_ck; CONTINUOUSLY_DIFFERENTIABLE_0] THEN
  MAP_EVERY X_GEN_TAC [`s:real^M->bool`; `f:real^M->real^N`] THEN
  DISCH_TAC THEN ASM_SIMP_TAC[] THEN EQ_TAC THENL
   [STRIP_TAC THEN ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_WITHIN_OPEN] THEN
    EXISTS_TAC `\x. frechet_derivative (f:real^M->real^N) (at x)` THEN
    ASM_SIMP_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    X_GEN_TAC `h:real^M` THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_EQ_OPEN THEN
    EXISTS_TAC
     `\x. vsum (1..dimindex(:M))
               (\k. (h:real^M)$k %
                    frechet_derivative (f:real^M->real^N) (at x) (basis k))` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC LINEAR_APPLY_EXPAND THEN REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_VSUM_OPEN THEN
      ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_CMUL_OPEN THEN
      ASM_SIMP_TAC[]];
    DISCH_TAC THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
       [MATCH_MP CONTINUOUSLY_DIFFERENTIABLE_WITHIN_OPEN
         (ASSUME `open(s:real^M->bool)`)]) THEN
      REWRITE_TAC[differentiable] THEN ASM_MESON_TAC[];
      REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`n:num`; `s:real^M->bool`; `f:real^M->real^N`]
        CONTINUOUSLY_DIFFERENTIABLE_FRECHET) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th])]]);;

let AUDEQ_BLIND_SMOOTH_EQ = prove
 (`!s (f:real^M->real^N).
        open s ==> (blind_smooth_on s f <=> smooth_map_on s f)`,
  SIMP_TAC[blind_smooth_on; smooth_map_on; AUDEQ_BLIND_CK_EQ]);;

let AUDEQ_SMOOTH_MAP_ON_EQ = prove
 (`!s (f:real^M->real^N) g.
        open s /\ (!x. x IN s ==> f x = g x) /\ smooth_map_on s f
        ==> smooth_map_on s g`,
  REWRITE_TAC[smooth_map_on] THEN
  MESON_TAC[CONTINUOUSLY_DIFFERENTIABLE_EQ_OPEN]);;

let AUDEQ_SMOOTH_MAP_ON_LOCAL = prove
 (`!s (f:real^M->real^N).
        open s /\
        (!x. x IN s
             ==> ?t. open t /\ x IN t /\ t SUBSET s /\ smooth_map_on t f)
        ==> smooth_map_on s f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[smooth_map_on] THEN
  X_GEN_TAC `n:num` THEN
  MP_TAC(ISPECL [`n:num`; `s:real^M->bool`; `f:real^M->real^N`]
    CONTINUOUSLY_DIFFERENTIABLE_LOCAL_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_MESON_TAC[smooth_map_on]);;

(* ------------------------------------------------------------------------- *)
(* Derivatives: local equality, one-sided inverses, determinants.            *)
(* ------------------------------------------------------------------------- *)

let AUDEQ_HAS_DERIVATIVE_LOCAL = prove
 (`!W (f:real^M->real^N) g f' y.
        open W /\ y IN W /\ (!w. w IN W ==> f w = g w) /\
        (f has_derivative f') (at y)
        ==> (g has_derivative f') (at y)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `f:real^M->real^N` THEN
  MP_TAC(ISPEC `W:real^M->bool` OPEN_CONTAINS_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `y:real^M`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
  ASM_REWRITE_TAC[IN_BALL] THEN ASM_MESON_TAC[DIST_SYM]);;

let AUDEQ_LEFT_INVERSE_DERIVATIVE_INJ = prove
 (`!W (p:real^M->real^N) (q:real^N->real^M) y h.
        open W /\ y IN W /\ p differentiable (at y) /\
        q differentiable (at (p y)) /\
        (!w. w IN W ==> q(p w) = w) /\
        frechet_derivative p (at y) h = vec 0
        ==> h = vec 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `((q:real^N->real^M) o (p:real^M->real^N) has_derivative
     frechet_derivative q (at (p y)) o frechet_derivative p (at y)) (at y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC DIFF_CHAIN_AT THEN
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((q:real^N->real^M) o (p:real^M->real^N) has_derivative (\h. h)) (at y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC AUDEQ_HAS_DERIVATIVE_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`W:real^M->bool`; `\w:real^M. w`] THEN
    ASM_SIMP_TAC[HAS_DERIVATIVE_ID; o_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(q:real^N->real^M) o (p:real^M->real^N)`;
                 `frechet_derivative (q:real^N->real^M) (at (p(y:real^M))) o
                  frechet_derivative (p:real^M->real^N) (at y)`;
                 `y:real^M`] FRECHET_DERIVATIVE_AT) THEN
  MP_TAC(ISPECL [`(q:real^N->real^M) o (p:real^M->real^N)`;
                 `\h:real^M. h`; `y:real^M`] FRECHET_DERIVATIVE_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  DISCH_THEN(MP_TAC o C AP_THM `h:real^M`) THEN
  ASM_REWRITE_TAC[o_THM] THEN
  MP_TAC(ISPEC `frechet_derivative (q:real^N->real^M) (at (p(y:real^M)))`
    LINEAR_0) THEN
  ASM_SIMP_TAC[LINEAR_FRECHET_DERIVATIVE] THEN MESON_TAC[]);;

let AUDEQ_DERIVATIVE_INJ_COMPOSE = prove
 (`!W (p:real^M->real^N) (k:real^M->real^P) (d:real^P->real^N) y h.
        open W /\ y IN W /\ k differentiable (at y) /\
        d differentiable (at (k y)) /\
        (!w. w IN W ==> p w = d(k w)) /\
        (!h. frechet_derivative p (at y) h = vec 0 ==> h = vec 0) /\
        frechet_derivative k (at y) h = vec 0
        ==> h = vec 0`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  SUBGOAL_THEN
   `((p:real^M->real^N) has_derivative
     frechet_derivative (d:real^P->real^N) (at (k(y:real^M))) o
     frechet_derivative (k:real^M->real^P) (at y)) (at y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC AUDEQ_HAS_DERIVATIVE_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`W:real^M->bool`;
                          `(d:real^P->real^N) o (k:real^M->real^P)`] THEN
    ASM_SIMP_TAC[o_THM] THEN MATCH_MP_TAC DIFF_CHAIN_AT THEN
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  ASM_REWRITE_TAC[o_THM] THEN
  MP_TAC(ISPEC
    `frechet_derivative (d:real^P->real^N) (at ((k:real^M->real^P) y))`
    LINEAR_0) THEN
  ASM_SIMP_TAC[LINEAR_FRECHET_DERIVATIVE]);;

let AUDEQ_INJECTIVE_LINEAR_DET = prove
 (`!f:real^N->real^N.
        linear f /\ (!h. f h = vec 0 ==> h = vec 0)
        ==> ~(det(matrix f) = &0)`,
  REWRITE_TAC[GSYM HOMOGENEOUS_LINEAR_EQUATIONS_DET] THEN
  SIMP_TAC[MATRIX_WORKS] THEN MESON_TAC[]);;

(* A smooth map with injective derivative and a left inverse G on an open    *)
(* set has open image, and G is smooth on the image.                         *)

let AUDEQ_SMOOTH_GLOBAL_INVERSE = prove
 (`!W (h:real^N->real^N) (G:real^N->real^N).
        open W /\ smooth_map_on W h /\
        (!w v. w IN W /\ frechet_derivative h (at w) v = vec 0 ==> v = vec 0) /\
        (!w. w IN W ==> G(h w) = w)
        ==> open (IMAGE h W) /\ smooth_map_on (IMAGE h W) G`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!w. w IN W
        ==> ?u. open u /\ (h:real^N->real^N) w IN u /\ u SUBSET IMAGE h W /\
                smooth_map_on u (G:real^N->real^N)`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`h:real^N->real^N`; `W:real^N->bool`; `w:real^N`]
      SMOOTH_INVERSE_FUNCTION_THEOREM) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC AUDEQ_INJECTIVE_LINEAR_DET THEN
      ASM_MESON_TAC[LINEAR_FRECHET_DERIVATIVE; SMOOTH_MAP_ON_DIFFERENTIABLE];
      ALL_TAC] THEN
    REWRITE_TAC[diffeomorphism_on; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC
     [`t:real^N->bool`; `u:real^N->bool`; `g':real^N->real^N`] THEN
    STRIP_TAC THEN EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC AUDEQ_SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `g':real^N->real^N` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(g':real^N->real^N) z IN W /\ (h:real^N->real^N)(g' z) = z`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (h:real^N->real^N) W)` ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [OPEN_SUBOPEN] THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC[];
    ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC AUDEQ_SMOOTH_MAP_ON_LOCAL THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE]);;

(* ------------------------------------------------------------------------- *)
(* Charts.                                                                   *)
(* ------------------------------------------------------------------------- *)

let AUDEQ_CHART_IMAGE_OPEN_GEN = prove
 (`!top (U:A->bool) (phi:A->real^N) W.
        open_in top U /\ open (IMAGE phi U) /\
        homeomorphic_map (subtopology top U,
                          subtopology euclidean (IMAGE phi U)) phi /\
        open_in top W /\ W SUBSET U
        ==> open (IMAGE phi W)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN
  EXISTS_TAC `IMAGE (phi:A->real^N) U` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_OPEN_MAP) THEN
  REWRITE_TAC[open_map] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC OPEN_IN_SUBSET_TOPSPACE THEN ASM_REWRITE_TAC[]);;

let AUDEQ_CHART_PREIMAGE_OPEN = prove
 (`!top atlas (u:A->bool) (c:A->real^N) top' (f:A->B) v.
        smooth_manifold_atlas top atlas /\ (u,c) IN atlas /\
        continuous_map (top,top') f /\ open_in top' v
        ==> open (IMAGE c {x | x IN u /\ f x IN v})`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CHART_IMAGE_OPEN THEN
  MAP_EVERY EXISTS_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `u:A->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `u:A->bool`; `c:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `{x:A | x IN u /\ (f:A->B) x IN v} =
    u INTER {x | x IN topspace top /\ f x IN v}`
  SUBST1_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The two notions of smooth atlas agree; atlases make spaces locally        *)
(* Euclidean in the blind sense.                                             *)
(* ------------------------------------------------------------------------- *)

let AUDEQ_ATLAS_EQ = prove
 (`!top (atlas:(A->bool)#(A->real^3)->bool).
        smooth_manifold_atlas top atlas <=> blind_smooth_atlas_3 top atlas`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[smooth_manifold_atlas; blind_smooth_atlas_3; FORALL_PAIR_THM;
              blind_chart_3; blind_smoothly_compatible_3] THEN
  ASM_CASES_TAC
   `!U (phi:A->real^3).
        (U,phi) IN atlas
        ==> open_in top U /\ open (IMAGE phi U) /\
            homeomorphic_map (subtopology top U,
                              subtopology euclidean (IMAGE phi U)) phi` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!U (phi:A->real^3) V (psi:A->real^3).
        (U,phi) IN atlas /\ (V,psi) IN atlas
        ==> open (IMAGE phi (U INTER V))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC AUDEQ_CHART_IMAGE_OPEN_GEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `U:A->bool`] THEN
    REWRITE_TAC[INTER_SUBSET] THEN ASM_MESON_TAC[OPEN_IN_INTER];
    ALL_TAC] THEN
  AP_TERM_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`U:A->bool`; `phi:A->real^3`; `V:A->bool`; `psi:A->real^3`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`U:A->bool`; `phi:A->real^3`; `V:A->bool`; `psi:A->real^3`]) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `g:real^3->real^3` THEN
  (SUBGOAL_THEN `open (IMAGE (phi:A->real^3) (U INTER V))` ASSUME_TAC THENL
    [ASM_MESON_TAC[]; ASM_SIMP_TAC[AUDEQ_BLIND_SMOOTH_EQ]]));;

let AUDEQ_ATLAS_IMP_BLIND_LOCALLY_EUCLIDEAN = prove
 (`!top (atlas:(A->bool)#(A->real^3)->bool).
        smooth_manifold_atlas top atlas ==> blind_locally_euclidean_3 top`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[blind_locally_euclidean_3] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `x:A` o CONJUNCT1 o CONJUNCT2 o
    GEN_REWRITE_RULE I [smooth_manifold_atlas]) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^3`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:(A->bool)#(A->real^3)->bool`;
                 `U:A->bool`; `phi:A->real^3`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`U:A->bool`; `IMAGE (phi:A->real^3) U`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HOMEOMORPHIC_MAP_IMP_HOMEOMORPHIC_SPACE THEN
  EXISTS_TAC `phi:A->real^3` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The smooth form.  The blind stereographic atlas is the atlas              *)
(* sphere3_atlas of pc_mfd_examples.ml; a smooth immersion into real^4 that  *)
(* is a homeomorphism onto the sphere is the same as a diffeomorphism onto   *)
(* the sphere with its stereographic atlas (smooth in charts both ways).     *)
(* ------------------------------------------------------------------------- *)

let AUDEQ_BLIND_SPHERE3_ATLAS = prove
 (`blind_sphere3_atlas = sphere3_atlas`,
  REWRITE_TAC[blind_sphere3_atlas; sphere3_atlas; blind_sphere3] THEN
  SUBGOAL_THEN `blind_stereo_north = stereo3_n /\ blind_stereo_south = stereo3_s`
   (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[FUN_EQ_THM; blind_stereo_north; blind_stereo_south;
              stereo3_n; stereo3_s]);;

let AUDEQ_SPHERE3_ATLAS_CHART = prove
 (`!v (d:real^4->real^3).
        (v,d) IN sphere3_atlas
        ==> ?t. open t /\ v SUBSET t /\ smooth_map_on t d /\
                smooth_map_on (:real^3) (chart_inv (v,d)) /\
                (!x. x IN v ==> chart_inv (v,d) (d x) = x) /\
                (!y. chart_inv (v,d) y IN v /\ d(chart_inv (v,d) y) = y)`,
  REWRITE_TAC[sphere3_atlas; IN_INSERT; NOT_IN_EMPTY; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[STEX_SPHERE3_CHART_INV] THENL
   [EXISTS_TAC `{x:real^4 | x$4 < &1}` THEN REWRITE_TAC[STEX_STEREO3_N_CHART];
    EXISTS_TAC `{x:real^4 | x$4 > -- &1}` THEN
    REWRITE_TAC[STEX_STEREO3_S_CHART]]);;

let AUDEQ_SPHERE3_CHART_OPEN = prove
 (`!v (d:real^4->real^3).
        (v,d) IN sphere3_atlas
        ==> open_in (subtopology euclidean (sphere(vec 0:real^4,&1))) v /\
            v SUBSET sphere(vec 0,&1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`;
                 `sphere3_atlas`; `v:real^4->bool`; `d:real^4->real^3`]
    SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[SPHERE3_ATLAS] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]);;

let AUDEQ_SPHERE3_ATLAS_COVER = prove
 (`!y. y IN sphere(vec 0:real^4,&1)
       ==> ?v (d:real^4->real^3). (v,d) IN sphere3_atlas /\ y IN v`,
  MP_TAC SPHERE3_ATLAS THEN
  REWRITE_TAC[smooth_manifold_atlas; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Ours implies blind: the immersion is smooth in charts, and its inverse is *)
(* smooth in charts by the inverse function theorem.                         *)
(* ------------------------------------------------------------------------- *)

let AUDEQ_IMMERSION_CHART_SMOOTH = prove
 (`!top (atlas:(A->bool)#(A->real^3)->bool) (f:A->real^4) u c v d k.
        smooth_manifold_atlas top atlas /\ (u,c) IN atlas /\
        continuous_map (top,subtopology euclidean (sphere(vec 0,&1))) f /\
        (v,d) IN sphere3_atlas /\
        smooth_map_on (IMAGE c u) k /\ (!x. x IN u ==> k(c x) = f x)
        ==> open (IMAGE c {x | x IN u /\ f x IN v}) /\
            smooth_map_on (IMAGE c {x | x IN u /\ f x IN v}) (d o k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`v:real^4->bool`; `d:real^4->real^3`]
    AUDEQ_SPHERE3_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^4->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`v:real^4->bool`; `d:real^4->real^3`]
    AUDEQ_SPHERE3_CHART_OPEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `open (IMAGE (c:A->real^3) {x | x IN u /\ (f:A->real^4) x IN v})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC AUDEQ_CHART_PREIMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:(A->bool)#(A->real^3)->bool`;
      `subtopology euclidean (sphere(vec 0:real^4,&1))`] THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `t:real^4->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN ASM SET_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (c:A->real^3) u` THEN ASM_REWRITE_TAC[] THEN
    SET_TAC[]]);;

let AUDEQ_IMMERSION_IMP_FORWARD = prove
 (`!top (atlas:(A->bool)#(A->real^3)->bool) (f:A->real^4).
        smooth_manifold_atlas top atlas /\ smooth_immersion_into atlas f /\
        continuous_map (top,subtopology euclidean (sphere(vec 0,&1))) f
        ==> blind_smooth_map_3 (top,atlas)
              (subtopology euclidean (sphere(vec 0,&1)),sphere3_atlas) f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[blind_smooth_map_3] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC
   [`u:A->bool`; `c:A->real^3`; `v:real^4->bool`; `d:real^4->real^3`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:A->bool`; `c:A->real^3`] o
    GEN_REWRITE_RULE I [smooth_immersion_into]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->real^4` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(d:real^4->real^3) o (k:real^3->real^4)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:(A->bool)#(A->real^3)->bool`;
                 `f:A->real^4`; `u:A->bool`; `c:A->real^3`;
                 `v:real^4->bool`; `d:real^4->real^3`; `k:real^3->real^4`]
    AUDEQ_IMMERSION_CHART_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[AUDEQ_BLIND_SMOOTH_EQ; o_THM]);;

let AUDEQ_IMMERSION_IMP_BACKWARD = prove
 (`!top (atlas:(A->bool)#(A->real^3)->bool) (f:A->real^4) g.
        smooth_manifold_atlas top atlas /\ smooth_immersion_into atlas f /\
        homeomorphic_maps (top,subtopology euclidean (sphere(vec 0,&1))) (f,g)
        ==> blind_smooth_map_3
              (subtopology euclidean (sphere(vec 0,&1)),sphere3_atlas)
              (top,atlas) g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic_maps]) THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN STRIP_TAC THEN
  REWRITE_TAC[blind_smooth_map_3] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC
   [`v:real^4->bool`; `d:real^4->real^3`; `u:A->bool`; `c:A->real^3`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:A->bool`; `c:A->real^3`] o
    GEN_REWRITE_RULE I [smooth_immersion_into]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->real^4` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`v:real^4->bool`; `d:real^4->real^3`]
    AUDEQ_SPHERE3_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^4->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`v:real^4->bool`; `d:real^4->real^3`]
    AUDEQ_SPHERE3_CHART_OPEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:(A->bool)#(A->real^3)->bool`;
                 `u:A->bool`; `c:A->real^3`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(u:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:(A->bool)#(A->real^3)->bool`;
                 `f:A->real^4`; `u:A->bool`; `c:A->real^3`;
                 `v:real^4->bool`; `d:real^4->real^3`; `k:real^3->real^4`]
    AUDEQ_IMMERSION_CHART_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`IMAGE (c:A->real^3) {x | x IN u /\ (f:A->real^4) x IN v}`;
    `(d:real^4->real^3) o (k:real^3->real^4)`;
    `\z:real^3. (c:A->real^3)((g:real^4->A)(chart_inv (v,d) z))`]
   AUDEQ_SMOOTH_GLOBAL_INVERSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE;
                  IN_ELIM_THM] THEN
      X_GEN_TAC `x:A` THEN REPEAT DISCH_TAC THEN X_GEN_TAC `h:real^3` THEN
      DISCH_TAC THEN MATCH_MP_TAC(INST_TYPE [`:3`,`:M`; `:4`,`:N`; `:3`,`:P`]
        AUDEQ_DERIVATIVE_INJ_COMPOSE) THEN
      MAP_EVERY EXISTS_TAC
       [`IMAGE (c:A->real^3) {x | x IN u /\ (f:A->real^4) x IN v}`;
        `k:real^3->real^4`; `(d:real^4->real^3) o (k:real^3->real^4)`;
        `chart_inv (v:real^4->bool,d:real^4->real^3)`;
        `(c:A->real^3) x`] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[];
        MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
        EXISTS_TAC
         `IMAGE (c:A->real^3) {x | x IN u /\ (f:A->real^4) x IN v}` THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
        ASM_MESON_TAC[];
        MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
        EXISTS_TAC `(:real^3)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
        REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; o_THM] THEN
        ASM_SIMP_TAC[];
        ASM_MESON_TAC[FUN_IN_IMAGE]];
      REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; o_THM] THEN
      X_GEN_TAC `x:A` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
      AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]];
    STRIP_TAC] THEN
  EXISTS_TAC `\z:real^3. (c:A->real^3)((g:real^4->A)(chart_inv (v,d) z))` THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN
   `open (IMAGE (d:real^4->real^3) {y | y IN v /\ (g:real^4->A) y IN u})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC AUDEQ_CHART_PREIMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC
     [`subtopology euclidean (sphere(vec 0:real^4,&1))`;
      `sphere3_atlas`; `top:A topology`] THEN
    ASM_REWRITE_TAC[SPHERE3_ATLAS];
    ALL_TAC] THEN
  ASM_SIMP_TAC[AUDEQ_BLIND_SMOOTH_EQ] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
  EXISTS_TAC `IMAGE ((d:real^4->real^3) o (k:real^3->real^4))
                    (IMAGE (c:A->real^3) {x | x IN u /\ (f:A->real^4) x IN v})` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^4` THEN STRIP_TAC THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; o_THM] THEN
  EXISTS_TAC `(c:A->real^3)((g:real^4->A) y)` THEN
  SUBGOAL_THEN `(f:A->real^4)((g:real^4->A) y) = y` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN EXISTS_TAC `(g:real^4->A) y` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Blind implies ours: f composed with chart inverses is smooth (it is the   *)
(* inverse stereographic map applied to a chart expression of f), and its    *)
(* derivative is injective because the chart expression of the inverse map  *)
(* is a left inverse.                                                         *)
(* ------------------------------------------------------------------------- *)

let AUDEQ_BLIND_LOCAL_CHART_DATA = prove
 (`!top (atlas:(A->bool)#(A->real^3)->bool) (f:A->real^4) g U phi x.
        smooth_manifold_atlas top atlas /\
        homeomorphic_maps (top,subtopology euclidean (sphere(vec 0,&1))) (f,g) /\
        blind_smooth_map_3 (top,atlas)
          (subtopology euclidean (sphere(vec 0,&1)),sphere3_atlas) f /\
        blind_smooth_map_3
          (subtopology euclidean (sphere(vec 0,&1)),sphere3_atlas)
          (top,atlas) g /\
        (U,phi) IN atlas /\ x IN U
        ==> ?v d G G'.
              (v,d) IN sphere3_atlas /\ f x IN v /\
              open (IMAGE phi {x | x IN U /\ f x IN v}) /\
              smooth_map_on (IMAGE phi {x | x IN U /\ f x IN v}) G /\
              (!x. x IN U /\ f x IN v ==> G(phi x) = d(f x)) /\
              open (IMAGE d {z | z IN v /\ g z IN U}) /\
              smooth_map_on (IMAGE d {z | z IN v /\ g z IN U}) G' /\
              (!z. z IN v /\ g z IN U ==> G'(d z) = phi(g z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic_maps]) THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:(A->bool)#(A->real^3)->bool`;
                 `U:A->bool`; `phi:A->real^3`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(f:A->real^4) x IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`;
                   `subtopology euclidean (sphere(vec 0:real^4,&1))`;
                   `f:A->real^4`] CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; SUBSET; FORALL_IN_IMAGE] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP AUDEQ_SPHERE3_ATLAS_COVER) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`v:real^4->bool`; `d:real^4->real^3`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`v:real^4->bool`; `d:real^4->real^3`]
    AUDEQ_SPHERE3_CHART_OPEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `open (IMAGE (phi:A->real^3) {x | x IN U /\ (f:A->real^4) x IN v}) /\
    open (IMAGE (d:real^4->real^3) {z | z IN v /\ (g:real^4->A) z IN U})`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC AUDEQ_CHART_PREIMAGE_OPEN THENL
     [MAP_EVERY EXISTS_TAC
       [`top:A topology`; `atlas:(A->bool)#(A->real^3)->bool`;
        `subtopology euclidean (sphere(vec 0:real^4,&1))`];
      MAP_EVERY EXISTS_TAC
       [`subtopology euclidean (sphere(vec 0:real^4,&1))`;
        `sphere3_atlas`; `top:A topology`]] THEN
    ASM_REWRITE_TAC[SPHERE3_ATLAS];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`v:real^4->bool`; `d:real^4->real^3`; `U:A->bool`; `phi:A->real^3`] o
   CONJUNCT2 o GEN_REWRITE_RULE I [blind_smooth_map_3]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`U:A->bool`; `phi:A->real^3`; `v:real^4->bool`; `d:real^4->real^3`] o
   CONJUNCT2 o GEN_REWRITE_RULE I [blind_smooth_map_3]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `G:real^3->real^3` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `G':real^3->real^3` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC
   [`v:real^4->bool`; `d:real^4->real^3`; `G:real^3->real^3`;
    `G':real^3->real^3`] THEN
  ASM_SIMP_TAC[GSYM AUDEQ_BLIND_SMOOTH_EQ]);;

let AUDEQ_BLIND_DIFFEO_IMP_IMMERSION = prove
 (`!top (atlas:(A->bool)#(A->real^3)->bool) (f:A->real^4) g.
        smooth_manifold_atlas top atlas /\
        homeomorphic_maps (top,subtopology euclidean (sphere(vec 0,&1))) (f,g) /\
        blind_smooth_map_3 (top,atlas)
          (subtopology euclidean (sphere(vec 0,&1)),sphere3_atlas) f /\
        blind_smooth_map_3
          (subtopology euclidean (sphere(vec 0,&1)),sphere3_atlas)
          (top,atlas) g
        ==> smooth_immersion_into atlas f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic_maps]) THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN STRIP_TAC THEN
  REWRITE_TAC[smooth_immersion_into] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^3`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:(A->bool)#(A->real^3)->bool`;
                 `U:A->bool`; `phi:A->real^3`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:(A->bool)#(A->real^3)->bool`;
                 `U:A->bool`; `phi:A->real^3`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  EXISTS_TAC `(f:A->real^4) o chart_inv (U:A->bool,phi:A->real^3)` THEN
  ASM_SIMP_TAC[o_THM] THEN
  SUBGOAL_THEN
   `!x. x IN U
        ==> ?v d G G'.
              (v,d) IN sphere3_atlas /\ (f:A->real^4) x IN v /\
              open (IMAGE (phi:A->real^3) {x | x IN U /\ f x IN v}) /\
              smooth_map_on (IMAGE phi {x | x IN U /\ f x IN v}) G /\
              (!x. x IN U /\ f x IN v ==> G(phi x) = d(f x)) /\
              open (IMAGE d {z | z IN v /\ (g:real^4->A) z IN U}) /\
              smooth_map_on (IMAGE d {z | z IN v /\ g z IN U}) G' /\
              (!z. z IN v /\ g z IN U ==> G'(d z) = phi(g z))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC AUDEQ_BLIND_LOCAL_CHART_DATA THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:(A->bool)#(A->real^3)->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (IMAGE (phi:A->real^3) U)
                  ((f:A->real^4) o chart_inv (U,phi))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC AUDEQ_SMOOTH_MAP_ON_LOCAL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`v:real^4->bool`; `d:real^4->real^3`;
                         `G:real^3->real^3`; `G':real^3->real^3`] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`v:real^4->bool`; `d:real^4->real^3`]
      AUDEQ_SPHERE3_ATLAS_CHART) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^4->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `IMAGE (phi:A->real^3) {x | x IN U /\ (f:A->real^4) x IN v}` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      SET_TAC[];
      MATCH_MP_TAC AUDEQ_SMOOTH_MAP_ON_EQ THEN
      EXISTS_TAC `chart_inv (v:real^4->bool,d:real^4->real^3) o
                  (G:real^3->real^3)` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; o_THM] THEN
        ASM_SIMP_TAC[];
        MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
        EXISTS_TAC `(:real^3)` THEN
        ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV]]];
    ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN X_GEN_TAC `h:real^3` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`v:real^4->bool`; `d:real^4->real^3`;
                       `G:real^3->real^3`; `G':real^3->real^3`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`v:real^4->bool`; `d:real^4->real^3`]
    AUDEQ_SPHERE3_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^4->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(phi:A->real^3) x IN
                IMAGE phi {x | x IN U /\ (f:A->real^4) x IN v}`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!h. frechet_derivative (G:real^3->real^3) (at ((phi:A->real^3) x)) h =
        vec 0 ==> h = vec 0`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC(INST_TYPE [`:3`,`:M`; `:3`,`:N`]
      AUDEQ_LEFT_INVERSE_DERIVATIVE_INJ) THEN
    MAP_EVERY EXISTS_TAC
     [`IMAGE (phi:A->real^3) {x | x IN U /\ (f:A->real^4) x IN v}`;
      `G:real^3->real^3`; `G':real^3->real^3`; `(phi:A->real^3) x`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[SMOOTH_MAP_ON_DIFFERENTIABLE];
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC
       `IMAGE (d:real^4->real^3) {z | z IN v /\ (g:real^4->A) z IN U}` THEN
      ASM_SIMP_TAC[] THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
      EXISTS_TAC `(f:A->real^4) x` THEN ASM_SIMP_TAC[] THEN ASM SET_TAC[];
      REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `y:A` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
      SUBGOAL_THEN `(g:real^4->A)((f:A->real^4) y) = y` ASSUME_TAC THENL
       [ASM SET_TAC[]; ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  MATCH_MP_TAC(INST_TYPE [`:3`,`:M`; `:3`,`:N`; `:4`,`:P`]
    AUDEQ_DERIVATIVE_INJ_COMPOSE) THEN
  MAP_EVERY EXISTS_TAC
   [`IMAGE (phi:A->real^3) {x | x IN U /\ (f:A->real^4) x IN v}`;
    `G:real^3->real^3`; `(f:A->real^4) o chart_inv (U:A->bool,phi:A->real^3)`;
    `d:real^4->real^3`; `(phi:A->real^3) x`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (phi:A->real^3) U` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `t:real^4->bool` THEN ASM_SIMP_TAC[o_THM] THEN ASM SET_TAC[];
    REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; o_THM] THEN ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The smooth headline statements are equivalent.                           *)
(* ------------------------------------------------------------------------- *)

let AUDEQ_SMOOTH_CONCLUSION_EQ = prove
 (`!top (atlas:(A->bool)#(A->real^3)->bool).
        smooth_manifold_atlas top atlas
        ==> ((?f:A->real^4.
                smooth_immersion_into atlas f /\
                homeomorphic_map
                  (top,subtopology euclidean (sphere(vec 0,&1))) f) <=>
             blind_diffeomorphic_3 (top,atlas)
               (blind_sphere3_topology,blind_sphere3_atlas))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[blind_diffeomorphic_3; AUDEQ_SPHERE3_TOPOLOGY;
              AUDEQ_BLIND_SPHERE3_ATLAS] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `f:A->real^4` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `g:real^4->A` o
      GEN_REWRITE_RULE I [HOMEOMORPHIC_MAP_MAPS]) THEN
    MAP_EVERY EXISTS_TAC [`f:A->real^4`; `g:real^4->A`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC AUDEQ_IMMERSION_IMP_FORWARD THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[homeomorphic_maps];
      MATCH_MP_TAC AUDEQ_IMMERSION_IMP_BACKWARD THEN
      EXISTS_TAC `f:A->real^4` THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`f:A->real^4`; `g:real^4->A`] THEN STRIP_TAC THEN
    EXISTS_TAC `f:A->real^4` THEN CONJ_TAC THENL
     [MATCH_MP_TAC AUDEQ_BLIND_DIFFEO_IMP_IMMERSION THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `g:real^4->A`] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[HOMEOMORPHIC_MAP_MAPS] THEN
      EXISTS_TAC `g:real^4->A` THEN ASM_REWRITE_TAC[]]]);;

let AUDEQ_SMOOTH_HYPOTHESES_EQ = prove
 (`!top (atlas:(A->bool)#(A->real^3)->bool).
        (hausdorff_space top /\ smooth_manifold_atlas top atlas /\
         compact_space top /\ ~(topspace top = {}) /\
         simply_connected_space top) <=>
        blind_closed_smooth_3_manifold top atlas /\
        blind_simply_connected_space top`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[blind_closed_smooth_3_manifold; blind_smooth_3_manifold] THEN
  REWRITE_TAC[GSYM AUDEQ_SIMPLY_CONNECTED_EQ; GSYM AUDEQ_ATLAS_EQ] THEN
  MP_TAC(SPEC `top:A topology`
    AUDEQ_BLIND_LOCALLY_EUCLIDEAN_SECOND_COUNTABLE) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:(A->bool)#(A->real^3)->bool`]
    AUDEQ_ATLAS_IMP_BLIND_LOCALLY_EUCLIDEAN) THEN
  CONV_TAC TAUT);;

let POINCARE_SMOOTH_BLIND_EQUIV = prove
 (`!u:A->bool. POINCARE_SMOOTH_STATEMENT u <=> BLIND_POINCARE_SMOOTH u`,
  GEN_TAC THEN REWRITE_TAC[POINCARE_SMOOTH_STATEMENT; BLIND_POINCARE_SMOOTH] THEN
  REWRITE_TAC[GSYM AUDEQ_SMOOTH_HYPOTHESES_EQ] THEN
  AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
  MATCH_MP_TAC(TAUT `(h ==> (c1 <=> c2)) ==> ((h ==> c1) <=> (h ==> c2))`) THEN
  STRIP_TAC THEN MATCH_MP_TAC AUDEQ_SMOOTH_CONCLUSION_EQ THEN
  ASM_REWRITE_TAC[]);;


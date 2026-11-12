(* ========================================================================= *)
(* pc_moi_lt_charts: MANIFOLD_CHARTS : |- MOI_LT_MANIFOLD_CHARTS, a          *)
(* statement term of the C25 loop theorem (pc_moi_loop_stmt.ml): small PL   *)
(* charts of a combinatorial 3-manifold with boundary onto the unit ball or *)
(* the unit half ball, from the half-space charts MOI_FMB_CHART of          *)
(* pc_moi_fnd_m3b.ml.                                                        *)
(* ========================================================================= *)

needs "src/pc_moi_loop_stmt.ml";;
needs "src/pc_moi_fnd_m3b.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Scaling a ball and a half ball onto the unit ones.                        *)
(* ------------------------------------------------------------------------- *)

let MOI_LCH_INV_LT = prove
 (`!r n. &0 < r ==> (inv r * n < &1 <=> n < r)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LT_LDIV_EQ; REAL_MUL_LID]);;

let MOI_LCH_SCALE_BALL = prove
 (`!(q:real^3) r. &0 < r
     ==> IMAGE (\z. inv r % (z - q)) (ball(q,r)) = ball(vec 0,&1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_BALL_0; IN_BALL] THEN
  X_GEN_TAC `w:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`; MOI_LCH_INV_LT] THEN
    UNDISCH_TAC `dist(q:real^3,z) < r` THEN CONV_TAC NORM_ARITH;
    DISCH_TAC THEN EXISTS_TAC `q + r % (w:real^3)` THEN CONJ_TAC THENL
     [REWRITE_TAC[VECTOR_ARITH `(q + r % w) - q:real^3 = r % w`; VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
      REWRITE_TAC[dist; VECTOR_ARITH `q - (q + r % w):real^3 = --(r % w)`; NORM_NEG;
                  NORM_MUL] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      ASM_SIMP_TAC[REAL_LT_LMUL_EQ]]]);;

let MOI_LCH_SCALE_HALF = prove
 (`!(q:real^3) r. &0 < r /\ q$3 = &0
     ==> IMAGE (\z. inv r % (z - q)) (ball(q,r) INTER {z:real^3 | &0 <= z$3}) =
         ball(vec 0,&1) INTER {z:real^3 | &0 <= z$3}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!z:real^3. (&0 <= (inv r % (z - q))$3 <=> &0 <= z$3)` ASSUME_TAC THENL
   [GEN_TAC THEN ASM_REWRITE_TAC[VECTOR_MUL_COMPONENT; VECTOR_SUB_COMPONENT;
                                 REAL_SUB_RZERO] THEN
    ASM_SIMP_TAC[REAL_LE_MUL_EQ; REAL_LT_INV_EQ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`q:real^3`; `r:real`] MOI_LCH_SCALE_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
  X_GEN_TAC `w:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    CONJ_TAC THENL [EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[]; ASM_MESON_TAC[]];
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC)
      ASSUME_TAC) THEN
    EXISTS_TAC `z:real^3` THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Shrinking a half-space chart: a radius r with the ball inside the chart   *)
(* open set and the inverse image of the half ball inside ball(y,e).        *)
(* ------------------------------------------------------------------------- *)

let MOI_LCH_RADIUS = prove
 (`!(W:real^N->bool) (p:real^N->real^3) p' oo y e b.
     homeomorphism (W,IMAGE p W) (p,p') /\ open oo /\
     IMAGE p W = oo INTER {z:real^3 | &0 <= z$3} /\ y IN W /\ &0 < e /\ &0 < b
     ==> ?r. &0 < r /\ r <= b /\ ball(p y,r) SUBSET oo /\
             !z. z IN ball(p y,r) /\ &0 <= z$3 ==> p' z IN ball(y,e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `(p:real^N->real^3) y IN IMAGE p W` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^N->real^3) y IN oo` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `oo:real^3->bool` OPEN_CONTAINS_BALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `(p:real^N->real^3) y`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "r1"))) THEN
  MP_TAC(ASSUME `(p':real^3->real^N) continuous_on IMAGE (p:real^N->real^3) W`) THEN
  REWRITE_TAC[continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `(p:real^N->real^3) y`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "d"))) THEN
  EXISTS_TAC `min r1 (min d b)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC;
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball((p:real^N->real^3) y,r1)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC;
    X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_BALL] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN oo` ASSUME_TAC THENL
     [REMOVE_THEN "r1" (MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
      REWRITE_TAC[IN_BALL] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REMOVE_THEN "d" (MP_TAC o SPEC `z:real^3`) THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ANTS_TAC THENL
     [ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(p':real^3->real^N) (p y) = y` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[DIST_SYM]]);;

(* ------------------------------------------------------------------------- *)
(* The rescaling z |-> inv r % (z - q) is a PL homeomorphism of any locally  *)
(* polyhedral set onto its image, with inverse w |-> q + r % w; it keeps    *)
(* the plane z$3 = 0 when q$3 = 0; balls of radius r <= q$3 lie in z$3 > 0. *)
(* ------------------------------------------------------------------------- *)

let MOI_LCH_SCALE_INV = prove
 (`!(q:real^3) r z w. &0 < r
     ==> q + r % (inv r % (z - q)) = z /\ inv r % ((q + r % w) - q) = w`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(r = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC; VECTOR_ARITH `(q + a:real^3) - q = a`] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_MUL_LINV; VECTOR_MUL_LID] THEN
  VECTOR_ARITH_TAC);;

let MOI_LCH_SCALE_PLH = prove
 (`!(s:real^3->bool) q r.
     &0 < r /\ locally_polyhedral s
     ==> pl_homeomorphism (s,IMAGE (\z. inv r % (z - q)) s)
                          ((\z. inv r % (z - q)),(\w. q + r % w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `homeomorphism (s:real^3->bool,IMAGE (\z. inv r % (z - q)) s)
                  ((\z. inv r % (z - q)),(\w. q + r % w))`
  ASSUME_TAC THENL
   [REWRITE_TAC[homeomorphism] THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[MOI_LCH_SCALE_INV];
      MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
      REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
      REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[MOI_LCH_SCALE_INV];
      REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
      ASM_SIMP_TAC[MOI_LCH_SCALE_INV; IMAGE_ID];
      MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN REWRITE_TAC[CONTINUOUS_ON_ID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_map_on (s:real^3->bool) (\z. inv r % (z - q))` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `\z:real^3. (\x:real^3. inv r % x) z + --(inv r % q)` THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN BETA_TAC THEN VECTOR_ARITH_TAC;
      MATCH_MP_TAC PL_MAP_ON_AFFINE THEN ASM_REWRITE_TAC[LINEAR_SCALING]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[pl_homeomorphism] THEN
  MATCH_MP_TAC PL_MAP_ON_HOMEOMORPHISM_INVERSE THEN
  EXISTS_TAC `s:real^3->bool` THEN
  EXISTS_TAC `\z:real^3. inv r % (z - q)` THEN ASM_REWRITE_TAC[]);;

let MOI_LCH_SCALE_ZERO = prove
 (`!(q:real^3) r z. &0 < r /\ q$3 = &0
     ==> ((inv r % (z - q))$3 = &0 <=> z$3 = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[VECTOR_MUL_COMPONENT; VECTOR_SUB_COMPONENT; REAL_SUB_RZERO;
                  REAL_ENTIRE; REAL_INV_EQ_0] THEN
  ASM_REAL_ARITH_TAC);;

let MOI_LCH_BALL_POS = prove
 (`!(q:real^3) r z. r <= q$3 /\ z IN ball(q,r) ==> &0 < z$3`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_BALL; dist] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`q - z:real^3`; `3`] COMPONENT_LE_NORM) THEN
  REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Small round charts at every point of a finite combinatorial 3-manifold    *)
(* with boundary: rescale the half-space chart of MOI_FMB_CHART on a small   *)
(* ball around the image point.                                              *)
(* ------------------------------------------------------------------------- *)

let MOI_LCH_MANIFOLD_CHARTS = prove
 (`!(c:(real^N->bool)->bool) y e.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\ y IN UNIONS c /\ &0 < e
     ==> ?u (h:real^N->real^3) h'.
           open_in (subtopology euclidean (UNIONS c)) u /\ y IN u /\ u SUBSET ball(y,e) /\
           pl_homeomorphism (u,IMAGE h u) (h,h') /\ h y = vec 0 /\
           ((~(y IN complex_boundary c) /\ u INTER complex_boundary c = {} /\
             IMAGE h u = ball(vec 0,&1)) \/
            (y IN complex_boundary c /\
             IMAGE h u = ball(vec 0,&1) INTER {z:real^3 | &0 <= z$3} /\
             IMAGE h (u INTER complex_boundary c) = IMAGE h u INTER {z:real^3 | z$3 = &0}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `y:real^N`] MOI_FMB_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:real^N->bool` (X_CHOOSE_THEN `p:real^N->real^3`
    (X_CHOOSE_THEN `p':real^3->real^N` (X_CHOOSE_THEN `oo:real^3->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "img")
     (LABEL_TAC "bd"))))))))))) THEN
  SUBGOAL_THEN `!x:real^N. x IN W ==> (p:real^N->real^3) x IN oo /\ &0 <= (p x)$3`
  (LABEL_TAC "half") THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(p:real^N->real^3) x IN IMAGE p W` MP_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      USE_THEN "img" SUBST1_TAC THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM]];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `&0 <= ((p:real^N->real^3) y)$3` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?b. &0 < b /\ (&0 < ((p:real^N->real^3) y)$3 ==> b <= (p y)$3)`
    (X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC) THENL
   [ASM_CASES_TAC `&0 < ((p:real^N->real^3) y)$3` THEN ASM_REWRITE_TAC[] THENL
     [EXISTS_TAC `((p:real^N->real^3) y)$3` THEN ASM_REWRITE_TAC[REAL_LE_REFL];
      EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`W:real^N->bool`; `p:real^N->real^3`; `p':real^3->real^N`;
                 `oo:real^3->bool`; `y:real^N`; `e:real`; `b:real`] MOI_LCH_RADIUS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rad"))))) THEN
  ABBREV_TAC `u = {x:real^N | x IN W /\ (p:real^N->real^3) x IN ball(p y,r)}` THEN
  SUBGOAL_THEN `(u:real^N->bool) SUBSET W` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN u` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN ASM_REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL]; ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (UNIONS c)) (u:real^N->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `W:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "u" THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `locally_polyhedral (u:real^N->bool)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_OPEN] o
      check (fun th -> concl th =
        `open_in (subtopology euclidean (UNIONS c)) (u:real^N->bool)`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOCALLY_POLYHEDRAL_INTER_OPEN THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOCALLY_POLYHEDRAL_LF_COMPLEX THEN
    ASM_MESON_TAC[combinatorial_manifold_with_boundary];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `homeomorphism (u:real^N->bool,IMAGE (p:real^N->real^3) u) (p,p')`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`W:real^N->bool`; `IMAGE (p:real^N->real^3) W`] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [MATCH_MP_TAC IMAGE_SUBSET THEN FIRST_ASSUM ACCEPT_TAC; REFL_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_map_on (u:real^N->bool) (p:real^N->real^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `W:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_map_on (IMAGE (p:real^N->real^3) u) (p':real^3->real^N)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_HOMEOMORPHISM_INVERSE THEN
    MAP_EVERY EXISTS_TAC [`u:real^N->bool`; `p:real^N->real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_homeomorphism (IMAGE (p:real^N->real^3) u,
                      IMAGE (\z:real^3. inv r % (z - p y)) (IMAGE p u))
                     ((\z:real^3. inv r % (z - p y)),(\w:real^3. p y + r % w))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LCH_SCALE_PLH THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_MAP_ON_IMP_LOCALLY_POLYHEDRAL THEN
    EXISTS_TAC `p':real^3->real^N` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `u:real^N->bool` THEN
  EXISTS_TAC `(\z:real^3. inv r % (z - (p:real^N->real^3) y)) o (p:real^N->real^3)` THEN
  EXISTS_TAC `(p':real^3->real^N) o (\w:real^3. (p:real^N->real^3) y + r % w)` THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [(* u SUBSET ball(y,e) *)
    EXPAND_TAC "u" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(p':real^3->real^N) (p x) = x` (SUBST1_TAC o SYM) THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REMOVE_THEN "rad" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "half" (MP_TAC o SPEC `x:real^N`) THEN ASM_SIMP_TAC[];
    (* the composed map is a PL homeomorphism *)
    REWRITE_TAC[IMAGE_o] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `IMAGE (p:real^N->real^3) u` THEN ASM_REWRITE_TAC[pl_homeomorphism];
    (* centre goes to the origin *)
    REWRITE_TAC[o_THM; VECTOR_SUB_REFL; VECTOR_MUL_RZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (p:real^N->real^3) u = ball(p y,r) INTER {z:real^3 | &0 <= z$3}`
  ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^3` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "half" (MP_TAC o SPEC `x:real^N`) THEN
      ASM_SIMP_TAC[];
      STRIP_TAC THEN
      SUBGOAL_THEN `(z:real^3) IN IMAGE (p:real^N->real^3) W` MP_TAC THENL
       [USE_THEN "img" SUBST1_TAC THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
        ASM_REWRITE_TAC[] THEN
        FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
          concl th = `ball((p:real^N->real^3) y,r) SUBSET oo`)) THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[IN_IMAGE] THEN MATCH_MP_TAC MONO_EXISTS THEN
        X_GEN_TAC `x:real^N` THEN
        DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `&0 < ((p:real^N->real^3) y)$3` THENL
   [DISJ1_TAC THEN
    SUBGOAL_THEN `b <= ((p:real^N->real^3) y)$3` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `r <= ((p:real^N->real^3) y)$3` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `ball((p:real^N->real^3) y,r) INTER {z:real^3 | &0 <= z$3} =
                  ball(p y,r)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM SUBSET_INTER_ABSORPTION; SUBSET; IN_ELIM_THM] THEN
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC MOI_LCH_BALL_POS THEN
      MAP_EVERY EXISTS_TAC [`(p:real^N->real^3) y`; `r:real`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "bd" (MP_TAC o C MATCH_MP (ASSUME `(y:real^N) IN W`) o
        SPEC `y:real^N`) THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
      X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(x:real^N) IN W /\ (p:real^N->real^3) x IN ball(p y,r)`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(x:real^N) IN u` THEN EXPAND_TAC "u" THEN
        REWRITE_TAC[IN_ELIM_THM];
        ALL_TAC] THEN
      USE_THEN "bd" (MP_TAC o C MATCH_MP (ASSUME `(x:real^N) IN W`) o
        SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC MOI_LCH_BALL_POS THEN
      MAP_EVERY EXISTS_TAC [`(p:real^N->real^3) y`; `r:real`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_LCH_SCALE_BALL THEN ASM_REWRITE_TAC[]];
    DISJ2_TAC THEN
    SUBGOAL_THEN `((p:real^N->real^3) y)$3 = &0` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "bd" (MP_TAC o C MATCH_MP (ASSUME `(y:real^N) IN W`) o
        SPEC `y:real^N`) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_LCH_SCALE_HALF THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `u INTER complex_boundary c =
      {x:real^N | x IN u /\ ((p:real^N->real^3) x)$3 = &0}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^N` THEN
      ASM_CASES_TAC `(x:real^N) IN u` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "bd" MATCH_MP_TAC THEN
      UNDISCH_TAC `(x:real^N) IN u` THEN UNDISCH_TAC `(u:real^N->bool) SUBSET W` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `IMAGE (p:real^N->real^3) {x:real^N | x IN u /\ ((p:real^N->real^3) x)$3 = &0} =
      IMAGE p u INTER {z:real^3 | z$3 = &0}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
    X_GEN_TAC `w:real^3` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
      CONJ_TAC THENL
       [EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[MOI_LCH_SCALE_ZERO]];
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC)
        ASSUME_TAC) THEN
      EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(w:real^3)$3 = &0` THEN ASM_SIMP_TAC[MOI_LCH_SCALE_ZERO]]]);;

(* ------------------------------------------------------------------------- *)
(* The main theorem (pc_moi_loop_stmt.ml, MOI_LT_MANIFOLD_CHARTS).           *)
(* ------------------------------------------------------------------------- *)

let MANIFOLD_CHARTS = prove
 (MOI_LT_MANIFOLD_CHARTS,
  ACCEPT_TAC MOI_LCH_MANIFOLD_CHARTS);;


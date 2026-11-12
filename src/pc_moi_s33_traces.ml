needs "src/pc_moi_s33_x2.ml";;
needs "src/pc_moi_fnd_split.ml";;
needs "src/pc_moi_fnd_rnb2.ml";;
needs "src/pc_moi_fnd_sptrace.ml";;
needs "src/pc_moi_fnd_nb2f.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* pc_moi_s33_traces: Lemmas 3-4 of 33.1 (Moise GTM 47, pp.231-232): after   *)
(* the operations every pseudo-cell meets Bd X in a single polygon bounding  *)
(* the disk E INTER X.  Main theorem                                         *)
(*   MOI_S3TR_TRACES_ANN : |- MOI_FND_SPLIT_ANNULUS_R3 ==> MOI_S33_TRACES    *)
(* (the statement MOI_S33_TRACES of pc_moi_s33_stmt.ml); the annulus split   *)
(* MOI_FND_SPLIT_ANNULUS_R3 is proved in pc_moi_fnd_splitann and             *)
(* pc_moi_fnd_annnbhd, and pc_moi_core_status combines the two.  Route: the  *)
(* traces are finitely many PL circles (MOI_S4L_CROSSING_CIRCLES); their     *)
(* disks in Int E come from Schoenflies in the open-cell chart; innermost    *)
(* circles not around the centre are removed by MOI_FND_SPLIT_DISK_R3,       *)
(* consecutive nested circles around the centre by MOI_FND_SPLIT_ANNULUS_R3, *)
(* with a thin neighbourhood so that no new trace appears (THIN_STEP); the   *)
(* annuli are PL by HOLED_RECOG and the planar annulus theorem               *)
(* MOI_S3TR_ANNULUS_THM.  The disk split MOI_FND_SPLIT_DISK_R3 is a theorem  *)
(* by composition of pc_moi_fnd_split, rnb2, sptrace and nb2f.               *)
(* ========================================================================= *)


(* ------------------------------------------------------------------------- *)
(* Crossing charts as ball charts, and the two sides of the frontier: at a  *)
(* crossing point of s with the frontier of a closed set x that is the      *)
(* closure of its interior, one open half ball of the chart lies in the     *)
(* interior of x and the other misses x.                                    *)
(* ------------------------------------------------------------------------- *)

let MOI_S3TR_CONNECTED_SIDE = prove
 (`!(c:real^3->bool) x.
     connected c /\ closed x /\ DISJOINT c (frontier x)
     ==> c SUBSET interior x \/ DISJOINT c x`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [connected]) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`interior x:real^3->bool`; `(:real^3) DIFF x`]) THEN
  ASM_REWRITE_TAC[OPEN_INTERIOR; GSYM closed] THEN
  MP_TAC(ISPEC `x:real^3->bool` INTERIOR_SUBSET) THEN
  UNDISCH_TAC `DISJOINT (c:real^3->bool) (frontier x)` THEN
  ASM_SIMP_TAC[frontier; CLOSURE_CLOSED] THEN SET_TAC[]);;

let MOI_S3TR_CROSS_BALL = prove
 (`!(s:real^3->bool) x y.
     pl_crossing_at s (frontier x) y /\ closed x /\ y IN closure (interior x)
     ==> ?u (f:real^3->real^3) g r.
           open u /\ y IN u /\ &0 < r /\
           pl_homeomorphism (u,ball(vec 0,r)) (f,g) /\ f y = vec 0 /\
           IMAGE f (s INTER u) = ball(vec 0,r) INTER {z | z$1 = &0} /\
           IMAGE f (frontier x INTER u) = ball(vec 0,r) INTER {z | z$2 = &0} /\
           (IMAGE f (x INTER u) = ball(vec 0,r) INTER {z | &0 <= z$2} \/
            IMAGE f (x INTER u) = ball(vec 0,r) INTER {z | z$2 <= &0})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_crossing_at] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u0:real^3->bool`
    (X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `g:real^3->real^3`
      STRIP_ASSUME_TAC))) STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism])
    STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?r. &0 < r /\ ball(vec 0:real^3,r) SUBSET IMAGE (f:real^3->real^3) u0`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `open (IMAGE (f:real^3->real^3) u0)` THEN
    REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_MESON_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  (* pointwise facts on the chart *)
  SUBGOAL_THEN
   `(!w. w IN u0 ==> (f:real^3->real^3) w IN IMAGE f u0 /\ (g:real^3->real^3)(f w) = w) /\
    (!z. z IN ball(vec 0,r) ==> (g:real^3->real^3) z IN u0 /\ (f:real^3->real^3)(g z) = z)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT STRIP_TAC THEN
    TRY(MATCH_MP_TAC FUN_IN_IMAGE) THEN ASM_SIMP_TAC[] THEN
    TRY(FIRST_X_ASSUM MATCH_MP_TAC) THEN
    UNDISCH_TAC `IMAGE (g:real^3->real^3) (IMAGE (f:real^3->real^3) u0) = u0` THEN
    UNDISCH_TAC `ball(vec 0:real^3,r) SUBSET IMAGE (f:real^3->real^3) u0` THEN
    UNDISCH_TAC `(z:real^3) IN ball(vec 0,r)` THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `u = {w | w IN u0 /\ (f:real^3->real^3) w IN ball(vec 0,r)}` THEN
  SUBGOAL_THEN `!w:real^3. w IN u <=> w IN u0 /\ (f:real^3->real^3) w IN ball(vec 0,r)`
  (LABEL_TAC "uu") THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `open (u:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!w. w IN u ==> (f:real^3->real^3) w IN ball(vec 0,r) /\
                    (g:real^3->real^3)(f w) = w) /\
    (!z. z IN ball(vec 0,r) ==> (g:real^3->real^3) z IN u /\
                                (f:real^3->real^3)(g z) = z) /\
    (u:real^3->bool) SUBSET u0 /\ IMAGE (f:real^3->real^3) u = ball(vec 0,r)`
  STRIP_ASSUME_TAC THENL
   [REMOVE_THEN "uu" (fun th -> REWRITE_TAC[th; SUBSET; EXTENSION; IN_IMAGE]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`u:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`;
                        `r:real`] THEN
  SUBGOAL_THEN `(y:real^3) IN u` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN ASM_REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL]; ALL_TAC] THEN
  SUBGOAL_THEN `pl_homeomorphism (u,ball(vec 0:real^3,r)) (f:real^3->real^3,g)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN CONJ_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
      MAP_EVERY EXISTS_TAC [`u0:real^3->bool`; `IMAGE (f:real^3->real^3) u0`] THEN
      ASM_REWRITE_TAC[homeomorphism];
      MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `u0:real^3->bool` THEN
      ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. IMAGE (f:real^3->real^3) (t INTER u) = IMAGE f (t INTER u0) INTER ball(vec 0,r)`
  ASSUME_TAC THENL
   [GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:real^3` THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (f:real^3->real^3) (s INTER u) = ball(vec 0,r) INTER {z | z$1 = &0} /\
    IMAGE f (frontier x INTER u) = ball(vec 0,r) INTER {z | z$2 = &0}`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ball(vec 0:real^3,r) SUBSET IMAGE (f:real^3->real^3) u0` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!w. w IN u ==> (w IN frontier x <=> ((f:real^3->real^3) w)$2 = &0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `((f:real^3->real^3) w IN IMAGE f (frontier x INTER u) <=> w IN frontier x)`
    MP_TAC THENL
     [REWRITE_TAC[IN_IMAGE; IN_INTER] THEN ASM_MESON_TAC[];
      ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN frontier x` ASSUME_TAC THENL
   [ASM_MESON_TAC[VEC_COMPONENT]; ALL_TAC] THEN
  SUBGOAL_THEN `frontier x SUBSET (x:real^3->bool) /\ DISJOINT (frontier x) (interior x)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[FRONTIER_SUBSET_CLOSED] THEN REWRITE_TAC[frontier] THEN SET_TAC[];
    ALL_TAC] THEN
  (* the two open half balls *)
  SUBGOAL_THEN
   `!sg. sg * sg = &1
         ==> (!z. z IN ball(vec 0,r) /\ &0 < sg * z$2
                  ==> (g:real^3->real^3) z IN interior x) \/
             (!z. z IN ball(vec 0,r) /\ &0 < sg * z$2
                  ==> ~((g:real^3->real^3) z IN x))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`IMAGE (g:real^3->real^3) (ball(vec 0,r) INTER {z | &0 < sg * z$2})`;
                   `x:real^3->bool`] MOI_S3TR_CONNECTED_SIDE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
          EXISTS_TAC `IMAGE (f:real^3->real^3) u0` THEN ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `ball(vec 0:real^3,r) SUBSET IMAGE (f:real^3->real^3) u0` THEN
          SET_TAC[];
          MATCH_MP_TAC CONVEX_CONNECTED THEN MATCH_MP_TAC CONVEX_INTER THEN
          REWRITE_TAC[CONVEX_BALL] THEN
          MP_TAC(ISPECL [`sg % basis 2:real^3`; `&0`] CONVEX_HALFSPACE_GT) THEN
          SIMP_TAC[DOT_LMUL; DOT_BASIS; DIMINDEX_3; ARITH] THEN
          MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
          REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN REAL_ARITH_TAC];
        REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE; IN_ELIM_THM] THEN
        X_GEN_TAC `w:real^3` THEN
        DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC)
          ASSUME_TAC) THEN
        SUBGOAL_THEN `(w:real^3) IN u /\ (f:real^3->real^3) w = z` STRIP_ASSUME_TAC THENL
         [ASM_MESON_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `((f:real^3->real^3) w)$2 = &0` MP_TAC THENL
         [ASM_MESON_TAC[]; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        UNDISCH_TAC `&0 < sg * (z:real^3)$2` THEN
        ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_LT_REFL]];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_OR THEN
    REWRITE_TAC[SUBSET; DISJOINT; EXTENSION; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM;
                NOT_IN_EMPTY; IN_IMAGE] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `&1`) THEN FIRST_X_ASSUM(MP_TAC o SPEC `-- &1`) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_MUL_LID; REAL_MUL_LNEG] THEN
  REWRITE_TAC[REAL_ARITH `&0 < --z <=> z < &0`] THEN
  DISCH_THEN DISJ_CASES_TAC THEN DISCH_THEN DISJ_CASES_TAC THENL
   [(* both halves inside: y would be interior *)
    SUBGOAL_THEN `(u:real^3->bool) SUBSET interior x` ASSUME_TAC THENL
     [MATCH_MP_TAC INTERIOR_MAXIMAL THEN ASM_REWRITE_TAC[SUBSET] THEN
      X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
      ASM_CASES_TAC `((f:real^3->real^3) w)$2 = &0` THENL
       [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
      SUBGOAL_THEN `(g:real^3->real^3)((f:real^3->real^3) w) IN interior x` MP_TAC THENL
       [FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (REAL_ARITH
          `~(a = &0) ==> &0 < a \/ a < &0`)) THEN ASM_MESON_TAC[];
        ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET]];
      ASM SET_TAC[]];
    (* lower half inside, upper half outside *)
    DISJ2_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:real^3` THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC)
        ASSUME_TAC) THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      SUBGOAL_THEN `(g:real^3->real^3) z = w` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ASM_MESON_TAC[]];
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `(g:real^3->real^3) z` THEN
      ASM_SIMP_TAC[] THEN
      ASM_CASES_TAC `(z:real^3)$2 = &0` THENL
       [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
      SUBGOAL_THEN `(z:real^3)$2 < &0` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET]]];
    (* lower half outside, upper half inside *)
    DISJ1_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:real^3` THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC)
        ASSUME_TAC) THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      SUBGOAL_THEN `(g:real^3->real^3) z = w` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ASM_MESON_TAC[]];
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `(g:real^3->real^3) z` THEN
      ASM_SIMP_TAC[] THEN
      ASM_CASES_TAC `(z:real^3)$2 = &0` THENL
       [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < (z:real^3)$2` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET]]];
    (* both halves outside: no interior point near y *)
    SUBGOAL_THEN `(u:real^3->bool) INTER interior x = {}` ASSUME_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
      X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
      ASM_CASES_TAC `((f:real^3->real^3) w)$2 = &0` THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `~((g:real^3->real^3)((f:real^3->real^3) w) IN x)` MP_TAC THENL
       [FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (REAL_ARITH
          `~(a = &0) ==> &0 < a \/ a < &0`)) THEN ASM_MESON_TAC[];
        ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`u:real^3->bool`; `interior x:real^3->bool`]
      OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:real^3) IN closure (interior x)` THEN
    UNDISCH_TAC `(y:real^3) IN u` THEN SET_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* Jordan curves in an open 2-cell bound disks inside it (Schoenflies in    *)
(* the chart).  MOI_S3TR_JORDAN_DISK repeats MOI_S3C2_JORDAN_DISK of        *)
(* pc_moi_s32_cap_b (three lines), whose load closure is much larger.        *)
(* ------------------------------------------------------------------------- *)

let MOI_S3TR_JORDAN_DISK = prove
 (`!c:real^2->bool.
     c homeomorphic sphere(vec 0:real^2,&1)
     ==> ?k k'. homeomorphism ((:real^2),(:real^2)) (k,k') /\
                IMAGE k (sphere(vec 0,&1)) = c /\
                IMAGE k (cball(vec 0,&1)) = c UNION inside c /\
                IMAGE k (ball(vec 0,&1)) = inside c`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:real^2->bool`; `vec 0:real^2`; `&1`]
    HOMEOMORPHIC_SIMPLE_PATH_IMAGE_CIRCLE_EQ) THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^1->real^2` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(c:real^2->bool) homeomorphic sphere(vec 0:real^2,&1)` THEN
  ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^2` (X_CHOOSE_THEN `f':real^2->real^2`
    ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`circlepath(vec 0:real^2,&1)`; `h:real^1->real^2`;
                 `f:real^2->real^2`; `f':real^2->real^2`] JORDAN_SCHOENFLIES) THEN
  ASM_SIMP_TAC[SIMPLE_PATH_CIRCLEPATH; PATH_IMAGE_CIRCLEPATH; REAL_POS; REAL_OF_NUM_EQ;
               ARITH_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^2->real^2` (X_CHOOSE_THEN `k':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`k:real^2->real^2`; `k':real^2->real^2`] THEN
  ASM_REWRITE_TAC[GSYM INSIDE_SPHERE] THEN
  REWRITE_TAC[GSYM SPHERE_UNION_BALL; IMAGE_UNION; INSIDE_SPHERE] THEN
  ASM_REWRITE_TAC[GSYM INSIDE_SPHERE]);;

let MOI_S3TR_CELL_DISK = prove
 (`!(m:real^N->bool) (phi:real^N->real^2) phi' j.
     homeomorphism (m,ball(vec 0,&1)) (phi,phi') /\
     j SUBSET m /\ j homeomorphic sphere(vec 0:real^2,&1)
     ==> IMAGE phi j homeomorphic sphere(vec 0:real^2,&1) /\
         IMAGE phi j UNION inside (IMAGE phi j) SUBSET ball(vec 0,&1) /\
         disk_with_boundary (IMAGE phi' (IMAGE phi j UNION inside (IMAGE phi j))) j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `IMAGE (phi:real^N->real^2) j SUBSET ball(vec 0,&1) /\
                IMAGE (phi':real^2->real^N) (IMAGE phi j) = j`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (phi:real^N->real^2) j homeomorphic sphere(vec 0:real^2,&1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHIC_TRANS THEN EXISTS_TAC `j:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
    REWRITE_TAC[homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [`phi:real^N->real^2`; `phi':real^2->real^N`] THEN
    MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`m:real^N->bool`; `ball(vec 0:real^2,&1)`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (phi:real^N->real^2) j UNION inside (IMAGE phi j) SUBSET ball(vec 0,&1)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[UNION_SUBSET] THEN MATCH_MP_TAC INSIDE_SUBSET_CONVEX THEN
    ASM_REWRITE_TAC[CONVEX_BALL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[disk_with_boundary] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MOI_S3TR_JORDAN_DISK o check (fun th ->
    concl th = `IMAGE (phi:real^N->real^2) j homeomorphic sphere(vec 0:real^2,&1)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^2->real^2` (X_CHOOSE_THEN `k':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`(phi':real^2->real^N) o (k:real^2->real^2)`;
                        `(k':real^2->real^2) o (phi:real^N->real^2)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `IMAGE (phi:real^N->real^2) j UNION inside (IMAGE phi j)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
      MAP_EVERY EXISTS_TAC [`(:real^2)`; `(:real^2)`] THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
      MAP_EVERY EXISTS_TAC [`ball(vec 0:real^2,&1)`; `m:real^N->bool`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
        ASM SET_TAC[]]];
    ASM_REWRITE_TAC[IMAGE_o]]);;


(* ------------------------------------------------------------------------- *)
(* Basic facts on the traces E INTER Bd X of an x2 neighbourhood.           *)
(* ------------------------------------------------------------------------- *)

let MOI_S3TR_PL_CIRCLE_TOP = prove
 (`!b:real^N->bool. pl_sphere 1 b ==> b homeomorphic sphere(vec 0:real^2,&1)`,
  GEN_TAC THEN REWRITE_TAC[pl_sphere; pl_homeomorphism; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`k:real^N->bool`; `f:real^N->real^N`; `g:real^N->real^N`] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC(ISPECL [`b:real^N->bool`; `relative_frontier(k:real^N->bool)`;
                       `sphere(vec 0:real^2,&1)`] HOMEOMORPHIC_TRANS) THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [`f:real^N->real^N`; `g:real^N->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sphere(vec 0:real^2,&1) = relative_frontier(cball(vec 0,&1))`
  SUBST1_TAC THENL
   [REWRITE_TAC[RELATIVE_FRONTIER_CBALL] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MATCH_MP_TAC HOMEOMORPHIC_RELATIVE_FRONTIERS_CONVEX_BOUNDED_SETS THEN
  REWRITE_TAC[CONVEX_CBALL; BOUNDED_CBALL; AFF_DIM_CBALL; DIMINDEX_2] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT; COMPACT_IMP_BOUNDED]);;

let MOI_S3TR_CMWB_FRONTIER_CLOSURE = prove
 (`!c:(real^3->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c
     ==> frontier (UNIONS c) SUBSET closure (interior (UNIONS c))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `c:(real^3->bool)->bool` COMPLEX_BOUNDARY_FRONTIER_3) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o
    GEN_REWRITE_RULE I [combinatorial_manifold_with_boundary]) THEN
  REWRITE_TAC[complex_boundary; UNIONS_SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `s:real^3->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `?r:real^3->bool. r IN c /\ aff_dim r = &3 /\ s SUBSET r`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `~({r:real^3->bool | P r} = {}) ==> ?r. P r`) THEN
    DISCH_TAC THEN UNDISCH_TAC
     `CARD {r:real^3->bool | r IN c /\ aff_dim r = &3 /\ s SUBSET r} = 1` THEN
    ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `polytope (r:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FM3_LF_POLYTOPE]; ALL_TAC] THEN
  SUBGOAL_THEN `~(interior (r:real^3->bool) = {})` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM AFF_DIM_NONEMPTY_INTERIOR_EQ; POLYTOPE_IMP_CONVEX; DIMINDEX_3];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `r:real^3->bool` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `closure (interior (r:real^3->bool))` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[CONVEX_CLOSURE_INTERIOR; POLYTOPE_IMP_CONVEX] THEN
    REWRITE_TAC[CLOSURE_SUBSET];
    MATCH_MP_TAC SUBSET_CLOSURE THEN MATCH_MP_TAC SUBSET_INTERIOR THEN
    ASM SET_TAC[]]);;

let MOI_S3TR_TRACE_FACTS = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c x u v.
     moi_s33_hd t l h e c /\ moi_s33_x2 t l h e x /\ ~(u = v) /\ segment[u,v] IN l
     ==> e(segment[u,v]) INTER frontier (UNIONS x) SUBSET
         (e(segment[u,v]) DIFF moi_s33_rim t l h u v) DELETE h(midpoint(u,v)) /\
         compact (e(segment[u,v]) INTER frontier (UNIONS x)) /\
         FINITE (components (e(segment[u,v]) INTER frontier (UNIONS x))) /\
         (!J. J IN components (e(segment[u,v]) INTER frontier (UNIONS x))
              ==> pl_sphere 1 J) /\
         (!y. y IN e(segment[u,v]) INTER frontier (UNIONS x)
              ==> pl_crossing_at (e(segment[u,v]) DIFF moi_s33_rim t l h u v)
                                 (frontier (UNIONS x)) y) /\
         closed (UNIONS x) /\
         frontier (UNIONS x) SUBSET closure (interior (UNIONS x)) /\
         h(midpoint(u,v)) IN interior (UNIONS x) /\
         e(segment[u,v]) INTER UNIONS x SUBSET e(segment[u,v]) DIFF moi_s33_rim t l h u v /\
         DISJOINT (moi_s33_rim t l h u v) (interior (IMAGE h (derived_nbhd t l)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `u:real^3`; `v:real^3`]
    MOI_S3X2_HD_EDGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s33_x2]) THEN
  ABBREV_TAC `E = (e:(real^3->bool)->real^3->bool) (segment[u,v])` THEN
  ABBREV_TAC `j = moi_s33_rim t l (h:real^3->real^3) u v` THEN
  ABBREV_TAC `p = (h:real^3->real^3) (midpoint(u,v))` THEN
  ABBREV_TAC `X = UNIONS (x:(real^3->bool)->bool)` THEN
  SUBGOAL_THEN `compact (X:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN MATCH_MP_TAC COMPACT_UNIONS THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MOI_FM3_LF_COMPACT; combinatorial_manifold_with_boundary];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier (X:real^3->bool) SUBSET X` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FRONTIER_SUBSET_COMPACT]; ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3) IN interior X` ASSUME_TAC THENL
   [UNDISCH_TAC `(p:real^3) IN IMAGE (h:real^3->real^3) (UNIONS l)` THEN
    UNDISCH_TAC `IMAGE (h:real^3->real^3) (UNIONS l) SUBSET interior X` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `DISJOINT (j:real^3->bool) (interior (IMAGE (h:real^3->real^3) (derived_nbhd t l)))`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [moi_s33_hd]) THEN
    DISCH_THEN(MP_TAC o SPECL [`u:real^3`; `v:real^3`]) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
    MP_TAC(ISPEC `IMAGE (h:real^3->real^3) (derived_nbhd t l)` frontier) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `E INTER (X:real^3->bool) SUBSET E DIFF j` ASSUME_TAC THENL
   [UNDISCH_TAC `X SUBSET interior (IMAGE (h:real^3->real^3) (derived_nbhd t l))` THEN
    UNDISCH_TAC
     `DISJOINT (j:real^3->bool) (interior (IMAGE (h:real^3->real^3) (derived_nbhd t l)))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `E INTER frontier (X:real^3->bool) SUBSET (E DIFF j) DELETE p`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `X:real^3->bool` frontier) THEN
    UNDISCH_TAC `E INTER (X:real^3->bool) SUBSET E DIFF j` THEN
    UNDISCH_TAC `(p:real^3) IN interior X` THEN
    UNDISCH_TAC `frontier (X:real^3->bool) SUBSET X` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (E INTER frontier (X:real^3->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_INTER_COMPACT THEN ASM_SIMP_TAC[COMPACT_FRONTIER];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN E INTER frontier X
        ==> pl_crossing_at (E DIFF j) (frontier (X:real^3->bool)) y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^3`; `v:real^3`; `y:real^3`] o check (fun th ->
      can (find_term ((=) `pl_crossing_at`)) (concl th) && is_forall (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`E DIFF j:real^3->bool`; `frontier X:real^3->bool`]
      MOI_S4L_CROSSING_CIRCLES) THEN
    SUBGOAL_THEN `(E DIFF j) INTER frontier X = E INTER frontier (X:real^3->bool)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `E INTER frontier (X:real^3->bool) SUBSET (E DIFF j) DELETE p` THEN
      SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    MP_TAC(ISPECL [`E DIFF j:real^3->bool`; `frontier X:real^3->bool`]
      MOI_S4L_CROSSING_CIRCLES) THEN
    SUBGOAL_THEN `(E DIFF j) INTER frontier X = E INTER frontier (X:real^3->bool)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `E INTER frontier (X:real^3->bool) SUBSET (E DIFF j) DELETE p` THEN
      SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    EXPAND_TAC "X" THEN MATCH_MP_TAC MOI_S3TR_CMWB_FRONTIER_CLOSURE THEN
    ASM_REWRITE_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* The halves of a surface at a crossing point: near a crossing point y of  *)
(* m with frontier x, m is the union of the trace line through y, a         *)
(* connected half in interior x and a connected half missing x.            *)
(* ------------------------------------------------------------------------- *)

let MOI_S3TR_PLANE_PIECES = prove
 (`!sg. convex {z:real^3 | z$1 = &0 /\ &0 < sg * z$2} /\
        convex {z:real^3 | z$1 = &0 /\ sg * z$2 < &0} /\
        convex {z:real^3 | z$1 = &0 /\ z$2 = &0} /\
        open {z:real^3 | &0 < sg * z$2} /\ open {z:real^3 | sg * z$2 < &0}`,
  GEN_TAC THEN
  SUBGOAL_THEN `!z:real^3. z$1 = basis 1 dot z /\ sg * z$2 = (sg % basis 2) dot z /\
                           z$2 = basis 2 dot z`
  (fun th -> REWRITE_TAC[th]) THENL
   [SIMP_TAC[DOT_LMUL; DOT_BASIS; DIMINDEX_3; ARITH]; ALL_TAC] THEN
  REWRITE_TAC[SET_RULE `{z:real^3 | P z /\ Q z} = {z | P z} INTER {z | Q z}`] THEN
  REWRITE_TAC[REAL_ARITH `&0 < a <=> a > &0`] THEN
  SIMP_TAC[CONVEX_INTER; CONVEX_HYPERPLANE; CONVEX_HALFSPACE_GT; CONVEX_HALFSPACE_LT;
           OPEN_HALFSPACE_GT; OPEN_HALFSPACE_LT]);;

let MOI_S3TR_CHART_HALVES = prove
 (`!(m:real^3->bool) x y.
     pl_crossing_at m (frontier x) y /\ closed x /\ y IN closure (interior x)
     ==> ?u hin hout ln.
           open u /\ y IN u /\ y IN ln /\
           connected hin /\ connected hout /\ connected ln /\
           hin SUBSET interior x /\ DISJOINT hout x /\
           m INTER u = hin UNION hout UNION ln /\
           ln = m INTER frontier x INTER u /\
           DISJOINT hin (frontier x) /\ DISJOINT hout (frontier x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3TR_CROSS_BALL) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` (X_CHOOSE_THEN `r:real`
      (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))))) THEN
  SUBGOAL_THEN
   `?sg. sg * sg = &1 /\
         IMAGE (f:real^3->real^3) (x INTER u) = ball(vec 0,r) INTER {z | &0 <= sg * z$2}`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
     [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_MUL_LID];
      EXISTS_TAC `-- &1` THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN AP_TERM_TAC THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o CONJUNCT1) THEN
  SUBGOAL_THEN
   `!t. t SUBSET ball(vec 0,r) /\ convex t ==> connected (IMAGE (g:real^3->real^3) t)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
    ASM_SIMP_TAC[CONVEX_CONNECTED] THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t SUBSET ball(vec 0,r) /\ open t ==> open (IMAGE (g:real^3->real^3) t)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `f:real^3->real^3`; `ball(vec 0:real^3,r)`;
                   `u:real^3->bool`; `t:real^3->bool`] HOMEOMORPHISM_IMP_OPEN_MAP) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[homeomorphism];
        MATCH_MP_TAC OPEN_SUBSET THEN ASM_REWRITE_TAC[]];
      ASM_MESON_TAC[OPEN_IN_OPEN_TRANS]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!w. w IN u ==> (f:real^3->real^3) w IN ball(vec 0,r) /\
                    (g:real^3->real^3)(f w) = w) /\
    (!z. z IN ball(vec 0,r) ==> (g:real^3->real^3) z IN u /\
                                (f:real^3->real^3)(g z) = z)`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. w IN u
        ==> (w IN m <=> ((f:real^3->real^3) w)$1 = &0) /\
            (w IN frontier x <=> (f w)$2 = &0) /\
            (w IN x <=> &0 <= sg * (f w)$2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `!t. (f:real^3->real^3) w IN IMAGE f (t INTER u) <=> w IN t`
    MP_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[IN_IMAGE; IN_INTER] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `m:real^3->bool` th) THEN
      MP_TAC(SPEC `frontier x:real^3->bool` th) THEN MP_TAC(SPEC `x:real^3->bool` th)) THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN ball(vec 0,r)
        ==> ((g:real^3->real^3) z IN m <=> z$1 = &0) /\
            (g z IN frontier x <=> z$2 = &0) /\
            (g z IN x <=> &0 <= sg * z$2)`
  (LABEL_TAC "gz") THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(g:real^3->real^3) z` o check (fun th ->
      can (term_match [] `!w:real^3. w IN u ==> P w`) (concl th) &&
      can (find_term (fun t -> t = `frontier (x:real^3->bool)`)) (concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`u:real^3->bool`;
    `IMAGE (g:real^3->real^3) (ball(vec 0,r) INTER {z | z$1 = &0 /\ &0 < sg * z$2})`;
    `IMAGE (g:real^3->real^3) (ball(vec 0,r) INTER {z | z$1 = &0 /\ sg * z$2 < &0})`;
    `IMAGE (g:real^3->real^3) (ball(vec 0,r) INTER {z | z$1 = &0 /\ z$2 = &0})`] THEN
  MP_TAC(SPEC `sg:real` MOI_S3TR_PLANE_PIECES) THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(sg = &0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `sg * sg = &1` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN EXISTS_TAC `vec 0:real^3` THEN
    REWRITE_TAC[CENTRE_IN_BALL; VEC_COMPONENT] THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[CONVEX_INTER; CONVEX_BALL; INTER_SUBSET];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[CONVEX_INTER; CONVEX_BALL; INTER_SUBSET];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[CONVEX_INTER; CONVEX_BALL; INTER_SUBSET];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (g:real^3->real^3) (ball(vec 0,r) INTER {z | &0 < sg * z$2})` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
      MATCH_MP_TAC INTERIOR_MAXIMAL THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
        X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
        USE_THEN "gz" (MP_TAC o C MATCH_MP (ASSUME `(z:real^3) IN ball(vec 0,r)`)) THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL; INTER_SUBSET]]];
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `w:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) MP_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "gz" (MP_TAC o C MATCH_MP (ASSUME `(z:real^3) IN ball(vec 0,r)`)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `w:real^3` THEN
    REWRITE_TAC[IN_INTER; IN_UNION; IN_IMAGE; IN_ELIM_THM] THEN EQ_TAC THENL
     [STRIP_TAC THEN
      SUBGOAL_THEN `(f:real^3->real^3) w IN ball(vec 0,r) /\ (g:real^3->real^3) (f w) = w`
      STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      USE_THEN "gz" (MP_TAC o C MATCH_MP (ASSUME `(f:real^3->real^3) w IN ball(vec 0,r)`)) THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `((f:real^3->real^3) w)$1 = &0` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_CASES_TAC `((f:real^3->real^3) w)$2 = &0` THENL
       [DISJ2_TAC THEN DISJ2_TAC THEN EXISTS_TAC `(f:real^3->real^3) w` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 < sg * ((f:real^3->real^3) w)$2 \/ sg * (f w)$2 < &0`
      DISJ_CASES_TAC THENL
       [ASM_REWRITE_TAC[REAL_ARITH `&0 < a \/ a < &0 <=> ~(a = &0)`; REAL_ENTIRE];
        DISJ1_TAC THEN EXISTS_TAC `(f:real^3->real^3) w` THEN
        ASM_REWRITE_TAC[];
        DISJ2_TAC THEN DISJ1_TAC THEN EXISTS_TAC `(f:real^3->real^3) w` THEN
        ASM_REWRITE_TAC[]];
      DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "gz" (MP_TAC o C MATCH_MP (ASSUME `(z:real^3) IN ball(vec 0,r)`)) THEN
      STRIP_TAC THEN ASM_SIMP_TAC[]];
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `w:real^3` THEN
    REWRITE_TAC[IN_INTER; IN_IMAGE; IN_ELIM_THM] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "gz" (MP_TAC o C MATCH_MP (ASSUME `(z:real^3) IN ball(vec 0,r)`)) THEN
      STRIP_TAC THEN ASM_SIMP_TAC[];
      STRIP_TAC THEN
      SUBGOAL_THEN `(f:real^3->real^3) w IN ball(vec 0,r) /\ (g:real^3->real^3) (f w) = w`
      STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      USE_THEN "gz" (MP_TAC o C MATCH_MP (ASSUME `(f:real^3->real^3) w IN ball(vec 0,r)`)) THEN
      STRIP_TAC THEN EXISTS_TAC `(f:real^3->real^3) w` THEN ASM_MESON_TAC[]];
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `w:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) MP_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "gz" (MP_TAC o C MATCH_MP (ASSUME `(z:real^3) IN ball(vec 0,r)`)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `&0 < sg * (z:real^3)$2` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `w:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) MP_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "gz" (MP_TAC o C MATCH_MP (ASSUME `(z:real^3) IN ball(vec 0,r)`)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `sg * (z:real^3)$2 < &0` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;


(* ------------------------------------------------------------------------- *)
(* The local side condition at a boundary point y of a region s of the      *)
(* surface m (s - Bd x clopen in m - Bd x, s INTER Bd x clopen in the       *)
(* trace): near y, if the region lies in x then x meets m only in s, and if *)
(* it misses x then m lies in s UNION interior x.                           *)
(* ------------------------------------------------------------------------- *)

let MOI_S3TR_LOCAL_SIDE = prove
 (`!(m:real^3->bool) x s y.
     closed x /\ y IN closure (interior x) /\
     pl_crossing_at m (frontier x) y /\ y IN s INTER frontier x /\
     s SUBSET m /\ closed s /\
     open_in (subtopology euclidean m) (s DIFF frontier x) /\
     open_in (subtopology euclidean (m INTER frontier x)) (s INTER frontier x) /\
     s SUBSET closure (s DIFF frontier x)
     ==> ?w. open w /\ y IN w /\
             (s DIFF frontier x SUBSET interior x ==> m INTER x INTER w SUBSET s) /\
             (DISJOINT (s DIFF frontier x) x ==> m INTER w SUBSET s UNION interior x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:real^3->bool`; `x:real^3->bool`; `y:real^3`]
    MOI_S3TR_CHART_HALVES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` (X_CHOOSE_THEN `hin:real^3->bool`
    (X_CHOOSE_THEN `hout:real^3->bool` (X_CHOOSE_THEN `ln:real^3->bool`
      STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq (concl th) &&
    lhs (concl th) = `ln:real^3->bool`)) THEN
  EXISTS_TAC `u:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `ln SUBSET (s:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`m INTER frontier x:real^3->bool`; `s INTER frontier x:real^3->bool`;
                   `ln:real^3->bool`] CONNECTED_SUBSET_CLOPEN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [SUBGOAL_THEN `s INTER frontier x:real^3->bool = (m INTER frontier x) INTER s`
        SUBST1_TAC THENL
         [UNDISCH_TAC `(s:real^3->bool) SUBSET m` THEN SET_TAC[];
          MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN ASM_REWRITE_TAC[]];
        UNDISCH_TAC `m INTER frontier x INTER u = (ln:real^3->bool)` THEN SET_TAC[];
        UNDISCH_TAC `(y:real^3) IN ln` THEN UNDISCH_TAC `(y:real^3) IN s INTER frontier x` THEN
        SET_TAC[]];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c. connected c /\ c SUBSET m INTER u /\ DISJOINT c (frontier x) /\
        ~(c INTER (s DIFF frontier x) = {})
        ==> c SUBSET (s:real^3->bool)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`m DIFF frontier x:real^3->bool`; `s DIFF frontier x:real^3->bool`;
                   `c:real^3->bool`] CONNECTED_SUBSET_CLOPEN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [SUBGOAL_THEN `s DIFF frontier x:real^3->bool = (m DIFF frontier x) INTER s`
        SUBST1_TAC THENL
         [UNDISCH_TAC `(s:real^3->bool) SUBSET m` THEN SET_TAC[];
          MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN ASM_REWRITE_TAC[]];
        MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN EXISTS_TAC `m:real^3->bool` THEN
        ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(s:real^3->bool) SUBSET m` THEN SET_TAC[];
        UNDISCH_TAC `(c:real^3->bool) SUBSET m INTER u` THEN
        UNDISCH_TAC `DISJOINT (c:real^3->bool) (frontier x)` THEN SET_TAC[]];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?z:real^3. z IN u /\ z IN s DIFF frontier x` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`u:real^3->bool`; `s DIFF frontier x:real^3->bool`]
      OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(s:real^3->bool) SUBSET closure (s DIFF frontier x)` THEN
    UNDISCH_TAC `(y:real^3) IN s INTER frontier x` THEN
    UNDISCH_TAC `(y:real^3) IN u` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3) IN hin UNION hout` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`m INTER (u:real^3->bool) = hin UNION hout UNION ln`;
      `m INTER frontier x INTER (u:real^3->bool) = ln`;
      `(z:real^3) IN u`; `(z:real^3) IN s DIFF frontier x`;
      `(s:real^3->bool) SUBSET m`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THEN DISCH_TAC THENL
   [SUBGOAL_THEN `(hin:real^3->bool) SUBSET s` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `m INTER (u:real^3->bool) = hin UNION hout UNION ln` THEN SET_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `z:real^3` THEN
      MAP_EVERY UNDISCH_TAC
       [`(z:real^3) IN hin UNION hout`; `DISJOINT (hout:real^3->bool) x`;
        `(z:real^3) IN s DIFF frontier x`; `(s:real^3->bool) DIFF frontier x SUBSET interior x`] THEN
      MP_TAC(ISPEC `x:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`m INTER (u:real^3->bool) = hin UNION hout UNION ln`;
        `DISJOINT (hout:real^3->bool) x`; `(hin:real^3->bool) SUBSET s`;
        `(ln:real^3->bool) SUBSET s`] THEN
      SET_TAC[]];
    SUBGOAL_THEN `(hout:real^3->bool) SUBSET s` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `m INTER (u:real^3->bool) = hin UNION hout UNION ln` THEN SET_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `z:real^3` THEN
      MAP_EVERY UNDISCH_TAC
       [`(z:real^3) IN hin UNION hout`; `(hin:real^3->bool) SUBSET interior x`;
        `(z:real^3) IN s DIFF frontier x`; `DISJOINT (s DIFF frontier x) (x:real^3->bool)`] THEN
      MP_TAC(ISPEC `x:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`m INTER (u:real^3->bool) = hin UNION hout UNION ln`;
        `(hin:real^3->bool) SUBSET interior x`; `(hout:real^3->bool) SUBSET s`;
        `(ln:real^3->bool) SUBSET s`] THEN
      SET_TAC[]]]);;


(* The side condition along the whole boundary of a region s of m.          *)

let MOI_S3TR_REGION_SIDE = prove
 (`!(m:real^3->bool) x s.
     closed x /\ frontier x SUBSET closure (interior x) /\ closed s /\
     s SUBSET m /\
     (!y. y IN s INTER frontier x ==> pl_crossing_at m (frontier x) y) /\
     open_in (subtopology euclidean m) (s DIFF frontier x) /\
     open_in (subtopology euclidean (m INTER frontier x)) (s INTER frontier x) /\
     s SUBSET closure (s DIFF frontier x) /\ connected (s DIFF frontier x)
     ==> (s DIFF frontier x SUBSET interior x \/ DISJOINT (s DIFF frontier x) x) /\
         (s DIFF frontier x SUBSET interior x ==> s SUBSET x) /\
         (DISJOINT (s DIFF frontier x) x ==> s INTER x = s INTER frontier x) /\
         ?w. open w /\ s SUBSET w /\
             (s DIFF frontier x SUBSET interior x ==> m INTER x INTER w SUBSET s) /\
             (DISJOINT (s DIFF frontier x) x ==> m INTER w SUBSET s UNION interior x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `frontier x SUBSET (x:real^3->bool) /\
                DISJOINT (interior x) (frontier x)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[FRONTIER_SUBSET_CLOSED] THEN REWRITE_TAC[frontier] THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S3TR_CONNECTED_SIDE THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    DISCH_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `closure (s DIFF frontier x:real^3->bool)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `x:real^3->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[];
    DISCH_TAC THEN UNDISCH_TAC `frontier x SUBSET (x:real^3->bool)` THEN
    UNDISCH_TAC `DISJOINT (s DIFF frontier x) (x:real^3->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_OPEN] o check (fun th ->
    concl th = `open_in (subtopology euclidean m) (s DIFF frontier x:real^3->bool)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `w0:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!y. ?w. y IN s INTER frontier x
            ==> open w /\ y IN w /\
                (s DIFF frontier x SUBSET interior x ==> m INTER x INTER w SUBSET s) /\
                (DISJOINT (s DIFF frontier x) x
                 ==> m INTER w SUBSET (s:real^3->bool) UNION interior x)`
  MP_TAC THENL
   [X_GEN_TAC `y:real^3` THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_S3TR_LOCAL_SIDE THEN ASM_SIMP_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:real^3->real^3->bool` (LABEL_TAC "W")) THEN
  EXISTS_TAC `w0 UNION UNIONS (IMAGE (W:real^3->real^3->bool) (s INTER frontier x))` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_UNION THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC OPEN_UNIONS THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "W" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    REWRITE_TAC[IN_UNION; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    ASM_CASES_TAC `(y:real^3) IN frontier x` THENL
     [DISJ2_TAC THEN EXISTS_TAC `y:real^3` THEN
      USE_THEN "W" (MP_TAC o SPEC `y:real^3`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[IN_INTER]; ASM_SIMP_TAC[IN_INTER]];
      DISJ1_TAC THEN
      UNDISCH_TAC `s DIFF frontier x:real^3->bool = m INTER w0` THEN
      UNDISCH_TAC `~((y:real^3) IN frontier x)` THEN UNDISCH_TAC `(y:real^3) IN s` THEN
      SET_TAC[]];
    DISCH_TAC THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_UNION; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    X_GEN_TAC `z:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)))) THENL
     [UNDISCH_TAC `s DIFF frontier x:real^3->bool = m INTER w0` THEN
      UNDISCH_TAC `(z:real^3) IN w0` THEN UNDISCH_TAC `(z:real^3) IN m` THEN SET_TAC[];
      USE_THEN "W" (MP_TAC o SPEC `y:real^3`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[IN_INTER]; STRIP_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP
        (ASSUME `(s:real^3->bool) DIFF frontier x SUBSET interior x`)) THEN
      UNDISCH_TAC `(z:real^3) IN W(y:real^3)` THEN UNDISCH_TAC `(z:real^3) IN x` THEN
      UNDISCH_TAC `(z:real^3) IN m` THEN SET_TAC[]];
    DISCH_TAC THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_UNION; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    X_GEN_TAC `z:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC))) THENL
     [UNDISCH_TAC `s DIFF frontier x:real^3->bool = m INTER w0` THEN
      UNDISCH_TAC `(z:real^3) IN w0` THEN UNDISCH_TAC `(z:real^3) IN m` THEN SET_TAC[];
      USE_THEN "W" (MP_TAC o SPEC `y:real^3`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[IN_INTER]; STRIP_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP
        (ASSUME `DISJOINT ((s:real^3->bool) DIFF frontier x) x`)) THEN
      UNDISCH_TAC `(z:real^3) IN W(y:real^3)` THEN
      UNDISCH_TAC `(z:real^3) IN m` THEN SET_TAC[]]]);;


(* ------------------------------------------------------------------------- *)
(* Frontiers are local; the other pseudo-cells form a closed set disjoint   *)
(* from E.                                                                   *)
(* ------------------------------------------------------------------------- *)

let MOI_S3TR_FRONTIER_LOCAL = prove
 (`!(s:real^N->bool) t q.
     open q /\ s INTER q = t INTER q ==> frontier s INTER q = frontier t INTER q`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!a:real^N->bool. frontier a INTER q = (closure (a INTER q) INTER q) DIFF
                                                       interior (a INTER q)`
  (fun th -> ASM_REWRITE_TAC[th]) THEN
  GEN_TAC THEN REWRITE_TAC[frontier; INTERIOR_INTER] THEN
  ASM_SIMP_TAC[INTERIOR_OPEN] THEN
  MP_TAC(GEN_REWRITE_RULE (RAND_CONV o RAND_CONV o RAND_CONV) [INTER_COMM]
    (ISPECL [`q:real^N->bool`; `a:real^N->bool`] OPEN_INTER_CLOSURE_SUBSET)) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`a INTER q:real^N->bool`; `a:real^N->bool`] SUBSET_CLOSURE) THEN
  REWRITE_TAC[INTER_SUBSET] THEN SET_TAC[]);;

let MOI_S3TR_OTHER_CELLS = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c u v.
     moi_s33_hd t l h e c /\ ~(u = v) /\ segment[u,v] IN l
     ==> closed (UNIONS {e s | s IN l /\ aff_dim s = &1 /\ ~(s = segment[u,v])}) /\
         DISJOINT (e(segment[u,v]))
                  (UNIONS {e s | s IN l /\ aff_dim s = &1 /\ ~(s = segment[u,v])})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [moi_s33_hd]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3FR_TUBE_BASIC) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SET_RULE
       `{(e:(real^3->bool)->real^3->bool) s | s IN l /\ P s} = IMAGE e {s | s IN l /\ P s}`] THEN
      MATCH_MP_TAC FINITE_IMAGE THEN ASM_SIMP_TAC[FINITE_RESTRICT];
      REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `s:real^3->bool` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                     `h:real^3->real^3`; `s:real^3->bool`] MOI_S3X2_TUBE_EDGE) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `a:real^3` (X_CHOOSE_THEN `b:real^3` STRIP_ASSUME_TAC)) THEN
      MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                     `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                     `c:real^3->real^3->bool`; `a:real^3`; `b:real^3`]
        MOI_S3X2_HD_EDGE) THEN
      ASM_MESON_TAC[]];
    REWRITE_TAC[DISJOINT; INTER_UNIONS; EMPTY_UNIONS; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `s:real^3->bool` THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM DISJOINT] THEN
    FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
      GEN_REWRITE_RULE I [moi_s33_hd]) THEN
    ASM_REWRITE_TAC[AFF_DIM_SEGMENT]]);;


(* ------------------------------------------------------------------------- *)
(* The thin surgery principle.  For a region s of the pseudo-cell E (a      *)
(* compact piece of E - rim - centre bounded by trace circles) there is an  *)
(* open w around s such that any CMWB 3 complex x' agreeing with x outside  *)
(* w and either cut along s (s in x) or thickened over s (s outside x) is   *)
(* again an x2 neighbourhood, with the traces on E those of x minus the      *)
(* boundary circles of s, and the traces on the other pseudo-cells kept.    *)
(* ------------------------------------------------------------------------- *)

let MOI_S3TR_THIN_STEP = prove
 (`!(t:(real^3->bool)->bool) l h e c x u v s.
     moi_s33_hd t l h e c /\ moi_s33_x2 t l h e x /\ ~(u = v) /\ segment[u,v] IN l /\
     compact s /\
     s SUBSET (e(segment[u,v]) DIFF moi_s33_rim t l h u v) DELETE h(midpoint(u,v)) /\
     open_in (subtopology euclidean (e(segment[u,v]) DIFF moi_s33_rim t l h u v))
             (s DIFF frontier (UNIONS x)) /\
     open_in (subtopology euclidean ((e(segment[u,v]) DIFF moi_s33_rim t l h u v) INTER
                                     frontier (UNIONS x)))
             (s INTER frontier (UNIONS x)) /\
     s SUBSET closure (s DIFF frontier (UNIONS x)) /\
     connected (s DIFF frontier (UNIONS x))
     ==> (s SUBSET UNIONS x \/ s INTER UNIONS x = s INTER frontier (UNIONS x)) /\
         ?w. open w /\ s SUBSET w /\
             !x'. FINITE x' /\ combinatorial_manifold_with_boundary 3 x' /\
                  (UNIONS x DIFF UNIONS x') UNION (UNIONS x' DIFF UNIONS x) SUBSET w /\
                  (s SUBSET UNIONS x
                   ==> UNIONS x' SUBSET UNIONS x /\ DISJOINT s (UNIONS x')) /\
                  (s INTER UNIONS x = s INTER frontier (UNIONS x)
                   ==> UNIONS x SUBSET UNIONS x' /\ s SUBSET interior (UNIONS x'))
                  ==> moi_s33_x2 t l h e x' /\
                      e(segment[u,v]) INTER frontier (UNIONS x') =
                      (e(segment[u,v]) INTER frontier (UNIONS x)) DIFF s /\
                      !s'. s' IN l /\ aff_dim s' = &1 /\ ~(s' = segment[u,v])
                           ==> e s' INTER frontier (UNIONS x') =
                               e s' INTER frontier (UNIONS x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_s33_x2] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`; `u:real^3`; `v:real^3`]
    MOI_S3TR_TRACE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `u:real^3`; `v:real^3`]
    MOI_S3X2_HD_EDGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `u:real^3`; `v:real^3`]
    MOI_S3TR_OTHER_CELLS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o MATCH_MP MOI_S3FR_IMAGE_FACTS o CONJUNCT1 o
    GEN_REWRITE_RULE I [moi_s33_hd]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s33_x2] o check (fun th ->
    concl th = `moi_s33_x2 t l h e (x:(real^3->bool)->bool)`)) THEN
  ABBREV_TAC `E = (e:(real^3->bool)->real^3->bool) (segment[u,v])` THEN
  ABBREV_TAC `j = moi_s33_rim t l (h:real^3->real^3) u v` THEN
  ABBREV_TAC `p = (h:real^3->real^3) (midpoint(u,v))` THEN
  ABBREV_TAC `X = UNIONS (x:(real^3->bool)->bool)` THEN
  ABBREV_TAC `K = IMAGE (h:real^3->real^3) (UNIONS l)` THEN
  ABBREV_TAC `U = interior (IMAGE (h:real^3->real^3) (derived_nbhd t l))` THEN
  ABBREV_TAC `OE = UNIONS {(e:(real^3->bool)->real^3->bool) s' |
                           s' IN l /\ aff_dim s' = &1 /\ ~(s' = segment[u,v])}` THEN
  (* the region side *)
  MP_TAC(ISPECL [`E DIFF j:real^3->bool`; `X:real^3->bool`; `s:real^3->bool`]
    MOI_S3TR_REGION_SIDE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `w1:real^3->bool` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `(s:real^3->bool) SUBSET X <=> s DIFF frontier X SUBSET interior X`
  ASSUME_TAC THENL
   [EQ_TAC THENL
     [DISCH_TAC THEN MP_TAC(ISPEC `X:real^3->bool` frontier) THEN
      ASM_SIMP_TAC[CLOSURE_CLOSED] THEN ASM SET_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `s INTER X = s INTER frontier X <=> DISJOINT (s DIFF frontier X) (X:real^3->bool)`
  ASSUME_TAC THENL
   [EQ_TAC THENL
     [SET_TAC[];
      DISCH_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_imp (concl th) && is_disj (lhand (concl th)) = false &&
        lhand (concl th) = `DISJOINT (s DIFF frontier X) (X:real^3->bool)` &&
        is_eq (rand (concl th)))) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* the open set G of allowed changes *)
  SUBGOAL_THEN `closed ((E INTER frontier X) DIFF (s:real^3->bool))` ASSUME_TAC THENL
   [SUBGOAL_THEN `(E DIFF j) INTER frontier X = E INTER frontier (X:real^3->bool)`
    ASSUME_TAC THENL
     [UNDISCH_TAC `E INTER frontier X SUBSET (E DIFF j) DELETE (p:real^3)` THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC CLOSED_IN_CLOSED_TRANS THEN
    EXISTS_TAC `E INTER frontier (X:real^3->bool)` THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
    SUBGOAL_THEN `(E INTER frontier X) DIFF (s:real^3->bool) =
                  (E INTER frontier X) DIFF (s INTER frontier X)` SUBST1_TAC THENL
     [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CLOSED_IN_DIFF THEN REWRITE_TAC[CLOSED_IN_REFL] THEN
    UNDISCH_TAC `open_in (subtopology euclidean ((E DIFF j) INTER frontier X))
                         (s INTER frontier (X:real^3->bool))` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `G = w1 INTER ((:real^3) DIFF K) INTER ((:real^3) DIFF OE) INTER
                  ((:real^3) DIFF ((E INTER frontier X) DIFF s)) INTER U` THEN
  SUBGOAL_THEN `open (G:real^3->bool) /\ s SUBSET G` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN CONJ_TAC THENL
     [SUBGOAL_THEN `closed (K:real^3->bool)` ASSUME_TAC THENL
       [EXPAND_TAC "K" THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
      SUBGOAL_THEN `open (U:real^3->bool)` ASSUME_TAC THENL
       [EXPAND_TAC "U" THEN REWRITE_TAC[OPEN_INTERIOR]; ALL_TAC] THEN
      REPEAT(MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC) THEN ASM_REWRITE_TAC[GSYM closed];
      MAP_EVERY UNDISCH_TAC
       [`(s:real^3->bool) SUBSET w1`;
        `(s:real^3->bool) SUBSET (E DIFF j) DELETE p`;
        `E INTER (U DIFF K) = (E DIFF j) DELETE (p:real^3)`;
        `DISJOINT (E:real^3->bool) OE`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `(:real^3) DIFF G`] SEPARATION_NORMAL_COMPACT) THEN
  ASM_REWRITE_TAC[GSYM OPEN_CLOSED] THEN ANTS_TAC THENL
   [UNDISCH_TAC `(s:real^3->bool) SUBSET G` THEN SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3->bool` (X_CHOOSE_THEN `w':real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `closure w SUBSET (G:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`w':real^3->bool`; `w:real^3->bool`] OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `w INTER w':real^3->bool = {}` THEN
    UNDISCH_TAC `(:real^3) DIFF G SUBSET w'` THEN SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `w:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x':(real^3->bool)->bool` THEN STRIP_TAC THEN
  ABBREV_TAC `X' = UNIONS (x':(real^3->bool)->bool)` THEN
  ABBREV_TAC `Q = (:real^3) DIFF closure w` THEN
  SUBGOAL_THEN `open (Q:real^3->bool) /\ X INTER Q = X' INTER Q /\
                frontier X INTER Q = frontier X' INTER Q`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `open (Q:real^3->bool) /\ X INTER Q = X' INTER Q` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "Q" THEN REWRITE_TAC[GSYM closed; CLOSED_CLOSURE] THEN
      MP_TAC(ISPEC `w:real^3->bool` CLOSURE_SUBSET) THEN
      UNDISCH_TAC `(X DIFF X') UNION (X' DIFF X) SUBSET (w:real^3->bool)` THEN SET_TAC[];
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S3TR_FRONTIER_LOCAL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (X':real^3->bool) /\ frontier X' SUBSET X'` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `compact (X':real^3->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "X'" THEN MATCH_MP_TAC COMPACT_UNIONS THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[MOI_FM3_LF_COMPACT; combinatorial_manifold_with_boundary];
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED; FRONTIER_SUBSET_COMPACT]];
    ALL_TAC] THEN
  (* no trace of x' on E near s *)
  SUBGOAL_THEN `(E:real^3->bool) INTER closure w INTER frontier X' = {}` ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj (concl th) &&
      can (find_term ((=) `interior (X:real^3->bool)`)) (concl th))) THENL
     [SUBGOAL_THEN `(X':real^3->bool) SUBSET X /\ DISJOINT s X'` STRIP_ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP
        (ASSUME `(s:real^3->bool) DIFF frontier X SUBSET interior X`) o check (fun th ->
          can (find_term ((=) `w1:real^3->bool`)) (concl th))) THEN
      MAP_EVERY UNDISCH_TAC
       [`closure w SUBSET (G:real^3->bool)`; `frontier X' SUBSET (X':real^3->bool)`;
        `(X':real^3->bool) SUBSET X`; `DISJOINT s (X':real^3->bool)`;
        `E INTER (X:real^3->bool) SUBSET E DIFF j`] THEN
      EXPAND_TAC "G" THEN SET_TAC[];
      SUBGOAL_THEN `(X:real^3->bool) SUBSET X' /\ s SUBSET interior X'` STRIP_ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP
        (ASSUME `DISJOINT ((s:real^3->bool) DIFF frontier X) X`) o check (fun th ->
          can (find_term ((=) `w1:real^3->bool`)) (concl th))) THEN
      SUBGOAL_THEN `interior X SUBSET interior (X':real^3->bool)` MP_TAC THENL
       [MATCH_MP_TAC SUBSET_INTERIOR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPEC `X':real^3->bool` frontier) THEN
      MAP_EVERY UNDISCH_TAC
       [`closure w SUBSET (G:real^3->bool)`; `(s:real^3->bool) SUBSET interior X'`;
        `DISJOINT j (U:real^3->bool)`] THEN
      EXPAND_TAC "G" THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. z IN Q ==> (z IN frontier X <=> z IN frontier X')`
  ASSUME_TAC THENL
   [UNDISCH_TAC `frontier X INTER Q = frontier X' INTER (Q:real^3->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `E INTER frontier X' = (E INTER frontier X) DIFF (s:real^3->bool)`
  ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(E:real^3->bool) INTER closure w INTER frontier X' = {}`;
      `!z:real^3. z IN Q ==> (z IN frontier X <=> z IN frontier X')`;
      `closure w SUBSET (G:real^3->bool)`; `(s:real^3->bool) SUBSET w`] THEN
    MP_TAC(ISPEC `w:real^3->bool` CLOSURE_SUBSET) THEN
    EXPAND_TAC "Q" THEN EXPAND_TAC "G" THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT OE (closure w:real^3->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `closure w SUBSET (G:real^3->bool)` THEN EXPAND_TAC "G" THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s'. s' IN l /\ aff_dim s' = &1 /\ ~(s' = segment[u,v])
         ==> (e:(real^3->bool)->real^3->bool) s' SUBSET Q`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "Q" THEN
    UNDISCH_TAC `DISJOINT OE (closure w:real^3->bool)` THEN EXPAND_TAC "OE" THEN
    REWRITE_TAC[DISJOINT; INTER_UNIONS; EMPTY_UNIONS; FORALL_IN_GSPEC] THEN
    DISCH_THEN(MP_TAC o SPEC `s':real^3->bool`) THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "Q" THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* K inside the interior *)
    SUBGOAL_THEN `(K:real^3->bool) SUBSET Q` ASSUME_TAC THENL
     [UNDISCH_TAC `closure w SUBSET (G:real^3->bool)` THEN EXPAND_TAC "Q" THEN
      EXPAND_TAC "G" THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `interior (X' INTER Q:real^3->bool)` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `X INTER Q = X' INTER (Q:real^3->bool)`)) THEN
      ASM_SIMP_TAC[INTERIOR_INTER; INTERIOR_OPEN] THEN ASM SET_TAC[];
      MATCH_MP_TAC SUBSET_INTERIOR THEN SET_TAC[]];
    (* inside U *)
    MAP_EVERY UNDISCH_TAC
     [`(X DIFF X') UNION (X' DIFF X) SUBSET (w:real^3->bool)`;
      `closure w SUBSET (G:real^3->bool)`; `X SUBSET (U:real^3->bool)`] THEN
    MP_TAC(ISPEC `w:real^3->bool` CLOSURE_SUBSET) THEN
    EXPAND_TAC "G" THEN SET_TAC[];
    (* crossings *)
    MAP_EVERY X_GEN_TAC [`u':real^3`; `v':real^3`; `y:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN Q` ASSUME_TAC THENL
     [ASM_CASES_TAC `segment[u':real^3,v'] = segment[u,v]` THENL
       [UNDISCH_TAC `(y:real^3) IN e(segment[u':real^3,v']) INTER frontier X'` THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `closure w SUBSET (G:real^3->bool)` THEN
        EXPAND_TAC "Q" THEN EXPAND_TAC "G" THEN SET_TAC[];
        FIRST_X_ASSUM(MP_TAC o SPEC `segment[u':real^3,v']` o check (fun th -> aconv (concl th)
          `!s'. s' IN l /\ aff_dim s' = &1 /\ ~(s' = segment[u,v])
                ==> (e:(real^3->bool)->real^3->bool) s' SUBSET Q`)) THEN
        ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN
        UNDISCH_TAC `(y:real^3) IN e(segment[u':real^3,v']) INTER frontier X'` THEN
        SET_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_FGB_CROSSING_LOCAL THEN
    MAP_EVERY EXISTS_TAC
     [`(e:(real^3->bool)->real^3->bool) (segment[u',v']) DIFF moi_s33_rim t l h u' v'`;
      `frontier X:real^3->bool`; `Q:real^3->bool`] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y:real^3) IN e(segment[u':real^3,v']) INTER frontier X'` THEN
      UNDISCH_TAC `(y:real^3) IN Q` THEN
      UNDISCH_TAC `!z:real^3. z IN Q ==> (z IN frontier X <=> z IN frontier X')` THEN
      SET_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      REWRITE_TAC[];
      FIRST_ASSUM ACCEPT_TAC];
    (* traces on the other pseudo-cells *)
    X_GEN_TAC `s':real^3->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s':real^3->bool` o check (fun th -> aconv (concl th)
          `!s'. s' IN l /\ aff_dim s' = &1 /\ ~(s' = segment[u,v])
                ==> (e:(real^3->bool)->real^3->bool) s' SUBSET Q`)) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `!z:real^3. z IN Q ==> (z IN frontier X <=> z IN frontier X')` THEN
    SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Planar Jordan curves: the standard facts in one list, the side of a       *)
(* connected set, nesting, and the trichotomy for disjoint Jordan curves     *)
(* (nested either way or with disjoint closed disks).                        *)
(* ------------------------------------------------------------------------- *)

let MOI_S3TR_JF = prove
 (`!c:real^2->bool.
     c homeomorphic sphere(vec 0:real^2,&1)
     ==> compact c /\ connected c /\ ~(c = {}) /\ ANR c /\
         ~(inside c = {}) /\ open(inside c) /\ connected(inside c) /\
         open(outside c) /\ connected(outside c) /\ bounded(inside c) /\
         inside c INTER outside c = {} /\
         inside c UNION outside c = (:real^2) DIFF c /\
         frontier(inside c) = c /\ frontier(outside c) = c /\
         closure(inside c) = c UNION inside c /\
         compact(c UNION inside c) /\ connected(c UNION inside c)`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `c:real^2->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN
  ASM_REWRITE_TAC[DIMINDEX_2; LE_REFL] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `closure(inside c) = (c:real^2->bool) UNION inside c` ASSUME_TAC THENL
   [REWRITE_TAC[CLOSURE_UNION_FRONTIER] THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[HOMEOMORPHIC_COMPACTNESS; COMPACT_SPHERE];
    ASM_MESON_TAC[HOMEOMORPHIC_CONNECTEDNESS; CONNECTED_SPHERE; DIMINDEX_2; LE_REFL];
    DISCH_TAC THEN UNDISCH_TAC `(c:real^2->bool) homeomorphic sphere(vec 0:real^2,&1)` THEN
    ASM_REWRITE_TAC[HOMEOMORPHIC_EMPTY] THEN
    REWRITE_TAC[SPHERE_EQ_EMPTY] THEN REAL_ARITH_TAC;
    ASM_MESON_TAC[HOMEOMORPHIC_ANRNESS; ANR_SPHERE];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `closure(inside c) = (c:real^2->bool) UNION inside c`)) THEN
    ASM_REWRITE_TAC[COMPACT_CLOSURE];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `closure(inside c) = (c:real^2->bool) UNION inside c`)) THEN
    MATCH_MP_TAC CONNECTED_CLOSURE THEN ASM_REWRITE_TAC[]]);;

let MOI_S3TR_JSIDE = prove
 (`!c d:real^2->bool.
     c homeomorphic sphere(vec 0:real^2,&1) /\ connected d /\ DISJOINT c d
     ==> d SUBSET inside c \/ d SUBSET outside c`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3TR_JF) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [connected] o check (fun th ->
    concl th = `connected (d:real^2->bool)`)) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`inside c:real^2->bool`; `outside c:real^2->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `inside c UNION outside c = (:real^2) DIFF c` THEN
  UNDISCH_TAC `inside c INTER outside c:real^2->bool = {}` THEN
  UNDISCH_TAC `DISJOINT (c:real^2->bool) d` THEN SET_TAC[]);;

let MOI_S3TR_JNEST = prove
 (`!c d:real^2->bool.
     c homeomorphic sphere(vec 0:real^2,&1) /\
     d homeomorphic sphere(vec 0:real^2,&1) /\ d SUBSET inside c
     ==> inside d SUBSET inside c /\ d UNION inside d SUBSET inside c /\
         c SUBSET outside d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3TR_JF o check (fun th ->
    concl th = `(c:real^2->bool) homeomorphic sphere(vec 0:real^2,&1)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3TR_JF o check (fun th ->
    concl th = `(d:real^2->bool) homeomorphic sphere(vec 0:real^2,&1)`)) THEN
  SUBGOAL_THEN `inside d SUBSET inside (c:real^2->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC INSIDE_INSIDE_COMPACT_CONNECTED THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[UNION_SUBSET] THEN
  MP_TAC(ISPECL [`d:real^2->bool`; `c:real^2->bool`] MOI_S3TR_JSIDE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MP_TAC(ISPEC `c:real^2->bool` INSIDE_NO_OVERLAP) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `c:real^2->bool` INSIDE_NO_OVERLAP) THEN ASM SET_TAC[]);;

let MOI_S3TR_JTRI = prove
 (`!c d:real^2->bool.
     c homeomorphic sphere(vec 0:real^2,&1) /\
     d homeomorphic sphere(vec 0:real^2,&1) /\ DISJOINT c d
     ==> d SUBSET inside c \/ c SUBSET inside d \/
         DISJOINT (c UNION inside c) (d UNION inside d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `(d:real^2->bool) SUBSET inside c` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(c:real^2->bool) SUBSET inside d` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3TR_JF o check (fun th ->
    concl th = `(c:real^2->bool) homeomorphic sphere(vec 0:real^2,&1)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3TR_JF o check (fun th ->
    concl th = `(d:real^2->bool) homeomorphic sphere(vec 0:real^2,&1)`)) THEN
  MP_TAC(ISPECL [`c:real^2->bool`; `d:real^2->bool`] MOI_S3TR_JSIDE) THEN
  MP_TAC(ISPECL [`d:real^2->bool`; `c:real^2->bool`] MOI_S3TR_JSIDE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM SET_TAC[]; DISCH_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* c UNION inside c is connected and misses d, so it lies outside d *)
  MP_TAC(ISPECL [`d:real^2->bool`; `c UNION inside c:real^2->bool`] MOI_S3TR_JSIDE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `(d:real^2->bool) SUBSET outside c` THEN
    UNDISCH_TAC `inside c INTER outside c:real^2->bool = {}` THEN
    UNDISCH_TAC `DISJOINT (c:real^2->bool) d` THEN SET_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [UNDISCH_TAC `(c:real^2->bool) SUBSET outside d` THEN
    UNDISCH_TAC `c UNION inside c SUBSET inside (d:real^2->bool)` THEN
    UNDISCH_TAC `inside d INTER outside d:real^2->bool = {}` THEN
    UNDISCH_TAC `~(c:real^2->bool = {})` THEN SET_TAC[];
    MP_TAC(ISPEC `d:real^2->bool` OUTSIDE_NO_OVERLAP) THEN
    UNDISCH_TAC `c UNION inside c SUBSET outside (d:real^2->bool)` THEN
    UNDISCH_TAC `inside d INTER outside d:real^2->bool = {}` THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Choice of the curves to remove.  For a finite family of disjoint Jordan   *)
(* curves missing q with at least two members: either some curve bounds a    *)
(* disk missing q and the other curves, or two curves c, d with q inside c   *)
(* and c inside d bound an annulus missing the other curves.  Minimise the   *)
(* number of curves inside.                                                  *)
(* ------------------------------------------------------------------------- *)

let MOI_S3TR_NUM_MIN = prove
 (`!(s:A->bool) (f:A->num). ~(s = {}) ==> ?x. x IN s /\ !y. y IN s ==> f x <= f y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\n. ?x:A. x IN s /\ (f:A->num) x = n` num_WOP) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
   [ASM_MESON_TAC[MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:A` THEN DISCH_TAC THEN REWRITE_TAC[GSYM NOT_LT] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `(f:A->num) y`) THEN
  ASM_MESON_TAC[]);;

let MOI_S3TR_NLT = prove
 (`!(ff:(real^2->bool)->bool) c d.
     FINITE ff /\ d IN ff /\ d SUBSET inside c /\ inside d SUBSET inside c /\
     ~(d = {})
     ==> CARD {b | b IN ff /\ b SUBSET inside d} <
         CARD {b | b IN ff /\ b SUBSET inside c}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CARD_PSUBSET THEN
  ASM_SIMP_TAC[FINITE_RESTRICT] THEN REWRITE_TAC[PSUBSET] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `d:real^2->bool`) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `d:real^2->bool` INSIDE_NO_OVERLAP) THEN ASM SET_TAC[]);;

let MOI_S3TR_PLANAR_CHOICE = prove
 (`!(ff:(real^2->bool)->bool) q.
     FINITE ff /\ 2 <= CARD ff /\
     (!c. c IN ff ==> c homeomorphic sphere(vec 0:real^2,&1) /\ ~(q IN c)) /\
     (!c d. c IN ff /\ d IN ff /\ ~(c = d) ==> DISJOINT c d)
     ==> (?c. c IN ff /\ ~(q IN inside c) /\
              !d. d IN ff /\ ~(d = c) ==> DISJOINT d (c UNION inside c)) \/
         (?c d. c IN ff /\ d IN ff /\ ~(c = d) /\ c SUBSET inside d /\
                q IN inside c /\
                !b. b IN ff /\ ~(b = c) /\ ~(b = d)
                    ==> DISJOINT b ((d UNION inside d) DIFF inside c))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `N = \c:real^2->bool. CARD {b | b IN ff /\ b SUBSET inside c}` THEN
  SUBGOAL_THEN
   `!c d:real^2->bool. c IN ff /\ d IN ff /\ d SUBSET inside c
                       ==> (N:(real^2->bool)->num) d < N c`
  (LABEL_TAC "nlt") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "N" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S3TR_NLT THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`c:real^2->bool`; `d:real^2->bool`] MOI_S3TR_JNEST) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; SIMP_TAC[]] THEN DISCH_TAC THEN
    ASM_MESON_TAC[MOI_S3TR_JF];
    ALL_TAC] THEN
  ASM_CASES_TAC `?c:real^2->bool. c IN ff /\ ~(q IN inside c)` THENL
   [DISJ1_TAC THEN
    MP_TAC(ISPECL [`{c:real^2->bool | c IN ff /\ ~(q IN inside c)}`;
                   `N:(real^2->bool)->num`] MOI_S3TR_NUM_MIN) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `c0:real^2->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `c0:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `d:real^2->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c0:real^2->bool`; `d:real^2->bool`] MOI_S3TR_JTRI) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `DISJOINT (c0:real^2->bool) d` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    STRIP_TAC THENL
     [(* d inside c0: a smaller count, contradiction *)
      MP_TAC(ISPECL [`c0:real^2->bool`; `d:real^2->bool`] MOI_S3TR_JNEST) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
      SUBGOAL_THEN `(N:(real^2->bool)->num) c0 <= N d` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(N:(real^2->bool)->num) d < N c0` MP_TAC THENL
       [USE_THEN "nlt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ARITH_TAC];
      (* c0 inside d: then d is outside c0 *)
      MP_TAC(ISPECL [`d:real^2->bool`; `c0:real^2->bool`] MOI_S3TR_JNEST) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
      MP_TAC(ISPEC `c0:real^2->bool` MOI_S3TR_JF) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
      UNDISCH_TAC `DISJOINT (c0:real^2->bool) d` THEN
      UNDISCH_TAC `(d:real^2->bool) SUBSET outside c0` THEN
      UNDISCH_TAC `inside c0 INTER outside c0:real^2->bool = {}` THEN SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  DISJ2_TAC THEN
  SUBGOAL_THEN `!c:real^2->bool. c IN ff ==> q IN inside c` (LABEL_TAC "qin") THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!c d:real^2->bool. c IN ff /\ d IN ff /\ ~(c = d)
                       ==> c SUBSET inside d \/ d SUBSET inside c`
  (LABEL_TAC "nest") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`c:real^2->bool`; `d:real^2->bool`] MOI_S3TR_JTRI) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(q:real^2) IN inside c /\ q IN inside d` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `DISJOINT (c UNION inside c) (d UNION inside (d:real^2->bool))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(ff:(real^2->bool)->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `2 <= CARD(ff:(real^2->bool)->bool)` THEN
    ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ff:(real^2->bool)->bool`; `N:(real^2->bool)->num`]
    MOI_S3TR_NUM_MIN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c0:real^2->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(ff DELETE (c0:real^2->bool) = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `ff = {c0:real^2->bool}` SUBST_ALL_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `2 <= CARD{c0:real^2->bool}` THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_EMPTY; NOT_IN_EMPTY] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ff DELETE (c0:real^2->bool)`; `N:(real^2->bool)->num`]
    MOI_S3TR_NUM_MIN) THEN
  ASM_REWRITE_TAC[IN_DELETE] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real^2->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(c0:real^2->bool) SUBSET inside d0` ASSUME_TAC THENL
   [USE_THEN "nest" (MP_TAC o SPECL [`c0:real^2->bool`; `d0:real^2->bool`]) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(N:(real^2->bool)->num) c0 <= N d0` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(N:(real^2->bool)->num) d0 < N c0` MP_TAC THENL
     [USE_THEN "nlt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`c0:real^2->bool`; `d0:real^2->bool`] THEN
  ASM_SIMP_TAC[] THEN
  X_GEN_TAC `b:real^2->bool` THEN STRIP_TAC THEN
  USE_THEN "nest" (MP_TAC o SPECL [`b:real^2->bool`; `c0:real^2->bool`]) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN STRIP_TAC THENL
   [SUBGOAL_THEN `(N:(real^2->bool)->num) c0 <= N b` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(N:(real^2->bool)->num) b < N c0` MP_TAC THENL
     [USE_THEN "nlt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "nest" (MP_TAC o SPECL [`b:real^2->bool`; `d0:real^2->bool`]) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN STRIP_TAC THENL
   [(* b inside d0 with c0 inside b: a smaller count than d0 *)
    MP_TAC(ISPECL [`d0:real^2->bool`; `b:real^2->bool`] MOI_S3TR_JNEST) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `(N:(real^2->bool)->num) d0 <= N b` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(N:(real^2->bool)->num) b < N d0` MP_TAC THENL
     [USE_THEN "nlt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ARITH_TAC];
    (* d0 inside b: the disk of d0 misses b *)
    MP_TAC(ISPECL [`b:real^2->bool`; `d0:real^2->bool`] MOI_S3TR_JNEST) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPEC `b:real^2->bool` INSIDE_NO_OVERLAP) THEN
    UNDISCH_TAC `d0 UNION inside d0 SUBSET inside (b:real^2->bool)` THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Cross-cuts of a planar annulus.  For Jordan curves c1 inside c2 the open  *)
(* annulus U = inside c2 INTER outside c1 is a component of the complement   *)
(* of c1 UNION c2 with both curves in its frontier (Janiszewski for          *)
(* connectedness); an arc from c1 to c2 through U comes from accessibility   *)
(* (ACCESSIBLE_FRONTIER_ANR_COMPLEMENT_COMPONENT twice and PATH_CONTAINS_ARC) *)
(* and a second, disjoint one the same way in U minus the first.             *)
(* ------------------------------------------------------------------------- *)

let MOI_S3TR_FRSUB = prove
 (`!s:real^N->bool. frontier s SUBSET closure s`,
  REWRITE_TAC[frontier; SUBSET_DIFF]);;

let MOI_S3TR_CROSS_ARC = prove
 (`!s u y z:real^N.
     compact s /\ ANR s /\ u IN components((:real^N) DIFF s) /\
     y IN frontier u /\ z IN frontier u /\ ~(y = z)
     ==> ?g. arc g /\ pathstart g = y /\ pathfinish g = z /\
             path_image g SUBSET u UNION {y,z}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(u:real^N->bool = {})` MP_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY]; ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `x:real^N`) THEN
  SUBGOAL_THEN
   `!g:real^1->real^N w.
      pathfinish g = w /\
      (!t. t IN interval[vec 0,vec 1] DELETE vec 1 ==> g t IN u)
      ==> path_image g SUBSET u UNION {w}`
  ASSUME_TAC THENL
   [REWRITE_TAC[path_image; pathfinish; SUBSET; FORALL_IN_IMAGE; IN_DELETE] THEN
    REPEAT STRIP_TAC THEN ASM_CASES_TAC `x' = vec 1:real^1` THEN
    ASM_SIMP_TAC[IN_UNION; IN_SING];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `u:real^N->bool`; `x:real^N`; `y:real^N`]
    ACCESSIBLE_FRONTIER_ANR_COMPLEMENT_COMPONENT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g1:real^1->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `u:real^N->bool`; `x:real^N`; `z:real^N`]
    ACCESSIBLE_FRONTIER_ANR_COMPLEMENT_COMPONENT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g2:real^1->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `path_image (g1:real^1->real^N) SUBSET u UNION {y} /\
                path_image (g2:real^1->real^N) SUBSET u UNION {z}`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`reversepath g1 ++ g2:real^1->real^N`; `y:real^N`; `z:real^N`]
    PATH_CONTAINS_ARC) THEN
  ASM_SIMP_TAC[PATH_JOIN; PATH_REVERSEPATH; ARC_IMP_PATH; PATHSTART_JOIN;
               PATHFINISH_JOIN; PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `q:real^1->real^N` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `path_image q SUBSET path_image (reversepath g1 ++ g2:real^1->real^N)` THEN
  ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHFINISH_REVERSEPATH; PATH_IMAGE_REVERSEPATH] THEN
  ASM SET_TAC[]);;

let MOI_S3TR_OPEN_COMPONENT = prove
 (`!s u v:real^N->bool.
     open u /\ open v /\ connected u /\ ~(u = {}) /\ DISJOINT u v /\
     s = u UNION v
     ==> u IN components s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_COMPONENTS_MAXIMAL] THEN
  ASM_REWRITE_TAC[SUBSET_UNION] THEN X_GEN_TAC `d:real^N->bool` THEN STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [connected] o check (fun th ->
    concl th = `connected (d:real^N->bool)`)) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`u:real^N->bool`; `v:real^N->bool`]) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_S3TR_FRONTIER_INTER = prove
 (`!s t y:real^N.
     open s /\ open t /\ y IN t /\ y IN closure s /\ ~(y IN s INTER t)
     ==> y IN frontier (s INTER t)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[frontier; INTERIOR_OPEN; OPEN_INTER] THEN
  ASM_REWRITE_TAC[IN_DIFF] THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `s:real^N->bool`] OPEN_INTER_CLOSURE_SUBSET) THEN
  ASM_REWRITE_TAC[INTER_COMM] THEN ASM SET_TAC[]);;

let MOI_S3TR_JOTHER = prove
 (`!c:real^2->bool y.
     c homeomorphic sphere(vec 0:real^2,&1) ==> ?z. z IN c /\ ~(z = y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:real^2->bool`; `vec 0:real^2`; `&1`]
    HOMEOMORPHIC_SIMPLE_PATH_IMAGE_CIRCLE_EQ) THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `g:real^1->real^2` INFINITE_SIMPLE_PATH_IMAGE) THEN
  ASM_REWRITE_TAC[INFINITE] THEN
  MATCH_MP_TAC(TAUT `(~q ==> p) ==> ~p ==> q`) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{y:real^2}` THEN
  REWRITE_TAC[FINITE_SING] THEN ASM SET_TAC[]);;

let MOI_S3TR_CROSS_CUTS = prove
 (`!c1 c2:real^2->bool.
     c1 homeomorphic sphere(vec 0:real^2,&1) /\
     c2 homeomorphic sphere(vec 0:real^2,&1) /\ c1 SUBSET inside c2
     ==> ?al be:real^1->real^2.
           arc al /\ arc be /\
           pathstart al IN c1 /\ pathfinish al IN c2 /\
           pathstart be IN c1 /\ pathfinish be IN c2 /\
           ~(pathstart al = pathstart be) /\ ~(pathfinish al = pathfinish be) /\
           path_image al INTER path_image be = {} /\
           path_image al INTER (c1 UNION c2) = {pathstart al, pathfinish al} /\
           path_image be INTER (c1 UNION c2) = {pathstart be, pathfinish be} /\
           path_image al SUBSET
           (inside c2 INTER outside c1) UNION {pathstart al, pathfinish al} /\
           path_image be SUBSET
           (inside c2 INTER outside c1) UNION {pathstart be, pathfinish be}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `c1:real^2->bool` MOI_S3TR_JF) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `c2:real^2->bool` MOI_S3TR_JF) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`c2:real^2->bool`; `c1:real^2->bool`] MOI_S3TR_JNEST) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(:real^2) DIFF (c1 UNION inside c1) = outside c1 /\
                (:real^2) DIFF (c2 UNION outside c2) = inside c2 /\
                c2 UNION outside c2 = (:real^2) DIFF inside c2`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[OUTSIDE_INSIDE] THEN
    MP_TAC(ISPEC `c2:real^2->bool` INSIDE_OUTSIDE) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (c2 UNION outside c2:real^2->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM OPEN_CLOSED]; ALL_TAC] THEN
  ABBREV_TAC `U = inside c2 INTER outside c1:real^2->bool` THEN
  SUBGOAL_THEN `open (U:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN ASM_SIMP_TAC[OPEN_INTER]; ALL_TAC] THEN
  (* the basic set relations, as one fact for SET_TAC *)
  SUBGOAL_THEN
   `DISJOINT (U:real^2->bool) (c1 UNION inside c1) /\
    DISJOINT U (c2 UNION outside c2) /\ U SUBSET inside c2 /\
    DISJOINT (c1 UNION inside c1) (c2 UNION outside c2) /\
    DISJOINT c1 c2 /\
    (:real^2) DIFF (c1 UNION c2) = U UNION (inside c1 UNION outside c2) /\
    DISJOINT U (inside c1 UNION outside c2)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN
    MP_TAC(ISPEC `c1:real^2->bool` OUTSIDE_NO_OVERLAP) THEN
    MP_TAC(ISPEC `c2:real^2->bool` INSIDE_NO_OVERLAP) THEN
    MP_TAC(ISPEC `c1:real^2->bool` INSIDE_NO_OVERLAP) THEN
    MP_TAC(ISPEC `c2:real^2->bool` OUTSIDE_NO_OVERLAP) THEN
    UNDISCH_TAC `inside c1 UNION outside c1 = (:real^2) DIFF c1` THEN
    UNDISCH_TAC `inside c2 UNION outside c2 = (:real^2) DIFF c2` THEN
    UNDISCH_TAC `inside c1 INTER outside c1:real^2->bool = {}` THEN
    UNDISCH_TAC `inside c2 INTER outside c2:real^2->bool = {}` THEN
    UNDISCH_TAC `c1 UNION inside c1 SUBSET inside (c2:real^2->bool)` THEN
    UNDISCH_TAC `(c2:real^2->bool) SUBSET outside c1` THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* U is connected (Janiszewski) *)
  SUBGOAL_THEN `connected (U:real^2->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `U = (:real^2) DIFF ((c1 UNION inside c1) UNION (c2 UNION outside c2))`
    SUBST1_TAC THENL
     [EXPAND_TAC "U" THEN
      UNDISCH_TAC `(:real^2) DIFF (c1 UNION inside c1) = outside c1` THEN
      UNDISCH_TAC `(:real^2) DIFF (c2 UNION outside c2) = inside c2` THEN
      SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC JANISZEWSKI_CONNECTED THEN REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `DISJOINT (c1 UNION inside c1) (c2 UNION outside c2:real^2->bool)` THEN
      REWRITE_TAC[DISJOINT] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[CONNECTED_EMPTY];
      REWRITE_TAC[ASSUME `(:real^2) DIFF (c1 UNION inside c1) = outside c1`] THEN
      FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[ASSUME `(:real^2) DIFF (c2 UNION outside c2) = inside c2`] THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  (* both curves lie in the frontier of U *)
  SUBGOAL_THEN `c1 UNION c2 SUBSET frontier (U:real^2->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[UNION_SUBSET; SUBSET] THEN CONJ_TAC THEN
    X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN EXPAND_TAC "U" THENL
     [GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [INTER_COMM] THEN
      MATCH_MP_TAC MOI_S3TR_FRONTIER_INTER THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [ASM SET_TAC[];
        MP_TAC(ISPEC `outside c1:real^2->bool` MOI_S3TR_FRSUB) THEN
        ASM SET_TAC[];
        MP_TAC(ISPEC `c1:real^2->bool` OUTSIDE_NO_OVERLAP) THEN ASM SET_TAC[]];
      MATCH_MP_TAC MOI_S3TR_FRONTIER_INTER THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [ASM SET_TAC[];
        MP_TAC(ISPEC `inside c2:real^2->bool` MOI_S3TR_FRSUB) THEN
        ASM SET_TAC[];
        MP_TAC(ISPEC `c2:real^2->bool` INSIDE_NO_OVERLAP) THEN ASM SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(U:real^2->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `c1 UNION c2 SUBSET frontier (U:real^2->bool)` THEN
    ASM_REWRITE_TAC[FRONTIER_EMPTY] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(U:real^2->bool) IN components ((:real^2) DIFF (c1 UNION c2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3TR_OPEN_COMPONENT THEN
    EXISTS_TAC `inside c1 UNION outside c2:real^2->bool` THEN
    ASM_SIMP_TAC[OPEN_UNION];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (c1 UNION c2:real^2->bool) /\ ANR (c1 UNION c2)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_UNION] THEN MATCH_MP_TAC ANR_CLOSED_UNION THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
    UNDISCH_TAC `DISJOINT (c1:real^2->bool) c2` THEN
    REWRITE_TAC[DISJOINT] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ANR_EMPTY];
    ALL_TAC] THEN
  (* the first cross-cut *)
  FIRST_X_ASSUM(X_CHOOSE_TAC `y1:real^2` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY] o
    check (fun th -> concl th = `~(c1:real^2->bool = {})`)) THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `y2:real^2` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY] o
    check (fun th -> concl th = `~(c2:real^2->bool = {})`)) THEN
  MP_TAC(ISPECL [`c1 UNION c2:real^2->bool`; `U:real^2->bool`; `y1:real^2`; `y2:real^2`]
    MOI_S3TR_CROSS_ARC) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    UNDISCH_TAC `c1 UNION c2 SUBSET frontier (U:real^2->bool)` THEN
    UNDISCH_TAC `DISJOINT (c1:real^2->bool) c2` THEN
    UNDISCH_TAC `(y1:real^2) IN c1` THEN UNDISCH_TAC `(y2:real^2) IN c2` THEN
    SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `al:real^1->real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y1:real^2) IN path_image al /\ (y2:real^2) IN path_image al`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (U:real^2->bool) (c1 UNION c2) /\
                ~((y2:real^2) IN c1 UNION inside c1) /\
                ~((y1:real^2) IN c2 UNION outside c2)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `DISJOINT (U:real^2->bool) (c1 UNION inside c1)` THEN
    UNDISCH_TAC `DISJOINT (U:real^2->bool) (c2 UNION outside c2)` THEN
    UNDISCH_TAC `DISJOINT (c1 UNION inside c1) (c2 UNION outside c2:real^2->bool)` THEN
    UNDISCH_TAC `(y1:real^2) IN c1` THEN UNDISCH_TAC `(y2:real^2) IN c2` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `path_image (al:real^1->real^2) INTER (c1 UNION c2) = {y1,y2}`
  ASSUME_TAC THENL
   [UNDISCH_TAC `path_image (al:real^1->real^2) SUBSET U UNION {y1, y2}` THEN
    UNDISCH_TAC `DISJOINT (U:real^2->bool) (c1 UNION c2)` THEN
    MAP_EVERY UNDISCH_TAC [`(y1:real^2) IN path_image al`; `(y2:real^2) IN path_image al`;
                           `(y1:real^2) IN c1`; `(y2:real^2) IN c2`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `path_image al INTER (c1 UNION inside c1) = {y1:real^2}`
  ASSUME_TAC THENL
   [UNDISCH_TAC `path_image (al:real^1->real^2) SUBSET U UNION {y1, y2}` THEN
    UNDISCH_TAC `DISJOINT (U:real^2->bool) (c1 UNION inside c1)` THEN
    MAP_EVERY UNDISCH_TAC [`(y1:real^2) IN path_image al`;
                           `~((y2:real^2) IN c1 UNION inside c1)`;
                           `(y1:real^2) IN c1`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((c1 UNION inside c1) UNION path_image (al:real^1->real^2)) INTER
                (c2 UNION outside c2) = {y2:real^2}`
  ASSUME_TAC THENL
   [UNDISCH_TAC `path_image (al:real^1->real^2) SUBSET U UNION {y1, y2}` THEN
    UNDISCH_TAC `DISJOINT (U:real^2->bool) (c2 UNION outside c2)` THEN
    UNDISCH_TAC `DISJOINT (c1 UNION inside c1) (c2 UNION outside c2:real^2->bool)` THEN
    MAP_EVERY UNDISCH_TAC [`(y2:real^2) IN path_image al`;
                           `~((y1:real^2) IN c2 UNION outside c2)`;
                           `(y2:real^2) IN c2`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* U minus the first cross-cut *)
  ABBREV_TAC `U' = U DIFF path_image (al:real^1->real^2)` THEN
  SUBGOAL_THEN `open (U':real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "U'" THEN MATCH_MP_TAC OPEN_DIFF THEN
    ASM_SIMP_TAC[CLOSED_ARC_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected (outside c1 DIFF path_image (al:real^1->real^2))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `outside c1 DIFF path_image (al:real^1->real^2) =
                  (:real^2) DIFF ((c1 UNION inside c1) UNION path_image al)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `(:real^2) DIFF (c1 UNION inside c1) = outside c1` THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC JANISZEWSKI_CONNECTED THEN REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      ASM_SIMP_TAC[CLOSED_ARC_IMAGE];
      ONCE_REWRITE_TAC[INTER_COMM] THEN
      REWRITE_TAC[ASSUME `path_image al INTER (c1 UNION inside c1) = {y1:real^2}`] THEN
      REWRITE_TAC[CONNECTED_SING];
      REWRITE_TAC[ASSUME `(:real^2) DIFF (c1 UNION inside c1) = outside c1`] THEN
      FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC CONNECTED_ARC_COMPLEMENT THEN ASM_REWRITE_TAC[DIMINDEX_2; LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected (U':real^2->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `U' = (:real^2) DIFF (((c1 UNION inside c1) UNION path_image (al:real^1->real^2)) UNION
                           (c2 UNION outside c2))`
    SUBST1_TAC THENL
     [EXPAND_TAC "U'" THEN EXPAND_TAC "U" THEN
      UNDISCH_TAC `(:real^2) DIFF (c1 UNION inside c1) = outside c1` THEN
      UNDISCH_TAC `(:real^2) DIFF (c2 UNION outside c2) = inside c2` THEN
      SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC JANISZEWSKI_CONNECTED THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_UNION THEN ASM_SIMP_TAC[COMPACT_ARC_IMAGE];
      FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[ASSUME `((c1 UNION inside c1) UNION path_image (al:real^1->real^2)) INTER
                          (c2 UNION outside c2) = {y2:real^2}`] THEN
      REWRITE_TAC[CONNECTED_SING];
      SUBGOAL_THEN `(:real^2) DIFF ((c1 UNION inside c1) UNION path_image al) =
                    outside c1 DIFF path_image (al:real^1->real^2)`
      SUBST1_TAC THENL
       [UNDISCH_TAC `(:real^2) DIFF (c1 UNION inside c1) = outside c1` THEN SET_TAC[];
        FIRST_ASSUM ACCEPT_TAC];
      REWRITE_TAC[ASSUME `(:real^2) DIFF (c2 UNION outside c2) = inside c2`] THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c1:real^2->bool`; `y1:real^2`] MOI_S3TR_JOTHER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `z1:real^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c2:real^2->bool`; `y2:real^2`] MOI_S3TR_JOTHER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `z2:real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~((z1:real^2) IN path_image (al:real^1->real^2)) /\
                ~((z2:real^2) IN path_image al) /\ ~(z1 = z2)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `path_image (al:real^1->real^2) INTER (c1 UNION c2) = {y1,y2}` THEN
    UNDISCH_TAC `DISJOINT (c1:real^2->bool) c2` THEN
    MAP_EVERY UNDISCH_TAC [`(z1:real^2) IN c1`; `(z2:real^2) IN c2`;
                           `(y1:real^2) IN c1`; `(y2:real^2) IN c2`;
                           `~(z1:real^2 = y1)`; `~(z2:real^2 = y2)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z1:real^2) IN frontier U' /\ (z2:real^2) IN frontier U'`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `U' = U INTER ((:real^2) DIFF path_image (al:real^1->real^2))`
    SUBST1_TAC THENL [EXPAND_TAC "U'" THEN SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THEN MATCH_MP_TAC MOI_S3TR_FRONTIER_INTER THEN
    ASM_SIMP_TAC[GSYM closed; CLOSED_ARC_IMAGE; IN_DIFF; IN_UNIV; IN_INTER] THEN
    (CONJ_TAC THENL
      [MP_TAC(ISPEC `U:real^2->bool` MOI_S3TR_FRSUB) THEN ASM SET_TAC[];
       ASM SET_TAC[]]);
    ALL_TAC] THEN
  SUBGOAL_THEN `(U':real^2->bool) IN
                components ((:real^2) DIFF ((c1 UNION c2) UNION path_image al))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3TR_OPEN_COMPONENT THEN
    EXISTS_TAC `inside c1 UNION outside c2:real^2->bool` THEN
    ASM_SIMP_TAC[OPEN_UNION] THEN CONJ_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `(z1:real^2) IN frontier U'` THEN
      ASM_REWRITE_TAC[FRONTIER_EMPTY; NOT_IN_EMPTY];
      ALL_TAC] THEN
    CONJ_TAC THENL [EXPAND_TAC "U'" THEN ASM SET_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "U'" THEN
    UNDISCH_TAC `path_image (al:real^1->real^2) SUBSET U UNION {y1, y2}` THEN
    UNDISCH_TAC `(:real^2) DIFF (c1 UNION c2) = U UNION (inside c1 UNION outside c2)` THEN
    UNDISCH_TAC `DISJOINT (U:real^2->bool) (inside c1 UNION outside c2)` THEN
    UNDISCH_TAC `(y1:real^2) IN c1` THEN UNDISCH_TAC `(y2:real^2) IN c2` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ANR ((c1 UNION c2) UNION path_image (al:real^1->real^2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ANR_CLOSED_UNION THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED; CLOSED_ARC_IMAGE; AR_IMP_ANR; AR_ARC_IMAGE] THEN
    ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FINITE_IMP_ANR THEN REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(c1 UNION c2) UNION path_image (al:real^1->real^2)`; `U':real^2->bool`;
                 `z1:real^2`; `z2:real^2`] MOI_S3TR_CROSS_ARC) THEN
  ASM_SIMP_TAC[COMPACT_UNION; COMPACT_ARC_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `be:real^1->real^2` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`al:real^1->real^2`; `be:real^1->real^2`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `U SUBSET inside c2 INTER outside (c1:real^2->bool)` MP_TAC THENL
   [EXPAND_TAC "U" THEN REWRITE_TAC[SUBSET_REFL]; ALL_TAC] THEN
  MP_TAC(ISPEC `be:real^1->real^2` PATHSTART_IN_PATH_IMAGE) THEN
  MP_TAC(ISPEC `be:real^1->real^2` PATHFINISH_IN_PATH_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `path_image (be:real^1->real^2) SUBSET U' UNION {z1, z2}` THEN
  EXPAND_TAC "U'" THEN
  UNDISCH_TAC `path_image (al:real^1->real^2) SUBSET U UNION {y1, y2}` THEN
  UNDISCH_TAC `DISJOINT (U:real^2->bool) (c1 UNION inside c1)` THEN
  UNDISCH_TAC `DISJOINT (U:real^2->bool) (c2 UNION outside c2)` THEN
  MAP_EVERY UNDISCH_TAC [`(z1:real^2) IN c1`; `(z2:real^2) IN c2`;
                         `~((z1:real^2) IN path_image (al:real^1->real^2))`;
                         `~((z2:real^2) IN path_image (al:real^1->real^2))`] THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The closed annulus between Jordan curves c1 inside c2, cut along two      *)
(* disjoint cross-cuts al (c1 to c2) and be, is the union of two closed      *)
(* disks bounded by the Jordan curves ka + al + pa + be and kb + al + pb +   *)
(* be (pa, pb the arcs of c1, ka, kb the arcs of c2), meeting exactly in     *)
(* the cross-cuts: the theta lemma SPLIT_INSIDE_SIMPLE_CLOSED_CURVE, first   *)
(* for c2 with the cross-cut al + pa + be, then for the side containing the  *)
(* inside of c1 with the cross-cut pb.                                       *)
(* ------------------------------------------------------------------------- *)

let MOI_S3TR_LOOP4 = prove
 (`!(ka:real^1->real^N) al pa be.
     arc ka /\ arc al /\ arc pa /\ arc be /\
     pathstart pa = pathstart al /\ pathfinish pa = pathstart be /\
     pathstart ka = pathfinish al /\ pathfinish ka = pathfinish be /\
     path_image ka INTER path_image al = {pathfinish al} /\
     path_image ka INTER path_image pa = {} /\
     path_image ka INTER path_image be = {pathfinish be} /\
     path_image al INTER path_image pa = {pathstart al} /\
     path_image al INTER path_image be = {} /\
     path_image pa INTER path_image be = {pathstart be}
     ==> arc (reversepath al ++ (pa ++ be)) /\
         pathstart (reversepath al ++ (pa ++ be)) = pathfinish al /\
         pathfinish (reversepath al ++ (pa ++ be)) = pathfinish be /\
         path_image (reversepath al ++ (pa ++ be)) =
         path_image al UNION path_image pa UNION path_image be /\
         simple_path (ka ++ reversepath (reversepath al ++ (pa ++ be))) /\
         pathfinish (ka ++ reversepath (reversepath al ++ (pa ++ be))) =
         pathstart (ka ++ reversepath (reversepath al ++ (pa ++ be))) /\
         path_image (ka ++ reversepath (reversepath al ++ (pa ++ be))) =
         path_image ka UNION path_image al UNION path_image pa UNION path_image be`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `arc (pa ++ be:real^1->real^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC ARC_JOIN THEN ASM_REWRITE_TAC[SUBSET_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `path_image (pa ++ be:real^1->real^N) = path_image pa UNION path_image be`
  ASSUME_TAC THENL [ASM_SIMP_TAC[PATH_IMAGE_JOIN]; ALL_TAC] THEN
  SUBGOAL_THEN `arc (reversepath al ++ (pa ++ be):real^1->real^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC ARC_JOIN THEN
    ASM_REWRITE_TAC[ARC_REVERSEPATH_EQ; PATHFINISH_REVERSEPATH; PATHSTART_JOIN;
                    PATH_IMAGE_REVERSEPATH] THEN
    UNDISCH_TAC `path_image al INTER path_image pa = {pathstart (al:real^1->real^N)}` THEN
    UNDISCH_TAC `path_image al INTER path_image be:real^N->bool = {}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `path_image (reversepath al ++ (pa ++ be):real^1->real^N) =
                path_image al UNION path_image pa UNION path_image be`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHFINISH_REVERSEPATH; PATHSTART_JOIN;
                 PATH_IMAGE_REVERSEPATH];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_REVERSEPATH;
                  PATHFINISH_REVERSEPATH] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_PATH_JOIN_LOOP THEN
    ASM_REWRITE_TAC[ARC_REVERSEPATH_EQ; PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH;
                    PATHSTART_JOIN; PATHFINISH_JOIN; PATH_IMAGE_REVERSEPATH] THEN
    UNDISCH_TAC `path_image ka INTER path_image al = {pathfinish (al:real^1->real^N)}` THEN
    UNDISCH_TAC `path_image ka INTER path_image pa:real^N->bool = {}` THEN
    UNDISCH_TAC `path_image ka INTER path_image be = {pathfinish (be:real^1->real^N)}` THEN
    SET_TAC[];
    ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_REVERSEPATH; PATHFINISH_JOIN;
                 PATH_IMAGE_REVERSEPATH]]);;

let MOI_S3TR_SIX_ARCS = prove
 (`!c1 c2 (al:real^1->real^2) be pa pb ka kb.
     pathstart pa = pathstart al /\ pathstart pb = pathstart al /\
     pathfinish pa = pathstart be /\ pathfinish pb = pathstart be /\
     pathstart ka = pathfinish al /\ pathstart kb = pathfinish al /\
     pathfinish ka = pathfinish be /\ pathfinish kb = pathfinish be /\
     path_image pa UNION path_image pb = c1 /\
     path_image pa INTER path_image pb = {pathstart al, pathstart be} /\
     path_image ka UNION path_image kb = c2 /\
     path_image ka INTER path_image kb = {pathfinish al, pathfinish be} /\
     DISJOINT c1 c2 /\
     path_image al INTER path_image be = {} /\
     path_image al INTER (c1 UNION c2) = {pathstart al, pathfinish al} /\
     path_image be INTER (c1 UNION c2) = {pathstart be, pathfinish be}
     ==> path_image ka INTER path_image al = {pathfinish al} /\
         path_image ka INTER path_image pa = {} /\
         path_image ka INTER path_image be = {pathfinish be} /\
         path_image kb INTER path_image al = {pathfinish al} /\
         path_image kb INTER path_image pb = {} /\
         path_image kb INTER path_image be = {pathfinish be} /\
         path_image al INTER path_image pa = {pathstart al} /\
         path_image pa INTER path_image be = {pathstart be} /\
         path_image al INTER path_image pb = {pathstart al} /\
         path_image pb INTER path_image be = {pathstart be} /\
         path_image ka INTER path_image pb = {} /\
         path_image kb INTER path_image pa = {} /\
         ~(pathstart al = pathstart be) /\ ~(pathfinish al = pathfinish be) /\
         pathstart al IN c1 /\ pathstart be IN c1 /\
         pathfinish al IN c2 /\ pathfinish be IN c2`,
  REPEAT GEN_TAC THEN
  MAP_EVERY ABBREV_TAC
   [`y1 = pathstart (al:real^1->real^2)`; `y2 = pathfinish (al:real^1->real^2)`;
    `z1 = pathstart (be:real^1->real^2)`; `z2 = pathfinish (be:real^1->real^2)`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(y1:real^2) IN path_image al /\ y1 IN path_image pa /\ y1 IN path_image pb /\
    (y2:real^2) IN path_image al /\ y2 IN path_image ka /\ y2 IN path_image kb /\
    (z1:real^2) IN path_image be /\ z1 IN path_image pa /\ z1 IN path_image pb /\
    (z2:real^2) IN path_image be /\ z2 IN path_image ka /\ z2 IN path_image kb`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `path_image pa SUBSET (c1:real^2->bool) /\ path_image pb SUBSET c1 /\
    path_image ka SUBSET (c2:real^2->bool) /\ path_image kb SUBSET c2`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(y1:real^2) IN c1 /\ (z1:real^2) IN c1 /\ (y2:real^2) IN c2 /\
                (z2:real^2) IN c2`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `path_image al INTER (c1:real^2->bool) = {y1} /\
                path_image al INTER (c2:real^2->bool) = {y2} /\
                path_image be INTER (c1:real^2->bool) = {z1} /\
                path_image be INTER (c2:real^2->bool) = {z2}`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `path_image al INTER (c1 UNION c2) = {y1:real^2, y2}` THEN
    UNDISCH_TAC `path_image be INTER (c1 UNION c2) = {z1:real^2, z2}` THEN
    UNDISCH_TAC `DISJOINT (c1:real^2->bool) c2` THEN
    MAP_EVERY UNDISCH_TAC [`(y1:real^2) IN c1`; `(z1:real^2) IN c1`;
                           `(y2:real^2) IN c2`; `(z2:real^2) IN c2`;
                           `(y1:real^2) IN path_image al`; `(y2:real^2) IN path_image al`;
                           `(z1:real^2) IN path_image be`; `(z2:real^2) IN path_image be`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(y1:real^2 = z1) /\ ~(y2:real^2 = z2)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `path_image al INTER path_image be:real^2->bool = {}` THEN
    MAP_EVERY UNDISCH_TAC [`(y1:real^2) IN path_image al`; `(y2:real^2) IN path_image al`;
                           `(z1:real^2) IN path_image be`; `(z2:real^2) IN path_image be`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN ASM SET_TAC[]);;

let MOI_S3TR_THETA_SETS = prove
 (`!c1 c2 Al Be Pa Pb Ka Kb I0 I1 I2 I3 IC2 (y1:real^2) y2 z1 z2.
     Pa UNION Pb = c1 /\ Pa INTER Pb = {y1,z1} /\ Ka UNION Kb = c2 /\
     Ka INTER Kb = {y2,z2} /\ DISJOINT c1 c2 /\ Al INTER Be = {} /\
     Al INTER (c1 UNION c2) = {y1,y2} /\ Be INTER (c1 UNION c2) = {z1,z2} /\
     y1 IN Pa /\ y1 IN Pb /\ y1 IN Al /\ z1 IN Pa /\ z1 IN Pb /\ z1 IN Be /\
     y2 IN Ka /\ y2 IN Kb /\ y2 IN Al /\ z2 IN Ka /\ z2 IN Kb /\ z2 IN Be /\
     I1 INTER I2 = {} /\ I1 UNION I2 UNION ((Al UNION Pa UNION Be) DIFF {y2,z2}) = IC2 /\
     I0 INTER I3 = {} /\ I0 UNION I3 UNION (Pb DIFF {y1,z1}) = I2 /\
     I1 INTER (Ka UNION Al UNION Pa UNION Be) = {} /\
     I2 INTER (Kb UNION Al UNION Pa UNION Be) = {} /\
     I3 INTER (Kb UNION Al UNION Pb UNION Be) = {} /\
     IC2 INTER c2 = {} /\ I0 INTER c1 = {} /\ I0 SUBSET IC2 /\ c1 SUBSET IC2
     ==> ((Ka UNION Al UNION Pa UNION Be) UNION I1) UNION
         ((Kb UNION Al UNION Pb UNION Be) UNION I3) = (c2 UNION IC2) DIFF I0 /\
         ((Ka UNION Al UNION Pa UNION Be) UNION I1) INTER
         ((Kb UNION Al UNION Pb UNION Be) UNION I3) = Al UNION Be`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN ASM SET_TAC[]);;

let MOI_S3TR_CLOSED4 = prove
 (`!a b c d:real^1->real^N.
     arc a /\ arc b /\ arc c /\ arc d
     ==> closed (path_image a UNION path_image b UNION path_image c UNION path_image d)`,
  REPEAT STRIP_TAC THEN REPEAT(MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC) THEN
  MATCH_MP_TAC CLOSED_ARC_IMAGE THEN ASM_REWRITE_TAC[]);;

let MOI_S3TR_THETA_SIDE = prove
 (`!c1 c2:real^2->bool (al:real^1->real^2) be pa pb ka kb.
     c1 homeomorphic sphere(vec 0:real^2,&1) /\
     c2 homeomorphic sphere(vec 0:real^2,&1) /\ c1 SUBSET inside c2 /\
     arc al /\ arc be /\ arc pa /\ arc pb /\ arc ka /\ arc kb /\
     pathstart pa = pathstart al /\ pathstart pb = pathstart al /\
     pathfinish pa = pathstart be /\ pathfinish pb = pathstart be /\
     pathstart ka = pathfinish al /\ pathstart kb = pathfinish al /\
     pathfinish ka = pathfinish be /\ pathfinish kb = pathfinish be /\
     path_image pa UNION path_image pb = c1 /\
     path_image pa INTER path_image pb = {pathstart al, pathstart be} /\
     path_image ka UNION path_image kb = c2 /\
     path_image ka INTER path_image kb = {pathfinish al, pathfinish be} /\
     path_image al INTER path_image be = {} /\
     path_image al INTER (c1 UNION c2) = {pathstart al, pathfinish al} /\
     path_image be INTER (c1 UNION c2) = {pathstart be, pathfinish be} /\
     path_image al SUBSET outside c1 UNION {pathstart al, pathfinish al} /\
     path_image be SUBSET outside c1 UNION {pathstart be, pathfinish be}
     ==> inside c1 SUBSET
         inside (path_image kb UNION path_image al UNION path_image pa UNION
                 path_image be) \/
         inside c1 SUBSET
         inside (path_image ka UNION path_image al UNION path_image pa UNION
                 path_image be)`,
  REPEAT GEN_TAC THEN
  MAP_EVERY ABBREV_TAC
   [`y1 = pathstart (al:real^1->real^2)`; `y2 = pathfinish (al:real^1->real^2)`;
    `z1 = pathstart (be:real^1->real^2)`; `z2 = pathfinish (be:real^1->real^2)`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `c1:real^2->bool` MOI_S3TR_JF) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `c2:real^2->bool` MOI_S3TR_JF) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`c2:real^2->bool`; `c1:real^2->bool`] MOI_S3TR_JNEST) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `DISJOINT (c1:real^2->bool) c2` ASSUME_TAC THENL
   [MP_TAC(ISPEC `c2:real^2->bool` INSIDE_NO_OVERLAP) THEN
    UNDISCH_TAC `(c1:real^2->bool) SUBSET inside c2` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c1:real^2->bool`; `c2:real^2->bool`; `al:real^1->real^2`;
                 `be:real^1->real^2`; `pa:real^1->real^2`; `pb:real^1->real^2`;
                 `ka:real^1->real^2`; `kb:real^1->real^2`] MOI_S3TR_SIX_ARCS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(y1:real^2) IN path_image al /\ y1 IN path_image pa /\ y1 IN path_image pb /\
    (y2:real^2) IN path_image al /\ y2 IN path_image ka /\ y2 IN path_image kb /\
    (z1:real^2) IN path_image be /\ z1 IN path_image pa /\ z1 IN path_image pb /\
    (z2:real^2) IN path_image be /\ z2 IN path_image ka /\ z2 IN path_image kb`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE]; ALL_TAC] THEN
  (* theta lemma 1: c2 = ka + kb with the cross-cut L = al + pa + be *)
  MP_TAC(ISPECL [`ka:real^1->real^2`; `al:real^1->real^2`; `pa:real^1->real^2`;
                 `be:real^1->real^2`] MOI_S3TR_LOOP4) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`ka:real^1->real^2`; `kb:real^1->real^2`;
                 `reversepath al ++ (pa ++ be):real^1->real^2`;
                 `y2:real^2`; `z2:real^2`] SPLIT_INSIDE_SIMPLE_CLOSED_CURVE) THEN
  ASM_SIMP_TAC[ARC_IMP_SIMPLE_PATH] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `path_image ka INTER path_image al = {y2:real^2}` THEN
      UNDISCH_TAC `path_image ka INTER path_image pa:real^2->bool = {}` THEN
      UNDISCH_TAC `path_image ka INTER path_image be = {z2:real^2}` THEN
      MAP_EVERY UNDISCH_TAC [`(y2:real^2) IN path_image ka`;
                             `(z2:real^2) IN path_image ka`] THEN SET_TAC[];
      UNDISCH_TAC `path_image kb INTER path_image al = {y2:real^2}` THEN
      UNDISCH_TAC `path_image kb INTER path_image pa:real^2->bool = {}` THEN
      UNDISCH_TAC `path_image kb INTER path_image be = {z2:real^2}` THEN
      MAP_EVERY UNDISCH_TAC [`(y2:real^2) IN path_image kb`;
                             `(z2:real^2) IN path_image kb`] THEN SET_TAC[];
      UNDISCH_TAC `path_image pa UNION path_image pb = (c1:real^2->bool)` THEN
      UNDISCH_TAC `(c1:real^2->bool) SUBSET inside c2` THEN
      UNDISCH_TAC `path_image ka UNION path_image kb = (c2:real^2->bool)` THEN
      UNDISCH_TAC `(y1:real^2) IN path_image pa` THEN SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the inside of c1 misses the cross-cut and lies in one of the two sides *)
  ABBREV_TAC `I1 = inside (path_image ka UNION path_image al UNION path_image pa UNION
                           path_image (be:real^1->real^2))` THEN
  ABBREV_TAC `I2 = inside (path_image kb UNION path_image al UNION path_image pa UNION
                           path_image (be:real^1->real^2))` THEN
  SUBGOAL_THEN `inside c1 SUBSET (I1:real^2->bool) UNION I2` ASSUME_TAC THENL
   [MP_TAC(ISPEC `c1:real^2->bool` INSIDE_NO_OVERLAP) THEN
    UNDISCH_TAC `inside c1 INTER outside c1:real^2->bool = {}` THEN
    UNDISCH_TAC `inside c1 SUBSET inside (c2:real^2->bool)` THEN
    UNDISCH_TAC `path_image pa UNION path_image pb = (c1:real^2->bool)` THEN
    UNDISCH_TAC `path_image al SUBSET outside c1 UNION {y1:real^2, y2}` THEN
    UNDISCH_TAC `path_image be SUBSET outside c1 UNION {z1:real^2, z2}` THEN
    UNDISCH_TAC `I1 UNION I2 UNION
                 (path_image al UNION path_image pa UNION path_image be) DIFF {y2, z2} =
                 inside (c2:real^2->bool)` THEN
    MAP_EVERY UNDISCH_TAC [`(y1:real^2) IN c1`; `(z1:real^2) IN c1`;
                           `(y2:real^2) IN c2`; `(z2:real^2) IN c2`;
                           `(c2:real^2->bool) SUBSET outside c1`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (I1:real^2->bool) /\ open (I2:real^2->bool)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["I1"; "I2"] THEN CONJ_TAC THEN
    MATCH_MP_TAC OPEN_INSIDE THEN MATCH_MP_TAC MOI_S3TR_CLOSED4 THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [connected] o check (fun th ->
    concl th = `connected (inside c1:real^2->bool)`)) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`I1:real^2->bool`; `I2:real^2->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `I1 INTER I2:real^2->bool = {}` THEN
  UNDISCH_TAC `inside c1 SUBSET (I1:real^2->bool) UNION I2` THEN
  SET_TAC[]);;

let MOI_S3TR_THETA_DECOMP = prove
 (`!c1 c2:real^2->bool (al:real^1->real^2) be pa pb ka kb.
     c1 homeomorphic sphere(vec 0:real^2,&1) /\
     c2 homeomorphic sphere(vec 0:real^2,&1) /\ c1 SUBSET inside c2 /\
     arc al /\ arc be /\ arc pa /\ arc pb /\ arc ka /\ arc kb /\
     pathstart pa = pathstart al /\ pathstart pb = pathstart al /\
     pathfinish pa = pathstart be /\ pathfinish pb = pathstart be /\
     pathstart ka = pathfinish al /\ pathstart kb = pathfinish al /\
     pathfinish ka = pathfinish be /\ pathfinish kb = pathfinish be /\
     path_image pa UNION path_image pb = c1 /\
     path_image pa INTER path_image pb = {pathstart al, pathstart be} /\
     path_image ka UNION path_image kb = c2 /\
     path_image ka INTER path_image kb = {pathfinish al, pathfinish be} /\
     path_image al INTER path_image be = {} /\
     path_image al INTER (c1 UNION c2) = {pathstart al, pathfinish al} /\
     path_image be INTER (c1 UNION c2) = {pathstart be, pathfinish be} /\
     inside c1 SUBSET
     inside (path_image kb UNION path_image al UNION path_image pa UNION path_image be)
     ==> ((path_image ka UNION path_image al UNION path_image pa UNION path_image be) UNION
          inside (path_image ka UNION path_image al UNION path_image pa UNION
                  path_image be)) UNION
         ((path_image kb UNION path_image al UNION path_image pb UNION path_image be) UNION
          inside (path_image kb UNION path_image al UNION path_image pb UNION
                  path_image be)) =
         (c2 UNION inside c2) DIFF inside c1 /\
         ((path_image ka UNION path_image al UNION path_image pa UNION path_image be) UNION
          inside (path_image ka UNION path_image al UNION path_image pa UNION
                  path_image be)) INTER
         ((path_image kb UNION path_image al UNION path_image pb UNION path_image be) UNION
          inside (path_image kb UNION path_image al UNION path_image pb UNION
                  path_image be)) =
         path_image al UNION path_image be`,
  REPEAT GEN_TAC THEN
  MAP_EVERY ABBREV_TAC
   [`y1 = pathstart (al:real^1->real^2)`; `y2 = pathfinish (al:real^1->real^2)`;
    `z1 = pathstart (be:real^1->real^2)`; `z2 = pathfinish (be:real^1->real^2)`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `c1:real^2->bool` MOI_S3TR_JF) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `c2:real^2->bool` MOI_S3TR_JF) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`c2:real^2->bool`; `c1:real^2->bool`] MOI_S3TR_JNEST) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `DISJOINT (c1:real^2->bool) c2` ASSUME_TAC THENL
   [MP_TAC(ISPEC `c2:real^2->bool` INSIDE_NO_OVERLAP) THEN
    UNDISCH_TAC `(c1:real^2->bool) SUBSET inside c2` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c1:real^2->bool`; `c2:real^2->bool`; `al:real^1->real^2`;
                 `be:real^1->real^2`; `pa:real^1->real^2`; `pb:real^1->real^2`;
                 `ka:real^1->real^2`; `kb:real^1->real^2`] MOI_S3TR_SIX_ARCS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(y1:real^2) IN path_image al /\ y1 IN path_image pa /\ y1 IN path_image pb /\
    (y2:real^2) IN path_image al /\ y2 IN path_image ka /\ y2 IN path_image kb /\
    (z1:real^2) IN path_image be /\ z1 IN path_image pa /\ z1 IN path_image pb /\
    (z2:real^2) IN path_image be /\ z2 IN path_image ka /\ z2 IN path_image kb`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE]; ALL_TAC] THEN
  (* theta lemma 1: c2 = ka + kb with the cross-cut L = al + pa + be *)
  MP_TAC(ISPECL [`ka:real^1->real^2`; `al:real^1->real^2`; `pa:real^1->real^2`;
                 `be:real^1->real^2`] MOI_S3TR_LOOP4) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`ka:real^1->real^2`; `kb:real^1->real^2`;
                 `reversepath al ++ (pa ++ be):real^1->real^2`;
                 `y2:real^2`; `z2:real^2`] SPLIT_INSIDE_SIMPLE_CLOSED_CURVE) THEN
  ASM_SIMP_TAC[ARC_IMP_SIMPLE_PATH] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `path_image ka INTER path_image al = {y2:real^2}` THEN
      UNDISCH_TAC `path_image ka INTER path_image pa:real^2->bool = {}` THEN
      UNDISCH_TAC `path_image ka INTER path_image be = {z2:real^2}` THEN
      MAP_EVERY UNDISCH_TAC [`(y2:real^2) IN path_image ka`;
                             `(z2:real^2) IN path_image ka`] THEN SET_TAC[];
      UNDISCH_TAC `path_image kb INTER path_image al = {y2:real^2}` THEN
      UNDISCH_TAC `path_image kb INTER path_image pa:real^2->bool = {}` THEN
      UNDISCH_TAC `path_image kb INTER path_image be = {z2:real^2}` THEN
      MAP_EVERY UNDISCH_TAC [`(y2:real^2) IN path_image kb`;
                             `(z2:real^2) IN path_image kb`] THEN SET_TAC[];
      UNDISCH_TAC `path_image pa UNION path_image pb = (c1:real^2->bool)` THEN
      UNDISCH_TAC `(c1:real^2->bool) SUBSET inside c2` THEN
      UNDISCH_TAC `path_image ka UNION path_image kb = (c2:real^2->bool)` THEN
      UNDISCH_TAC `(y1:real^2) IN path_image pa` THEN SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `arc (kb ++ reversepath be:real^1->real^2)` ASSUME_TAC THENL
   [MATCH_MP_TAC ARC_JOIN THEN
    ASM_REWRITE_TAC[ARC_REVERSEPATH_EQ; PATHSTART_REVERSEPATH; PATH_IMAGE_REVERSEPATH] THEN
    UNDISCH_TAC `path_image kb INTER path_image be = {z2:real^2}` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `path_image (kb ++ reversepath be:real^1->real^2) =
                path_image kb UNION path_image be` ASSUME_TAC THENL
   [ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_REVERSEPATH; PATH_IMAGE_REVERSEPATH];
    ALL_TAC] THEN
  SUBGOAL_THEN `arc (al ++ (kb ++ reversepath be):real^1->real^2)` ASSUME_TAC THENL
   [MATCH_MP_TAC ARC_JOIN THEN ASM_REWRITE_TAC[PATHSTART_JOIN] THEN
    UNDISCH_TAC `path_image kb INTER path_image al = {y2:real^2}` THEN
    UNDISCH_TAC `path_image al INTER path_image be:real^2->bool = {}` THEN
    UNDISCH_TAC `(y2:real^2) IN path_image al` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `path_image (al ++ (kb ++ reversepath be):real^1->real^2) =
                path_image al UNION path_image kb UNION path_image be` ASSUME_TAC THENL
   [ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_JOIN];
    ALL_TAC] THEN
  SUBGOAL_THEN `?w:real^2. w IN path_image pb /\ ~(w = y1) /\ ~(w = z1)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `pb:real^1->real^2` INFINITE_ARC_IMAGE) THEN
    ASM_REWRITE_TAC[INFINITE] THEN
    MATCH_MP_TAC(TAUT `(~q ==> p) ==> ~p ==> q`) THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{y1:real^2, z1}` THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN
    POP_ASSUM MP_TAC THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^2) IN c1` ASSUME_TAC THENL
   [UNDISCH_TAC `path_image pa UNION path_image pb = (c1:real^2->bool)` THEN
    UNDISCH_TAC `(w:real^2) IN path_image pb` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((w:real^2) IN path_image kb UNION path_image al UNION
                              path_image pa UNION path_image be)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNION; DE_MORGAN_THM] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `path_image ka UNION path_image kb = (c2:real^2->bool)` THEN
      UNDISCH_TAC `DISJOINT (c1:real^2->bool) c2` THEN
      UNDISCH_TAC `(w:real^2) IN c1` THEN SET_TAC[];
      UNDISCH_TAC `path_image al INTER (c1 UNION c2) = {y1:real^2, y2}` THEN
      UNDISCH_TAC `DISJOINT (c1:real^2->bool) c2` THEN
      MAP_EVERY UNDISCH_TAC [`(w:real^2) IN c1`; `~(w:real^2 = y1)`; `(y2:real^2) IN c2`] THEN
      SET_TAC[];
      UNDISCH_TAC `path_image pa INTER path_image pb = {y1:real^2, z1}` THEN
      MAP_EVERY UNDISCH_TAC [`(w:real^2) IN path_image pb`; `~(w:real^2 = y1)`;
                             `~(w:real^2 = z1)`] THEN
      SET_TAC[];
      UNDISCH_TAC `path_image be INTER (c1 UNION c2) = {z1:real^2, z2}` THEN
      UNDISCH_TAC `DISJOINT (c1:real^2->bool) c2` THEN
      MAP_EVERY UNDISCH_TAC [`(w:real^2) IN c1`; `~(w:real^2 = z1)`; `(z2:real^2) IN c2`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(w:real^2) IN inside (path_image kb UNION path_image al UNION
                          path_image pa UNION path_image be)`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `path_image kb UNION path_image al UNION path_image pa UNION
                  path_image (be:real^1->real^2)` CLOSURE_INSIDE_SUBSET) THEN
    ANTS_TAC THENL [MATCH_MP_TAC MOI_S3TR_CLOSED4 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `(w:real^2) IN cl /\ ~(w IN g) ==> cl SUBSET g UNION i ==> w IN i`) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`inside c1:real^2->bool`;
                   `inside (path_image kb UNION path_image al UNION path_image pa UNION
                            path_image (be:real^1->real^2))`] SUBSET_CLOSURE) THEN
    REWRITE_TAC[ASSUME `inside c1 SUBSET
                        inside (path_image kb UNION path_image al UNION path_image pa UNION
                                path_image (be:real^1->real^2))`] THEN
    MP_TAC(ISPEC `inside c1:real^2->bool` MOI_S3TR_FRSUB) THEN
    REWRITE_TAC[ASSUME `frontier (inside c1:real^2->bool) = c1`] THEN
    UNDISCH_TAC `(w:real^2) IN c1` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `path_image pa UNION path_image al UNION path_image kb UNION path_image be =
    path_image kb UNION path_image al UNION path_image pa UNION
    path_image (be:real^1->real^2) /\
    (path_image al UNION path_image kb UNION path_image be) UNION path_image pb =
    path_image kb UNION path_image al UNION path_image pb UNION
    path_image (be:real^1->real^2)`
  STRIP_ASSUME_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`pa:real^1->real^2`; `al ++ (kb ++ reversepath be):real^1->real^2`;
                 `pb:real^1->real^2`; `y1:real^2`; `z1:real^2`]
    SPLIT_INSIDE_SIMPLE_CLOSED_CURVE) THEN
  ASM_SIMP_TAC[ARC_IMP_SIMPLE_PATH; PATHSTART_JOIN; PATHFINISH_JOIN;
               PATHFINISH_REVERSEPATH] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `path_image al INTER path_image pa = {y1:real^2}` THEN
      UNDISCH_TAC `path_image kb INTER path_image pa:real^2->bool = {}` THEN
      UNDISCH_TAC `path_image pa INTER path_image be = {z1:real^2}` THEN SET_TAC[];
      UNDISCH_TAC `path_image al INTER path_image pb = {y1:real^2}` THEN
      UNDISCH_TAC `path_image kb INTER path_image pb:real^2->bool = {}` THEN
      UNDISCH_TAC `path_image pb INTER path_image be = {z1:real^2}` THEN SET_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `w:real^2` THEN
      ASM_REWRITE_TAC[IN_INTER]];
    STRIP_TAC] THEN
  MATCH_MP_TAC(ISPECL
   [`c1:real^2->bool`; `c2:real^2->bool`; `path_image (al:real^1->real^2)`;
    `path_image (be:real^1->real^2)`; `path_image (pa:real^1->real^2)`;
    `path_image (pb:real^1->real^2)`; `path_image (ka:real^1->real^2)`;
    `path_image (kb:real^1->real^2)`; `inside c1:real^2->bool`;
    `inside (path_image ka UNION path_image al UNION path_image pa UNION
             path_image (be:real^1->real^2))`;
    `inside (path_image kb UNION path_image al UNION path_image pa UNION
             path_image (be:real^1->real^2))`;
    `inside (path_image kb UNION path_image al UNION path_image pb UNION
             path_image (be:real^1->real^2))`;
    `inside c2:real^2->bool`; `y1:real^2`; `y2:real^2`; `z1:real^2`; `z2:real^2`]
   MOI_S3TR_THETA_SETS) THEN
  ASM_REWRITE_TAC[INSIDE_NO_OVERLAP]);;

(* ------------------------------------------------------------------------- *)
(* Pasting homeomorphisms of compact sets that agree on the overlap and     *)
(* whose images overlap only in the image of the overlap; the four-arc       *)
(* version for the Jordan curves ka + al + pa + be, with prescribed maps on  *)
(* the cross-cuts al and be (HOMEOMORPHISM_ARC_IMAGES for the other arcs).   *)
(* ------------------------------------------------------------------------- *)

let MOI_S3TR_PASTE2 = prove
 (`!(f1:real^N->real^M) g1 f2 g2 s1 t1 s2 t2.
     homeomorphism (s1,t1) (f1,g1) /\ homeomorphism (s2,t2) (f2,g2) /\
     compact s1 /\ compact s2 /\
     (!x. x IN s1 INTER s2 ==> f1 x = f2 x) /\
     t1 INTER t2 SUBSET IMAGE f1 (s1 INTER s2)
     ==> ?f g. homeomorphism (s1 UNION s2,t1 UNION t2) (f,g) /\
               (!x. x IN s1 ==> f x = f1 x) /\ (!x. x IN s2 ==> f x = f2 x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
    concl th = `homeomorphism (s1:real^N->bool,t1:real^M->bool) (f1,g1)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
    concl th = `homeomorphism (s2:real^N->bool,t2:real^M->bool) (f2,g2)`)) THEN
  ABBREV_TAC `f = \x:real^N. if x IN s1 then (f1:real^N->real^M) x else f2 x` THEN
  SUBGOAL_THEN `(!x:real^N. x IN s1 ==> f x = (f1:real^N->real^M) x) /\
                (!x. x IN s2 ==> f x = f2 x)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN REWRITE_TAC[] THEN ASM_MESON_TAC[IN_INTER]; ALL_TAC] THEN
  SUBGOAL_THEN `!x y:real^N. x IN s1 /\ y IN s2 /\ (f1:real^N->real^M) x = f2 y ==> x = y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(f1:real^N->real^M) x IN IMAGE f1 (s1 INTER s2)` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        concl th = `t1 INTER t2 SUBSET IMAGE (f1:real^N->real^M) (s1 INTER s2)`)) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `x:real^N = w` SUBST_ALL_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[IN_INTER];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s1 UNION s2:real^N->bool`; `f:real^N->real^M`;
                 `t1 UNION t2:real^M->bool`] HOMEOMORPHISM_COMPACT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_UNION] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_UNION THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
      CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THENL
       [EXISTS_TAC `f1:real^N->real^M`; EXISTS_TAC `f2:real^N->real^M`] THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[IMAGE_UNION] THEN BINOP_TAC THEN ASM SET_TAC[];
      REWRITE_TAC[IN_UNION] THEN MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
      STRIP_TAC THEN ASM_MESON_TAC[]];
    DISCH_THEN(X_CHOOSE_TAC `g:real^M->real^N`) THEN
    MAP_EVERY EXISTS_TAC [`f:real^N->real^M`; `g:real^M->real^N`] THEN
    ASM_REWRITE_TAC[]]);;

let MOI_S3TR_PASTE4 = prove
 (`!(ka:real^1->real^2) al pa be (ka2:real^1->real^2) al2 pa2 be2 fa fa' fb fb'.
     arc ka /\ arc al /\ arc pa /\ arc be /\
     pathstart pa = pathstart al /\ pathfinish pa = pathstart be /\
     pathstart ka = pathfinish al /\ pathfinish ka = pathfinish be /\
     path_image ka INTER path_image al = {pathfinish al} /\
     path_image ka INTER path_image pa = {} /\
     path_image ka INTER path_image be = {pathfinish be} /\
     path_image al INTER path_image pa = {pathstart al} /\
     path_image al INTER path_image be = {} /\
     path_image pa INTER path_image be = {pathstart be} /\
     arc ka2 /\ arc al2 /\ arc pa2 /\ arc be2 /\
     pathstart pa2 = pathstart al2 /\ pathfinish pa2 = pathstart be2 /\
     pathstart ka2 = pathfinish al2 /\ pathfinish ka2 = pathfinish be2 /\
     path_image ka2 INTER path_image al2 = {pathfinish al2} /\
     path_image ka2 INTER path_image pa2 = {} /\
     path_image ka2 INTER path_image be2 = {pathfinish be2} /\
     path_image al2 INTER path_image pa2 = {pathstart al2} /\
     path_image al2 INTER path_image be2 = {} /\
     path_image pa2 INTER path_image be2 = {pathstart be2} /\
     homeomorphism (path_image al,path_image al2) (fa,fa') /\
     fa (pathstart al) = pathstart al2 /\ fa (pathfinish al) = pathfinish al2 /\
     homeomorphism (path_image be,path_image be2) (fb,fb') /\
     fb (pathstart be) = pathstart be2 /\ fb (pathfinish be) = pathfinish be2
     ==> ?G G'. homeomorphism
                  (path_image ka UNION path_image al UNION path_image pa UNION
                   path_image be,
                   path_image ka2 UNION path_image al2 UNION path_image pa2 UNION
                   path_image be2) (G,G') /\
                (!x. x IN path_image al ==> G x = fa x) /\
                (!x. x IN path_image be ==> G x = fb x)`,
  REPEAT GEN_TAC THEN
  MAP_EVERY ABBREV_TAC
   [`y1 = pathstart (al:real^1->real^2)`; `y2 = pathfinish (al:real^1->real^2)`;
    `z1 = pathstart (be:real^1->real^2)`; `z2 = pathfinish (be:real^1->real^2)`;
    `y1' = pathstart (al2:real^1->real^2)`; `y2' = pathfinish (al2:real^1->real^2)`;
    `z1' = pathstart (be2:real^1->real^2)`; `z2' = pathfinish (be2:real^1->real^2)`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`pa:real^1->real^2`; `pa2:real^1->real^2`] HOMEOMORPHISM_ARC_IMAGES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `fp:real^2->real^2` (X_CHOOSE_THEN `fp':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`ka:real^1->real^2`; `ka2:real^1->real^2`] HOMEOMORPHISM_ARC_IMAGES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `fk:real^2->real^2` (X_CHOOSE_THEN `fk':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `(y1:real^2) IN path_image al /\ (y2:real^2) IN path_image al /\
    (z1:real^2) IN path_image be /\ (z2:real^2) IN path_image be /\
    y1 IN path_image pa /\ z1 IN path_image pa /\
    y2 IN path_image ka /\ z2 IN path_image ka`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE]; ALL_TAC] THEN
  (* al + pa *)
  MP_TAC(ISPECL [`fa:real^2->real^2`; `fa':real^2->real^2`; `fp:real^2->real^2`;
                 `fp':real^2->real^2`; `path_image (al:real^1->real^2)`;
                 `path_image (al2:real^1->real^2)`; `path_image (pa:real^1->real^2)`;
                 `path_image (pa2:real^1->real^2)`] MOI_S3TR_PASTE2) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_ARC_IMAGE] THEN
    REWRITE_TAC[ASSUME `path_image al INTER path_image pa = {y1:real^2}`;
                ASSUME `path_image al2 INTER path_image pa2 = {y1':real^2}`;
                IN_SING; IMAGE_CLAUSES] THEN
    CONJ_TAC THENL
     [GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[SUBSET_REFL]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h1:real^2->real^2` (X_CHOOSE_THEN `h1':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  (* + be *)
  MP_TAC(ISPECL [`h1:real^2->real^2`; `h1':real^2->real^2`; `fb:real^2->real^2`;
                 `fb':real^2->real^2`; `path_image al UNION path_image (pa:real^1->real^2)`;
                 `path_image al2 UNION path_image (pa2:real^1->real^2)`;
                 `path_image (be:real^1->real^2)`;
                 `path_image (be2:real^1->real^2)`] MOI_S3TR_PASTE2) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_ARC_IMAGE; COMPACT_UNION] THEN
    SUBGOAL_THEN `(path_image al UNION path_image pa) INTER path_image be = {z1:real^2} /\
                  (path_image al2 UNION path_image pa2) INTER path_image be2 = {z1':real^2}`
    (fun th -> REWRITE_TAC[th; IN_SING; IMAGE_CLAUSES]) THENL
     [UNDISCH_TAC `path_image al INTER path_image be:real^2->bool = {}` THEN
      UNDISCH_TAC `path_image pa INTER path_image be = {z1:real^2}` THEN
      UNDISCH_TAC `path_image al2 INTER path_image be2:real^2->bool = {}` THEN
      UNDISCH_TAC `path_image pa2 INTER path_image be2 = {z1':real^2}` THEN
      SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN `(h1:real^2->real^2) z1 = fp z1` SUBST1_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
      SUBGOAL_THEN `(h1:real^2->real^2) z1 = fp z1` SUBST1_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[SUBSET_REFL]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h2:real^2->real^2` (X_CHOOSE_THEN `h2':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(h2:real^2->real^2) y2 = y2' /\ (h2:real^2->real^2) z2 = z2'`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(h1:real^2->real^2) y2` THEN CONJ_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_UNION];
        MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(fa:real^2->real^2) y2` THEN CONJ_TAC THENL
         [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]];
      MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(fb:real^2->real^2) z2` THEN CONJ_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h2:real^2->real^2`; `h2':real^2->real^2`; `fk:real^2->real^2`;
                 `fk':real^2->real^2`;
                 `(path_image al UNION path_image pa) UNION path_image (be:real^1->real^2)`;
                 `(path_image al2 UNION path_image pa2) UNION path_image (be2:real^1->real^2)`;
                 `path_image (ka:real^1->real^2)`;
                 `path_image (ka2:real^1->real^2)`] MOI_S3TR_PASTE2) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_ARC_IMAGE; COMPACT_UNION] THEN
    SUBGOAL_THEN `((path_image al UNION path_image pa) UNION path_image be) INTER
                  path_image ka = {y2:real^2, z2} /\
                  ((path_image al2 UNION path_image pa2) UNION path_image be2) INTER
                  path_image ka2 = {y2':real^2, z2'}`
    (fun th -> REWRITE_TAC[th; IN_INSERT; NOT_IN_EMPTY; IMAGE_CLAUSES]) THENL
     [UNDISCH_TAC `path_image ka INTER path_image al = {y2:real^2}` THEN
      UNDISCH_TAC `path_image ka INTER path_image pa:real^2->bool = {}` THEN
      UNDISCH_TAC `path_image ka INTER path_image be = {z2:real^2}` THEN
      UNDISCH_TAC `path_image ka2 INTER path_image al2 = {y2':real^2}` THEN
      UNDISCH_TAC `path_image ka2 INTER path_image pa2:real^2->bool = {}` THEN
      UNDISCH_TAC `path_image ka2 INTER path_image be2 = {z2':real^2}` THEN
      SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `G:real^2->real^2` (X_CHOOSE_THEN `G':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`G:real^2->real^2`; `G':real^2->real^2`] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `path_image ka UNION path_image al UNION path_image pa UNION path_image be =
      ((path_image al UNION path_image pa) UNION path_image be) UNION
      path_image (ka:real^1->real^2) /\
      path_image ka2 UNION path_image al2 UNION path_image pa2 UNION path_image be2 =
      ((path_image al2 UNION path_image pa2) UNION path_image be2) UNION
      path_image (ka2:real^1->real^2)`
    (fun th -> REWRITE_TAC[th]) THENL [SET_TAC[]; FIRST_ASSUM ACCEPT_TAC];
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(h2:real^2->real^2) x` THEN CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_UNION]; ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(h1:real^2->real^2) x` THEN CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_UNION];
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(h2:real^2->real^2) x` THEN CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_UNION];
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Annulus configurations: two cross-cuts al, be of the closed annulus       *)
(* between Jordan curves c1 inside c2, the arcs pa, pb of c1 and ka, kb of   *)
(* c2 between their ends, with the annulus the union of the two closed disks *)
(* bounded by ka + al + pa + be and kb + al + pb + be, meeting exactly in    *)
(* the cross-cuts.  Every nested pair has one, and two configurations give a *)
(* homeomorphism of the closed annuli (strong Schoenflies JORDAN_SCHOENFLIES *)
(* on the two disks with the same maps on the cross-cuts, then pasting).     *)
(* ------------------------------------------------------------------------- *)

let moi_s3tr_anncfg = new_definition
 `moi_s3tr_anncfg (c1:real^2->bool) c2 (al:real^1->real^2) be pa pb ka kb <=>
    arc al /\ arc be /\ arc pa /\ arc pb /\ arc ka /\ arc kb /\
    pathstart pa = pathstart al /\ pathstart pb = pathstart al /\
    pathfinish pa = pathstart be /\ pathfinish pb = pathstart be /\
    pathstart ka = pathfinish al /\ pathstart kb = pathfinish al /\
    pathfinish ka = pathfinish be /\ pathfinish kb = pathfinish be /\
    path_image pa UNION path_image pb = c1 /\
    path_image pa INTER path_image pb = {pathstart al, pathstart be} /\
    path_image ka UNION path_image kb = c2 /\
    path_image ka INTER path_image kb = {pathfinish al, pathfinish be} /\
    DISJOINT c1 c2 /\
    path_image al INTER path_image be = {} /\
    path_image al INTER (c1 UNION c2) = {pathstart al, pathfinish al} /\
    path_image be INTER (c1 UNION c2) = {pathstart be, pathfinish be} /\
    ((path_image ka UNION path_image al UNION path_image pa UNION path_image be) UNION
     inside (path_image ka UNION path_image al UNION path_image pa UNION
             path_image be)) UNION
    ((path_image kb UNION path_image al UNION path_image pb UNION path_image be) UNION
     inside (path_image kb UNION path_image al UNION path_image pb UNION
             path_image be)) =
    (c2 UNION inside c2) DIFF inside c1 /\
    ((path_image ka UNION path_image al UNION path_image pa UNION path_image be) UNION
     inside (path_image ka UNION path_image al UNION path_image pa UNION
             path_image be)) INTER
    ((path_image kb UNION path_image al UNION path_image pb UNION path_image be) UNION
     inside (path_image kb UNION path_image al UNION path_image pb UNION
             path_image be)) =
    path_image al UNION path_image be`;;

let MOI_S3TR_CONFIG_EXISTS = prove
 (`!c1 c2:real^2->bool.
     c1 homeomorphic sphere(vec 0:real^2,&1) /\
     c2 homeomorphic sphere(vec 0:real^2,&1) /\ c1 SUBSET inside c2
     ==> ?al be pa pb ka kb. moi_s3tr_anncfg c1 c2 al be pa pb ka kb`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c1:real^2->bool`; `c2:real^2->bool`] MOI_S3TR_CROSS_CUTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `al:real^1->real^2` (X_CHOOSE_THEN `be:real^1->real^2`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`c1:real^2->bool`; `vec 0:real^2`; `&1`]
    HOMEOMORPHIC_SIMPLE_PATH_IMAGE_CIRCLE_EQ) THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `g1:real^1->real^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`g1:real^1->real^2`; `pathstart (al:real^1->real^2)`;
                 `pathstart (be:real^1->real^2)`] EXISTS_DOUBLE_ARC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `pa:real^1->real^2` (X_CHOOSE_THEN `d1:real^1->real^2`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`c2:real^2->bool`; `vec 0:real^2`; `&1`]
    HOMEOMORPHIC_SIMPLE_PATH_IMAGE_CIRCLE_EQ) THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `g2:real^1->real^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`g2:real^1->real^2`; `pathfinish (al:real^1->real^2)`;
                 `pathfinish (be:real^1->real^2)`] EXISTS_DOUBLE_ARC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ka:real^1->real^2` (X_CHOOSE_THEN `d2:real^1->real^2`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `DISJOINT (c1:real^2->bool) c2` ASSUME_TAC THENL
   [MP_TAC(ISPEC `c2:real^2->bool` INSIDE_NO_OVERLAP) THEN
    UNDISCH_TAC `(c1:real^2->bool) SUBSET inside c2` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `path_image al SUBSET outside c1 UNION {pathstart al, pathfinish (al:real^1->real^2)} /\
    path_image be SUBSET outside c1 UNION {pathstart be, pathfinish (be:real^1->real^2)}`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c1:real^2->bool`; `c2:real^2->bool`; `al:real^1->real^2`;
                 `be:real^1->real^2`; `pa:real^1->real^2`; `reversepath d1:real^1->real^2`;
                 `ka:real^1->real^2`; `reversepath d2:real^1->real^2`]
    MOI_S3TR_THETA_SIDE) THEN
  ASM_REWRITE_TAC[ARC_REVERSEPATH_EQ; PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH;
                  PATH_IMAGE_REVERSEPATH] THEN
  STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`al:real^1->real^2`; `be:real^1->real^2`; `pa:real^1->real^2`;
                          `reversepath d1:real^1->real^2`; `ka:real^1->real^2`;
                          `reversepath d2:real^1->real^2`] THEN
    REWRITE_TAC[moi_s3tr_anncfg] THEN
    MP_TAC(ISPECL [`c1:real^2->bool`; `c2:real^2->bool`; `al:real^1->real^2`;
                   `be:real^1->real^2`; `pa:real^1->real^2`;
                   `reversepath d1:real^1->real^2`;
                   `ka:real^1->real^2`; `reversepath d2:real^1->real^2`]
      MOI_S3TR_THETA_DECOMP) THEN
    ASM_REWRITE_TAC[ARC_REVERSEPATH_EQ; PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH;
                    PATH_IMAGE_REVERSEPATH];
    SUBGOAL_THEN
     `path_image d2 UNION path_image ka = (c2:real^2->bool) /\
      path_image d2 INTER path_image ka =
      {pathfinish al, pathfinish (be:real^1->real^2)}`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[UNION_COMM; INTER_COMM]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`al:real^1->real^2`; `be:real^1->real^2`; `pa:real^1->real^2`;
                          `reversepath d1:real^1->real^2`;
                          `reversepath d2:real^1->real^2`; `ka:real^1->real^2`] THEN
    REWRITE_TAC[moi_s3tr_anncfg] THEN
    MP_TAC(ISPECL [`c1:real^2->bool`; `c2:real^2->bool`; `al:real^1->real^2`;
                   `be:real^1->real^2`; `pa:real^1->real^2`;
                   `reversepath d1:real^1->real^2`;
                   `reversepath d2:real^1->real^2`; `ka:real^1->real^2`]
      MOI_S3TR_THETA_DECOMP) THEN
    ASM_REWRITE_TAC[ARC_REVERSEPATH_EQ; PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH;
                    PATH_IMAGE_REVERSEPATH]]);;

let MOI_S3TR_CONFIG_HOMEO = prove
 (`!(c1:real^2->bool) c2 (al:real^1->real^2) be pa pb ka kb
    (d1:real^2->bool) d2 (al2:real^1->real^2) be2 pa2 pb2 ka2 kb2.
     moi_s3tr_anncfg c1 c2 al be pa pb ka kb /\
     moi_s3tr_anncfg d1 d2 al2 be2 pa2 pb2 ka2 kb2
     ==> ?f g. homeomorphism ((c2 UNION inside c2) DIFF inside c1,
                              (d2 UNION inside d2) DIFF inside d1) (f,g)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s3tr_anncfg] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c1:real^2->bool`; `c2:real^2->bool`; `al:real^1->real^2`;
                 `be:real^1->real^2`; `pa:real^1->real^2`; `pb:real^1->real^2`;
                 `ka:real^1->real^2`; `kb:real^1->real^2`] MOI_S3TR_SIX_ARCS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`d1:real^2->bool`; `d2:real^2->bool`; `al2:real^1->real^2`;
                 `be2:real^1->real^2`; `pa2:real^1->real^2`; `pb2:real^1->real^2`;
                 `ka2:real^1->real^2`; `kb2:real^1->real^2`] MOI_S3TR_SIX_ARCS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`al:real^1->real^2`; `al2:real^1->real^2`] HOMEOMORPHISM_ARC_IMAGES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `fa:real^2->real^2` (X_CHOOSE_THEN `fa':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`be:real^1->real^2`; `be2:real^1->real^2`] HOMEOMORPHISM_ARC_IMAGES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `fb:real^2->real^2` (X_CHOOSE_THEN `fb':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`ka:real^1->real^2`; `al:real^1->real^2`; `pa:real^1->real^2`;
                 `be:real^1->real^2`; `ka2:real^1->real^2`; `al2:real^1->real^2`;
                 `pa2:real^1->real^2`; `be2:real^1->real^2`; `fa:real^2->real^2`;
                 `fa':real^2->real^2`; `fb:real^2->real^2`; `fb':real^2->real^2`]
    MOI_S3TR_PASTE4) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `G1:real^2->real^2` (X_CHOOSE_THEN `G1':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`kb:real^1->real^2`; `al:real^1->real^2`; `pb:real^1->real^2`;
                 `be:real^1->real^2`; `kb2:real^1->real^2`; `al2:real^1->real^2`;
                 `pb2:real^1->real^2`; `be2:real^1->real^2`; `fa:real^2->real^2`;
                 `fa':real^2->real^2`; `fb:real^2->real^2`; `fb':real^2->real^2`]
    MOI_S3TR_PASTE4) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `G2:real^2->real^2` (X_CHOOSE_THEN `G2':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY (fun (k,a,p,b) ->
     MP_TAC(ISPECL [k; a; p; b] MOI_S3TR_LOOP4) THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC])
   [`ka:real^1->real^2`,`al:real^1->real^2`,`pa:real^1->real^2`,`be:real^1->real^2`;
    `kb:real^1->real^2`,`al:real^1->real^2`,`pb:real^1->real^2`,`be:real^1->real^2`;
    `ka2:real^1->real^2`,`al2:real^1->real^2`,`pa2:real^1->real^2`,`be2:real^1->real^2`;
    `kb2:real^1->real^2`,`al2:real^1->real^2`,`pb2:real^1->real^2`,`be2:real^1->real^2`] THEN
  MP_TAC(ISPECL [`ka ++ reversepath (reversepath al ++ (pa ++ be)):real^1->real^2`;
                 `ka2 ++ reversepath (reversepath al2 ++ (pa2 ++ be2)):real^1->real^2`;
                 `G1:real^2->real^2`; `G1':real^2->real^2`] JORDAN_SCHOENFLIES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:real^2->real^2` (X_CHOOSE_THEN `k1':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`kb ++ reversepath (reversepath al ++ (pb ++ be)):real^1->real^2`;
                 `kb2 ++ reversepath (reversepath al2 ++ (pb2 ++ be2)):real^1->real^2`;
                 `G2:real^2->real^2`; `G2':real^2->real^2`] JORDAN_SCHOENFLIES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k2:real^2->real^2` (X_CHOOSE_THEN `k2':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY ABBREV_TAC
   [`Q1 = path_image ka UNION path_image al UNION path_image pa UNION
          path_image (be:real^1->real^2)`;
    `Q2 = path_image kb UNION path_image al UNION path_image pb UNION
          path_image (be:real^1->real^2)`;
    `R1 = path_image ka2 UNION path_image al2 UNION path_image pa2 UNION
          path_image (be2:real^1->real^2)`;
    `R2 = path_image kb2 UNION path_image al2 UNION path_image pb2 UNION
          path_image (be2:real^1->real^2)`] THEN
  SUBGOAL_THEN `compact (Q1 UNION inside Q1:real^2->bool) /\
                compact (Q2 UNION inside Q2:real^2->bool)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC COMPACT_WITH_INSIDE THEN
    MAP_EVERY EXPAND_TAC ["Q1"; "Q2"] THEN
    REPEAT(MATCH_MP_TAC COMPACT_UNION THEN CONJ_TAC) THEN
    MATCH_MP_TAC COMPACT_ARC_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `homeomorphism (Q1 UNION inside Q1,R1 UNION inside R1)
                  (k1:real^2->real^2,k1') /\
                homeomorphism (Q2 UNION inside Q2,R2 UNION inside R2)
                  (k2:real^2->real^2,k2')` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`(:real^2)`; `(:real^2)`] THEN
    ASM_REWRITE_TAC[SUBSET_UNIV; IMAGE_UNION];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k1:real^2->real^2`; `k1':real^2->real^2`; `k2:real^2->real^2`;
                 `k2':real^2->real^2`; `Q1 UNION inside Q1:real^2->bool`;
                 `R1 UNION inside R1:real^2->bool`; `Q2 UNION inside Q2:real^2->bool`;
                 `R2 UNION inside R2:real^2->bool`] MOI_S3TR_PASTE2) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(!x. x IN path_image al ==> (k1:real^2->real^2) x = fa x /\ (k2:real^2->real^2) x = fa x) /\
    (!x. x IN path_image be ==> (k1:real^2->real^2) x = fb x /\ (k2:real^2->real^2) x = fb x)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN CONJ_TAC THEN
    MATCH_MP_TAC EQ_TRANS THENL
     [EXISTS_TAC `(G1:real^2->real^2) x`; EXISTS_TAC `(G2:real^2->real^2) x`;
      EXISTS_TAC `(G1:real^2->real^2) x`; EXISTS_TAC `(G2:real^2->real^2) x`] THEN
    CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXPAND_TAC ["Q1"; "Q2"] THEN ASM_REWRITE_TAC[IN_UNION];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (fa:real^2->real^2) (path_image al) = path_image al2 /\
                IMAGE (fb:real^2->real^2) (path_image be) = path_image be2`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[homeomorphism]; ALL_TAC] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_UNION] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`!x. x IN path_image al ==> (k1:real^2->real^2) x = fa x /\ (k2:real^2->real^2) x = fa x`;
        `!x. x IN path_image be ==> (k1:real^2->real^2) x = fb x /\ (k2:real^2->real^2) x = fb x`;
        `IMAGE (fa:real^2->real^2) (path_image al) = path_image al2`;
        `IMAGE (fb:real^2->real^2) (path_image be) = path_image be2`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The planar annulus theorem: the closed region between Jordan curves c1   *)
(* inside c2 is homeomorphic to holed_disk_model 1, the frontier going to    *)
(* c1 UNION c2 (the model is the region between two square frontiers; the    *)
(* frontier is preserved by MOI_FPS_HOMEOMORPHISM_FRONTIER).                 *)
(* ------------------------------------------------------------------------- *)

let MOI_S3TR_ANNULUS_FRONTIER = prove
 (`!c1 c2:real^2->bool.
     c1 homeomorphic sphere(vec 0:real^2,&1) /\
     c2 homeomorphic sphere(vec 0:real^2,&1) /\ c1 SUBSET inside c2
     ==> closed ((c2 UNION inside c2) DIFF inside c1) /\
         interior ((c2 UNION inside c2) DIFF inside c1) = inside c2 INTER outside c1 /\
         frontier ((c2 UNION inside c2) DIFF inside c1) = c1 UNION c2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `c1:real^2->bool` MOI_S3TR_JF) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `c2:real^2->bool` MOI_S3TR_JF) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`c2:real^2->bool`; `c1:real^2->bool`] MOI_S3TR_JNEST) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `closed ((c2 UNION inside c2) DIFF inside c1:real^2->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_DIFF THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `interior ((c2 UNION inside c2) DIFF inside c1) =
                inside c2 INTER outside (c1:real^2->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [ABBREV_TAC `w = interior ((c2 UNION inside c2) DIFF inside c1:real^2->bool)` THEN
      SUBGOAL_THEN `open (w:real^2->bool) /\ w SUBSET (c2 UNION inside c2) DIFF inside c1`
      STRIP_ASSUME_TAC THENL
       [EXPAND_TAC "w" THEN REWRITE_TAC[OPEN_INTERIOR; INTERIOR_SUBSET]; ALL_TAC] THEN
      SUBGOAL_THEN `(w:real^2->bool) INTER closure (inside c1) = {} /\
                    w INTER closure (outside c2) = {}`
      MP_TAC THENL
       [ASM_SIMP_TAC[OPEN_INTER_CLOSURE_EQ_EMPTY] THEN
        UNDISCH_TAC `w SUBSET (c2 UNION inside c2) DIFF inside (c1:real^2->bool)` THEN
        MP_TAC(ISPEC `c2:real^2->bool` OUTSIDE_NO_OVERLAP) THEN
        UNDISCH_TAC `inside c2 INTER outside c2:real^2->bool = {}` THEN SET_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPEC `inside c1:real^2->bool` MOI_S3TR_FRSUB) THEN
      MP_TAC(ISPEC `outside c2:real^2->bool` MOI_S3TR_FRSUB) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `w SUBSET (c2 UNION inside c2) DIFF inside (c1:real^2->bool)` THEN
      UNDISCH_TAC `inside c1 UNION outside c1 = (:real^2) DIFF c1` THEN
      SET_TAC[];
      MATCH_MP_TAC INTERIOR_MAXIMAL THEN ASM_SIMP_TAC[OPEN_INTER] THEN
      MP_TAC(ISPEC `c1:real^2->bool` OUTSIDE_NO_OVERLAP) THEN
      UNDISCH_TAC `inside c1 INTER outside c1:real^2->bool = {}` THEN SET_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[frontier; CLOSURE_CLOSED] THEN
  MP_TAC(ISPEC `c1:real^2->bool` OUTSIDE_NO_OVERLAP) THEN
  MP_TAC(ISPEC `c2:real^2->bool` INSIDE_NO_OVERLAP) THEN
  MP_TAC(ISPEC `c1:real^2->bool` INSIDE_NO_OVERLAP) THEN
  UNDISCH_TAC `inside c1 UNION outside c1 = (:real^2) DIFF c1` THEN
  UNDISCH_TAC `inside c1 SUBSET inside (c2:real^2->bool)` THEN
  UNDISCH_TAC `(c1:real^2->bool) SUBSET inside c2` THEN
  UNDISCH_TAC `(c2:real^2->bool) SUBSET outside c1` THEN
  SET_TAC[]);;

let MOI_S3TR_SQUARE_FRONTIER = prove
 (`!a b:real^2.
     ~(interval(a,b) = {})
     ==> frontier (interval[a,b]) homeomorphic sphere(vec 0:real^2,&1) /\
         inside (frontier (interval[a,b])) = interval(a,b) /\
         frontier (interval[a,b]) UNION inside (frontier (interval[a,b])) =
         interval[a,b]`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(interior (interval[a:real^2,b]) = {})` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[INTERIOR_CLOSED_INTERVAL]; ALL_TAC] THEN
  ASM_SIMP_TAC[INSIDE_FRONTIER_EQ_INTERIOR; BOUNDED_INTERVAL; CONVEX_INTERVAL;
               INTERIOR_CLOSED_INTERVAL] THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[GSYM RELATIVE_FRONTIER_NONEMPTY_INTERIOR] THEN
    MP_TAC(ISPECL [`vec 0:real^2`; `&1`] RELATIVE_FRONTIER_CBALL) THEN
    REWRITE_TAC[REAL_OF_NUM_EQ; ARITH_EQ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC HOMEOMORPHIC_RELATIVE_FRONTIERS_CONVEX_BOUNDED_SETS THEN
    REWRITE_TAC[BOUNDED_INTERVAL; CONVEX_INTERVAL; BOUNDED_CBALL; CONVEX_CBALL] THEN
    ASM_SIMP_TAC[AFF_DIM_NONEMPTY_INTERIOR; AFF_DIM_CBALL; REAL_LT_01];
    REWRITE_TAC[FRONTIER_CLOSED_INTERVAL] THEN
    MP_TAC(ISPECL [`a:real^2`; `b:real^2`] INTERVAL_OPEN_SUBSET_CLOSED) THEN
    SET_TAC[]]);;

let MOI_S3TR_HD1_MODEL = prove
 (`frontier (interval[vector[&2;&1],vector[&4;&3]]:real^2->bool)
   homeomorphic sphere(vec 0:real^2,&1) /\
   frontier (interval[vec 0,vector[&8;&4]]:real^2->bool)
   homeomorphic sphere(vec 0:real^2,&1) /\
   frontier (interval[vector[&2;&1],vector[&4;&3]]:real^2->bool) SUBSET
   inside (frontier (interval[vec 0,vector[&8;&4]])) /\
   holed_disk_model 1 =
   (frontier (interval[vec 0,vector[&8;&4]]) UNION
    inside (frontier (interval[vec 0,vector[&8;&4]]))) DIFF
   inside (frontier (interval[vector[&2;&1],vector[&4;&3]]:real^2->bool))`,
  MP_TAC(ISPECL [`vector[&2;&1]:real^2`; `vector[&4;&3]:real^2`]
    MOI_S3TR_SQUARE_FRONTIER) THEN
  MP_TAC(ISPECL [`vec 0:real^2`; `vector[&8;&4]:real^2`] MOI_S3TR_SQUARE_FRONTIER) THEN
  REWRITE_TAC[INTERVAL_NE_EMPTY; DIMINDEX_2; FORALL_2; VECTOR_2; VEC_COMPONENT] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `interval[vector[&2;&1],vector[&4;&3]]:real^2->bool` THEN
    REWRITE_TAC[FRONTIER_CLOSED_INTERVAL; SUBSET_DIFF] THEN
    REWRITE_TAC[SUBSET; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2; VEC_COMPONENT] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[holed_disk_model] THEN
    SUBGOAL_THEN `{interval(vector[&4 * &i + &2; &1]:real^2,vector[&4 * &i + &4; &3]) |
                   i | i < 1} =
                  {interval(vector[&2; &1],vector[&4; &3])}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN GEN_TAC THEN
      REWRITE_TAC[ARITH_RULE `i < 1 <=> i = 0`] THEN
      REWRITE_TAC[UNWIND_THM2] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[UNIONS_1] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[]]);;

let MOI_S3TR_ANNULUS_THM = prove
 (`!c1 c2:real^2->bool.
     c1 homeomorphic sphere(vec 0:real^2,&1) /\
     c2 homeomorphic sphere(vec 0:real^2,&1) /\ c1 SUBSET inside c2
     ==> ?f g. homeomorphism (holed_disk_model 1,(c2 UNION inside c2) DIFF inside c1)
                             (f,g) /\
               IMAGE f (frontier (holed_disk_model 1)) = c1 UNION c2`,
  REPEAT STRIP_TAC THEN
  STRIP_ASSUME_TAC MOI_S3TR_HD1_MODEL THEN
  MP_TAC(ISPECL [`frontier (interval[vector[&2;&1],vector[&4;&3]]:real^2->bool)`;
                 `frontier (interval[vec 0,vector[&8;&4]]:real^2->bool)`]
    MOI_S3TR_CONFIG_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `al:real^1->real^2` (X_CHOOSE_THEN `be:real^1->real^2`
   (X_CHOOSE_THEN `pa:real^1->real^2` (X_CHOOSE_THEN `pb:real^1->real^2`
   (X_CHOOSE_THEN `ka:real^1->real^2` (X_CHOOSE_TAC `kb:real^1->real^2`)))))) THEN
  MP_TAC(ISPECL [`c1:real^2->bool`; `c2:real^2->bool`] MOI_S3TR_CONFIG_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `al2:real^1->real^2` (X_CHOOSE_THEN `be2:real^1->real^2`
   (X_CHOOSE_THEN `pa2:real^1->real^2` (X_CHOOSE_THEN `pb2:real^1->real^2`
   (X_CHOOSE_THEN `ka2:real^1->real^2` (X_CHOOSE_TAC `kb2:real^1->real^2`)))))) THEN
  MP_TAC(ISPECL
   [`frontier (interval[vector[&2;&1],vector[&4;&3]]:real^2->bool)`;
    `frontier (interval[vec 0,vector[&8;&4]]:real^2->bool)`;
    `al:real^1->real^2`; `be:real^1->real^2`; `pa:real^1->real^2`; `pb:real^1->real^2`;
    `ka:real^1->real^2`; `kb:real^1->real^2`;
    `c1:real^2->bool`; `c2:real^2->bool`;
    `al2:real^1->real^2`; `be2:real^1->real^2`; `pa2:real^1->real^2`;
    `pb2:real^1->real^2`; `ka2:real^1->real^2`; `kb2:real^1->real^2`]
   MOI_S3TR_CONFIG_HOMEO) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^2` (X_CHOOSE_TAC `g:real^2->real^2`)) THEN
  MAP_EVERY EXISTS_TAC [`f:real^2->real^2`; `g:real^2->real^2`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`c1:real^2->bool`; `c2:real^2->bool`] MOI_S3TR_ANNULUS_FRONTIER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`frontier (interval[vector[&2;&1],vector[&4;&3]]:real^2->bool)`;
                 `frontier (interval[vec 0,vector[&8;&4]]:real^2->bool)`]
    MOI_S3TR_ANNULUS_FRONTIER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    concl th = `frontier ((c2 UNION inside c2) DIFF inside c1:real^2->bool) = c1 UNION c2`)) THEN
  MATCH_MP_TAC MOI_FPS_HOMEOMORPHISM_FRONTIER THEN
  EXISTS_TAC `g:real^2->real^2` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Local polyhedrality of the two sides of the trace in the pseudo-cell:     *)
(* (E - rim - centre) INTER X and (E - rim) DIFF interior X.  The first is an *)
(* intersection of locally polyhedral sets; the second is, near a trace      *)
(* point, the preimage of a half plane under the PL crossing chart, and near *)
(* other points an open part of E - rim - centre.                            *)
(* ------------------------------------------------------------------------- *)

let MOI_S3TR_LP_LOCAL = prove
 (`!s:real^N->bool.
     (!y. y IN s ==> ?u. open u /\ y IN u /\ locally_polyhedral (s INTER u))
     ==> locally_polyhedral s`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[locally_polyhedral] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o GEN_REWRITE_RULE I [locally_polyhedral]) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^N->bool)->bool` (X_CHOOSE_THEN `u':real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `u INTER u':real^N->bool`] THEN
  ASM_SIMP_TAC[OPEN_INTER; IN_INTER] THEN ASM SET_TAC[]);;

let MOI_S3TR_IMAGE_IFF = prove
 (`!(f:real^M->real^N) g w w' s q.
     homeomorphism (w,w') (f,g) /\ IMAGE f (s INTER w) = w' INTER q
     ==> !x. x IN w ==> (x IN s <=> f x IN q)`,
  REWRITE_TAC[homeomorphism] THEN REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(f:real^M->real^N) x IN IMAGE f (s INTER w)` MP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `x':real^M` STRIP_ASSUME_TAC) THEN
  ASM_MESON_TAC[]);;

let MOI_S3TR_POLY_HALF = prove
 (`polyhedron {z:real^3 | z$1 = &0 /\ z$2 <= &0} /\
   polyhedron {z:real^3 | z$1 = &0 /\ &0 <= z$2}`,
  SUBGOAL_THEN
   `{z:real^3 | z$1 = &0 /\ z$2 <= &0} =
    {z | basis 1 dot z = &0} INTER {z | basis 2 dot z <= &0} /\
    {z:real^3 | z$1 = &0 /\ &0 <= z$2} =
    {z | basis 1 dot z = &0} INTER {z | --(basis 2) dot z <= &0}`
  (fun th -> REWRITE_TAC[th]) THENL
   [SIMP_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; DOT_BASIS; DOT_LNEG; DIMINDEX_3; ARITH] THEN
    REAL_ARITH_TAC;
    SIMP_TAC[POLYHEDRON_INTER; POLYHEDRON_HYPERPLANE; POLYHEDRON_HALFSPACE_LE]]);;

let MOI_S3TR_LP_SIDES = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c x u v.
     moi_s33_hd t l h e c /\ moi_s33_x2 t l h e x /\ ~(u = v) /\ segment[u,v] IN l
     ==> locally_polyhedral
           (((e(segment[u,v]) DIFF moi_s33_rim t l h u v) DELETE h(midpoint(u,v))) INTER
            UNIONS x) /\
         locally_polyhedral
           ((e(segment[u,v]) DIFF moi_s33_rim t l h u v) DIFF interior (UNIONS x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`; `u:real^3`; `v:real^3`]
    MOI_S3TR_TRACE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `u:real^3`; `v:real^3`]
    MOI_S3X2_HD_EDGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `locally_polyhedral (UNIONS x:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOCALLY_POLYHEDRAL_LF_COMPLEX THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s33_x2]) THEN
    ASM_MESON_TAC[combinatorial_manifold_with_boundary];
    ALL_TAC] THEN
  ABBREV_TAC `M = (e:(real^3->bool)->real^3->bool) (segment[u,v]) DIFF
                  moi_s33_rim t l (h:real^3->real^3) u v` THEN
  ABBREV_TAC `X = UNIONS (x:(real^3->bool)->bool)` THEN
  ABBREV_TAC `p = (h:real^3->real^3) (midpoint(u,v))` THEN
  CONJ_TAC THENL [MATCH_MP_TAC MOI_S3X2_LP_INTER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `interior X = X DIFF frontier (X:real^3->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[frontier; CLOSURE_CLOSED] THEN
    MP_TAC(ISPEC `X:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S3TR_LP_LOCAL THEN X_GEN_TAC `y:real^3` THEN
  REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
  ASM_CASES_TAC `(y:real^3) IN X` THENL
   [ALL_TAC;
    EXISTS_TAC `(:real^3) DIFF X` THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM closed] THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[IN_DIFF; IN_UNIV];
      ALL_TAC] THEN
    SUBGOAL_THEN `(M DIFF interior X) INTER ((:real^3) DIFF X) =
                  ((M:real^3->bool) DELETE p) INTER ((:real^3) DIFF X)`
    SUBST1_TAC THENL
     [MP_TAC(ISPEC `X:real^3->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(p:real^3) IN interior X` THEN SET_TAC[];
      MATCH_MP_TAC LOCALLY_POLYHEDRAL_INTER_OPEN THEN
      REWRITE_TAC[GSYM closed] THEN ASM_REWRITE_TAC[]]] THEN
  (* a trace point: the crossing chart *)
  SUBGOAL_THEN `(y:real^3) IN (e:(real^3->bool)->real^3->bool) (segment[u,v]) INTER
                frontier X` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN M` THEN EXPAND_TAC "M" THEN ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`M:real^3->bool`; `X:real^3->bool`; `y:real^3`] MOI_S3TR_CROSS_BALL) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `frontier (X:real^3->bool) SUBSET closure (interior X)` THEN
      UNDISCH_TAC `(y:real^3) IN (e:(real^3->bool)->real^3->bool) (segment[u,v]) INTER
                   frontier X` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` (X_CHOOSE_THEN `r:real`
      (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))))) THEN
  EXISTS_TAC `w:real^3->bool` THEN
  REPEAT CONJ_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `g:real^3->real^3`; `w:real^3->bool`;
                 `ball(vec 0:real^3,r)`; `M:real^3->bool`; `{z:real^3 | z$1 = &0}`]
    MOI_S3TR_IMAGE_IFF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC] THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `g:real^3->real^3`; `w:real^3->bool`;
                 `ball(vec 0:real^3,r)`; `frontier X:real^3->bool`; `{z:real^3 | z$2 = &0}`]
    MOI_S3TR_IMAGE_IFF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th))) THENL
   [MP_TAC(ISPECL [`f:real^3->real^3`; `g:real^3->real^3`; `w:real^3->bool`;
                   `ball(vec 0:real^3,r)`; `X:real^3->bool`; `{z:real^3 | &0 <= z$2}`]
      MOI_S3TR_IMAGE_IFF) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC] THEN
    SUBGOAL_THEN `(M DIFF interior X) INTER w =
                  {z:real^3 | z IN w /\ f z IN {z:real^3 | z$1 = &0 /\ z$2 <= &0}}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; IN_DIFF] THEN
      X_GEN_TAC `z:real^3` THEN ASM_CASES_TAC `(z:real^3) IN w` THEN ASM_SIMP_TAC[IN_DIFF] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC MOI_PTR_LOCALLY_POLYHEDRAL_PL_PREIMAGE THEN
      ASM_REWRITE_TAC[MOI_S3TR_POLY_HALF]];
    MP_TAC(ISPECL [`f:real^3->real^3`; `g:real^3->real^3`; `w:real^3->bool`;
                   `ball(vec 0:real^3,r)`; `X:real^3->bool`; `{z:real^3 | z$2 <= &0}`]
      MOI_S3TR_IMAGE_IFF) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC] THEN
    SUBGOAL_THEN `(M DIFF interior X) INTER w =
                  {z:real^3 | z IN w /\ f z IN {z:real^3 | z$1 = &0 /\ &0 <= z$2}}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; IN_DIFF] THEN
      X_GEN_TAC `z:real^3` THEN ASM_CASES_TAC `(z:real^3) IN w` THEN ASM_SIMP_TAC[IN_DIFF] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC MOI_PTR_LOCALLY_POLYHEDRAL_PL_PREIMAGE THEN
      ASM_REWRITE_TAC[MOI_S3TR_POLY_HALF]]]);;

(* ------------------------------------------------------------------------- *)
(* Components after removing some components; finite unions of components   *)
(* are open in the set; the THIN_STEP hypotheses for a region given by a      *)
(* compact planar set in the cell chart; PL-ness of such a region from the   *)
(* two locally polyhedral sides; the open planar annulus.                    *)
(* ------------------------------------------------------------------------- *)

let MOI_S3TR_COMPONENTS_DIFF = prove
 (`!s k:(real^N->bool)->bool.
     k SUBSET components s ==> components (s DIFF UNIONS k) = components s DIFF k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!c:real^N->bool. c IN components s /\ ~(c IN k) ==> c IN components (s DIFF UNIONS k)`
  ASSUME_TAC THENL
   [X_GEN_TAC `c:real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(c:real^N->bool) SUBSET s DIFF UNIONS k` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIONS; NOT_EXISTS_THM] THEN
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN CONJ_TAC THENL
       [ASM_MESON_TAC[IN_COMPONENTS_SUBSET; SUBSET]; ALL_TAC] THEN
      X_GEN_TAC `d:real^N->bool` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(d:real^N->bool) IN components s` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `c:real^N->bool`; `d:real^N->bool`]
        COMPONENTS_EQ) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~(c:real^N->bool = d)` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `~(c INTER d:real^N->bool = {})` ASSUME_TAC THENL
       [ASM SET_TAC[]; ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[IN_COMPONENTS_MAXIMAL] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY];
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[IN_COMPONENTS_CONNECTED];
      X_GEN_TAC `d:real^N->bool` THEN STRIP_TAC THEN
      MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC COMPONENTS_MAXIMAL THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_NONEMPTY o check (fun th ->
        concl th = `(c:real^N->bool) IN components s`)) THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[SUBSET; IN_DIFF] THEN ASM_MESON_TAC[]] THEN
  REWRITE_TAC[SUBSET; IN_DIFF] THEN X_GEN_TAC `c':real^N->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(c':real^N->bool) SUBSET s DIFF UNIONS k /\ connected c' /\ ~(c' = {})`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET; IN_COMPONENTS_CONNECTED; IN_COMPONENTS_NONEMPTY];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `c':real^N->bool`] EXISTS_COMPONENT_SUPERSET) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `~((c:real^N->bool) IN k)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^N->bool) IN components (s DIFF UNIONS k)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `c':real^N->bool = c` (fun th -> ASM_REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`s DIFF UNIONS k:real^N->bool`; `c':real^N->bool`; `c:real^N->bool`]
    COMPONENTS_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM SET_TAC[]);;

let MOI_S3TR_OPEN_IN_COMPONENTS = prove
 (`!s k:(real^N->bool)->bool.
     FINITE (components s) /\ k SUBSET components s
     ==> open_in (subtopology euclidean s) (UNIONS k)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `UNIONS k = s DIFF UNIONS (components s DIFF k:(real^N->bool)->bool)`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^N` THEN
    REWRITE_TAC[IN_UNIONS; IN_DIFF; NOT_EXISTS_THM] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN CONJ_TAC THENL
       [ASM_MESON_TAC[IN_COMPONENTS_SUBSET; SUBSET]; ALL_TAC] THEN
      X_GEN_TAC `d:real^N->bool` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(c:real^N->bool) IN components s` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `c:real^N->bool`; `d:real^N->bool`]
        COMPONENTS_EQ) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~(c:real^N->bool = d)` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `~(c INTER d:real^N->bool = {})` ASSUME_TAC THENL
       [ASM SET_TAC[]; ASM_REWRITE_TAC[]];
      STRIP_TAC THEN
      SUBGOAL_THEN `?c:real^N->bool. c IN components s /\ y IN c` STRIP_ASSUME_TAC THENL
       [MP_TAC(ISPEC `s:real^N->bool` UNIONS_COMPONENTS) THEN
        UNDISCH_TAC `(y:real^N) IN s` THEN SET_TAC[];
        ALL_TAC] THEN
      EXISTS_TAC `c:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC[OPEN_IN_REFL] THEN
  MATCH_MP_TAC CLOSED_IN_UNIONS THEN ASM_SIMP_TAC[FINITE_DIFF; IN_DIFF] THEN
  MESON_TAC[CLOSED_IN_COMPONENT]);;

let MOI_S3TR_REGION_HYPS = prove
 (`!(m:real^N->bool) (phi:real^N->real^2) phi' tr S.
     homeomorphism (m,ball(vec 0,&1)) (phi,phi') /\ tr SUBSET m /\
     compact S /\ S SUBSET ball(vec 0,&1) /\
     open (S DIFF IMAGE phi tr) /\ connected (S DIFF IMAGE phi tr) /\
     S SUBSET closure (S DIFF IMAGE phi tr)
     ==> compact (IMAGE phi' S) /\ IMAGE phi' S SUBSET m /\
         IMAGE phi' S DIFF tr = IMAGE phi' (S DIFF IMAGE phi tr) /\
         IMAGE phi' S INTER tr = IMAGE phi' (S INTER IMAGE phi tr) /\
         open_in (subtopology euclidean m) (IMAGE phi' S DIFF tr) /\
         IMAGE phi' S SUBSET closure (IMAGE phi' S DIFF tr) /\
         connected (IMAGE phi' S DIFF tr)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `IMAGE (phi':real^2->real^N) S DIFF tr = IMAGE phi' (S DIFF IMAGE (phi:real^N->real^2) tr) /\
                IMAGE (phi':real^2->real^N) S INTER tr = IMAGE phi' (S INTER IMAGE (phi:real^N->real^2) tr)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    ASM SET_TAC[];
    MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`phi:real^N->real^2`; `ball(vec 0:real^2,&1)`] THEN
    ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC OPEN_SUBSET THEN ASM SET_TAC[];
    SUBGOAL_THEN `closure (S DIFF IMAGE (phi:real^N->real^2) tr) SUBSET S` ASSUME_TAC THENL
     [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (phi':real^2->real^N) (closure (S DIFF IMAGE (phi:real^N->real^2) tr))` THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC IMAGE_CLOSURE_SUBSET THEN REWRITE_TAC[CLOSED_CLOSURE; CLOSURE_SUBSET] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:real^2,&1)` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:real^2,&1)` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

let MOI_S3TR_REGION_PL = prove
 (`!(m:real^3->bool) p x s.
     locally_polyhedral ((m DELETE p) INTER x) /\
     locally_polyhedral (m DIFF interior x) /\
     compact s /\ s SUBSET m DELETE p /\
     (s DIFF frontier x SUBSET interior x \/ DISJOINT (s DIFF frontier x) x) /\
     (s DIFF frontier x SUBSET interior x ==> s SUBSET x) /\
     (DISJOINT (s DIFF frontier x) x ==> s INTER x = s INTER frontier x) /\
     (?w. open w /\ s SUBSET w /\
          (s DIFF frontier x SUBSET interior x ==> m INTER x INTER w SUBSET s) /\
          (DISJOINT (s DIFF frontier x) x ==> m INTER w SUBSET s UNION interior x))
     ==> pl_polyhedron s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC MOI_PTR_COMPACT_LOCALLY_POLYHEDRAL THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th))) THENL
   [SUBGOAL_THEN `s = (((m:real^3->bool) DELETE p) INTER x) INTER w` SUBST1_TAC THENL
     [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [UNDISCH_TAC `(s:real^3->bool) SUBSET m DELETE p` THEN
        UNDISCH_TAC `(s:real^3->bool) SUBSET w` THEN
        UNDISCH_TAC `s DIFF frontier x SUBSET interior x ==> (s:real^3->bool) SUBSET x` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        UNDISCH_TAC `s DIFF frontier x SUBSET interior x
                     ==> (m:real^3->bool) INTER x INTER w SUBSET s` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[]];
      MATCH_MP_TAC LOCALLY_POLYHEDRAL_INTER_OPEN THEN ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `s = ((m:real^3->bool) DIFF interior x) INTER w` SUBST1_TAC THENL
     [MP_TAC(ISPEC `x:real^3->bool` INTERIOR_SUBSET) THEN
      MP_TAC(ISPEC `x:real^3->bool` frontier) THEN
      UNDISCH_TAC `(s:real^3->bool) SUBSET m DELETE p` THEN
      UNDISCH_TAC `(s:real^3->bool) SUBSET w` THEN
      UNDISCH_TAC `DISJOINT (s DIFF frontier x) (x:real^3->bool)
                   ==> s INTER x = s INTER frontier x` THEN
      UNDISCH_TAC `DISJOINT (s DIFF frontier x) (x:real^3->bool)
                   ==> m INTER w SUBSET s UNION interior x` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      MATCH_MP_TAC LOCALLY_POLYHEDRAL_INTER_OPEN THEN ASM_REWRITE_TAC[]]]);;

let MOI_S3TR_OPEN_ANNULUS = prove
 (`!c1 c2:real^2->bool.
     c1 homeomorphic sphere(vec 0:real^2,&1) /\
     c2 homeomorphic sphere(vec 0:real^2,&1) /\ c1 SUBSET inside c2
     ==> open (inside c2 INTER outside c1) /\ connected (inside c2 INTER outside c1) /\
         c1 UNION c2 SUBSET closure (inside c2 INTER outside c1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `c1:real^2->bool` MOI_S3TR_JF) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `c2:real^2->bool` MOI_S3TR_JF) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`c2:real^2->bool`; `c1:real^2->bool`] MOI_S3TR_JNEST) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[OPEN_INTER] THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `inside c2 INTER outside c1 =
      (:real^2) DIFF ((c1 UNION inside c1) UNION (c2 UNION outside c2))`
    SUBST1_TAC THENL
     [REWRITE_TAC[OUTSIDE_INSIDE] THEN
      MP_TAC(ISPEC `c2:real^2->bool` INSIDE_NO_OVERLAP) THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC JANISZEWSKI_CONNECTED THEN REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      SUBGOAL_THEN `c2 UNION outside c2 = (:real^2) DIFF inside c2` SUBST1_TAC THENL
       [MP_TAC(ISPEC `c2:real^2->bool` INSIDE_OUTSIDE) THEN SET_TAC[];
        ASM_REWRITE_TAC[GSYM OPEN_CLOSED]];
      SUBGOAL_THEN `(c1 UNION inside c1) INTER (c2 UNION outside c2):real^2->bool = {}`
      SUBST1_TAC THENL
       [MP_TAC(ISPEC `c2:real^2->bool` INSIDE_NO_OVERLAP) THEN
        UNDISCH_TAC `inside c2 INTER outside c2:real^2->bool = {}` THEN
        UNDISCH_TAC `c1 UNION inside c1 SUBSET inside (c2:real^2->bool)` THEN
        SET_TAC[];
        REWRITE_TAC[CONNECTED_EMPTY]];
      REWRITE_TAC[GSYM OUTSIDE_INSIDE] THEN FIRST_ASSUM ACCEPT_TAC;
      SUBGOAL_THEN `(:real^2) DIFF (c2 UNION outside c2) = inside c2` SUBST1_TAC THENL
       [REWRITE_TAC[INSIDE_OUTSIDE]; FIRST_ASSUM ACCEPT_TAC]];
    MP_TAC(ISPECL [`inside c2:real^2->bool`; `outside c1:real^2->bool`]
      OPEN_INTER_CLOSURE_SUBSET) THEN
    MP_TAC(ONCE_REWRITE_RULE[INTER_COMM]
      (ISPECL [`outside c1:real^2->bool`; `inside c2:real^2->bool`]
        OPEN_INTER_CLOSURE_SUBSET)) THEN
    REWRITE_TAC[ASSUME `open (inside c2:real^2->bool)`;
                ASSUME `open (outside c1:real^2->bool)`] THEN
    MP_TAC(ISPEC `outside c1:real^2->bool` MOI_S3TR_FRSUB) THEN
    MP_TAC(ISPEC `inside c2:real^2->bool` MOI_S3TR_FRSUB) THEN
    REWRITE_TAC[ASSUME `frontier (outside c1:real^2->bool) = c1`;
                ASSUME `frontier (inside c2:real^2->bool) = c2`] THEN
    UNDISCH_TAC `(c1:real^2->bool) SUBSET inside c2` THEN
    UNDISCH_TAC `(c2:real^2->bool) SUBSET outside c1` THEN
    SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* A region s of the pseudo-cell bounded by trace circles: it is a compact  *)
(* polyhedron, lies inside or outside X, and has a thin neighbourhood w for *)
(* the surgery of THIN_STEP.                                                 *)
(* ------------------------------------------------------------------------- *)

let MOI_S3TR_REGION_PREP = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c x u v s.
     moi_s33_hd t l h e c /\ moi_s33_x2 t l h e x /\ ~(u = v) /\ segment[u,v] IN l /\
     compact s /\
     s SUBSET (e(segment[u,v]) DIFF moi_s33_rim t l h u v) DELETE h(midpoint(u,v)) /\
     open_in (subtopology euclidean (e(segment[u,v]) DIFF moi_s33_rim t l h u v))
             (s DIFF frontier (UNIONS x)) /\
     open_in (subtopology euclidean (e(segment[u,v]) INTER frontier (UNIONS x)))
             (s INTER frontier (UNIONS x)) /\
     s SUBSET closure (s DIFF frontier (UNIONS x)) /\
     connected (s DIFF frontier (UNIONS x))
     ==> pl_polyhedron s /\
         (s SUBSET UNIONS x \/ s INTER UNIONS x = s INTER frontier (UNIONS x)) /\
         ?w. open w /\ s SUBSET w /\
             !x'. FINITE x' /\ combinatorial_manifold_with_boundary 3 x' /\
                  (UNIONS x DIFF UNIONS x') UNION (UNIONS x' DIFF UNIONS x) SUBSET w /\
                  (s SUBSET UNIONS x
                   ==> UNIONS x' SUBSET UNIONS x /\ DISJOINT s (UNIONS x')) /\
                  (s INTER UNIONS x = s INTER frontier (UNIONS x)
                   ==> UNIONS x SUBSET UNIONS x' /\ s SUBSET interior (UNIONS x'))
                  ==> moi_s33_x2 t l h e x' /\
                      e(segment[u,v]) INTER frontier (UNIONS x') =
                      (e(segment[u,v]) INTER frontier (UNIONS x)) DIFF s /\
                      !s'. s' IN l /\ aff_dim s' = &1 /\ ~(s' = segment[u,v])
                           ==> e s' INTER frontier (UNIONS x') =
                               e s' INTER frontier (UNIONS x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`; `u:real^3`; `v:real^3`]
    MOI_S3TR_TRACE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(e(segment[u,v]) DIFF moi_s33_rim t l h u v) INTER frontier (UNIONS x) =
    (e:(real^3->bool)->real^3->bool) (segment[u,v]) INTER frontier (UNIONS x)`
  ASSUME_TAC THENL
   [UNDISCH_TAC
     `(e:(real^3->bool)->real^3->bool) (segment[u,v]) INTER frontier (UNIONS x) SUBSET
      (e(segment[u,v]) DIFF moi_s33_rim t l (h:real^3->real^3) u v) DELETE
      h(midpoint(u,v))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`; `u:real^3`; `v:real^3`;
                 `s:real^3->bool`] MOI_S3TR_THIN_STEP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `w:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  CONJ_TAC THENL
   [ALL_TAC;
    CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; EXISTS_TAC `w:real^3->bool` THEN ASM_REWRITE_TAC[]]] THEN
  MP_TAC(ISPECL [`e(segment[u,v]) DIFF moi_s33_rim t l (h:real^3->real^3) u v`;
                 `UNIONS x:real^3->bool`; `s:real^3->bool`] MOI_S3TR_REGION_SIDE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN CONJ_TAC THENL
     [UNDISCH_TAC
       `s SUBSET (e(segment[u,v]) DIFF moi_s33_rim t l (h:real^3->real^3) u v) DELETE
        h(midpoint(u,v))` THEN SET_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(y:real^3) IN s INTER frontier (UNIONS x)` THEN
    UNDISCH_TAC
     `s SUBSET (e(segment[u,v]) DIFF moi_s33_rim t l (h:real^3->real^3) u v) DELETE
      h(midpoint(u,v))` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC MOI_S3TR_REGION_PL THEN
  MAP_EVERY EXISTS_TAC [`e(segment[u,v]) DIFF moi_s33_rim t l (h:real^3->real^3) u v`;
                        `(h:real^3->real^3) (midpoint(u,v))`; `UNIONS x:real^3->bool`] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`; `u:real^3`; `v:real^3`]
    MOI_S3TR_LP_SIDES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The disk step (Moise Lemma 3): a trace circle J whose disk in the cell   *)
(* misses the centre and the other traces is removed by splitting Bd X at   *)
(* the PL disk bounded by J (DISK_RECOG, MOI_FND_SPLIT_DISK_R3, THIN_STEP).  *)
(* ------------------------------------------------------------------------- *)

let MOI_S3TR_BC_FACTS = prove
 (`!x:(real^3->bool)->bool.
     FINITE x /\ combinatorial_manifold_with_boundary 3 x
     ==> FINITE (boundary_complex x) /\ combinatorial_manifold 2 (boundary_complex x) /\
         UNIONS (boundary_complex x) = frontier (UNIONS x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `x:(real^3->bool)->bool` BOUNDARY_COMPLEX_SURFACE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `x:(real^3->bool)->bool` COMPLEX_BOUNDARY_FRONTIER_3) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `x:(real^3->bool)->bool` THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `simplicial_subcomplex (boundary_complex x) (x:(real^3->bool)->bool)` THEN
  SIMP_TAC[simplicial_subcomplex]);;

let MOI_S3TR_PSEUDO = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c u v.
     moi_s33_hd t l h e c /\ ~(u = v) /\ segment[u,v] IN l
     ==> moi_s33_rim t l h u v SUBSET e(segment[u,v]) /\
         (e(segment[u,v]) DIFF moi_s33_rim t l h u v) homeomorphic
         ball(vec 0:real^2,&1) /\
         moi_s33_rim t l h u v homeomorphic sphere(vec 0:real^2,&1) /\
         closure(e(segment[u,v]) DIFF moi_s33_rim t l h u v) = e(segment[u,v]) /\
         h(midpoint(u,v)) IN e(segment[u,v]) DIFF moi_s33_rim t l h u v /\
         locally_polyhedral
           ((e(segment[u,v]) DIFF moi_s33_rim t l h u v) DELETE h(midpoint(u,v)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s33_hd] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^3`; `v:real^3`] o check (fun th ->
    is_forall(concl th) &&
    can (find_term ((=) `pseudo_cell:(real^3->bool)->(real^3->bool)->real^3->bool`))
        (concl th))) THEN
  ASM_REWRITE_TAC[pseudo_cell] THEN SIMP_TAC[]);;

let MOI_S3TR_COMP_FACTS = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c x u v (phi:real^3->real^2) phi' J.
     moi_s33_hd t l h e c /\ moi_s33_x2 t l h e x /\ ~(u = v) /\ segment[u,v] IN l /\
     homeomorphism (e(segment[u,v]) DIFF moi_s33_rim t l h u v,ball(vec 0,&1))
                   (phi,phi') /\
     J IN components (e(segment[u,v]) INTER frontier (UNIONS x))
     ==> J SUBSET (e(segment[u,v]) DIFF moi_s33_rim t l h u v) DELETE h(midpoint(u,v)) /\
         pl_sphere 1 J /\ connected J /\ ~(J = {}) /\
         IMAGE phi J homeomorphic sphere(vec 0:real^2,&1) /\
         IMAGE phi J UNION inside (IMAGE phi J) SUBSET ball(vec 0,&1) /\
         disk_with_boundary (IMAGE phi' (IMAGE phi J UNION inside (IMAGE phi J))) J /\
         IMAGE phi' (IMAGE phi J) = J /\
         ~(phi(h(midpoint(u,v))) IN IMAGE phi J)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`; `u:real^3`; `v:real^3`]
    MOI_S3TR_TRACE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `u:real^3`; `v:real^3`]
    MOI_S3X2_HD_EDGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `M = (e:(real^3->bool)->real^3->bool) (segment[u,v]) DIFF
                  moi_s33_rim t l (h:real^3->real^3) u v` THEN
  ABBREV_TAC `p = (h:real^3->real^3) (midpoint(u,v))` THEN
  SUBGOAL_THEN `J SUBSET (M:real^3->bool) DELETE p` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3) IN M` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                   `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                   `c:real^3->real^3->bool`; `u:real^3`; `v:real^3`]
      MOI_S3TR_PSEUDO) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_sphere 1 (J:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
    can (term_match [] `homeomorphism (a:real^3->bool,b:real^2->bool) (f,g)`) (concl th))) THEN
  MP_TAC(ISPECL [`M:real^3->bool`; `phi:real^3->real^2`; `phi':real^2->real^3`;
                 `J:real^3->bool`] MOI_S3TR_CELL_DISK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM SET_TAC[]; ASM_MESON_TAC[MOI_S3TR_PL_CIRCLE_TOP]];
    STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_CONNECTED];
    ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY];
    ASM SET_TAC[];
    ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The disk step (Moise Lemma 3): a trace circle J whose disk in the cell   *)
(* misses the centre and the other traces is removed: the disk is a PL disk  *)
(* (DISK_RECOG), Bd X is split at it (MOI_FND_SPLIT_DISK_R3), and THIN_STEP *)
(* controls the new traces.                                                  *)
(* ------------------------------------------------------------------------- *)

let MOI_S3TR_DISK_STEP = prove
 ((mk_imp(mk_conj(MOI_FND_SPLIT_DISK_R3, inst [`:3`,`:N`] MOI_S33_DISK_RECOG_BODY),
  `!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c x u v (phi:real^3->real^2) phi' J.
     moi_s33_hd t l h e c /\ moi_s33_x2 t l h e x /\ ~(u = v) /\ segment[u,v] IN l /\
     homeomorphism (e(segment[u,v]) DIFF moi_s33_rim t l h u v,ball(vec 0,&1))
                   (phi,phi') /\
     J IN components (e(segment[u,v]) INTER frontier (UNIONS x)) /\
     ~(phi(h(midpoint(u,v))) IN inside (IMAGE phi J)) /\
     (!J'. J' IN components (e(segment[u,v]) INTER frontier (UNIONS x)) /\ ~(J' = J)
           ==> DISJOINT (IMAGE phi J') (IMAGE phi J UNION inside (IMAGE phi J)))
     ==> ?x'. moi_s33_x2 t l h e x' /\
              e(segment[u,v]) INTER frontier (UNIONS x') =
              (e(segment[u,v]) INTER frontier (UNIONS x)) DIFF J /\
              !s'. s' IN l /\ aff_dim s' = &1 /\ ~(s' = segment[u,v])
                   ==> e s' INTER frontier (UNIONS x') = e s' INTER frontier (UNIONS x)`)),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "split") (LABEL_TAC "recog")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`; `u:real^3`; `v:real^3`]
    MOI_S3TR_TRACE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`; `u:real^3`; `v:real^3`;
                 `phi:real^3->real^2`; `phi':real^2->real^3`; `J:real^3->bool`]
    MOI_S3TR_COMP_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `tr = (e:(real^3->bool)->real^3->bool) (segment[u,v]) INTER
                  frontier (UNIONS x)` THEN
  ABBREV_TAC `M = (e:(real^3->bool)->real^3->bool) (segment[u,v]) DIFF
                  moi_s33_rim t l (h:real^3->real^3) u v` THEN
  ABBREV_TAC `cJ = IMAGE (phi:real^3->real^2) J` THEN
  MP_TAC(ISPEC `cJ:real^2->bool` MOI_S3TR_JF) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(cJ UNION inside cJ) INTER IMAGE (phi:real^3->real^2) tr = cJ`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_INTER; IN_IMAGE] THEN X_GEN_TAC `z:real^2` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `?J':real^3->bool. J' IN components tr /\ y IN J'` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(y:real^3) IN tr` THEN
        GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [UNIONS_COMPONENTS] THEN
        REWRITE_TAC[IN_UNIONS] THEN MESON_TAC[];
        ALL_TAC] THEN
      ASM_CASES_TAC `J':real^3->bool = J` THENL
       [UNDISCH_TAC `IMAGE (phi:real^3->real^2) J = cJ` THEN
        UNDISCH_TAC `(y:real^3) IN J'` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `z = (phi:real^3->real^2) y` THEN SET_TAC[];
        ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o SPEC `J':real^3->bool` o check (fun th ->
        is_forall (concl th) &&
        can (find_term ((=) `inside cJ:real^2->bool`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(z:real^2) IN cJ UNION inside cJ` THEN
      UNDISCH_TAC `(y:real^3) IN J'` THEN
      UNDISCH_TAC `z = (phi:real^3->real^2) y` THEN SET_TAC[];
      UNDISCH_TAC `IMAGE (phi:real^3->real^2) J = cJ` THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET o check (fun th ->
        concl th = `(J:real^3->bool) IN components tr`)) THEN
      SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `S = cJ UNION inside (cJ:real^2->bool)` THEN
  SUBGOAL_THEN `S DIFF IMAGE (phi:real^3->real^2) tr = inside cJ` ASSUME_TAC THENL
   [MP_TAC(ISPEC `cJ:real^2->bool` INSIDE_NO_OVERLAP) THEN
    UNDISCH_TAC `S INTER IMAGE (phi:real^3->real^2) tr = cJ` THEN
    EXPAND_TAC "S" THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`M:real^3->bool`; `phi:real^3->real^2`; `phi':real^2->real^3`;
                 `tr:real^3->bool`; `S:real^2->bool`] MOI_S3TR_REGION_HYPS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `tr SUBSET (M:real^3->bool) DELETE (h:real^3->real^3) (midpoint(u,v))` THEN
      SET_TAC[];
      REWRITE_TAC[SUBSET_REFL]];
    STRIP_TAC] THEN
  ABBREV_TAC `s = IMAGE (phi':real^2->real^3) S` THEN
  SUBGOAL_THEN `s INTER tr = J:real^3->bool` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `s INTER frontier (UNIONS x) = J:real^3->bool /\
                s DIFF frontier (UNIONS x) = s DIFF tr`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `s INTER tr = J:real^3->bool` THEN
    UNDISCH_TAC `(s:real^3->bool) SUBSET M` THEN
    UNDISCH_TAC `(e:(real^3->bool)->real^3->bool) (segment[u,v]) INTER
                 frontier (UNIONS x) = tr` THEN
    UNDISCH_TAC `(e:(real^3->bool)->real^3->bool) (segment[u,v]) DIFF
                 moi_s33_rim t l (h:real^3->real^3) u v = M` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((h:real^3->real^3) (midpoint(u,v)) IN s)` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
      can (term_match [] `homeomorphism (a:real^3->bool,b:real^2->bool) (f,g)`)
          (concl th))) THEN
    SUBGOAL_THEN `(phi:real^3->real^2) ((h:real^3->real^3) (midpoint(u,v))) = z`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `S SUBSET ball(vec 0:real^2,&1)` THEN
      UNDISCH_TAC `(z:real^2) IN S` THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(z:real^2) IN S` THEN EXPAND_TAC "S" THEN
    REWRITE_TAC[IN_UNION] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `(phi:real^3->real^2) ((h:real^3->real^3) (midpoint(u,v))) = z`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `s SUBSET (M:real^3->bool) DELETE (h:real^3->real^3) (midpoint(u,v)) /\
                open_in (subtopology euclidean tr) (J:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `(s:real^3->bool) SUBSET M` THEN
      UNDISCH_TAC `~((h:real^3->real^3) (midpoint(u,v)) IN s)` THEN SET_TAC[];
      MP_TAC(ISPECL [`tr:real^3->bool`; `{J:real^3->bool}`]
        MOI_S3TR_OPEN_IN_COMPONENTS) THEN
      ASM_REWRITE_TAC[UNIONS_1; SING_SUBSET]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`; `u:real^3`; `v:real^3`;
                 `s:real^3->bool`] MOI_S3TR_REGION_PREP) THEN
  REWRITE_TAC[ASSUME `(e:(real^3->bool)->real^3->bool) (segment[u,v]) DIFF
                      moi_s33_rim t l (h:real^3->real^3) u v = M`;
              ASSUME `(e:(real^3->bool)->real^3->bool) (segment[u,v]) INTER
                      frontier (UNIONS x) = tr`;
              ASSUME `s DIFF frontier (UNIONS (x:(real^3->bool)->bool)) = s DIFF tr`;
              ASSUME `s INTER frontier (UNIONS (x:(real^3->bool)->bool)) = J`] THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `w:real^3->bool` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 s (J:real^3->bool)` ASSUME_TAC THENL
   [USE_THEN "recog" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `x:(real^3->bool)->bool` MOI_S3TR_BC_FACTS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[moi_s33_x2]; STRIP_TAC] THEN
  USE_THEN "split" (MP_TAC o SPECL [`boundary_complex (x:(real^3->bool)->bool)`;
                                    `s:real^3->bool`; `J:real^3->bool`; `w:real^3->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:(real^3->bool)->bool` o check (fun th ->
    is_forall (concl th) &&
    type_of(fst(dest_forall(concl th))) = `:(real^3->bool)->bool` &&
    can (find_term ((=) `boundary_complex (x:(real^3->bool)->bool)`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[moi_s33_x2]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x':(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x':(real^3->bool)->bool` o check (fun th ->
    is_forall (concl th) &&
    type_of(fst(dest_forall(concl th))) = `:(real^3->bool)->bool` &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s33_x2")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN EXISTS_TAC `x':(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `s INTER tr = J:real^3->bool` THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The annulus step (Moise Lemma 4): two consecutive trace circles Ja inside *)
(* Jb around the centre bound an annulus missing the other traces; it is a   *)
(* PL annulus (planar annulus theorem through the cell chart, HOLED_RECOG,   *)
(* ANNULUS_FROM_HOLED), Bd X is split along it (MOI_FND_SPLIT_ANNULUS_R3),   *)
(* and THIN_STEP controls the new traces.                                    *)
(* ------------------------------------------------------------------------- *)

let MOI_S3TR_ANN_STEP = prove
 ((mk_imp(mk_conj(MOI_FND_SPLIT_ANNULUS_R3, inst [`:3`,`:N`] MOI_S33_HOLED_RECOG_BODY),
  `!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c x u v (phi:real^3->real^2) phi' Ja Jb.
     moi_s33_hd t l h e c /\ moi_s33_x2 t l h e x /\ ~(u = v) /\ segment[u,v] IN l /\
     homeomorphism (e(segment[u,v]) DIFF moi_s33_rim t l h u v,ball(vec 0,&1))
                   (phi,phi') /\
     Ja IN components (e(segment[u,v]) INTER frontier (UNIONS x)) /\
     Jb IN components (e(segment[u,v]) INTER frontier (UNIONS x)) /\ ~(Ja = Jb) /\
     IMAGE phi Ja SUBSET inside (IMAGE phi Jb) /\
     phi(h(midpoint(u,v))) IN inside (IMAGE phi Ja) /\
     (!J'. J' IN components (e(segment[u,v]) INTER frontier (UNIONS x)) /\
           ~(J' = Ja) /\ ~(J' = Jb)
           ==> DISJOINT (IMAGE phi J')
                        ((IMAGE phi Jb UNION inside (IMAGE phi Jb)) DIFF
                         inside (IMAGE phi Ja)))
     ==> ?x'. moi_s33_x2 t l h e x' /\
              e(segment[u,v]) INTER frontier (UNIONS x') =
              (e(segment[u,v]) INTER frontier (UNIONS x)) DIFF (Ja UNION Jb) /\
              !s'. s' IN l /\ aff_dim s' = &1 /\ ~(s' = segment[u,v])
                   ==> e s' INTER frontier (UNIONS x') = e s' INTER frontier (UNIONS x)`)),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "split") (LABEL_TAC "recog")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`; `u:real^3`; `v:real^3`]
    MOI_S3TR_TRACE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`; `u:real^3`; `v:real^3`;
                 `phi:real^3->real^2`; `phi':real^2->real^3`; `Ja:real^3->bool`]
    MOI_S3TR_COMP_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`; `u:real^3`; `v:real^3`;
                 `phi:real^3->real^2`; `phi':real^2->real^3`; `Jb:real^3->bool`]
    MOI_S3TR_COMP_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `tr = (e:(real^3->bool)->real^3->bool) (segment[u,v]) INTER
                  frontier (UNIONS x)` THEN
  ABBREV_TAC `M = (e:(real^3->bool)->real^3->bool) (segment[u,v]) DIFF
                  moi_s33_rim t l (h:real^3->real^3) u v` THEN
  ABBREV_TAC `ca = IMAGE (phi:real^3->real^2) Ja` THEN
  ABBREV_TAC `cb = IMAGE (phi:real^3->real^2) Jb` THEN
  MP_TAC(ISPEC `ca:real^2->bool` MOI_S3TR_JF) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `cb:real^2->bool` MOI_S3TR_JF) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`cb:real^2->bool`; `ca:real^2->bool`] MOI_S3TR_JNEST) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `DISJOINT (ca:real^2->bool) cb /\ ca SUBSET (cb UNION inside cb) DIFF inside ca /\
                cb SUBSET (cb UNION inside cb) DIFF inside ca`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `ca:real^2->bool` INSIDE_NO_OVERLAP) THEN
    MP_TAC(ISPEC `cb:real^2->bool` INSIDE_NO_OVERLAP) THEN
    UNDISCH_TAC `inside ca INTER outside ca:real^2->bool = {}` THEN
    UNDISCH_TAC `(ca:real^2->bool) SUBSET inside cb` THEN
    UNDISCH_TAC `(cb:real^2->bool) SUBSET outside ca` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((cb UNION inside cb) DIFF inside ca) INTER IMAGE (phi:real^3->real^2) tr =
                ca UNION cb`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_INTER; IN_IMAGE] THEN X_GEN_TAC `z:real^2` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `?J':real^3->bool. J' IN components tr /\ y IN J'` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(y:real^3) IN tr` THEN
        GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [UNIONS_COMPONENTS] THEN
        REWRITE_TAC[IN_UNIONS] THEN MESON_TAC[];
        ALL_TAC] THEN
      ASM_CASES_TAC `J':real^3->bool = Ja` THENL
       [UNDISCH_TAC `IMAGE (phi:real^3->real^2) Ja = ca` THEN
        UNDISCH_TAC `(y:real^3) IN J'` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `z = (phi:real^3->real^2) y` THEN SET_TAC[];
        ALL_TAC] THEN
      ASM_CASES_TAC `J':real^3->bool = Jb` THENL
       [UNDISCH_TAC `IMAGE (phi:real^3->real^2) Jb = cb` THEN
        UNDISCH_TAC `(y:real^3) IN J'` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `z = (phi:real^3->real^2) y` THEN SET_TAC[];
        ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o SPEC `J':real^3->bool` o check (fun th ->
        is_forall (concl th) &&
        can (find_term ((=) `inside ca:real^2->bool`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(z:real^2) IN (cb UNION inside cb) DIFF inside ca` THEN
      UNDISCH_TAC `(y:real^3) IN J'` THEN
      UNDISCH_TAC `z = (phi:real^3->real^2) y` THEN SET_TAC[];
      UNDISCH_TAC `IMAGE (phi:real^3->real^2) Ja = ca` THEN
      UNDISCH_TAC `IMAGE (phi:real^3->real^2) Jb = cb` THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET o check (fun th ->
        concl th = `(Ja:real^3->bool) IN components tr`)) THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET o check (fun th ->
        concl th = `(Jb:real^3->bool) IN components tr`)) THEN
      UNDISCH_TAC `(ca:real^2->bool) SUBSET (cb UNION inside cb) DIFF inside ca` THEN
      UNDISCH_TAC `(cb:real^2->bool) SUBSET (cb UNION inside cb) DIFF inside ca` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `S = (cb UNION inside cb) DIFF inside (ca:real^2->bool)` THEN
  MP_TAC(ISPECL [`ca:real^2->bool`; `cb:real^2->bool`] MOI_S3TR_OPEN_ANNULUS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `S DIFF IMAGE (phi:real^3->real^2) tr = inside cb INTER outside ca`
  ASSUME_TAC THENL
   [UNDISCH_TAC `S INTER IMAGE (phi:real^3->real^2) tr = ca UNION cb` THEN
    EXPAND_TAC "S" THEN REWRITE_TAC[OUTSIDE_INSIDE] THEN
    MP_TAC(ISPEC `cb:real^2->bool` INSIDE_NO_OVERLAP) THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`M:real^3->bool`; `phi:real^3->real^2`; `phi':real^2->real^3`;
                 `tr:real^3->bool`; `S:real^2->bool`] MOI_S3TR_REGION_HYPS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `tr SUBSET (M:real^3->bool) DELETE (h:real^3->real^3) (midpoint(u,v))` THEN
      SET_TAC[];
      EXPAND_TAC "S" THEN MATCH_MP_TAC COMPACT_DIFF THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `cb UNION inside cb SUBSET ball(vec 0:real^2,&1)` THEN
      EXPAND_TAC "S" THEN SET_TAC[];
      MP_TAC(ISPEC `inside cb INTER outside ca:real^2->bool` CLOSURE_SUBSET) THEN
      UNDISCH_TAC `ca UNION cb SUBSET closure (inside cb INTER outside ca:real^2->bool)` THEN
      UNDISCH_TAC `S INTER IMAGE (phi:real^3->real^2) tr = ca UNION cb` THEN
      UNDISCH_TAC `S DIFF IMAGE (phi:real^3->real^2) tr = inside cb INTER outside ca` THEN
      SET_TAC[]];
    STRIP_TAC] THEN
  ABBREV_TAC `s = IMAGE (phi':real^2->real^3) S` THEN
  SUBGOAL_THEN `s INTER tr = Ja UNION Jb:real^3->bool` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IMAGE_UNION]; ALL_TAC] THEN
  SUBGOAL_THEN `s INTER frontier (UNIONS (x:(real^3->bool)->bool)) = Ja UNION Jb /\
                s DIFF frontier (UNIONS (x:(real^3->bool)->bool)) = s DIFF tr`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `s INTER tr = Ja UNION Jb:real^3->bool` THEN
    UNDISCH_TAC `(s:real^3->bool) SUBSET M` THEN
    UNDISCH_TAC `(e:(real^3->bool)->real^3->bool) (segment[u,v]) INTER
                 frontier (UNIONS x) = tr` THEN
    UNDISCH_TAC `(e:(real^3->bool)->real^3->bool) (segment[u,v]) DIFF
                 moi_s33_rim t l (h:real^3->real^3) u v = M` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `S SUBSET ball(vec 0:real^2,&1)` ASSUME_TAC THENL
   [UNDISCH_TAC `cb UNION inside cb SUBSET ball(vec 0:real^2,&1)` THEN
    EXPAND_TAC "S" THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((h:real^3->real^3) (midpoint(u,v)) IN s)` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
      can (term_match [] `homeomorphism (a:real^3->bool,b:real^2->bool) (f,g)`)
          (concl th))) THEN
    SUBGOAL_THEN `(phi:real^3->real^2) ((h:real^3->real^3) (midpoint(u,v))) = z`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `S SUBSET ball(vec 0:real^2,&1)` THEN
      UNDISCH_TAC `(z:real^2) IN S` THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(z:real^2) IN S` THEN EXPAND_TAC "S" THEN
    REWRITE_TAC[IN_DIFF] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `(phi:real^3->real^2) ((h:real^3->real^3) (midpoint(u,v))) = z`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `s SUBSET (M:real^3->bool) DELETE (h:real^3->real^3) (midpoint(u,v)) /\
                open_in (subtopology euclidean tr) (Ja UNION Jb:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `(s:real^3->bool) SUBSET M` THEN
      UNDISCH_TAC `~((h:real^3->real^3) (midpoint(u,v)) IN s)` THEN SET_TAC[];
      MP_TAC(ISPECL [`tr:real^3->bool`; `{Ja:real^3->bool, Jb}`]
        MOI_S3TR_OPEN_IN_COMPONENTS) THEN
      ASM_REWRITE_TAC[UNIONS_2; INSERT_SUBSET; EMPTY_SUBSET]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`; `u:real^3`; `v:real^3`;
                 `s:real^3->bool`] MOI_S3TR_REGION_PREP) THEN
  REWRITE_TAC[ASSUME `(e:(real^3->bool)->real^3->bool) (segment[u,v]) DIFF
                      moi_s33_rim t l (h:real^3->real^3) u v = M`;
              ASSUME `(e:(real^3->bool)->real^3->bool) (segment[u,v]) INTER
                      frontier (UNIONS x) = tr`;
              ASSUME `s DIFF frontier (UNIONS (x:(real^3->bool)->bool)) = s DIFF tr`;
              ASSUME `s INTER frontier (UNIONS (x:(real^3->bool)->bool)) = Ja UNION Jb`] THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `w:real^3->bool` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`ca:real^2->bool`; `cb:real^2->bool`] MOI_S3TR_ANNULUS_THM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f0:real^2->real^2` (X_CHOOSE_THEN `g0:real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `homeomorphism (S,s) (phi':real^2->real^3,phi:real^3->real^2)` ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`ball(vec 0:real^2,&1)`; `M:real^3->bool`] THEN
    ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f0:real^2->real^2`; `g0:real^2->real^2`; `phi':real^2->real^3`;
                 `phi:real^3->real^2`; `holed_disk_model 1`; `S:real^2->bool`;
                 `s:real^3->bool`] HOMEOMORPHISM_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  USE_THEN "recog" (MP_TAC o SPECL [`1`; `s:real^3->bool`;
                                    `(phi':real^2->real^3) o (f0:real^2->real^2)`;
                                    `(g0:real^2->real^2) o (phi:real^3->real^2)`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IMAGE_o; IMAGE_UNION] THEN
    MATCH_MP_TAC PL_POLYHEDRON_UNION THEN CONJ_TAC THEN
    MATCH_MP_TAC MOI_SCD_PL_SPHERE_POLYHEDRON THEN EXISTS_TAC `1` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f1:real^2->real^3` (X_CHOOSE_THEN `g1:real^3->real^2`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `f1:real^2->real^3`; `g1:real^3->real^2`;
                 `Ja:real^3->bool`; `Jb:real^3->bool`] ANNULUS_FROM_HOLED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IMAGE_o; IMAGE_UNION] THEN
    REWRITE_TAC[DISJOINT] THEN
    MP_TAC(ISPECL [`tr:real^3->bool`; `Ja:real^3->bool`; `Jb:real^3->bool`]
      COMPONENTS_NONOVERLAP) THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  MP_TAC(ISPEC `x:(real^3->bool)->bool` MOI_S3TR_BC_FACTS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[moi_s33_x2]; STRIP_TAC] THEN
  USE_THEN "split" (MP_TAC o SPECL [`boundary_complex (x:(real^3->bool)->bool)`;
                                    `s:real^3->bool`; `Ja:real^3->bool`; `Jb:real^3->bool`;
                                    `w:real^3->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:(real^3->bool)->bool` o check (fun th ->
    is_forall (concl th) &&
    type_of(fst(dest_forall(concl th))) = `:(real^3->bool)->bool` &&
    can (find_term ((=) `boundary_complex (x:(real^3->bool)->bool)`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[moi_s33_x2]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x':(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x':(real^3->bool)->bool` o check (fun th ->
    is_forall (concl th) &&
    type_of(fst(dest_forall(concl th))) = `:(real^3->bool)->bool` &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s33_x2")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN EXISTS_TAC `x':(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `s INTER tr = Ja UNION Jb:real^3->bool` THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* One step at an edge: with two or more trace circles, the planar choice    *)
(* in the cell chart gives a disk step or an annulus step, and the number of *)
(* trace circles drops while the other pseudo-cells keep their traces.       *)
(* ------------------------------------------------------------------------- *)

let MOI_S3TR_EDGE_STEP = prove
 ((mk_imp(list_mk_conj[MOI_FND_SPLIT_DISK_R3; MOI_FND_SPLIT_ANNULUS_R3;
                       inst [`:3`,`:N`] MOI_S33_DISK_RECOG_BODY;
                       inst [`:3`,`:N`] MOI_S33_HOLED_RECOG_BODY],
  `!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c x u v.
     moi_s33_hd t l h e c /\ moi_s33_x2 t l h e x /\ ~(u = v) /\ segment[u,v] IN l /\
     2 <= CARD (components (e(segment[u,v]) INTER frontier (UNIONS x)))
     ==> ?x'. moi_s33_x2 t l h e x' /\
              CARD (components (e(segment[u,v]) INTER frontier (UNIONS x'))) <
              CARD (components (e(segment[u,v]) INTER frontier (UNIONS x))) /\
              !s'. s' IN l /\ aff_dim s' = &1 /\ ~(s' = segment[u,v])
                   ==> e s' INTER frontier (UNIONS x') = e s' INTER frontier (UNIONS x)`)),
  DISCH_THEN(fun th ->
    LABEL_TAC "dstep" (MATCH_MP MOI_S3TR_DISK_STEP
      (CONJ (CONJUNCT1 th) (CONJUNCT1(CONJUNCT2(CONJUNCT2 th))))) THEN
    LABEL_TAC "astep" (MATCH_MP MOI_S3TR_ANN_STEP
      (CONJ (CONJUNCT1(CONJUNCT2 th)) (CONJUNCT2(CONJUNCT2(CONJUNCT2 th)))))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`; `u:real^3`; `v:real^3`]
    MOI_S3TR_TRACE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `u:real^3`; `v:real^3`]
    MOI_S3TR_PSEUDO) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic] o check (fun th ->
    can (term_match [] `(a:real^3->bool) homeomorphic (ball(vec 0:real^2,&1))`)
        (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `phi:real^3->real^2` (X_CHOOSE_TAC `phi':real^2->real^3`)) THEN
  SUBGOAL_THEN
   `!J. J IN components (e(segment[u,v]) INTER frontier (UNIONS x))
        ==> IMAGE (phi:real^3->real^2) J homeomorphic sphere(vec 0:real^2,&1) /\
            ~(phi((h:real^3->real^3)(midpoint(u,v))) IN IMAGE phi J) /\
            J SUBSET (e:(real^3->bool)->real^3->bool)(segment[u,v]) DIFF
                     moi_s33_rim t l h u v /\
            ~(J = {})`
  ASSUME_TAC THENL
   [X_GEN_TAC `J:real^3->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                   `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                   `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`; `u:real^3`; `v:real^3`;
                   `phi:real^3->real^2`; `phi':real^2->real^3`; `J:real^3->bool`]
      MOI_S3TR_COMP_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    UNDISCH_TAC `J SUBSET ((e:(real^3->bool)->real^3->bool) (segment[u,v]) DIFF
                           moi_s33_rim t l (h:real^3->real^3) u v) DELETE
                          h(midpoint(u,v))` THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `tr = (e:(real^3->bool)->real^3->bool) (segment[u,v]) INTER
                  frontier (UNIONS x)` THEN
  ABBREV_TAC `M = (e:(real^3->bool)->real^3->bool) (segment[u,v]) DIFF
                  moi_s33_rim t l (h:real^3->real^3) u v` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
    can (term_match [] `homeomorphism (a:real^3->bool,b:real^2->bool) (f,g)`)
        (concl th))) THEN
  SUBGOAL_THEN
   `!J1 J2:real^3->bool.
      J1 IN components tr /\ J2 IN components tr /\ ~(J1 = J2)
      ==> DISJOINT (IMAGE (phi:real^3->real^2) J1) (IMAGE phi J2) /\
          ~(IMAGE phi J1 = IMAGE phi J2)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `DISJOINT (J1:real^3->bool) J2` ASSUME_TAC THENL
     [REWRITE_TAC[DISJOINT] THEN
      MP_TAC(ISPECL [`tr:real^3->bool`; `J1:real^3->bool`; `J2:real^3->bool`]
        COMPONENTS_NONOVERLAP) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(fun th ->
      MP_TAC(MATCH_MP th (ASSUME `(J1:real^3->bool) IN components tr`)) THEN
      MP_TAC(MATCH_MP th (ASSUME `(J2:real^3->bool) IN components tr`))) THEN
    REPEAT STRIP_TAC THENL
     [ALL_TAC;
      UNDISCH_TAC `IMAGE (phi:real^3->real^2) J1 = IMAGE phi J2`] THEN
    UNDISCH_TAC `!x. x IN M ==> (phi':real^2->real^3) ((phi:real^3->real^2) x) = x` THEN
    UNDISCH_TAC `DISJOINT (J1:real^3->bool) J2` THEN
    UNDISCH_TAC `J1 SUBSET (M:real^3->bool)` THEN
    UNDISCH_TAC `J2 SUBSET (M:real^3->bool)` THEN
    UNDISCH_TAC `~(J1:real^3->bool = {})` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (IMAGE (phi:real^3->real^2)) (components tr)`;
                 `(phi:real^3->real^2) ((h:real^3->real^3) (midpoint(u,v)))`]
    MOI_S3TR_PLANAR_CHOICE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMAGE] THEN REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `CARD (IMAGE (IMAGE (phi:real^3->real^2)) (components tr)) =
                    CARD (components tr)` (fun th -> ASM_REWRITE_TAC[th]) THEN
      MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
   [REMOVE_THEN "astep" (K ALL_TAC) THEN
  REWRITE_TAC[EXISTS_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `J:real^3->bool` STRIP_ASSUME_TAC) THEN
  REMOVE_THEN "dstep" (MP_TAC o SPECL
   [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
    `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
    `x:(real^3->bool)->bool`; `u:real^3`; `v:real^3`;
    `phi:real^3->real^2`; `phi':real^2->real^3`; `J:real^3->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `J':real^3->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `inside (IMAGE (phi:real^3->real^2) J)`)) (concl th))) THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x':(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `x':(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`tr:real^3->bool`; `{J:real^3->bool}`] MOI_S3TR_COMPONENTS_DIFF) THEN
  ASM_REWRITE_TAC[SING_SUBSET; UNIONS_1] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[CARD_DIFF; SING_SUBSET; CARD_SING] THEN
  UNDISCH_TAC `2 <= CARD(components(tr:real^3->bool))` THEN ARITH_TAC;
    REMOVE_THEN "dstep" (K ALL_TAC) THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; RIGHT_EXISTS_AND_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `Ja:real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `Jb:real^3->bool` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `~(Ja:real^3->bool = Jb)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(IMAGE (phi:real^3->real^2) Ja = IMAGE phi Jb)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "astep" (MP_TAC o SPECL
   [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
    `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
    `x:(real^3->bool)->bool`; `u:real^3`; `v:real^3`;
    `phi:real^3->real^2`; `phi':real^2->real^3`; `Ja:real^3->bool`; `Jb:real^3->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `J':real^3->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `inside (IMAGE (phi:real^3->real^2) Jb)`)) (concl th))) THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x':(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `x':(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`tr:real^3->bool`; `{Ja:real^3->bool, Jb}`] MOI_S3TR_COMPONENTS_DIFF) THEN
  ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; UNIONS_2] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[CARD_DIFF; INSERT_SUBSET; EMPTY_SUBSET; CARD_CLAUSES; FINITE_INSERT;
               FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
  UNDISCH_TAC `2 <= CARD(components(tr:real^3->bool))` THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Induction on the number of trace circles at an edge.                      *)
(* ------------------------------------------------------------------------- *)

let MOI_S3TR_EDGE_REDUCE = prove
 (mk_imp(list_mk_conj[MOI_FND_SPLIT_DISK_R3; MOI_FND_SPLIT_ANNULUS_R3;
                      inst [`:3`,`:N`] MOI_S33_DISK_RECOG_BODY;
                      inst [`:3`,`:N`] MOI_S33_HOLED_RECOG_BODY],
  `!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c u v x.
     moi_s33_hd t l h e c /\ ~(u = v) /\ segment[u,v] IN l /\ moi_s33_x2 t l h e x
     ==> ?x'. moi_s33_x2 t l h e x' /\
              CARD (components (e(segment[u,v]) INTER frontier (UNIONS x'))) <= 1 /\
              !s'. s' IN l /\ aff_dim s' = &1 /\ ~(s' = segment[u,v])
                   ==> e s' INTER frontier (UNIONS x') = e s' INTER frontier (UNIONS x)`),
  DISCH_THEN(LABEL_TAC "step" o MATCH_MP MOI_S3TR_EDGE_STEP) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!n (y:(real^3->bool)->bool).
      moi_s33_x2 t l h e y /\
      CARD (components ((e:(real^3->bool)->real^3->bool) (segment[u,v]) INTER
                        frontier (UNIONS y))) = n
      ==> ?x'. moi_s33_x2 t l h e x' /\
               CARD (components (e(segment[u,v]) INTER frontier (UNIONS x'))) <= 1 /\
               !s'. s' IN l /\ aff_dim s' = &1 /\ ~(s' = segment[u,v])
                    ==> e s' INTER frontier (UNIONS x') = e s' INTER frontier (UNIONS y)`
  (fun th -> MATCH_MP_TAC th THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `y:(real^3->bool)->bool` THEN STRIP_TAC THEN
  ASM_CASES_TAC `n <= 1` THENL
   [EXISTS_TAC `y:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "step" (MP_TAC o SPECL
   [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
    `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
    `y:(real^3->bool)->bool`; `u:real^3`; `v:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y1:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `CARD (components ((e:(real^3->bool)->real^3->bool) (segment[u,v]) INTER
                       frontier (UNIONS y1)))`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `y1:(real^3->bool)->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x':(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `x':(real^3->bool)->bool` THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* One trace circle: it is a PL circle and E INTER X is the disk it bounds   *)
(* in the cell (the trace is nonempty since E is the closure of the         *)
(* connected cell meeting int X at the centre and missing X on the rim; the  *)
(* outer side reaches the rim, so it misses X, and the inner side contains  *)
(* the centre).                                                              *)
(* ------------------------------------------------------------------------- *)

let MOI_S3TR_FINAL = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c x u v.
     moi_s33_hd t l h e c /\ moi_s33_x2 t l h e x /\ ~(u = v) /\ segment[u,v] IN l /\
     CARD (components (e(segment[u,v]) INTER frontier (UNIONS x))) <= 1
     ==> pl_sphere 1 (e(segment[u,v]) INTER frontier (UNIONS x)) /\
         disk_with_boundary (e(segment[u,v]) INTER UNIONS x)
                            (e(segment[u,v]) INTER frontier (UNIONS x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`; `u:real^3`; `v:real^3`]
    MOI_S3TR_TRACE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `u:real^3`; `v:real^3`]
    MOI_S3TR_PSEUDO) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic] o check (fun th ->
    can (term_match [] `(a:real^3->bool) homeomorphic (ball(vec 0:real^2,&1))`)
        (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `phi:real^3->real^2` (X_CHOOSE_TAC `phi':real^2->real^3`)) THEN
  SUBGOAL_THEN `connected ((e:(real^3->bool)->real^3->bool) (segment[u,v]) DIFF
                           moi_s33_rim t l (h:real^3->real^3) u v)` ASSUME_TAC THENL
   [ASM_MESON_TAC[HOMEOMORPHIC_CONNECTEDNESS; CONNECTED_BALL]; ALL_TAC] THEN
  SUBGOAL_THEN `~(moi_s33_rim t l (h:real^3->real^3) u v = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `moi_s33_rim t l (h:real^3->real^3) u v homeomorphic
                 sphere(vec 0:real^2,&1)` THEN
    ASM_REWRITE_TAC[HOMEOMORPHIC_EMPTY; SPHERE_EQ_EMPTY] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `tr = (e:(real^3->bool)->real^3->bool) (segment[u,v]) INTER
                  frontier (UNIONS x)` THEN
  ABBREV_TAC `M = (e:(real^3->bool)->real^3->bool) (segment[u,v]) DIFF
                  moi_s33_rim t l (h:real^3->real^3) u v` THEN
  ABBREV_TAC `E = (e:(real^3->bool)->real^3->bool) (segment[u,v])` THEN
  ABBREV_TAC `R = moi_s33_rim t l (h:real^3->real^3) u v` THEN
  ABBREV_TAC `X = UNIONS (x:(real^3->bool)->bool)` THEN
  ABBREV_TAC `p = (h:real^3->real^3) (midpoint(u,v))` THEN
  SUBGOAL_THEN `DISJOINT (R:real^3->bool) X` ASSUME_TAC THENL
   [UNDISCH_TAC `E INTER X SUBSET (M:real^3->bool)` THEN
    UNDISCH_TAC `E DIFF R = (M:real^3->bool)` THEN
    UNDISCH_TAC `(R:real^3->bool) SUBSET E` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(tr:real^3->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`M:real^3->bool`; `X:real^3->bool`] MOI_S3TR_CONNECTED_SIDE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `E INTER frontier X = (tr:real^3->bool)` THEN
      UNDISCH_TAC `E DIFF R = (M:real^3->bool)` THEN
      UNDISCH_TAC `tr:real^3->bool = {}` THEN SET_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THENL
     [SUBGOAL_THEN `(E:real^3->bool) SUBSET X` ASSUME_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          concl th = `closure M = (E:real^3->bool)`)) THEN
        MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPEC `X:real^3->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `DISJOINT (R:real^3->bool) X` THEN
      UNDISCH_TAC `(R:real^3->bool) SUBSET E` THEN
      UNDISCH_TAC `(E:real^3->bool) SUBSET X` THEN
      UNDISCH_TAC `~(R:real^3->bool = {})` THEN SET_TAC[];
      MP_TAC(ISPEC `X:real^3->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(p:real^3) IN interior X` THEN
      UNDISCH_TAC `(p:real^3) IN M` THEN
      UNDISCH_TAC `DISJOINT (M:real^3->bool) X` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?J:real^3->bool. components tr = {J}` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `components (tr:real^3->bool)` CARD_LE_1) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `J:real^3->bool`) THEN
    EXISTS_TAC `J:real^3->bool` THEN
    MP_TAC(ISPEC `tr:real^3->bool` COMPONENTS_EQ_EMPTY) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `components tr SUBSET {J:real^3->bool}` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`; `u:real^3`; `v:real^3`;
                 `phi:real^3->real^2`; `phi':real^2->real^3`; `J:real^3->bool`]
    MOI_S3TR_COMP_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_SING]; STRIP_TAC] THEN
  SUBGOAL_THEN `tr:real^3->bool = J` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [UNIONS_COMPONENTS] THEN ASM_REWRITE_TAC[UNIONS_1];
    ALL_TAC] THEN
  ABBREV_TAC `cJ = IMAGE (phi:real^3->real^2) J` THEN
  MP_TAC(ISPEC `cJ:real^2->bool` MOI_S3TR_JF) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
    can (term_match [] `homeomorphism (a:real^3->bool,b:real^2->bool) (f,g)`)
        (concl th))) THEN
  ABBREV_TAC `Din = IMAGE (phi':real^2->real^3) (inside cJ)` THEN
  ABBREV_TAC `Dout = IMAGE (phi':real^2->real^3) (ball(vec 0,&1) INTER outside cJ)` THEN
  SUBGOAL_THEN `connected (Din:real^3->bool) /\ connected (Dout:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Din"; "Dout"] THEN CONJ_TAC THEN
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:real^2,&1)` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `cJ UNION inside cJ SUBSET ball(vec 0:real^2,&1)` THEN SET_TAC[];
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:real^2,&1)` THEN
      ASM_REWRITE_TAC[INTER_SUBSET];
      MP_TAC(ISPECL [`cJ:real^2->bool`; `sphere(vec 0:real^2,&1)`] MOI_S3TR_OPEN_ANNULUS) THEN
      REWRITE_TAC[INSIDE_SPHERE; HOMEOMORPHIC_REFL] THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `cJ UNION inside cJ SUBSET ball(vec 0:real^2,&1)` THEN SET_TAC[];
        SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `M = (Din UNION J) UNION (Dout:real^3->bool) /\
    IMAGE (phi':real^2->real^3) (cJ UNION inside cJ) = Din UNION J /\
    DISJOINT (Din:real^3->bool) J /\ DISJOINT (Dout:real^3->bool) J /\
    DISJOINT (Din UNION J) (Dout:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Din"; "Dout"] THEN
    MP_TAC(ISPEC `cJ:real^2->bool` INSIDE_NO_OVERLAP) THEN
    MP_TAC(ISPEC `cJ:real^2->bool` OUTSIDE_NO_OVERLAP) THEN
    UNDISCH_TAC `inside cJ INTER outside cJ:real^2->bool = {}` THEN
    UNDISCH_TAC `inside cJ UNION outside cJ = (:real^2) DIFF cJ` THEN
    UNDISCH_TAC `cJ UNION inside cJ SUBSET ball(vec 0:real^2,&1)` THEN
    UNDISCH_TAC `IMAGE (phi':real^2->real^3) cJ = J` THEN
    UNDISCH_TAC `IMAGE (phi':real^2->real^3) (ball(vec 0,&1)) = M` THEN
    UNDISCH_TAC `!y. y IN ball(vec 0:real^2,&1)
                     ==> (phi:real^3->real^2) ((phi':real^2->real^3) y) = y` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `M INTER frontier X = J:real^3->bool` ASSUME_TAC THENL
   [UNDISCH_TAC `E INTER frontier X = (tr:real^3->bool)` THEN
    UNDISCH_TAC `E DIFF R = (M:real^3->bool)` THEN
    UNDISCH_TAC `tr:real^3->bool = J` THEN
    UNDISCH_TAC `tr SUBSET (M:real^3->bool) DELETE p` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (Din:real^3->bool) (frontier X) /\
                DISJOINT (Dout:real^3->bool) (frontier X)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `M INTER frontier X = J:real^3->bool` THEN
    UNDISCH_TAC `M = (Din UNION J) UNION (Dout:real^3->bool)` THEN
    UNDISCH_TAC `DISJOINT (Din:real^3->bool) J` THEN
    UNDISCH_TAC `DISJOINT (Dout:real^3->bool) J` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (Din UNION J:real^3->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `IMAGE (phi':real^2->real^3) (cJ UNION inside cJ) = Din UNION J`)) THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:real^2,&1)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (Dout:real^3->bool) X` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`Dout:real^3->bool`; `X:real^3->bool`] MOI_S3TR_CONNECTED_SIDE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    SUBGOAL_THEN `closure (Dout:real^3->bool) SUBSET X` ASSUME_TAC THENL
     [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `X:real^3->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(Dout:real^3->bool) SUBSET interior X` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(E:real^3->bool) = (Din UNION J) UNION closure Dout` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `closure M = (E:real^3->bool)`)) THEN
    FIRST_ASSUM(SUBST1_TAC o check (fun th ->
      concl th = `M = (Din UNION J) UNION (Dout:real^3->bool)`)) THEN
    ONCE_REWRITE_TAC[CLOSURE_UNION] THEN
    ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
    UNDISCH_TAC `DISJOINT (R:real^3->bool) X` THEN
  UNDISCH_TAC `(R:real^3->bool) SUBSET E` THEN
  UNDISCH_TAC `E DIFF R = (M:real^3->bool)` THEN
  UNDISCH_TAC `M = (Din UNION J) UNION (Dout:real^3->bool)` THEN
  UNDISCH_TAC `(E:real^3->bool) = (Din UNION J) UNION closure Dout` THEN
  UNDISCH_TAC `closure (Dout:real^3->bool) SUBSET X` THEN
  UNDISCH_TAC `~(R:real^3->bool = {})` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Din:real^3->bool) SUBSET X` ASSUME_TAC THENL
   [SUBGOAL_THEN `(p:real^3) IN Din` ASSUME_TAC THENL
     [MP_TAC(ISPEC `X:real^3->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(p:real^3) IN interior X` THEN
      UNDISCH_TAC `(p:real^3) IN M` THEN
      UNDISCH_TAC `M = (Din UNION J) UNION (Dout:real^3->bool)` THEN
      UNDISCH_TAC `DISJOINT (Dout:real^3->bool) X` THEN
      UNDISCH_TAC `tr SUBSET (M:real^3->bool) DELETE p` THEN
      UNDISCH_TAC `tr:real^3->bool = J` THEN
      SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`Din:real^3->bool`; `X:real^3->bool`] MOI_S3TR_CONNECTED_SIDE) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `X:real^3->bool` INTERIOR_SUBSET) THEN
    MP_TAC(ISPEC `X:real^3->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(p:real^3) IN interior X` THEN
    UNDISCH_TAC `(p:real^3) IN Din` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `E INTER X = Din UNION J:real^3->bool` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`X:real^3->bool`] FRONTIER_SUBSET_CLOSED) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `E INTER X SUBSET (M:real^3->bool)` THEN
    UNDISCH_TAC `E DIFF R = (M:real^3->bool)` THEN
    UNDISCH_TAC `M = (Din UNION J) UNION (Dout:real^3->bool)` THEN
    UNDISCH_TAC `DISJOINT (Dout:real^3->bool) X` THEN
    UNDISCH_TAC `(Din:real^3->bool) SUBSET X` THEN
    UNDISCH_TAC `M INTER frontier X = J:real^3->bool` THEN
    UNDISCH_TAC `frontier X SUBSET (X:real^3->bool)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    concl th = `IMAGE (phi':real^2->real^3) (cJ UNION inside cJ) = Din UNION J`)) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* All edges at once (induction over finite sets of edges), and              *)
(* MOI_S33_TRACES with the two splitting operations as antecedents.          *)
(* ------------------------------------------------------------------------- *)

let MOI_S3TR_ALL_EDGES = prove
 (mk_imp(list_mk_conj[MOI_FND_SPLIT_DISK_R3; MOI_FND_SPLIT_ANNULUS_R3;
                      inst [`:3`,`:N`] MOI_S33_DISK_RECOG_BODY;
                      inst [`:3`,`:N`] MOI_S33_HOLED_RECOG_BODY],
  `!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c.
     moi_s33_hd t l h e c
     ==> !S. FINITE S
             ==> S SUBSET {s | s IN l /\ aff_dim s = &1}
                 ==> !x. moi_s33_x2 t l h e x
                         ==> ?x'. moi_s33_x2 t l h e x' /\
                                  !s. s IN S
                                      ==> CARD (components (e s INTER
                                                            frontier (UNIONS x'))) <= 1`),
  DISCH_THEN(LABEL_TAC "red" o MATCH_MP MOI_S3TR_EDGE_REDUCE) THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[NOT_IN_EMPTY] THEN MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s0:real^3->bool`; `S:(real^3->bool)->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[INSERT_SUBSET; IN_ELIM_THM] THEN STRIP_TAC THEN
  X_GEN_TAC `x:(real^3->bool)->bool` THEN DISCH_TAC THEN
  REMOVE_THEN "ih" (MP_TAC o C MATCH_MP
    (ASSUME `S SUBSET {s:real^3->bool | s IN l /\ aff_dim s = &1}`)) THEN
  DISCH_THEN(MP_TAC o C MATCH_MP (ASSUME `moi_s33_x2 t l (h:real^3->real^3) e x`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `x1:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `s0:real^3->bool`] MOI_S3X2_TUBE_EDGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[moi_s33_hd]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3` (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)) THEN
  REMOVE_THEN "red" (MP_TAC o SPECL
   [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
    `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`; `u:real^3`; `v:real^3`;
    `x1:(real^3->bool)->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x':(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `x':(real^3->bool)->bool` THEN REWRITE_TAC[FORALL_IN_INSERT] THEN
  REPEAT CONJ_TAC THENL [ASM_REWRITE_TAC[]; ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `s:real^3->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(e:(real^3->bool)->real^3->bool) s INTER frontier (UNIONS x') =
    e s INTER frontier (UNIONS x1)`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `S SUBSET {s:real^3->bool | s IN l /\ aff_dim s = &1}` THEN
    UNDISCH_TAC `(s:real^3->bool) IN S` THEN
    UNDISCH_TAC `~((s0:real^3->bool) IN S)` THEN
    UNDISCH_TAC `s0:real^3->bool = segment[u,v]` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ASM_SIMP_TAC[]]);;

let MOI_S3TR_TRACES_COND = prove
 (mk_imp(mk_conj(MOI_FND_SPLIT_DISK_R3, MOI_FND_SPLIT_ANNULUS_R3), MOI_S33_TRACES),
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  MP_TAC MOI_S3TR_ALL_EDGES THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "all") THEN
  MAP_EVERY X_GEN_TAC
   [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
    `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
    `x:(real^3->bool)->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (l:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S3FR_TUBE_BASIC; moi_s33_hd]; ALL_TAC] THEN
  REMOVE_THEN "all" (MP_TAC o SPECL
   [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
    `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `{s:real^3->bool | s IN l /\ aff_dim s = &1}`) THEN
  ASM_SIMP_TAC[FINITE_RESTRICT; SUBSET_REFL] THEN
  DISCH_THEN(MP_TAC o SPEC `x:(real^3->bool)->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x':(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `x':(real^3->bool)->bool` THEN ASM_REWRITE_TAC[moi_s33_traces] THEN
  MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `x':(real^3->bool)->bool`; `u:real^3`; `v:real^3`]
    MOI_S3TR_FINAL) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM; AFF_DIM_SEGMENT]);;

(* ------------------------------------------------------------------------- *)
(* The disk half of the splitting operations is a theorem (pc_moi_fnd_split  *)
(* with pc_moi_fnd_rnb2, pc_moi_fnd_sptrace and pc_moi_fnd_nb2f), so only    *)
(* MOI_FND_SPLIT_ANNULUS_R3 stays an antecedent; pc_moi_core_status          *)
(* discharges it.                                                            *)
(* ------------------------------------------------------------------------- *)

let MOI_S3TR_SPLIT_DISK =
  MP SPLIT_SURFACE_DISK_3
     (CONJ DERIVED_NBHD_BALL_2
           (MP SPLIT_TRACE_ANNULUS (INST_TYPE [`:3`,`:N`] DERIVED_NBHD_POLYGON_2)));;

let MOI_S3TR_TRACES_ANN = prove
 (mk_imp(MOI_FND_SPLIT_ANNULUS_R3, MOI_S33_TRACES),
  DISCH_THEN(fun th ->
    ACCEPT_TAC(MP MOI_S3TR_TRACES_COND (CONJ MOI_S3TR_SPLIT_DISK th))));;


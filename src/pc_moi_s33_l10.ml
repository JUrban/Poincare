(* ========================================================================= *)
(* pc_moi_s33_l10: Moise 33.1 Lemma 10 (GTM 47, pp.234-236), surjectivity    *)
(* on loops.  Main theorem                                                   *)
(*   S33_SURJ |- MOI_S33_SURJ   (pc_moi_s33_stmt.ml)                         *)
(* Route (following the ideas of DG): W = Int N' - K' is a product D x (0,1) *)
(* (TUBE_FACTS); Bd X = S is a compact surface in W whose two sides O1, O2   *)
(* contain the two chart ends; loops on one side are pushed to the extreme   *)
(* level of S on the other side (the square argument: an eta-chain in the    *)
(* preimage of S from the left to the right edge, by 30.2 in the plane), and *)
(* a general path is cut at its visits to S.                                 *)
(* ========================================================================= *)

needs "src/pc_moi_s33_stmt.ml";;
needs "src/pc_moi_s30sep.ml";;
needs "src/pc_moi_fnd_m3a.ml";;   (* COMPLEX_BOUNDARY_FRONTIER_3 *)

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Part 1: generic helpers.  CONNECTED_OPEN_SPLIT; STAR: a finite union      *)
(* of compact convex sets is star-shaped at each of its points within some   *)
(* ball; ULPC: such a union is uniformly locally path connected; BALL_HOMOT: *)
(* two paths with common ends in a convex subset of W are homotopic in W.    *)
(* ========================================================================= *)

let MOI_S3SJ_CONNECTED_OPEN_SPLIT = prove
 (`!c u v:real^N->bool.
     connected c /\ open u /\ open v /\ DISJOINT u v /\ c SUBSET u UNION v
     ==> c SUBSET u \/ c SUBSET v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONNECTED; NOT_EXISTS_THM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N->bool`; `v:real^N->bool`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DISJOINT]) THEN ASM_REWRITE_TAC[] THEN
  ASM SET_TAC[]);;

let MOI_S3SJ_STAR = prove
 (`!(ff:(real^N->bool)->bool) x.
     FINITE ff /\ (!k. k IN ff ==> compact k /\ convex k) /\ x IN UNIONS ff
     ==> ?r. &0 < r /\
             !y. y IN UNIONS ff /\ dist(x,y) < r ==> segment[x,y] SUBSET UNIONS ff`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `closed (UNIONS {k | k IN ff /\ ~((x:real^N) IN k)})` MP_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN
    ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  REWRITE_TAC[closed; OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ANTS_TAC THENL
   [REWRITE_TAC[IN_DIFF; IN_UNIV; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
  UNDISCH_TAC `(y:real^N) IN UNIONS ff` THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:real^N) IN k` ASSUME_TAC THENL
   [ASM_CASES_TAC `(x:real^N) IN k` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ball(x:real^N,r) SUBSET
                 (:real^N) DIFF UNIONS {k | k IN ff /\ ~((x:real^N) IN k)}` THEN
    REWRITE_TAC[SUBSET; IN_BALL; IN_DIFF; IN_UNIV; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `k:real^N->bool` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `convex (k:real^N->bool)` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[CONVEX_CONTAINS_SEGMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `(k:real^N->bool) IN ff` THEN SET_TAC[]]);;

let MOI_S3SJ_ULPC = prove
 (`!(ff:(real^N->bool)->bool) e.
     FINITE ff /\ (!k. k IN ff ==> compact k /\ convex k) /\ &0 < e
     ==> ?d. &0 < d /\
             !x y. x IN UNIONS ff /\ y IN UNIONS ff /\ dist(x,y) < d
                   ==> ?p. path p /\ path_image p SUBSET UNIONS ff /\
                           path_image p SUBSET ball(x,e) /\
                           pathstart p = x /\ pathfinish p = y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?r. !x:real^N. x IN UNIONS ff
          ==> &0 < r x /\ r x <= e / &2 /\
              !y. y IN UNIONS ff /\ dist(x,y) < r x ==> segment[x,y] SUBSET UNIONS ff`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`ff:(real^N->bool)->bool`; `x:real^N`] MOI_S3SJ_STAR) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min r0 (e / &2)` THEN
    ASM_REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    CONJ_TAC THENL [UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `UNIONS ff:real^N->bool` HEINE_BOREL_LEMMA) THEN ANTS_TAC THENL
   [MATCH_MP_TAC COMPACT_UNIONS THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `{ball(x:real^N,r x / &2) | x IN UNIONS ff}`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_GSPEC; OPEN_BALL] THEN
    REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN EXISTS_TAC `x:real^N` THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`x0:real^N`; `y0:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x0:real^N`) THEN ASM_REWRITE_TAC[EXISTS_IN_GSPEC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x0:real^N) IN ball(z,r z / &2) /\ (y0:real^N) IN ball(z,r z / &2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (term_match [] `ball(x0:real^N,d) SUBSET s`) (concl th))) THEN
    REWRITE_TAC[IN_BALL] THEN ASM_REWRITE_TAC[DIST_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `segment[z:real^N,x0] SUBSET UNIONS ff /\ segment[z,y0] SUBSET UNIONS ff /\
    segment[z:real^N,x0] SUBSET ball(z,r z / &2) /\ segment[z,y0] SUBSET ball(z,r z / &2)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(x0:real^N) IN ball(z,r z / &2)` THEN REWRITE_TAC[IN_BALL] THEN
      UNDISCH_TAC `&0 < (r:real^N->real) z` THEN REAL_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y0:real^N) IN ball(z,r z / &2)` THEN REWRITE_TAC[IN_BALL] THEN
      UNDISCH_TAC `&0 < (r:real^N->real) z` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC(REWRITE_RULE[CONVEX_CONTAINS_SEGMENT] (ISPECL
        [`z:real^N`; `(r:real^N->real) z / &2`] CONVEX_BALL)) THEN
      ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN
      UNDISCH_TAC `&0 < (r:real^N->real) z` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC(REWRITE_RULE[CONVEX_CONTAINS_SEGMENT] (ISPECL
        [`z:real^N`; `(r:real^N->real) z / &2`] CONVEX_BALL)) THEN
      ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN
      UNDISCH_TAC `&0 < (r:real^N->real) z` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `linepath(x0:real^N,z) ++ linepath(z,y0)` THEN
  REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH;
              PATHFINISH_LINEPATH] THEN
  SIMP_TAC[PATH_JOIN; PATH_LINEPATH; PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
  SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
           PATH_IMAGE_LINEPATH] THEN
  SUBGOAL_THEN
   `segment[x0:real^N,z] SUBSET UNIONS ff /\ segment[x0:real^N,z] SUBSET ball(z,r z / &2)`
  STRIP_ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[SEGMENT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[UNION_SUBSET] THEN
  SUBGOAL_THEN `ball(z:real^N,r z / &2) SUBSET ball(x0,e)` MP_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL] THEN X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    UNDISCH_TAC `(x0:real^N) IN ball(z,r z / &2)` THEN REWRITE_TAC[IN_BALL] THEN
    UNDISCH_TAC `(r:real^N->real) z <= e / &2` THEN UNDISCH_TAC `&0 < e` THEN
    UNDISCH_TAC `dist(z:real^N,w) < r z / &2` THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`segment[x0:real^N,z] SUBSET ball(z,r z / &2)`;
    `segment[z:real^N,y0] SUBSET ball(z,r z / &2)`] THEN
  SET_TAC[]);;

(* Two paths with the same ends inside a convex subset of w are homotopic. *)

let MOI_S3SJ_CONVEX_HOMOT = prove
 (`!(p:real^1->real^N) q c w.
     path p /\ path q /\ pathstart p = pathstart q /\ pathfinish p = pathfinish q /\
     convex c /\ c SUBSET w /\ path_image p SUBSET c /\ path_image q SUBSET c
     ==> homotopic_paths w p q`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMOTOPIC_PATHS_LINEAR THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `c:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `convex (c:real^N->bool)` THEN REWRITE_TAC[CONVEX_CONTAINS_SEGMENT] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  UNDISCH_TAC `path_image (p:real^1->real^N) SUBSET c` THEN
  UNDISCH_TAC `path_image (q:real^1->real^N) SUBSET c` THEN
  REWRITE_TAC[path_image; SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[]);;

(* ========================================================================= *)
(* Part 2: helpers for the square chain argument.  REL_CONNECTED: a          *)
(* transitive relation holding between eta-close points of G holds between  *)
(* any two points of a connected subset of G.  STRIP_CROSS: a path from     *)
(* below the strip 0 <= y <= 1 to above it has a sub-path inside the strip  *)
(* from its bottom line to its top line.  SEP_CONNECTED: a connected set    *)
(* missing c and meeting h and k contradicts separates_in UNIV c h k.       *)
(* FINITE_COMPONENTS: a finite union of nonempty connected sets has finitely *)
(* many components.  GRID_INDEX: the grid interval of a point of [0,1].     *)
(* ========================================================================= *)

let MOI_S3SJ_REL_CONNECTED = prove
 (`!(R:real^N->real^N->bool) G c a eta.
     &0 < eta /\ (!x y. x IN G /\ y IN G /\ dist(x,y) < eta ==> R x y) /\
     (!x y z. R x y /\ R y z ==> R x z) /\
     connected c /\ c SUBSET G /\ a IN c
     ==> !b. b IN c ==> R a b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `connected (c:real^N->bool)` THEN REWRITE_TAC[connected] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`UNIONS {ball(w:real^N,eta) | w IN c /\ R (a:real^N) w}`;
    `UNIONS {ball(w:real^N,eta) | w IN c /\ ~R (a:real^N) w}`]) THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN
  SUBGOAL_THEN `!w:real^N. w IN c ==> w IN G` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT
   `(a /\ b /\ c /\ d /\ ~e) /\ (f ==> g) ==> (~a \/ ~b \/ ~c \/ ~d \/ e \/ f) ==> g`) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_UNIONS THEN REWRITE_TAC[FORALL_IN_GSPEC; OPEN_BALL];
    MATCH_MP_TAC OPEN_UNIONS THEN REWRITE_TAC[FORALL_IN_GSPEC; OPEN_BALL];
    REWRITE_TAC[SUBSET; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(R:real^N->real^N->bool) a z` THENL
     [DISJ1_TAC; DISJ2_TAC] THEN
    EXISTS_TAC `z:real^N` THEN ASM_REWRITE_TAC[CENTRE_IN_BALL];
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; UNIONS_GSPEC; IN_ELIM_THM;
                IN_BALL] THEN
    X_GEN_TAC `z:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `w1:real^N` STRIP_ASSUME_TAC)
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `w2:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    UNDISCH_TAC `~(R (a:real^N) (w2:real^N))` THEN REWRITE_TAC[] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `z:real^N` THEN CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `w1:real^N` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `dist:real^N#real^N->real`)) (concl th))) THEN
      ASM_SIMP_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `dist:real^N#real^N->real`)) (concl th))) THEN
      ASM_SIMP_TAC[] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; UNIONS_GSPEC; IN_ELIM_THM] THEN
    EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `dist:real^N#real^N->real`)) (concl th))) THEN
    ASM_SIMP_TAC[DIST_REFL];
    DISCH_TAC THEN X_GEN_TAC `b:real^N` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(R:real^N->real^N->bool) a b` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC
     `UNIONS {ball(w:real^N,eta) | w IN c /\ ~R (a:real^N) w} INTER c = {}` THEN
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; UNIONS_GSPEC; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `b:real^N`) THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `b:real^N` THEN ASM_REWRITE_TAC[CENTRE_IN_BALL]]);;

(* A compact nonempty set of reals in real^1 has a largest and a smallest *)
(* element.                                                                 *)

let MOI_S3SJ_COMPACT_MAX_MIN = prove
 (`!s:real^1->bool.
     compact s /\ ~(s = {})
     ==> (?a. a IN s /\ !t. t IN s ==> drop t <= drop a) /\
         (?a. a IN s /\ !t. t IN s ==> drop a <= drop t)`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPEC `IMAGE drop s` COMPACT_ATTAINS_SUP);
    MP_TAC(ISPEC `IMAGE drop s` COMPACT_ATTAINS_INF)] THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; LIFT_DROP; IMAGE_ID; IMAGE_EQ_EMPTY] THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE; EXISTS_IN_IMAGE]);;

let MOI_S3SJ_STRIP_CROSS = prove
 (`!g:real^1->real^2.
     path g /\ (pathstart g)$2 < &0 /\ &1 < (pathfinish g)$2
     ==> ?a b. a IN interval[vec 0,vec 1] /\ b IN interval[vec 0,vec 1] /\
               drop a <= drop b /\ (g a)$2 = &0 /\ (g b)$2 = &1 /\
               !t. t IN interval[a,b] ==> &0 <= (g t)$2 /\ (g t)$2 <= &1`,
  GEN_TAC THEN REWRITE_TAC[path; pathstart; pathfinish] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `{t | t IN interval[vec 0,vec 1] /\
                     (g:real^1->real^2) t IN {y:real^2 | y$2 <= &0}}`
    MOI_S3SJ_COMPACT_MAX_MIN) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_CLOSED_IMP_COMPACT THEN CONJ_TAC THENL
       [MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
        REWRITE_TAC[BOUNDED_INTERVAL] THEN SET_TAC[];
        MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
        ASM_REWRITE_TAC[CLOSED_INTERVAL; CLOSED_HALFSPACE_COMPONENT_LE]];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN EXISTS_TAC `vec 0:real^1` THEN
      ASM_SIMP_TAC[ENDS_IN_UNIT_INTERVAL; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^1` STRIP_ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `interval[a:real^1,vec 1] SUBSET interval[vec 0,vec 1]` ASSUME_TAC THENL
   [UNDISCH_TAC `(a:real^1) IN interval[vec 0,vec 1]` THEN
    REWRITE_TAC[SUBSET; IN_INTERVAL_1; DROP_VEC] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `{t | t IN interval[a,vec 1] /\
                     (g:real^1->real^2) t IN {y:real^2 | y$2 >= &1}}`
    MOI_S3SJ_COMPACT_MAX_MIN) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_CLOSED_IMP_COMPACT THEN CONJ_TAC THENL
       [MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `interval[a:real^1,vec 1]` THEN
        REWRITE_TAC[BOUNDED_INTERVAL] THEN SET_TAC[];
        MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
        REWRITE_TAC[CLOSED_INTERVAL; CLOSED_HALFSPACE_COMPONENT_GE] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN EXISTS_TAC `vec 1:real^1` THEN
      UNDISCH_TAC `(a:real^1) IN interval[vec 0,vec 1]` THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; real_ge] THEN
      UNDISCH_TAC `&1 < ((g:real^1->real^2) (vec 1))$2` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^1` STRIP_ASSUME_TAC o CONJUNCT2) THEN
  MAP_EVERY EXISTS_TAC [`a:real^1`; `b:real^1`] THEN
  SUBGOAL_THEN `drop a <= drop b /\ (b:real^1) IN interval[vec 0,vec 1]`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(b:real^1) IN interval[a,vec 1]` THEN
    UNDISCH_TAC `(a:real^1) IN interval[vec 0,vec 1]` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `interval[a:real^1,b] SUBSET interval[vec 0,vec 1]` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(a:real^1) IN interval[vec 0,vec 1]`; `(b:real^1) IN interval[vec 0,vec 1]`] THEN
    REWRITE_TAC[SUBSET; IN_INTERVAL_1; DROP_VEC] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^1->real^2) continuous_on interval[a,b]` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((g:real^1->real^2) a)$2 = &0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:real^1->real^2`; `a:real^1`; `b:real^1`; `&0`; `2`]
      IVT_INCREASING_COMPONENT_ON_1) THEN
    ASM_REWRITE_TAC[DIMINDEX_2; ARITH] THEN ANTS_TAC THENL
     [UNDISCH_TAC `((g:real^1->real^2) b)$2 >= &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real^1` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `&0`)) (concl th) &&
      can (find_term (fun t -> t = `a:real^1`)) (concl th))) THEN
    ANTS_TAC THENL [ASM SET_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `t:real^1 = a` (fun th -> ASM_MESON_TAC[th]) THEN
    REWRITE_TAC[GSYM DROP_EQ] THEN
    UNDISCH_TAC `(t:real^1) IN interval[a,b]` THEN REWRITE_TAC[IN_INTERVAL_1] THEN
    UNDISCH_TAC `drop t <= drop a` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `((g:real^1->real^2) b)$2 = &1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:real^1->real^2`; `a:real^1`; `b:real^1`; `&1`; `2`]
      IVT_INCREASING_COMPONENT_ON_1) THEN
    ASM_REWRITE_TAC[DIMINDEX_2; ARITH] THEN ANTS_TAC THENL
     [UNDISCH_TAC `((g:real^1->real^2) b)$2 >= &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real^1` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `b:real^1`)) (concl th))) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `(t:real^1) IN interval[a,b]` THEN
        UNDISCH_TAC `(b:real^1) IN interval[vec 0,vec 1]` THEN
        REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN REAL_ARITH_TAC;
        ASM_REWRITE_TAC[real_ge; REAL_LE_REFL]];
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `t:real^1 = b` (fun th -> ASM_MESON_TAC[th]) THEN
    REWRITE_TAC[GSYM DROP_EQ] THEN
    UNDISCH_TAC `(t:real^1) IN interval[a,b]` THEN REWRITE_TAC[IN_INTERVAL_1] THEN
    UNDISCH_TAC `drop b <= drop t` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN CONJ_TAC THENL
   [ASM_CASES_TAC `t:real^1 = a` THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real^1` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `&0`)) (concl th) &&
      can (find_term (fun t -> t = `a:real^1`)) (concl th))) THEN
    REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
     [CONJ_TAC THENL [ASM SET_TAC[]; ASM_SIMP_TAC[REAL_LT_IMP_LE]];
      UNDISCH_TAC `~(t:real^1 = a)` THEN REWRITE_TAC[GSYM DROP_EQ] THEN
      UNDISCH_TAC `(t:real^1) IN interval[a,b]` THEN REWRITE_TAC[IN_INTERVAL_1] THEN
      REAL_ARITH_TAC];
    ASM_CASES_TAC `t:real^1 = b` THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real^1` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `b:real^1`)) (concl th))) THEN
    REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `(t:real^1) IN interval[a,b]` THEN
        UNDISCH_TAC `(b:real^1) IN interval[vec 0,vec 1]` THEN
        REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN REAL_ARITH_TAC;
        ASM_SIMP_TAC[real_ge; REAL_LT_IMP_LE]];
      UNDISCH_TAC `~(t:real^1 = b)` THEN REWRITE_TAC[GSYM DROP_EQ] THEN
      UNDISCH_TAC `(t:real^1) IN interval[a,b]` THEN REWRITE_TAC[IN_INTERVAL_1] THEN
      REAL_ARITH_TAC]]);;

let MOI_S3SJ_SEP_CONNECTED = prove
 (`!c h k ll:real^N->bool.
     separates_in (:real^N) c h k /\ connected ll /\ DISJOINT ll c /\
     ~(ll INTER h = {}) /\ ~(ll INTER k = {})
     ==> F`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[separates_in; SUBTOPOLOGY_UNIV; GSYM OPEN_IN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN
    `v:real^N->bool` STRIP_ASSUME_TAC)) STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`ll:real^N->bool`; `u:real^N->bool`; `v:real^N->bool`]
    MOI_S3SJ_CONNECTED_OPEN_SPLIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  ASM SET_TAC[]);;

let MOI_S3SJ_FINITE_COMPONENTS = prove
 (`!pp:(real^N->bool)->bool.
     FINITE pp /\ (!p. p IN pp ==> connected p /\ ~(p = {}))
     ==> FINITE (components (UNIONS pp))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE (\p:real^N->bool. connected_component (UNIONS pp) (CHOICE p)) pp` THEN
  ASM_SIMP_TAC[FINITE_IMAGE] THEN
  REWRITE_TAC[SUBSET; components; FORALL_IN_GSPEC; IN_IMAGE] THEN
  X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `p:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC CONNECTED_COMPONENT_EQ THEN
  SUBGOAL_THEN `(p:real^N->bool) SUBSET connected_component (UNIONS pp) y` MP_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_SIMP_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC CHOICE_DEF THEN ASM_SIMP_TAC[]);;

let MOI_S3SJ_GRID_INDEX = prove
 (`!x n. ~(n = 0) /\ &0 <= x /\ x <= &1
         ==> ?i. i < n /\ &i / &n <= x /\ x <= (&i + &1) / &n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&(n - 1) + &1 = &n` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?i. x <= (&i + &1) / &n` MP_TAC THENL
   [EXISTS_TAC `n - 1` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&n / &n = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_DIV_REFL THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&n / &n = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_DIV_REFL THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `i = 0` THENL
   [ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i - 1`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&(i - 1) + &1 = &i` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Part 3: the grid.  moi_s3sj_sq n i j is the closed grid square           *)
(* [i/n,(i+1)/n] x [j/n,(j+1)/n].  SQ_FACTS: membership, inside the unit    *)
(* square, small, closed, convex, nonempty.  SQ_COVER: the unit square is   *)
(* covered.  PLANE_SEP: a closed set in the strip 0 <= y <= 1 containing    *)
(* the two outer half-strips and G separates the half planes below and     *)
(* above the strip when no connected subset of the square minus G joins     *)
(* the bottom to the top.  BAR_IN: such a separating component contains     *)
(* each outer half-strip.                                                    *)
(* ========================================================================= *)

let moi_s3sj_sq = new_definition
 `moi_s3sj_sq n i j =
    interval[vector[&i / &n; &j / &n]:real^2,
             vector[(&i + &1) / &n; (&j + &1) / &n]]`;;

let MOI_S3SJ_SQ_FACTS = prove
 (`!n i j.
     ~(n = 0)
     ==> (!x. x IN moi_s3sj_sq n i j <=>
              &i / &n <= x$1 /\ x$1 <= (&i + &1) / &n /\
              &j / &n <= x$2 /\ x$2 <= (&j + &1) / &n) /\
         (i < n /\ j < n ==> moi_s3sj_sq n i j SUBSET interval[vec 0,vec 1]) /\
         (!x y. x IN moi_s3sj_sq n i j /\ y IN moi_s3sj_sq n i j
                ==> abs(x$1 - y$1) <= inv(&n) /\ abs(x$2 - y$2) <= inv(&n) /\
                    dist(x,y) <= &2 * inv(&n)) /\
         closed (moi_s3sj_sq n i j) /\ convex (moi_s3sj_sq n i j) /\
         ~(moi_s3sj_sq n i j = {})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN moi_s3sj_sq n i j <=>
        &i / &n <= x$1 /\ x$1 <= (&i + &1) / &n /\
        &j / &n <= x$2 /\ x$2 <= (&j + &1) / &n`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_s3sj_sq; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [STRIP_TAC THEN REWRITE_TAC[SUBSET; IN_INTERVAL; DIMINDEX_2; FORALL_2; VEC_COMPONENT] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= &i / &n /\ &0 <= &j / &n /\ (&i + &1) / &n <= &1 /\
                  (&j + &1) / &n <= &1` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ] THEN
      REWRITE_TAC[REAL_MUL_LID; REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(&i + &1) / &n - &i / &n = inv(&n) /\
                  (&j + &1) / &n - &j / &n = inv(&n)` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `abs((x:real^2)$1 - (y:real^2)$1) <= inv(&n) /\ abs(x$2 - y$2) <= inv(&n)`
    STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[dist] THEN
    MP_TAC(ISPEC `x - y:real^2` NORM_LE_L1) THEN
    REWRITE_TAC[DIMINDEX_2; SUM_2; VECTOR_SUB_COMPONENT] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[moi_s3sj_sq; CLOSED_INTERVAL];
    REWRITE_TAC[moi_s3sj_sq; CONVEX_INTERVAL];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `vector[&i / &n; &j / &n]:real^2` THEN ASM_REWRITE_TAC[VECTOR_2] THEN
    REWRITE_TAC[REAL_LE_REFL; real_div; REAL_ADD_RDISTRIB] THEN
    MP_TAC(SPEC `&n` REAL_LT_INV) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let MOI_S3SJ_SQ_COVER = prove
 (`!n x. ~(n = 0) /\ x IN interval[vec 0:real^2,vec 1]
         ==> ?i j. i < n /\ j < n /\ x IN moi_s3sj_sq n i j`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VEC_COMPONENT] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`(x:real^2)$1`; `n:num`] MOI_S3SJ_GRID_INDEX) THEN
  MP_TAC(SPECL [`(x:real^2)$2`; `n:num`] MOI_S3SJ_GRID_INDEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`i:num`; `j:num`] THEN ASM_SIMP_TAC[MOI_S3SJ_SQ_FACTS]);;

let MOI_S3SJ_PLANE_SEP = prove
 (`!(cp:real^2->bool) G.
     closed cp /\ G SUBSET cp /\ cp SUBSET {x | &0 <= x$2 /\ x$2 <= &1} /\
     {x:real^2 | x$1 <= &0 /\ &0 <= x$2 /\ x$2 <= &1} SUBSET cp /\
     {x:real^2 | &1 <= x$1 /\ &0 <= x$2 /\ x$2 <= &1} SUBSET cp /\
     ~(?c a b. connected c /\ c SUBSET interval[vec 0,vec 1] DIFF G /\
               a IN c /\ b IN c /\ a$2 = &0 /\ b$2 = &1)
     ==> separates_in (:real^2) cp {x | x$2 < &0} {x | x$2 > &1}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `oo = (:real^2) DIFF cp` THEN
  SUBGOAL_THEN `open (oo:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "oo" THEN ASM_REWRITE_TAC[GSYM closed]; ALL_TAC] THEN
  SUBGOAL_THEN
   `{x:real^2 | x$2 < &0} SUBSET oo /\ {x:real^2 | x$2 > &1} SUBSET oo`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "oo" THEN
    UNDISCH_TAC `cp SUBSET {x:real^2 | &0 <= x$2 /\ x$2 <= &1}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DIFF; IN_UNIV; real_gt] THEN
    MESON_TAC[REAL_NOT_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `connected {x:real^2 | x$2 < &0} /\ connected {x:real^2 | x$2 > &1}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CONVEX_CONNECTED THEN
    REWRITE_TAC[CONVEX_HALFSPACE_COMPONENT_LT; CONVEX_HALFSPACE_COMPONENT_GT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?h0 k0:real^2. h0 IN {x:real^2 | x$2 < &0} /\ k0 IN {x:real^2 | x$2 > &1}`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXISTS_TAC [`vector[&0; --(&1)]:real^2`; `vector[&0; &2]:real^2`] THEN
    REWRITE_TAC[IN_ELIM_THM; VECTOR_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{x:real^2 | x$2 < &0} SUBSET connected_component oo h0 /\
    {x:real^2 | x$2 > &1} SUBSET connected_component oo k0`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((k0:real^2) IN connected_component oo h0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `path_connected (connected_component oo (h0:real^2))` MP_TAC THENL
     [MATCH_MP_TAC CONNECTED_OPEN_PATH_CONNECTED THEN
      ASM_SIMP_TAC[OPEN_CONNECTED_COMPONENT; CONNECTED_CONNECTED_COMPONENT];
      ALL_TAC] THEN
    REWRITE_TAC[path_connected] THEN
    DISCH_THEN(MP_TAC o SPECL [`h0:real^2`; `k0:real^2`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[CONNECTED_COMPONENT_REFL_EQ] THEN ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^2` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPEC `g:real^1->real^2` MOI_S3SJ_STRIP_CROSS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC
       [`(h0:real^2) IN {x:real^2 | x$2 < &0}`; `(k0:real^2) IN {x:real^2 | x$2 > &1}`] THEN
      REWRITE_TAC[IN_ELIM_THM; real_gt] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^1` (X_CHOOSE_THEN `b:real^1` STRIP_ASSUME_TAC)) THEN
    UNDISCH_TAC `~(?c a b:real^2. connected c /\ c SUBSET interval[vec 0,vec 1] DIFF G /\
                   a IN c /\ b IN c /\ a$2 = &0 /\ b$2 = &1)` THEN
    REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (g:real^1->real^2) (interval[a,b])`;
                          `(g:real^1->real^2) a`; `(g:real^1->real^2) b`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN REWRITE_TAC[CONNECTED_INTERVAL] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[path]; ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC
       [`(a:real^1) IN interval[vec 0,vec 1]`; `(b:real^1) IN interval[vec 0,vec 1]`] THEN
      REWRITE_TAC[SUBSET; IN_INTERVAL_1; DROP_VEC] THEN REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(t:real^1) IN interval[vec 0,vec 1]` ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`(t:real^1) IN interval[a,b]`; `(a:real^1) IN interval[vec 0,vec 1]`;
          `(b:real^1) IN interval[vec 0,vec 1]`] THEN
        REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `(g:real^1->real^2) t IN oo` MP_TAC THENL
       [UNDISCH_TAC `path_image (g:real^1->real^2) SUBSET connected_component oo h0` THEN
        MP_TAC(ISPECL [`oo:real^2->bool`; `h0:real^2`] CONNECTED_COMPONENT_SUBSET) THEN
        REWRITE_TAC[path_image] THEN UNDISCH_TAC `(t:real^1) IN interval[vec 0,vec 1]` THEN
        SET_TAC[];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real^1` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `interval[a:real^1,b]`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXPAND_TAC "oo" THEN
      REWRITE_TAC[IN_DIFF; IN_UNIV; IN_INTERVAL; DIMINDEX_2; FORALL_2; VEC_COMPONENT] THEN
      DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
        UNDISCH_TAC `~((g:real^1->real^2) t IN cp)` THEN REWRITE_TAC[] THEN
        UNDISCH_TAC `{x:real^2 | x$1 <= &0 /\ &0 <= x$2 /\ x$2 <= &1} SUBSET cp` THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE];
        REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
        UNDISCH_TAC `~((g:real^1->real^2) t IN cp)` THEN REWRITE_TAC[] THEN
        UNDISCH_TAC `{x:real^2 | &1 <= x$1 /\ &0 <= x$2 /\ x$2 <= &1} SUBSET cp` THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE];
        UNDISCH_TAC `(G:real^2->bool) SUBSET cp` THEN
        UNDISCH_TAC `~((g:real^1->real^2) t IN cp)` THEN SET_TAC[]];
      MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[ENDS_IN_INTERVAL] THEN
      REWRITE_TAC[INTERVAL_NE_EMPTY_1] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[ENDS_IN_INTERVAL] THEN
      REWRITE_TAC[INTERVAL_NE_EMPTY_1] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[separates_in; SUBTOPOLOGY_UNIV; GSYM OPEN_IN] THEN
  MAP_EVERY EXISTS_TAC [`connected_component oo (h0:real^2)`;
                        `oo DIFF connected_component oo (h0:real^2)`] THEN
  ASM_SIMP_TAC[OPEN_CONNECTED_COMPONENT] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN EXISTS_TAC `oo:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`oo:real^2->bool`; `h0:real^2`] CLOSED_IN_CONNECTED_COMPONENT) THEN
    REWRITE_TAC[closed_in; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN SIMP_TAC[];
    SET_TAC[];
    MP_TAC(ISPECL [`oo:real^2->bool`; `h0:real^2`] CONNECTED_COMPONENT_SUBSET) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `DISJOINT (connected_component oo (h0:real^2)) (connected_component oo k0)`
  MP_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
    UNDISCH_TAC `~((k0:real^2) IN connected_component oo h0)` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `connected_component oo (z:real^2) = connected_component oo h0 /\
                  connected_component oo z = connected_component oo k0`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC CONNECTED_COMPONENT_EQ THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(k0:real^2) IN connected_component oo k0` MP_TAC THENL
     [REWRITE_TAC[CONNECTED_COMPONENT_REFL_EQ] THEN ASM SET_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`oo:real^2->bool`; `k0:real^2`] CONNECTED_COMPONENT_SUBSET) THEN
  UNDISCH_TAC `{x:real^2 | x$2 > &1} SUBSET connected_component oo k0` THEN
  SET_TAC[]);;

let MOI_S3SJ_BAR_IN = prove
 (`!(cp:real^2->bool) d bb ll h k.
     d IN components cp /\ separates_in (:real^2) d h k /\
     connected bb /\ ~(bb = {}) /\ bb SUBSET cp /\
     connected ll /\ ll INTER cp SUBSET bb /\
     ~(ll INTER h = {}) /\ ~(ll INTER k = {})
     ==> bb SUBSET d`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `bb INTER (d:real^2->bool) = {}` THENL
   [ALL_TAC;
    MATCH_MP_TAC COMPONENTS_MAXIMAL THEN EXISTS_TAC `cp:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]] THEN
  MP_TAC(ISPECL [`d:real^2->bool`; `h:real^2->bool`; `k:real^2->bool`;
                 `ll:real^2->bool`] MOI_S3SJ_SEP_CONNECTED) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN
  ASM SET_TAC[]);;

(* ========================================================================= *)
(* Part 4: CHAIN.  G in the unit square contains the left and right         *)
(* edges, and no connected subset of the square minus G joins the bottom   *)
(* edge to the top edge.  Then any transitive relation holding between      *)
(* eta-close points of G holds from the origin to (1,0).  Route (DG): the   *)
(* grid squares of size 1/n < eta/4 meeting G together with the two outer   *)
(* half-strips separate the half planes y < 0 and y > 1 (PLANE_SEP); 30.2   *)
(* (MOI_S30_302_GEN in real^2) gives one separating component, which        *)
(* contains both half-strips (BAR_IN); the pieces reachable from the origin *)
(* form a clopen part of it, which therefore contains the right half-strip. *)
(* ========================================================================= *)

let MOI_S3SJ_EDGE_FACTS = prove
 (`!a. connected {x:real^2 | x$1 = a /\ &0 <= x$2 /\ x$2 <= &1} /\
       (!x. x IN {x:real^2 | x$1 = a /\ &0 <= x$2 /\ x$2 <= &1}
            ==> x = vector[a; x$2])`,
  GEN_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONVEX_CONNECTED THEN
    SUBGOAL_THEN
     `{x:real^2 | x$1 = a /\ &0 <= x$2 /\ x$2 <= &1} =
      {x | x$1 <= a} INTER {x | x$1 >= a} INTER {x | x$2 >= &0} INTER {x | x$2 <= &1}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC CONVEX_INTER THEN CONJ_TAC) THEN
    REWRITE_TAC[CONVEX_HALFSPACE_COMPONENT_LE; CONVEX_HALFSPACE_COMPONENT_GE];
    REWRITE_TAC[IN_ELIM_THM; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
    MESON_TAC[]]);;

let MOI_S3SJ_DIST_EDGE = prove
 (`!x:real^2 a. dist(vector[a; x$2],x) <= abs(a - x$1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[dist] THEN
  MP_TAC(ISPEC `vector[a; (x:real^2)$2] - x` NORM_LE_L1) THEN
  REWRITE_TAC[DIMINDEX_2; SUM_2; VECTOR_SUB_COMPONENT; VECTOR_2] THEN
  REAL_ARITH_TAC);;

let MOI_S3SJ_CHAIN = prove
 (`!(G:real^2->bool) (R:real^2->real^2->bool) eta.
     G SUBSET interval[vec 0,vec 1] /\ closed G /\
     (!u. &0 <= u /\ u <= &1 ==> vector[&0;u] IN G /\ vector[&1;u] IN G) /\
     ~(?c a b. connected c /\ c SUBSET interval[vec 0,vec 1] DIFF G /\
               a IN c /\ b IN c /\ a$2 = &0 /\ b$2 = &1) /\
     &0 < eta /\
     (!x y. x IN G /\ y IN G /\ dist(x,y) < eta ==> R x y) /\
     (!x y z. R x y /\ R y z ==> R x z)
     ==> R (vec 0) (vector[&1;&0])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `eta / &4` REAL_ARCH_INV) THEN
  ASM_REWRITE_TAC[REAL_ARITH `&0 < e / &4 <=> &0 < e`] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  (* the edges and reachability along them *)
  ABBREV_TAC `le = {x:real^2 | x$1 = &0 /\ &0 <= x$2 /\ x$2 <= &1}` THEN
  ABBREV_TAC `re = {x:real^2 | x$1 = &1 /\ &0 <= x$2 /\ x$2 <= &1}` THEN
  SUBGOAL_THEN
   `connected (le:real^2->bool) /\ connected (re:real^2->bool) /\
    le SUBSET G /\ re SUBSET G /\ vec 0 IN le /\ vector[&1;&0] IN re`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["le"; "re"] THEN
    REWRITE_TAC[MOI_S3SJ_EDGE_FACTS] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      FIRST_ASSUM(SUBST1_TAC o MATCH_MP (CONJUNCT2 (SPEC `&0` MOI_S3SJ_EDGE_FACTS))) THEN
      UNDISCH_TAC `(x:real^2) IN {x:real^2 | x$1 = &0 /\ &0 <= x$2 /\ x$2 <= &1}` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[];
      REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      FIRST_ASSUM(SUBST1_TAC o MATCH_MP (CONJUNCT2 (SPEC `&1` MOI_S3SJ_EDGE_FACTS))) THEN
      UNDISCH_TAC `(x:real^2) IN {x:real^2 | x$1 = &1 /\ &0 <= x$2 /\ x$2 <= &1}` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[];
      REWRITE_TAC[IN_ELIM_THM; VEC_COMPONENT] THEN REAL_ARITH_TAC;
      REWRITE_TAC[IN_ELIM_THM; VECTOR_2] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^2. z IN le ==> (R:real^2->real^2->bool) (vec 0) z`
  (LABEL_TAC "lereach") THENL
   [MATCH_MP_TAC MOI_S3SJ_REL_CONNECTED THEN
    MAP_EVERY EXISTS_TAC [`G:real^2->bool`; `eta:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z w:real^2. z IN re /\ w IN re ==> (R:real^2->real^2->bool) z w`
  (LABEL_TAC "rereach") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`R:real^2->real^2->bool`; `G:real^2->bool`; `re:real^2->bool`;
                   `z:real^2`; `eta:real`] MOI_S3SJ_REL_CONNECTED) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^2. x IN G ==> x IN interval[vec 0,vec 1]` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^2. x IN G ==> &0 <= x$1 /\ x$1 <= &1 /\ &0 <= x$2 /\ x$2 <= &1`
  (LABEL_TAC "Gq") THENL
   [GEN_TAC THEN DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VEC_COMPONENT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the pieces *)
  ABBREV_TAC `bl = {x:real^2 | x$1 <= &0 /\ &0 <= x$2 /\ x$2 <= &1}` THEN
  ABBREV_TAC `br = {x:real^2 | &1 <= x$1 /\ &0 <= x$2 /\ x$2 <= &1}` THEN
  ABBREV_TAC
   `sqs = {moi_s3sj_sq n i j | i,j | i < n /\ j < n /\
                                    ~(moi_s3sj_sq n i j INTER G = {})}` THEN
  SUBGOAL_THEN
   `!p:real^2->bool. p IN sqs <=>
       ?i j. i < n /\ j < n /\ p = moi_s3sj_sq n i j /\ ~(p INTER G = {})`
  (LABEL_TAC "sqsdef") THENL
   [EXPAND_TAC "sqs" THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (sqs:(real^2->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{moi_s3sj_sq n i j | i,j | i IN {i | i < n} /\ j IN {j:num | j < n}}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN REWRITE_TAC[FINITE_NUMSEG_LT];
      REWRITE_TAC[SUBSET] THEN X_GEN_TAC `p:real^2->bool` THEN
      USE_THEN "sqsdef" (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p:real^2->bool. p IN sqs
        ==> p SUBSET interval[vec 0,vec 1] /\ closed p /\ connected p /\ ~(p = {}) /\
            (!x y. x IN p /\ y IN p ==> abs(x$1 - y$1) <= inv(&n) /\
                                        dist(x,y) <= &2 * inv(&n)) /\
            ~(p INTER G = {})`
  (LABEL_TAC "sqf") THENL
   [GEN_TAC THEN USE_THEN "sqsdef" (fun th -> REWRITE_TAC[th]) THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC)) THEN
    MP_TAC(SPECL [`n:num`; `i:num`; `j:num`] MOI_S3SJ_SQ_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[CONVEX_CONNECTED] THEN
    UNDISCH_TAC `~(p INTER (G:real^2->bool) = {})` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `pp = (bl:real^2->bool) INSERT br INSERT sqs` THEN
  SUBGOAL_THEN `FINITE (pp:(real^2->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "pp" THEN ASM_REWRITE_TAC[FINITE_INSERT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `connected (bl:real^2->bool) /\ connected (br:real^2->bool) /\
    closed bl /\ closed br /\ ~(bl = {}) /\ ~(br = {}) /\
    (vec 0:real^2) IN bl /\ DISJOINT bl br`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["bl"; "br"] THEN
    SUBGOAL_THEN
     `{x:real^2 | x$1 <= &0 /\ &0 <= x$2 /\ x$2 <= &1} =
      {x | x$1 <= &0} INTER {x | x$2 >= &0} INTER {x | x$2 <= &1} /\
      {x:real^2 | &1 <= x$1 /\ &0 <= x$2 /\ x$2 <= &1} =
      {x | x$1 >= &1} INTER {x | x$2 >= &0} INTER {x | x$2 <= &1}`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONVEX_CONNECTED THEN
      REPEAT(MATCH_MP_TAC CONVEX_INTER THEN CONJ_TAC) THEN
      REWRITE_TAC[CONVEX_HALFSPACE_COMPONENT_LE; CONVEX_HALFSPACE_COMPONENT_GE];
      MATCH_MP_TAC CONVEX_CONNECTED THEN
      REPEAT(MATCH_MP_TAC CONVEX_INTER THEN CONJ_TAC) THEN
      REWRITE_TAC[CONVEX_HALFSPACE_COMPONENT_LE; CONVEX_HALFSPACE_COMPONENT_GE];
      REPEAT(MATCH_MP_TAC CLOSED_INTER THEN CONJ_TAC) THEN
      REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_LE; CLOSED_HALFSPACE_COMPONENT_GE];
      REPEAT(MATCH_MP_TAC CLOSED_INTER THEN CONJ_TAC) THEN
      REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_LE; CLOSED_HALFSPACE_COMPONENT_GE];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM] THEN
      EXISTS_TAC `vec 0:real^2` THEN REWRITE_TAC[VEC_COMPONENT] THEN REAL_ARITH_TAC;
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM] THEN
      EXISTS_TAC `vector[&1;&0]:real^2` THEN REWRITE_TAC[VECTOR_2] THEN REAL_ARITH_TAC;
      REWRITE_TAC[IN_INTER; IN_ELIM_THM; VEC_COMPONENT] THEN REAL_ARITH_TAC;
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p:real^2->bool. p IN pp ==> closed p /\ connected p /\ ~(p = {}) /\
                                p SUBSET {x | &0 <= x$2 /\ x$2 <= &1}`
  (LABEL_TAC "ppf") THENL
   [EXPAND_TAC "pp" THEN REWRITE_TAC[IN_INSERT] THEN GEN_TAC THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THENL
     [EXPAND_TAC "bl" THEN SET_TAC[];
      EXPAND_TAC "br" THEN SET_TAC[];
      USE_THEN "sqf" (fun th -> MP_TAC(MP (SPEC `p:real^2->bool` th)
        (ASSUME `(p:real^2->bool) IN sqs`))) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `interval[vec 0:real^2,vec 1]` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_INTERVAL; DIMINDEX_2; FORALL_2; VEC_COMPONENT;
                  IN_ELIM_THM] THEN
      MESON_TAC[]];
    ALL_TAC] THEN
  (* the separating component *)
  ABBREV_TAC `cp = UNIONS (pp:(real^2->bool)->bool)` THEN
  SUBGOAL_THEN
   `closed (cp:real^2->bool) /\ G SUBSET cp /\ cp SUBSET {x | &0 <= x$2 /\ x$2 <= &1} /\
    bl SUBSET cp /\ br SUBSET cp`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "cp" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_UNIONS THEN ASM_SIMP_TAC[];
      REWRITE_TAC[SUBSET; IN_UNIONS] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      MP_TAC(SPECL [`n:num`; `x:real^2`] MOI_S3SJ_SQ_COVER) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `moi_s3sj_sq n i j` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "pp" THEN REWRITE_TAC[IN_INSERT] THEN DISJ2_TAC THEN DISJ2_TAC THEN
      USE_THEN "sqsdef" (fun th -> REWRITE_TAC[th]) THEN
      MAP_EVERY EXISTS_TAC [`i:num`; `j:num`] THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[];
      REWRITE_TAC[UNIONS_SUBSET] THEN ASM_SIMP_TAC[];
      EXPAND_TAC "pp" THEN SET_TAC[];
      EXPAND_TAC "pp" THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`cp:real^2->bool`; `G:real^2->bool`] MOI_S3SJ_PLANE_SEP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["bl"; "br"] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`(:real^2)`; `cp:real^2->bool`; `{x:real^2 | x$2 < &0}`;
                 `{x:real^2 | x$2 > &1}`] MOI_S30_302_GEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV; GSYM CLOSED_IN] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONVEX_IMP_SIMPLY_CONNECTED THEN REWRITE_TAC[CONVEX_UNIV];
      MATCH_MP_TAC CONVEX_CONNECTED THEN REWRITE_TAC[CONVEX_HALFSPACE_COMPONENT_LT];
      MATCH_MP_TAC CONVEX_CONNECTED THEN REWRITE_TAC[CONVEX_HALFSPACE_COMPONENT_GT];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      EXISTS_TAC `vector[&0; --(&1)]:real^2` THEN REWRITE_TAC[VECTOR_2] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      EXISTS_TAC `vector[&0; &2]:real^2` THEN REWRITE_TAC[VECTOR_2] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `cp SUBSET {x:real^2 | &0 <= x$2 /\ x$2 <= &1}` THEN
      REWRITE_TAC[SUBSET; DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
      MESON_TAC[REAL_NOT_LE];
      UNDISCH_TAC `cp SUBSET {x:real^2 | &0 <= x$2 /\ x$2 <= &1}` THEN
      REWRITE_TAC[SUBSET; DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY;
                  real_gt] THEN
      MESON_TAC[REAL_NOT_LE];
      EXPAND_TAC "cp" THEN MATCH_MP_TAC MOI_S3SJ_FINITE_COMPONENTS THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^2->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!x:real^2. x IN cp ==> x IN bl \/ x IN br \/ x IN interval[vec 0,vec 1]`
  (LABEL_TAC "cpcase") THENL
   [EXPAND_TAC "cp" THEN EXPAND_TAC "pp" THEN
    REWRITE_TAC[UNIONS_INSERT] THEN REWRITE_TAC[IN_UNION; IN_UNIONS] THEN
    X_GEN_TAC `x:real^2` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN DISJ2_TAC THEN
    USE_THEN "sqf" (fun th -> MP_TAC(MP (SPEC `t:real^2->bool` th)
      (ASSUME `(t:real^2->bool) IN sqs`))) THEN
    STRIP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a. connected {x:real^2 | x$1 = a}` (LABEL_TAC "vline") THENL
   [GEN_TAC THEN MATCH_MP_TAC CONVEX_CONNECTED THEN
    SUBGOAL_THEN `{x:real^2 | x$1 = a} = {x | x$1 <= a} INTER {x | x$1 >= a}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC CONVEX_INTER THEN
    REWRITE_TAC[CONVEX_HALFSPACE_COMPONENT_LE; CONVEX_HALFSPACE_COMPONENT_GE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(bl:real^2->bool) SUBSET d /\ (br:real^2->bool) SUBSET d`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_S3SJ_BAR_IN THEN
    EXISTS_TAC `cp:real^2->bool` THENL
     [MAP_EVERY EXISTS_TAC [`{x:real^2 | x$1 = --(&1)}`; `{x:real^2 | x$2 < &0}`;
                            `{x:real^2 | x$2 > &1}`] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `x:real^2` THEN
        STRIP_TAC THEN
        USE_THEN "cpcase" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:real^2) IN cp`))) THEN
        MAP_EVERY EXPAND_TAC ["bl"; "br"] THEN
        REWRITE_TAC[IN_ELIM_THM; IN_INTERVAL; DIMINDEX_2; FORALL_2; VEC_COMPONENT] THEN
        UNDISCH_TAC `(x:real^2)$1 = --(&1)` THEN REAL_ARITH_TAC;
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM] THEN
        EXISTS_TAC `vector[--(&1); --(&1)]:real^2` THEN REWRITE_TAC[VECTOR_2] THEN
        REAL_ARITH_TAC;
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM] THEN
        EXISTS_TAC `vector[--(&1); &2]:real^2` THEN REWRITE_TAC[VECTOR_2] THEN
        REAL_ARITH_TAC];
      MAP_EVERY EXISTS_TAC [`{x:real^2 | x$1 = &2}`; `{x:real^2 | x$2 < &0}`;
                            `{x:real^2 | x$2 > &1}`] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `x:real^2` THEN
        STRIP_TAC THEN
        USE_THEN "cpcase" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:real^2) IN cp`))) THEN
        MAP_EVERY EXPAND_TAC ["bl"; "br"] THEN
        REWRITE_TAC[IN_ELIM_THM; IN_INTERVAL; DIMINDEX_2; FORALL_2; VEC_COMPONENT] THEN
        UNDISCH_TAC `(x:real^2)$1 = &2` THEN REAL_ARITH_TAC;
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM] THEN
        EXISTS_TAC `vector[&2; --(&1)]:real^2` THEN REWRITE_TAC[VECTOR_2] THEN
        REAL_ARITH_TAC;
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM] THEN
        EXISTS_TAC `vector[&2; &2]:real^2` THEN REWRITE_TAC[VECTOR_2] THEN
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* the good pieces: closure under intersection *)
  SUBGOAL_THEN `(vec 0:real^2) IN G /\ (R:real^2->real^2->bool) (vec 0) (vec 0)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `dist:real^2#real^2->real`)) (concl th))) THEN
    REWRITE_TAC[DIST_REFL] THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y:real^2. x IN G /\ y IN G /\ dist(x,y) <= &4 * inv(&n) ==> R x y`
  (LABEL_TAC "near") THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `dist:real^2#real^2->real`)) (concl th) &&
      not (can (find_term (fun t -> t = `inv(&n)`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p q:real^2->bool.
      p IN pp /\ q IN pp /\ ~(p INTER q = {}) /\
      (?z. z IN p /\ z IN G /\ R (vec 0:real^2) z)
      ==> (?w. w IN q /\ w IN G /\ R (vec 0:real^2) w)`
  (LABEL_TAC "closure") THENL
   [MAP_EVERY X_GEN_TAC [`p:real^2->bool`; `q:real^2->bool`] THEN
    EXPAND_TAC "pp" THEN REWRITE_TAC[IN_INSERT] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC)))) THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN2 SUBST_ALL_TAC (DISJ_CASES_THEN2 SUBST_ALL_TAC
      ASSUME_TAC) o check (fun th -> is_disj(concl th) &&
        free_in `q:real^2->bool` (concl th))) THENL
     [(* q = bl *)
      EXISTS_TAC `vec 0:real^2` THEN ASM_REWRITE_TAC[];
      (* q = br *)
      FIRST_X_ASSUM(DISJ_CASES_THEN2 SUBST_ALL_TAC (DISJ_CASES_THEN2 SUBST_ALL_TAC
        ASSUME_TAC) o check (fun th -> is_disj(concl th) &&
          free_in `p:real^2->bool` (concl th))) THENL
       [UNDISCH_TAC `~(bl INTER br:real^2->bool = {})` THEN
        UNDISCH_TAC `DISJOINT (bl:real^2->bool) br` THEN SET_TAC[];
        EXISTS_TAC `z:real^2` THEN ASM_REWRITE_TAC[];
        USE_THEN "sqf" (fun th -> MP_TAC(MP (SPEC `p:real^2->bool` th)
          (ASSUME `(p:real^2->bool) IN sqs`))) THEN STRIP_TAC THEN
        UNDISCH_TAC `~(p INTER br:real^2->bool = {})` THEN
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
        DISCH_THEN(X_CHOOSE_THEN `m:real^2` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `vector[&1; (z:real^2)$2]:real^2` THEN
        SUBGOAL_THEN `(vector[&1; (z:real^2)$2]:real^2) IN re` ASSUME_TAC THENL
         [EXPAND_TAC "re" THEN REWRITE_TAC[IN_ELIM_THM; VECTOR_2] THEN
          USE_THEN "Gq" (fun th -> MP_TAC(MP (SPEC `z:real^2` th) (ASSUME `(z:real^2) IN G`))) THEN ASM_SIMP_TAC[];
          ALL_TAC] THEN
        REPEAT CONJ_TAC THENL
         [UNDISCH_TAC `(vector[&1; (z:real^2)$2]:real^2) IN re` THEN
          MAP_EVERY EXPAND_TAC ["re"; "br"] THEN REWRITE_TAC[IN_ELIM_THM] THEN
          REAL_ARITH_TAC;
          ASM SET_TAC[];
          FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
            length(fst(strip_forall(concl th))) = 3)) THEN
          EXISTS_TAC `z:real^2` THEN ASM_REWRITE_TAC[] THEN
          USE_THEN "near" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
          CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
          ONCE_REWRITE_TAC[DIST_SYM] THEN
          MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC `abs(&1 - (z:real^2)$1)` THEN REWRITE_TAC[MOI_S3SJ_DIST_EDGE] THEN
          UNDISCH_TAC `(m:real^2) IN br` THEN EXPAND_TAC "br" THEN
          REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
          USE_THEN "Gq" (fun th -> MP_TAC(MP (SPEC `z:real^2` th) (ASSUME `(z:real^2) IN G`))) THEN ASM_REWRITE_TAC[] THEN
          FIRST_X_ASSUM(MP_TAC o SPECL [`z:real^2`; `m:real^2`] o check (fun th ->
            is_forall(concl th) &&
            can (find_term (fun t -> t = `inv(&n)`)) (concl th))) THEN
          ASM_REWRITE_TAC[] THEN
          MP_TAC(SPEC `&n` REAL_LT_INV) THEN ASM_REAL_ARITH_TAC]];
      (* q in sqs *)
      USE_THEN "sqf" (fun th -> MP_TAC(MP (SPEC `q:real^2->bool` th)
        (ASSUME `(q:real^2->bool) IN sqs`))) THEN STRIP_TAC THEN
      UNDISCH_TAC `~(q INTER G:real^2->bool = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      DISCH_THEN(X_CHOOSE_THEN `w:real^2` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `w:real^2` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(p INTER q:real^2->bool = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      DISCH_THEN(X_CHOOSE_THEN `m:real^2` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(DISJ_CASES_THEN2 SUBST_ALL_TAC (DISJ_CASES_THEN2 SUBST_ALL_TAC
        ASSUME_TAC) o check (fun th -> is_disj(concl th) &&
          free_in `p:real^2->bool` (concl th))) THENL
       [(* p = bl *)
        SUBGOAL_THEN `(vector[&0; (w:real^2)$2]:real^2) IN le` ASSUME_TAC THENL
         [EXPAND_TAC "le" THEN REWRITE_TAC[IN_ELIM_THM; VECTOR_2] THEN
          USE_THEN "Gq" (fun th -> MP_TAC(MP (SPEC `w:real^2` th) (ASSUME `(w:real^2) IN G`))) THEN ASM_SIMP_TAC[];
          ALL_TAC] THEN
        FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          length(fst(strip_forall(concl th))) = 3)) THEN
        EXISTS_TAC `vector[&0; (w:real^2)$2]:real^2` THEN CONJ_TAC THENL
         [USE_THEN "lereach" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        USE_THEN "near" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `abs(&0 - (w:real^2)$1)` THEN REWRITE_TAC[MOI_S3SJ_DIST_EDGE] THEN
        UNDISCH_TAC `(m:real^2) IN bl` THEN EXPAND_TAC "bl" THEN
        REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
        USE_THEN "Gq" (fun th -> MP_TAC(MP (SPEC `w:real^2` th) (ASSUME `(w:real^2) IN G`))) THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`w:real^2`; `m:real^2`] o check (fun th ->
          is_forall(concl th) &&
          can (find_term (fun t -> t = `inv(&n)`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN
        MP_TAC(SPEC `&n` REAL_LT_INV) THEN ASM_REAL_ARITH_TAC;
        (* p = br *)
        SUBGOAL_THEN `(z:real^2) IN re /\ (vector[&1; (w:real^2)$2]:real^2) IN re`
        STRIP_ASSUME_TAC THENL
         [EXPAND_TAC "re" THEN REWRITE_TAC[IN_ELIM_THM; VECTOR_2] THEN
          USE_THEN "Gq" (fun th -> MP_TAC(MP (SPEC `z:real^2` th) (ASSUME `(z:real^2) IN G`))) THEN
          USE_THEN "Gq" (fun th -> MP_TAC(MP (SPEC `w:real^2` th) (ASSUME `(w:real^2) IN G`))) THEN ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `(z:real^2) IN br` THEN EXPAND_TAC "br" THEN
          REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC;
          ALL_TAC] THEN
        FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          length(fst(strip_forall(concl th))) = 3)) THEN
        EXISTS_TAC `vector[&1; (w:real^2)$2]:real^2` THEN CONJ_TAC THENL
         [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
            length(fst(strip_forall(concl th))) = 3)) THEN
          EXISTS_TAC `z:real^2` THEN ASM_REWRITE_TAC[] THEN
          USE_THEN "rereach" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        USE_THEN "near" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `abs(&1 - (w:real^2)$1)` THEN REWRITE_TAC[MOI_S3SJ_DIST_EDGE] THEN
        UNDISCH_TAC `(m:real^2) IN br` THEN EXPAND_TAC "br" THEN
        REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
        USE_THEN "Gq" (fun th -> MP_TAC(MP (SPEC `w:real^2` th) (ASSUME `(w:real^2) IN G`))) THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`w:real^2`; `m:real^2`] o check (fun th ->
          is_forall(concl th) &&
          can (find_term (fun t -> t = `inv(&n)`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN
        MP_TAC(SPEC `&n` REAL_LT_INV) THEN ASM_REAL_ARITH_TAC;
        (* p in sqs *)
        USE_THEN "sqf" (fun th -> MP_TAC(MP (SPEC `p:real^2->bool` th)
          (ASSUME `(p:real^2->bool) IN sqs`))) THEN STRIP_TAC THEN
        FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          length(fst(strip_forall(concl th))) = 3)) THEN
        EXISTS_TAC `z:real^2` THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "near" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `dist(z:real^2,m) + dist(m,w)` THEN REWRITE_TAC[DIST_TRIANGLE] THEN
        MATCH_MP_TAC(REAL_ARITH `a <= &2 * e /\ b <= &2 * e ==> a + b <= &4 * e`) THEN
        CONJ_TAC THENL
         [FIRST_X_ASSUM(MP_TAC o SPECL [`z:real^2`; `m:real^2`] o check (fun th ->
            is_forall(concl th) &&
            can (find_term (fun t -> t = `inv(&n)`)) (concl th))) THEN
          ASM_SIMP_TAC[];
          FIRST_X_ASSUM(MP_TAC o SPECL [`m:real^2`; `w:real^2`] o check (fun th ->
            is_forall(concl th) &&
            can (find_term (fun t -> t = `inv(&n)`)) (concl th))) THEN
          ASM_SIMP_TAC[]]]];
    ALL_TAC] THEN
  (* the good part of the separating component is clopen *)
  ABBREV_TAC
   `aa = UNIONS {p:real^2->bool | p IN pp /\ ?z. z IN p /\ z IN G /\ R (vec 0:real^2) z}` THEN
  ABBREV_TAC
   `bb = UNIONS {p:real^2->bool | p IN pp /\ ~(?z. z IN p /\ z IN G /\ R (vec 0:real^2) z)}` THEN
  SUBGOAL_THEN
   `closed (aa:real^2->bool) /\ closed (bb:real^2->bool) /\ DISJOINT aa bb /\
    d SUBSET aa UNION bb`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["aa"; "bb"] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_UNIONS THEN
      ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM];
      MATCH_MP_TAC CLOSED_UNIONS THEN
      ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM];
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_UNIONS;
                  IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^2` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `p:real^2->bool` STRIP_ASSUME_TAC)
        (X_CHOOSE_THEN `q:real^2->bool` STRIP_ASSUME_TAC)) THEN
      UNDISCH_TAC `~(?z:real^2. z IN q /\ z IN G /\ R (vec 0:real^2) z)` THEN
      REWRITE_TAC[] THEN USE_THEN "closure" MATCH_MP_TAC THEN
      EXISTS_TAC `p:real^2->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`(x:real^2) IN p`; `(x:real^2) IN q`] THEN SET_TAC[];
        EXISTS_TAC `z:real^2` THEN ASM_REWRITE_TAC[]];
      MP_TAC(MATCH_MP IN_COMPONENTS_SUBSET (ASSUME `(d:real^2->bool) IN components cp`)) THEN
      EXPAND_TAC "cp" THEN
      REWRITE_TAC[SUBSET; IN_UNION; IN_UNIONS; IN_ELIM_THM] THEN
      DISCH_TAC THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `p:real^2->bool` STRIP_ASSUME_TAC) THEN
      ASM_CASES_TAC `?z:real^2. z IN p /\ z IN G /\ R (vec 0:real^2) z` THENL
       [DISJ1_TAC; DISJ2_TAC] THEN
      EXISTS_TAC `p:real^2->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^2)`; `aa:real^2->bool`; `bb:real^2->bool`; `d:real^2->bool`]
    MOI_S30_CONNECTED_SUBSET_DISJOINT_UNION) THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM CLOSED_IN] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[IN_COMPONENTS_CONNECTED]; ALL_TAC] THEN
  SUBGOAL_THEN `(vec 0:real^2) IN aa` ASSUME_TAC THENL
   [EXPAND_TAC "aa" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `bl:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [EXPAND_TAC "pp" THEN REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
    EXISTS_TAC `vec 0:real^2` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
   [ALL_TAC;
    UNDISCH_TAC `DISJOINT (aa:real^2->bool) bb` THEN
    UNDISCH_TAC `(vec 0:real^2) IN aa` THEN UNDISCH_TAC `(vec 0:real^2) IN bl` THEN
    UNDISCH_TAC `(bl:real^2->bool) SUBSET d` THEN
    UNDISCH_TAC `(d:real^2->bool) SUBSET bb` THEN SET_TAC[]] THEN
  SUBGOAL_THEN `vector[&2; &0] IN (aa:real^2->bool)` MP_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!x:real^2. x IN br /\ br SUBSET d /\ d SUBSET aa ==> x IN aa`) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "br" THEN REWRITE_TAC[IN_ELIM_THM; VECTOR_2] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXPAND_TAC "aa" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^2->bool` (CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC)) MP_TAC)) THEN
  UNDISCH_TAC `(p:real^2->bool) IN pp` THEN
  EXPAND_TAC "pp" THEN REWRITE_TAC[IN_INSERT] THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC (DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC))
  THENL
   [EXPAND_TAC "bl" THEN REWRITE_TAC[IN_ELIM_THM; VECTOR_2] THEN REAL_ARITH_TAC;
    DISCH_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 3)) THEN
    EXISTS_TAC `z:real^2` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "rereach" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "re" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    USE_THEN "Gq" (fun th -> MP_TAC(MP (SPEC `z:real^2` th) (ASSUME `(z:real^2) IN G`))) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(z:real^2) IN br` THEN EXPAND_TAC "br" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC;
    USE_THEN "sqf" (fun th -> MP_TAC(MP (SPEC `p:real^2->bool` th)
      (ASSUME `(p:real^2->bool) IN sqs`))) THEN STRIP_TAC THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `vector[&2; &0] IN interval[vec 0:real^2,vec 1]` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VEC_COMPONENT; VECTOR_2] THEN
    REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Part 5: SQUARE.  A map psi of the unit square into the open set W,       *)
(* constant x0 IN S on the left and right edges, with the bottom edge in    *)
(* O1 UNION S and the top edge in O2 UNION S (W DIFF S inside O1 UNION O2,  *)
(* O1, O2 disjoint open): the bottom loop is homotopic in W to a loop in S. *)
(* The relation R a b (a path in S from psi a to psi b homotopic in W to    *)
(* psi o linepath(a,b)) is transitive and holds between close points of     *)
(* the preimage of S (uniform continuity, uniform local path connectivity   *)
(* of S, convex balls inside W), so CHAIN applies.                           *)
(* ========================================================================= *)

let MOI_S3SJ_SQUARE = prove
 (`!(W:real^3->bool) S O1 O2 (psi:real^2->real^3) x0.
     open W /\ compact S /\ S SUBSET W /\
     (!e. &0 < e
          ==> ?d. &0 < d /\
                  !x y. x IN S /\ y IN S /\ dist(x,y) < d
                        ==> ?p. path p /\ path_image p SUBSET S /\
                                path_image p SUBSET ball(x,e) /\
                                pathstart p = x /\ pathfinish p = y) /\
     open O1 /\ open O2 /\ DISJOINT O1 O2 /\ W DIFF S SUBSET O1 UNION O2 /\
     psi continuous_on interval[vec 0,vec 1] /\
     IMAGE psi (interval[vec 0,vec 1]) SUBSET W /\ x0 IN S /\
     (!u. &0 <= u /\ u <= &1 ==> psi(vector[&0;u]) = x0 /\ psi(vector[&1;u]) = x0) /\
     (!s. &0 <= s /\ s <= &1 ==> psi(vector[s;&0]) IN O1 UNION S) /\
     (!s. &0 <= s /\ s <= &1 ==> psi(vector[s;&1]) IN O2 UNION S)
     ==> ?q. path q /\ path_image q SUBSET S /\ pathstart q = x0 /\ pathfinish q = x0 /\
             homotopic_paths W (\t. psi(vector[drop t;&0])) q`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "ulpc")
      STRIP_ASSUME_TAC)))) THEN
  ABBREV_TAC `Q = interval[vec 0:real^2,vec 1]` THEN
  SUBGOAL_THEN
   `!s u. &0 <= s /\ s <= &1 /\ &0 <= u /\ u <= &1 ==> vector[s;u] IN (Q:real^2->bool)`
  (LABEL_TAC "inq") THENL
   [EXPAND_TAC "Q" THEN
    REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2; VEC_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^2. z IN Q ==> z = vector[z$1; z$2] /\ &0 <= z$1 /\ z$1 <= &1 /\
                         &0 <= z$2 /\ z$2 <= &1`
  (LABEL_TAC "qco") THENL
   [EXPAND_TAC "Q" THEN
    REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VEC_COMPONENT; CART_EQ; VECTOR_2] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex (Q:real^2->bool) /\ compact Q /\ closed Q` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN REWRITE_TAC[CONVEX_INTERVAL; COMPACT_INTERVAL; CLOSED_INTERVAL];
    ALL_TAC] THEN
  (* a margin of W around psi(Q) *)
  MP_TAC(ISPEC `IMAGE (psi:real^2->real^3) Q` HEINE_BOREL_LEMMA) THEN ANTS_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `{W:real^3->bool}`) THEN
  REWRITE_TAC[UNIONS_1; IN_SING; UNWIND_THM2; FORALL_UNWIND_THM2] THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC) THEN
  USE_THEN "ulpc" (MP_TAC o SPEC `rho / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "short"))) THEN
  MP_TAC(ISPECL [`psi:real^2->real^3`; `Q:real^2->bool`] COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ASM_REWRITE_TAC[uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `min d (rho / &2)`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "uc"))) THEN
  (* the chain lemma *)
  MP_TAC(ISPECL
   [`{z:real^2 | z IN Q /\ (psi:real^2->real^3) z IN S}`;
    `\a b:real^2. a IN Q /\ b IN Q /\
                  ?p. path p /\ path_image p SUBSET S /\
                      pathstart p = (psi:real^2->real^3) a /\ pathfinish p = psi b /\
                      homotopic_paths W (psi o linepath(a,b)) p`;
    `eta:real`] MOI_S3SJ_CHAIN) THEN
  REWRITE_TAC[] THEN REWRITE_TAC[ASSUME `interval[vec 0:real^2,vec 1] = Q`] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_RESTRICT] THEN REPEAT CONJ_TAC THENL
     [(* closed *)
      MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
      (* edges *)
      X_GEN_TAC `u:real` THEN STRIP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
      REPEAT CONJ_TAC THEN TRY(USE_THEN "inq" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `u:real` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `x0:real^3`)) (concl th))) THEN
      ASM_SIMP_TAC[];
      (* no crossing *)
      REWRITE_TAC[NOT_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`c:real^2->bool`; `a:real^2`; `b:real^2`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(c:real^2->bool) SUBSET Q` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`IMAGE (psi:real^2->real^3) c`; `O1:real^3->bool`; `O2:real^3->bool`]
        MOI_S3SJ_CONNECTED_OPEN_SPLIT) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `Q:real^2->bool` THEN
          ASM_REWRITE_TAC[];
          REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^2` THEN
          DISCH_TAC THEN
          SUBGOAL_THEN `(psi:real^2->real^3) z IN W DIFF S` MP_TAC THENL
           [REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
            UNDISCH_TAC `(c:real^2->bool) SUBSET Q DIFF {z:real^2 | z IN Q /\ (psi:real^2->real^3) z IN S}` THEN
            UNDISCH_TAC `(z:real^2) IN c` THEN SET_TAC[];
            ASM SET_TAC[]]];
        ALL_TAC] THEN
      SUBGOAL_THEN `(psi:real^2->real^3) a IN O1 /\ (psi:real^2->real^3) b IN O2`
      MP_TAC THENL
       [CONJ_TAC THENL
         [SUBGOAL_THEN `(a:real^2) IN Q /\ ~((psi:real^2->real^3) a IN S)` STRIP_ASSUME_TAC
          THENL [ASM SET_TAC[]; ALL_TAC] THEN
          USE_THEN "qco" (MP_TAC o C MATCH_MP (ASSUME `(a:real^2) IN Q`)) THEN
          ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
          FIRST_X_ASSUM(MP_TAC o SPEC `(a:real^2)$1` o check (fun th ->
            is_forall(concl th) && can (find_term (fun t -> t = `O1:real^3->bool`)) (concl th) &&
            not (can (find_term (fun t -> t = `O2:real^3->bool`)) (concl th)))) THEN
          ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `(a:real^2) = vector[a$1; &0]` THEN
          DISCH_THEN(fun th -> REWRITE_TAC[SYM th]) THEN
          ASM SET_TAC[];
          SUBGOAL_THEN `(b:real^2) IN Q /\ ~((psi:real^2->real^3) b IN S)` STRIP_ASSUME_TAC
          THENL [ASM SET_TAC[]; ALL_TAC] THEN
          USE_THEN "qco" (MP_TAC o C MATCH_MP (ASSUME `(b:real^2) IN Q`)) THEN
          ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
          FIRST_X_ASSUM(MP_TAC o SPEC `(b:real^2)$1` o check (fun th ->
            is_forall(concl th) && can (find_term (fun t -> t = `O2:real^3->bool`)) (concl th) &&
            not (can (find_term (fun t -> t = `O1:real^3->bool`)) (concl th)))) THEN
          ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `(b:real^2) = vector[b$1; &1]` THEN
          DISCH_THEN(fun th -> REWRITE_TAC[SYM th]) THEN
          ASM SET_TAC[]];
        ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC [`DISJOINT (O1:real^3->bool) O2`; `(a:real^2) IN c`;
                             `(b:real^2) IN c`] THEN
      SET_TAC[];
      (* close points *)
      MAP_EVERY X_GEN_TAC [`a:real^2`; `b:real^2`] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "short" (MP_TAC o SPECL [`(psi:real^2->real^3) a`; `(psi:real^2->real^3) b`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
        MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `min d (rho / &2)` THEN
        CONJ_TAC THENL
         [USE_THEN "uc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
          ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
          REAL_ARITH_TAC];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `p:real^1->real^3` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `p:real^1->real^3` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `segment[a:real^2,b] SUBSET Q` ASSUME_TAC THENL
       [MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MOI_S3SJ_CONVEX_HOMOT THEN
      EXISTS_TAC `ball((psi:real^2->real^3) a,rho / &2)` THEN
      ASM_REWRITE_TAC[CONVEX_BALL; PATHSTART_COMPOSE; PATHFINISH_COMPOSE;
                      PATHSTART_LINEPATH; PATHFINISH_LINEPATH; PATH_IMAGE_COMPOSE;
                      PATH_IMAGE_LINEPATH] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN
        REWRITE_TAC[PATH_LINEPATH; PATH_IMAGE_LINEPATH] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `Q:real^2->bool` THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball((psi:real^2->real^3) a,rho)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_BALL] THEN
        X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
        MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `min d (rho / &2)` THEN
        CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
        ONCE_REWRITE_TAC[DIST_SYM] THEN
        USE_THEN "uc" MATCH_MP_TAC THEN
        CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `dist(a:real^2,b)` THEN
        ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`a:real^2`; `b:real^2`; `z:real^2`] DIST_IN_CLOSED_SEGMENT) THEN
        ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN SIMP_TAC[]];
      (* transitivity *)
      MAP_EVERY X_GEN_TAC [`a:real^2`; `b:real^2`; `c:real^2`] THEN
      DISCH_THEN(CONJUNCTS_THEN2
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
          (X_CHOOSE_THEN `p1:real^1->real^3` STRIP_ASSUME_TAC)))
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
          (X_CHOOSE_THEN `p2:real^1->real^3` STRIP_ASSUME_TAC)))) THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `(p1:real^1->real^3) ++ p2` THEN
      ASM_SIMP_TAC[PATH_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `path_image (p1:real^1->real^3) UNION path_image p2` THEN
        ASM_SIMP_TAC[PATH_IMAGE_JOIN_SUBSET; UNION_SUBSET];
        ALL_TAC] THEN
      MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
      EXISTS_TAC `(psi:real^2->real^3) o (linepath(a,b) ++ linepath(b,c))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC HOMOTOPIC_PATHS_CONTINUOUS_IMAGE THEN
        EXISTS_TAC `Q:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC MOI_S3SJ_CONVEX_HOMOT THEN EXISTS_TAC `Q:real^2->bool` THEN
        ASM_REWRITE_TAC[SUBSET_REFL] THEN
        SIMP_TAC[PATH_JOIN; PATH_LINEPATH; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                 PATHSTART_JOIN; PATHFINISH_JOIN; PATH_IMAGE_LINEPATH] THEN
        SUBGOAL_THEN `segment[a:real^2,b] SUBSET Q /\ segment[b,c] SUBSET Q /\
                      segment[a,c] SUBSET Q` STRIP_ASSUME_TAC THENL
         [REPEAT CONJ_TAC THEN MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `path_image(linepath(a:real^2,b)) UNION path_image(linepath(b,c))` THEN
        SIMP_TAC[PATH_IMAGE_JOIN_SUBSET; PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
        ASM_REWRITE_TAC[PATH_IMAGE_LINEPATH; UNION_SUBSET];
        REWRITE_TAC[PATH_COMPOSE_JOIN] THEN MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
        ASM_REWRITE_TAC[PATHFINISH_COMPOSE; PATHSTART_COMPOSE; PATHSTART_LINEPATH;
                        PATHFINISH_LINEPATH]]];
    ALL_TAC] THEN
  STRIP_TAC THEN
  EXISTS_TAC `p:real^1->real^3` THEN
  SUBGOAL_THEN `(psi:real^2->real^3) (vec 0) = x0 /\ psi(vector[&1;&0]) = x0`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `&0` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `x0:real^3`)) (concl th))) THEN
    REWRITE_TAC[REAL_LE_REFL; REAL_POS] THEN
    SUBGOAL_THEN `vector[&0;&0]:real^2 = vec 0` (fun th -> SIMP_TAC[th]) THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VEC_COMPONENT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(\t. (psi:real^2->real^3)(vector[drop t;&0])) = psi o linepath(vec 0,vector[&1;&0])`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; linepath] THEN X_GEN_TAC `t:real^1` THEN
    AP_TERM_TAC THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VEC_COMPONENT;
                VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    REAL_ARITH_TAC;
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Part 6: the side lemmas.  W carries a product chart: a homeomorphism      *)
(* (f,g) from D PCROSS (0,1) onto W; the height of z IN W is sndcart(g z).  *)
(* SIDE_LOOP: if every point of W at the height of xs IN S lies in          *)
(* O' UNION S, then every loop at xs in O UNION S is homotopic in W to a    *)
(* loop in S (push the loop vertically to the height of xs and apply        *)
(* SQUARE).  CONJ: path algebra for conjugating by two paths.  SIDE_PATH:  *)
(* with S path connected, every path in O UNION S between points of S is    *)
(* homotopic in W, with fixed ends, to a path in S.                          *)
(* ========================================================================= *)

let MOI_S3SJ_SIDE_LOOP = prove
 (`!(W:real^3->bool) S O O' (D:real^3->bool) (f:real^(3,1)finite_sum->real^3) g xs.
     homeomorphism (D PCROSS {x:real^1 | &0 < drop x /\ drop x < &1},W) (f,g) /\
     open W /\ compact S /\ S SUBSET W /\
     (!e. &0 < e
          ==> ?d. &0 < d /\
                  !x y. x IN S /\ y IN S /\ dist(x,y) < d
                        ==> ?p. path p /\ path_image p SUBSET S /\
                                path_image p SUBSET ball(x,e) /\
                                pathstart p = x /\ pathfinish p = y) /\
     open O /\ open O' /\ DISJOINT O O' /\ W DIFF S SUBSET O UNION O' /\
     xs IN S /\
     (!z. z IN W /\ sndcart(g z) = sndcart(g xs) ==> z IN O' UNION S)
     ==> !gm. path gm /\ path_image gm SUBSET W /\ path_image gm SUBSET O UNION S /\
              pathstart gm = xs /\ pathfinish gm = xs
              ==> ?q. path q /\ path_image q SUBSET S /\ pathstart q = xs /\
                      pathfinish q = xs /\ homotopic_paths W gm q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `gm:real^1->real^3` THEN STRIP_TAC THEN
  UNDISCH_TAC `!z. z IN W /\ sndcart((g:real^3->real^(3,1)finite_sum) z) = sndcart(g xs)
                   ==> z IN O' UNION S` THEN
  DISCH_THEN(LABEL_TAC "lev") THEN
  ABBREV_TAC `I0 = {x:real^1 | &0 < drop x /\ drop x < &1}` THEN
  SUBGOAL_THEN `convex(I0:real^1->bool)` (LABEL_TAC "cvx") THENL
   [SUBGOAL_THEN `I0 = interval(vec 0:real^1,vec 1)` SUBST1_TAC THENL
     [EXPAND_TAC "I0" THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTERVAL_1; DROP_VEC];
      REWRITE_TAC[CONVEX_INTERVAL]];
    ALL_TAC] THEN
  UNDISCH_TAC `homeomorphism ((D:real^3->bool) PCROSS I0,(W:real^3->bool))
                 (f:real^(3,1)finite_sum->real^3,g)` THEN
  REWRITE_TAC[homeomorphism] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "gf") (CONJUNCTS_THEN2 (LABEL_TAC "fim")
    (CONJUNCTS_THEN2 (LABEL_TAC "fco") (CONJUNCTS_THEN2 (LABEL_TAC "fg")
      (CONJUNCTS_THEN2 (LABEL_TAC "gim") (LABEL_TAC "gcont")))))) THEN
  SUBGOAL_THEN `(xs:real^3) IN W` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!w:real^3. w IN W ==> fstcart((g:real^3->real^(3,1)finite_sum) w) IN D /\ sndcart(g w) IN I0`
  (LABEL_TAC "gco") THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(g:real^3->real^(3,1)finite_sum) w IN D PCROSS I0` MP_TAC THENL
     [USE_THEN "gim" (fun th -> REWRITE_TAC[GSYM th]) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM PASTECART_FST_SND] THEN
    REWRITE_TAC[PASTECART_IN_PCROSS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. &0 <= s /\ s <= &1 ==> (gm:real^1->real^3)(lift s) IN W /\ gm(lift s) IN O UNION S`
  (LABEL_TAC "gmw") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(gm:real^1->real^3)(lift s) IN path_image gm` MP_TAC THENL
     [REWRITE_TAC[path_image] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gm:real^1->real^3)(vec 0) = xs /\ gm(vec 1) = xs` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[pathstart; pathfinish]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^(3,1)finite_sum->real^3)(g(xs:real^3)) = xs` ASSUME_TAC THENL
   [USE_THEN "fg" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the vertical push H and the square map psi = f o H *)
  SUBGOAL_THEN
   `?H:real^2->real^(3,1)finite_sum.
      !z. H z = pastecart (fstcart((g:real^3->real^(3,1)finite_sum)
                                    ((gm:real^1->real^3)(lift(z$1)))))
                          ((&1 - z$2) % sndcart(g(gm(lift(z$1)))) +
                           z$2 % sndcart(g(xs:real^3)))`
  (X_CHOOSE_THEN `H:real^2->real^(3,1)finite_sum` (LABEL_TAC "Hdef")) THENL
   [EXISTS_TAC `\z:real^2. pastecart (fstcart((g:real^3->real^(3,1)finite_sum)
                                       ((gm:real^1->real^3)(lift(z$1)))))
                  ((&1 - z$2) % sndcart(g(gm(lift(z$1)))) + z$2 % sndcart(g(xs:real^3)))` THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^2. z IN interval[vec 0,vec 1] ==> (H:real^2->real^(3,1)finite_sum) z IN D PCROSS I0`
  (LABEL_TAC "hin") THENL
   [X_GEN_TAC `z:real^2` THEN REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VEC_COMPONENT] THEN
    STRIP_TAC THEN USE_THEN "Hdef" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[PASTECART_IN_PCROSS] THEN
    USE_THEN "gmw" (MP_TAC o SPEC `(z:real^2)$1`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "gco" (MP_TAC o C MATCH_MP (ASSUME `(xs:real^3) IN W`)) THEN
    USE_THEN "gco" (MP_TAC o C MATCH_MP
      (ASSUME `(gm:real^1->real^3)(lift((z:real^2)$1)) IN W`)) THEN
    STRIP_TAC THEN STRIP_TAC THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "cvx" (MP_TAC o REWRITE_RULE[convex]) THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(H:real^2->real^(3,1)finite_sum) continuous_on interval[vec 0,vec 1]`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\z:real^2. (g:real^3->real^(3,1)finite_sum)((gm:real^1->real^3)(lift(z$1))))
      continuous_on interval[vec 0,vec 1]`
    ASSUME_TAC THENL
     [SUBGOAL_THEN
       `(\z:real^2. (g:real^3->real^(3,1)finite_sum)((gm:real^1->real^3)(lift(z$1)))) =
        g o gm o (\z:real^2. lift(z$1))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT THEN REWRITE_TAC[DIMINDEX_2] THEN ARITH_TAC;
          MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
          CONJ_TAC THENL [ASM_MESON_TAC[path]; ALL_TAC] THEN
          REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL; DIMINDEX_2; FORALL_2;
                      VEC_COMPONENT; IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
          SIMP_TAC[]];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `W:real^3->bool` THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM; IN_INTERVAL; DIMINDEX_2; FORALL_2;
                    VEC_COMPONENT] THEN
        X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
        USE_THEN "gmw" (MP_TAC o SPEC `(z:real^2)$1`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `H = (\z:real^2. pastecart (fstcart((g:real^3->real^(3,1)finite_sum)
                                         ((gm:real^1->real^3)(lift(z$1)))))
                ((&1 - z$2) % sndcart(g(gm(lift(z$1)))) + z$2 % sndcart(g(xs:real^3))))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN USE_THEN "Hdef" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_FSTCART THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
      MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
       [REWRITE_TAC[o_DEF; LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
        REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
        MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT THEN REWRITE_TAC[DIMINDEX_2] THEN ARITH_TAC;
        MATCH_MP_TAC CONTINUOUS_ON_SNDCART THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[o_DEF] THEN
        MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT THEN REWRITE_TAC[DIMINDEX_2] THEN ARITH_TAC;
        REWRITE_TAC[CONTINUOUS_ON_CONST]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?psi:real^2->real^3. !z. psi z = (f:real^(3,1)finite_sum->real^3)(H z)`
  (X_CHOOSE_THEN `psi:real^2->real^3` (LABEL_TAC "psidef")) THENL
   [EXISTS_TAC `\z:real^2. (f:real^(3,1)finite_sum->real^3)(H z)` THEN REWRITE_TAC[];
    ALL_TAC] THEN
  (* the five square facts *)
  SUBGOAL_THEN `(psi:real^2->real^3) continuous_on interval[vec 0,vec 1]` ASSUME_TAC THENL
   [SUBGOAL_THEN `psi = (f:real^(3,1)finite_sum->real^3) o (H:real^2->real^(3,1)finite_sum)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN USE_THEN "psidef" (fun th -> REWRITE_TAC[th]);
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(D:real^3->bool) PCROSS (I0:real^1->bool)` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    USE_THEN "hin" ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (psi:real^2->real^3) (interval[vec 0,vec 1]) SUBSET W` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    USE_THEN "psidef" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "fim" (fun th -> REWRITE_TAC[GSYM th]) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    USE_THEN "hin" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. &0 <= u /\ u <= &1
        ==> (psi:real^2->real^3)(vector[&0;u]) = xs /\ psi(vector[&1;u]) = xs`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:real` THEN STRIP_TAC THEN
    USE_THEN "psidef" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "Hdef" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[VECTOR_2; LIFT_NUM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VECTOR_ARITH `(&1 - u) % a + u % a:real^1 = a`; PASTECART_FST_SND] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. &0 <= s /\ s <= &1 ==> (psi:real^2->real^3)(vector[s;&0]) IN O UNION S`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "psidef" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "Hdef" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[VECTOR_2; REAL_SUB_RZERO; VECTOR_MUL_LID; VECTOR_MUL_LZERO;
                VECTOR_ADD_RID; PASTECART_FST_SND] THEN
    USE_THEN "gmw" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `(f:real^(3,1)finite_sum->real^3)(g((gm:real^1->real^3)(lift s))) = gm(lift s)`
    SUBST1_TAC THENL [USE_THEN "fg" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. &0 <= s /\ s <= &1 ==> (psi:real^2->real^3)(vector[s;&1]) IN O' UNION S`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "psidef" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "Hdef" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[VECTOR_2; REAL_SUB_REFL; VECTOR_MUL_LZERO; VECTOR_ADD_LID; VECTOR_MUL_LID] THEN
    USE_THEN "gmw" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ABBREV_TAC `y = pastecart (fstcart((g:real^3->real^(3,1)finite_sum)
                                        ((gm:real^1->real^3)(lift s))))
                              (sndcart(g(xs:real^3)))` THEN
    SUBGOAL_THEN `(y:real^(3,1)finite_sum) IN D PCROSS I0` ASSUME_TAC THENL
     [EXPAND_TAC "y" THEN REWRITE_TAC[PASTECART_IN_PCROSS] THEN
      USE_THEN "gco" (MP_TAC o C MATCH_MP (ASSUME `(xs:real^3) IN W`)) THEN
      USE_THEN "gco" (MP_TAC o C MATCH_MP
        (ASSUME `(gm:real^1->real^3)(lift s) IN W`)) THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    USE_THEN "lev" MATCH_MP_TAC THEN CONJ_TAC THENL
     [USE_THEN "fim" (fun th -> REWRITE_TAC[GSYM th]) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN `(g:real^3->real^(3,1)finite_sum)(f(y:real^(3,1)finite_sum)) = y`
      SUBST1_TAC THENL [USE_THEN "gf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "y" THEN REWRITE_TAC[SNDCART_PASTECART]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`W:real^3->bool`; `S:real^3->bool`; `O:real^3->bool`; `O':real^3->bool`;
                 `psi:real^2->real^3`; `xs:real^3`] MOI_S3SJ_SQUARE) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^1->real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `q:real^1->real^3` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
  EXISTS_TAC `\t. (psi:real^2->real^3)(vector[drop t;&0])` THEN
  CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_EQ THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  USE_THEN "psidef" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "Hdef" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[VECTOR_2; LIFT_DROP; REAL_SUB_RZERO; VECTOR_MUL_LID; VECTOR_MUL_LZERO;
              VECTOR_ADD_RID; PASTECART_FST_SND] THEN
  CONV_TAC SYM_CONV THEN USE_THEN "fg" MATCH_MP_TAC THEN
  UNDISCH_TAC `path_image (gm:real^1->real^3) SUBSET W` THEN
  REWRITE_TAC[path_image; SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* Conjugation: if c1 ++ r ++ c2 is homotopic to q0, then r is homotopic to *)
(* reversepath c1 ++ q0 ++ reversepath c2.                                   *)

let MOI_S3SJ_CONJ = prove
 (`!s (r:real^1->real^N) c1 c2 q0.
     path r /\ path_image r SUBSET s /\ path c1 /\ path_image c1 SUBSET s /\
     path c2 /\ path_image c2 SUBSET s /\
     pathfinish c1 = pathstart r /\ pathfinish r = pathstart c2 /\
     homotopic_paths s (c1 ++ (r ++ c2)) q0
     ==> homotopic_paths s r (reversepath c1 ++ (q0 ++ reversepath c2))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `path(reversepath(c1:real^1->real^N)) /\ path_image(reversepath c1) SUBSET s /\
                path(reversepath(c2:real^1->real^N)) /\ path_image(reversepath c2) SUBSET s`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[PATH_REVERSEPATH; PATH_IMAGE_REVERSEPATH]; ALL_TAC] THEN
  SUBGOAL_THEN `path((c1:real^1->real^N) ++ r) /\ path_image(c1 ++ r) SUBSET s`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; UNION_SUBSET]; ALL_TAC] THEN
  (* step 1: r ~ reversepath c1 ++ (c1 ++ r) *)
  SUBGOAL_THEN `homotopic_paths s (r:real^1->real^N) (reversepath c1 ++ (c1 ++ r))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
    EXISTS_TAC `(reversepath(c1:real^1->real^N) ++ c1) ++ r` THEN CONJ_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
      EXISTS_TAC `linepath(pathstart r,pathstart r) ++ (r:real^1->real^N)` THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN MATCH_MP_TAC HOMOTOPIC_PATHS_LID THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
        ASM_REWRITE_TAC[PATHFINISH_LINEPATH; HOMOTOPIC_PATHS_REFL] THEN
        ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN
        MP_TAC(ISPECL [`s:real^N->bool`; `c1:real^1->real^N`] HOMOTOPIC_PATHS_LINV) THEN
        ASM_REWRITE_TAC[]];
      ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN MATCH_MP_TAC HOMOTOPIC_PATHS_ASSOC THEN
      ASM_REWRITE_TAC[PATHFINISH_REVERSEPATH]];
    ALL_TAC] THEN
  (* step 2: c1 ++ r ~ q0 ++ reversepath c2 *)
  SUBGOAL_THEN `homotopic_paths s ((c1:real^1->real^N) ++ r) (q0 ++ reversepath c2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
    EXISTS_TAC `((c1:real^1->real^N) ++ r) ++ (c2 ++ reversepath c2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
      EXISTS_TAC `((c1:real^1->real^N) ++ r) ++ linepath(pathfinish r,pathfinish r)` THEN
      CONJ_TAC THENL
       [ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN
        MP_TAC(ISPECL [`s:real^N->bool`; `(c1:real^1->real^N) ++ r`] HOMOTOPIC_PATHS_RID) THEN
        ASM_REWRITE_TAC[PATHFINISH_JOIN];
        MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
        ASM_REWRITE_TAC[PATHFINISH_JOIN; PATHSTART_LINEPATH; HOMOTOPIC_PATHS_REFL] THEN
        ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN
        MP_TAC(ISPECL [`s:real^N->bool`; `c2:real^1->real^N`] HOMOTOPIC_PATHS_RINV) THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
    EXISTS_TAC `(((c1:real^1->real^N) ++ r) ++ c2) ++ reversepath c2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_PATHS_ASSOC THEN
      ASM_REWRITE_TAC[PATHFINISH_JOIN; PATHSTART_REVERSEPATH];
      MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
      ASM_REWRITE_TAC[PATHFINISH_JOIN; PATHSTART_REVERSEPATH; HOMOTOPIC_PATHS_REFL] THEN
      MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
      EXISTS_TAC `(c1:real^1->real^N) ++ (r ++ c2)` THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN MATCH_MP_TAC HOMOTOPIC_PATHS_ASSOC THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
  EXISTS_TAC `reversepath(c1:real^1->real^N) ++ (c1 ++ r)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
  ASM_REWRITE_TAC[HOMOTOPIC_PATHS_REFL; PATHFINISH_REVERSEPATH; PATHSTART_JOIN]);;

let MOI_S3SJ_SIDE_PATH = prove
 (`!(W:real^3->bool) S O O' (D:real^3->bool) (f:real^(3,1)finite_sum->real^3) g xs.
     homeomorphism (D PCROSS {x:real^1 | &0 < drop x /\ drop x < &1},W) (f,g) /\
     open W /\ compact S /\ S SUBSET W /\
     (!e. &0 < e
          ==> ?d. &0 < d /\
                  !x y. x IN S /\ y IN S /\ dist(x,y) < d
                        ==> ?p. path p /\ path_image p SUBSET S /\
                                path_image p SUBSET ball(x,e) /\
                                pathstart p = x /\ pathfinish p = y) /\
     path_connected S /\
     open O /\ open O' /\ DISJOINT O O' /\ W DIFF S SUBSET O UNION O' /\
     xs IN S /\
     (!z. z IN W /\ sndcart(g z) = sndcart(g xs) ==> z IN O' UNION S)
     ==> !r. path r /\ path_image r SUBSET W /\ path_image r SUBSET O UNION S /\
             pathstart r IN S /\ pathfinish r IN S
             ==> ?q. path q /\ path_image q SUBSET S /\ pathstart q = pathstart r /\
                     pathfinish q = pathfinish r /\ homotopic_paths W r q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `r:real^1->real^3` THEN STRIP_TAC THEN
  UNDISCH_TAC `path_connected (S:real^3->bool)` THEN REWRITE_TAC[path_connected] THEN
  DISCH_THEN(LABEL_TAC "pc") THEN
  USE_THEN "pc" (MP_TAC o SPECL [`xs:real^3`; `pathstart(r:real^1->real^3)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:real^1->real^3` STRIP_ASSUME_TAC) THEN
  USE_THEN "pc" (MP_TAC o SPECL [`pathfinish(r:real^1->real^3)`; `xs:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c2:real^1->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `path_image (c1:real^1->real^3) SUBSET W /\ path_image (c2:real^1->real^3) SUBSET W`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`W:real^3->bool`; `S:real^3->bool`; `O:real^3->bool`; `O':real^3->bool`;
                 `D:real^3->bool`; `f:real^(3,1)finite_sum->real^3`;
                 `g:real^3->real^(3,1)finite_sum`; `xs:real^3`] MOI_S3SJ_SIDE_LOOP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `(c1:real^1->real^3) ++ (r ++ c2)`) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN; UNION_SUBSET] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q0:real^1->real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `reversepath(c1:real^1->real^3) ++ (q0 ++ reversepath c2)` THEN
  ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN; UNION_SUBSET;
               PATH_REVERSEPATH; PATH_IMAGE_REVERSEPATH; PATHSTART_REVERSEPATH;
               PATHFINISH_REVERSEPATH] THEN
  MATCH_MP_TAC MOI_S3SJ_CONJ THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Part 7: the decomposition.  INTERVAL_INDUCT: a set gs of good times       *)
(* inside a closed set ts of [0,1] (containing 1), with 0 good, closed under *)
(* short steps inside ts and under jumps over gaps of ts, contains 1.        *)
(* DECOMP: if paths in Oi UNION S between points of S are homotopic in W to  *)
(* paths in S (i = 1, 2), then so is every path of W between points of S    *)
(* (good time t: the initial piece of the path up to t is homotopic to a     *)
(* path in S; short steps by uniform continuity, uniform local path          *)
(* connectivity of S and convex balls in W; jumps are excursions into one    *)
(* side).                                                                     *)
(* ========================================================================= *)

let MOI_S3SJ_INTERVAL_INDUCT = prove
 (`!(ts:real^1->bool) gs m.
     closed ts /\ ts SUBSET interval[vec 0,vec 1] /\ vec 1 IN ts /\ gs SUBSET ts /\
     vec 0 IN gs /\ &0 < m /\
     (!u v. u IN gs /\ v IN ts /\ drop u <= drop v /\ drop v < drop u + m ==> v IN gs) /\
     (!u v. u IN gs /\ v IN ts /\ drop u < drop v /\
            (!w. drop u < drop w /\ drop w < drop v ==> ~(w IN ts))
            ==> v IN gs)
     ==> vec 1 IN gs`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "near") (LABEL_TAC "jump")))))))) THEN
  MP_TAC(ISPEC `closure gs:real^1->bool` MOI_S3SJ_COMPACT_MAX_MIN) THEN ANTS_TAC THENL
   [REWRITE_TAC[COMPACT_CLOSURE; CLOSURE_EQ_EMPTY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
      REWRITE_TAC[BOUNDED_INTERVAL] THEN ASM SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^1` STRIP_ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `closure gs SUBSET (ts:real^1->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^1) IN ts` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!t:real^1. t IN gs ==> drop t <= drop s` ASSUME_TAC THENL
   [X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(ISPEC `gs:real^1->bool` CLOSURE_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^1) IN gs` ASSUME_TAC THENL
   [UNDISCH_TAC `(s:real^1) IN closure gs` THEN REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
    DISCH_THEN(MP_TAC o SPEC `m:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^1` STRIP_ASSUME_TAC) THEN
    USE_THEN "near" MATCH_MP_TAC THEN EXISTS_TAC `y:real^1` THEN ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `dist(y:real^1,s) < m` THEN REWRITE_TAC[DIST_REAL; GSYM drop] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `drop s <= &1` ASSUME_TAC THENL
   [UNDISCH_TAC `(s:real^1) IN ts` THEN UNDISCH_TAC `ts SUBSET interval[vec 0:real^1,vec 1]` THEN
    REWRITE_TAC[SUBSET; IN_INTERVAL_1; DROP_VEC] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(drop s < &1)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    ASM_CASES_TAC `?v:real^1. v IN ts /\ drop s < drop v /\ drop v < drop s + m` THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `v:real^1` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(v:real^1) IN gs` ASSUME_TAC THENL
       [USE_THEN "near" MATCH_MP_TAC THEN EXISTS_TAC `s:real^1` THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `drop v <= drop s` MP_TAC THENL [ASM_SIMP_TAC[]; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ABBREV_TAC `ts' = (ts:real^1->bool) INTER interval[lift(drop s + m),vec 1]` THEN
    MP_TAC(ISPEC `ts':real^1->bool` MOI_S3SJ_COMPACT_MAX_MIN) THEN ANTS_TAC THENL
     [EXPAND_TAC "ts'" THEN CONJ_TAC THENL
       [MATCH_MP_TAC CLOSED_INTER_COMPACT THEN ASM_REWRITE_TAC[COMPACT_INTERVAL];
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `vec 1:real^1` THEN
        ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC; REAL_LE_REFL] THEN
        UNDISCH_TAC `~(?v:real^1. v IN ts /\ drop s < drop v /\ drop v < drop s + m)` THEN
        REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_THEN(MP_TAC o SPEC `vec 1:real^1`) THEN
        ASM_REWRITE_TAC[DROP_VEC] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC o CONJUNCT2) THEN
    SUBGOAL_THEN `(t:real^1) IN ts /\ drop s + m <= drop t` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(t:real^1) IN ts'` THEN EXPAND_TAC "ts'" THEN
      REWRITE_TAC[IN_INTER; IN_INTERVAL_1; LIFT_DROP] THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(t:real^1) IN gs` ASSUME_TAC THENL
     [USE_THEN "jump" MATCH_MP_TAC THEN EXISTS_TAC `s:real^1` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `w:real^1` THEN STRIP_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN `(w:real^1) IN ts'` ASSUME_TAC THENL
       [EXPAND_TAC "ts'" THEN REWRITE_TAC[IN_INTER; IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [UNDISCH_TAC `~(?v:real^1. v IN ts /\ drop s < drop v /\ drop v < drop s + m)` THEN
          REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_THEN(MP_TAC o SPEC `w:real^1`) THEN
          ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
          UNDISCH_TAC `(w:real^1) IN ts` THEN
          UNDISCH_TAC `ts SUBSET interval[vec 0:real^1,vec 1]` THEN
          REWRITE_TAC[SUBSET; IN_INTERVAL_1; DROP_VEC] THEN MESON_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `drop t <= drop w` MP_TAC THENL [ASM_SIMP_TAC[]; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `drop t <= drop s` MP_TAC THENL [ASM_SIMP_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `s = vec 1:real^1` (fun th -> ASM_MESON_TAC[th]) THEN
  REWRITE_TAC[GSYM DROP_EQ; DROP_VEC] THEN ASM_REAL_ARITH_TAC);;

let MOI_S3SJ_DECOMP = prove
 (`!(W:real^N->bool) S O1 O2 p.
     open W /\ compact S /\ S SUBSET W /\
     (!e. &0 < e
          ==> ?d. &0 < d /\
                  !x y. x IN S /\ y IN S /\ dist(x,y) < d
                        ==> ?p. path p /\ path_image p SUBSET S /\
                                path_image p SUBSET ball(x,e) /\
                                pathstart p = x /\ pathfinish p = y) /\
     open O1 /\ open O2 /\ DISJOINT O1 O2 /\ W DIFF S SUBSET O1 UNION O2 /\
     (!r. path r /\ path_image r SUBSET W /\
          (path_image r SUBSET O1 UNION S \/ path_image r SUBSET O2 UNION S) /\
          pathstart r IN S /\ pathfinish r IN S
          ==> ?q. path q /\ path_image q SUBSET S /\ pathstart q = pathstart r /\
                  pathfinish q = pathfinish r /\ homotopic_paths W r q) /\
     path p /\ path_image p SUBSET W /\ pathstart p IN S /\ pathfinish p IN S
     ==> ?q. path q /\ path_image q SUBSET S /\ pathstart q = pathstart p /\
             pathfinish q = pathfinish p /\ homotopic_paths W p q`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "ulpc")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "side")
     STRIP_ASSUME_TAC))))))))) THEN
  (* a margin of W around the path, then the scales d and m *)
  MP_TAC(ISPEC `path_image(p:real^1->real^N)` HEINE_BOREL_LEMMA) THEN ANTS_TAC THENL
   [MATCH_MP_TAC COMPACT_PATH_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `{W:real^N->bool}`) THEN
  REWRITE_TAC[UNIONS_1; IN_SING; UNWIND_THM2; FORALL_UNWIND_THM2] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "margin"))) THEN
  USE_THEN "ulpc" (MP_TAC o SPEC `rho / &2`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "short"))) THEN
  MP_TAC(ISPECL [`p:real^1->real^N`; `interval[vec 0:real^1,vec 1]`]
    COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[path; COMPACT_INTERVAL]; ALL_TAC] THEN
  REWRITE_TAC[uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `min d (rho / &2)`) THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "uc"))) THEN
  SUBGOAL_THEN `!t. t IN interval[vec 0,vec 1] ==> (p:real^1->real^N) t IN path_image p`
  (LABEL_TAC "inim") THENL
   [REWRITE_TAC[path_image] THEN SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  (* short steps between visits of S *)
  SUBGOAL_THEN
   `!u v. u IN interval[vec 0,vec 1] /\ v IN interval[vec 0,vec 1] /\ drop u <= drop v /\
          drop v < drop u + m /\ (p:real^1->real^N) u IN S /\ p v IN S
          ==> ?q. path q /\ path_image q SUBSET S /\ pathstart q = p u /\
                  pathfinish q = p v /\ homotopic_paths W (subpath u v p) q`
  (LABEL_TAC "sh") THENL
   [MAP_EVERY X_GEN_TAC [`u:real^1`; `v:real^1`] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!w. w IN interval[u,v]
          ==> w IN interval[vec 0,vec 1] /\
              dist((p:real^1->real^N) u,p w) < min d (rho / &2)`
    ASSUME_TAC THENL
     [X_GEN_TAC `w:real^1` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(w:real^1) IN interval[vec 0,vec 1]` ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`(w:real^1) IN interval[u,v]`;
          `(u:real^1) IN interval[vec 0,vec 1]`; `(v:real^1) IN interval[vec 0,vec 1]`] THEN
        REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
      USE_THEN "uc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[DIST_REAL; GSYM drop] THEN
      UNDISCH_TAC `(w:real^1) IN interval[u,v]` THEN REWRITE_TAC[IN_INTERVAL_1] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "short" (MP_TAC o SPECL [`(p:real^1->real^N) u`; `(p:real^1->real^N) v`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC `min d (rho / &2)` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `v:real^1`) THEN
        ASM_REWRITE_TAC[IN_INTERVAL_1; REAL_LE_REFL] THEN SIMP_TAC[];
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^1->real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `q:real^1->real^N` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S3SJ_CONVEX_HOMOT THEN
    EXISTS_TAC `ball((p:real^1->real^N) u,rho / &2)` THEN
    ASM_SIMP_TAC[CONVEX_BALL; PATH_SUBPATH; PATHSTART_SUBPATH; PATHFINISH_SUBPATH;
                 PATH_IMAGE_SUBPATH] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball((p:real^1->real^N) u,rho)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
        USE_THEN "margin" MATCH_MP_TAC THEN USE_THEN "inim" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[]];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_BALL] THEN X_GEN_TAC `w:real^1` THEN
      DISCH_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `min d (rho / &2)` THEN
      CONJ_TAC THENL [ASM_SIMP_TAC[]; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* visit times and good times *)
  ABBREV_TAC `ts = {t | t IN interval[vec 0,vec 1] /\ (p:real^1->real^N) t IN S}` THEN
  ABBREV_TAC
   `gs = {t | t IN ts /\
              ?q. path q /\ path_image q SUBSET S /\ pathstart q = pathstart p /\
                  pathfinish q = (p:real^1->real^N) t /\
                  homotopic_paths W (subpath (vec 0) t p) q}` THEN
  SUBGOAL_THEN
   `!u v. u IN gs /\ v IN ts /\ drop u <= drop v /\
          (?q'. path q' /\ path_image q' SUBSET S /\ pathstart q' = (p:real^1->real^N) u /\
                pathfinish q' = p v /\ homotopic_paths W (subpath u v p) q')
          ==> v IN gs`
  (LABEL_TAC "ext") THENL
   [MAP_EVERY X_GEN_TAC [`u:real^1`; `v:real^1`] THEN
    EXPAND_TAC "gs" THEN EXPAND_TAC "ts" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (X_CHOOSE_THEN `q1:real^1->real^N` STRIP_ASSUME_TAC))
      (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `q2:real^1->real^N` STRIP_ASSUME_TAC)))) THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `(q1:real^1->real^N) ++ q2` THEN
    ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN; UNION_SUBSET] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
    EXISTS_TAC `subpath (vec 0) u (p:real^1->real^N) ++ subpath u v p` THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN MATCH_MP_TAC HOMOTOPIC_JOIN_SUBPATHS THEN
      ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL];
      MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
      ASM_REWRITE_TAC[PATHFINISH_SUBPATH; PATHSTART_SUBPATH]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ts:real^1->bool`; `gs:real^1->bool`; `m:real`] MOI_S3SJ_INTERVAL_INDUCT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "ts" THEN MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
      ASM_SIMP_TAC[CLOSED_INTERVAL; COMPACT_IMP_CLOSED] THEN ASM_MESON_TAC[path];
      EXPAND_TAC "ts" THEN SET_TAC[];
      EXPAND_TAC "ts" THEN REWRITE_TAC[IN_ELIM_THM; ENDS_IN_UNIT_INTERVAL] THEN
      ASM_MESON_TAC[pathfinish];
      EXPAND_TAC "gs" THEN SET_TAC[];
      EXPAND_TAC "gs" THEN EXPAND_TAC "ts" THEN
      REWRITE_TAC[IN_ELIM_THM; ENDS_IN_UNIT_INTERVAL; SUBPATH_REFL] THEN
      SUBGOAL_THEN `(p:real^1->real^N)(vec 0) = pathstart p` SUBST1_TAC THENL
       [REWRITE_TAC[pathstart]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `linepath(pathstart p,pathstart(p:real^1->real^N))` THEN
      REWRITE_TAC[PATH_LINEPATH; PATH_IMAGE_LINEPATH; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                  SEGMENT_REFL; SING_SUBSET; HOMOTOPIC_PATHS_REFL] THEN
      ASM SET_TAC[];
      ASM_REWRITE_TAC[];
      (* short steps *)
      MAP_EVERY X_GEN_TAC [`u:real^1`; `v:real^1`] THEN STRIP_TAC THEN
      USE_THEN "ext" MATCH_MP_TAC THEN EXISTS_TAC `u:real^1` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "sh" MATCH_MP_TAC THEN
      SUBGOAL_THEN `(u:real^1) IN ts` MP_TAC THENL
       [UNDISCH_TAC `(u:real^1) IN gs` THEN EXPAND_TAC "gs" THEN SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(v:real^1) IN ts` THEN EXPAND_TAC "ts" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_SIMP_TAC[];
      (* jumps over gaps of ts: excursions into one side *)
      MAP_EVERY X_GEN_TAC [`u:real^1`; `v:real^1`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(u:real^1) IN ts` ASSUME_TAC THENL
       [UNDISCH_TAC `(u:real^1) IN gs` THEN EXPAND_TAC "gs" THEN SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(u:real^1) IN interval[vec 0,vec 1] /\ (p:real^1->real^N) u IN S /\
                    (v:real^1) IN interval[vec 0,vec 1] /\ p v IN S` STRIP_ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`(u:real^1) IN ts`; `(v:real^1) IN ts`] THEN EXPAND_TAC "ts" THEN
        REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `interval[u:real^1,v] SUBSET interval[vec 0,vec 1]` ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`(u:real^1) IN interval[vec 0,vec 1]`; `(v:real^1) IN interval[vec 0,vec 1]`] THEN
        REWRITE_TAC[SUBSET; IN_INTERVAL_1; DROP_VEC] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `IMAGE (p:real^1->real^N) (interval[u,v]) SUBSET W` ASSUME_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `path_image(p:real^1->real^N)` THEN
        ASM_REWRITE_TAC[path_image] THEN ASM SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `IMAGE (p:real^1->real^N) (interval(u,v)) SUBSET O1 \/
                    IMAGE (p:real^1->real^N) (interval(u,v)) SUBSET O2`
      ASSUME_TAC THENL
       [MATCH_MP_TAC MOI_S3SJ_CONNECTED_OPEN_SPLIT THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN REWRITE_TAC[CONNECTED_INTERVAL] THEN
          MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
          CONJ_TAC THENL [ASM_MESON_TAC[path]; ALL_TAC] THEN
          MP_TAC(ISPECL [`u:real^1`; `v:real^1`] INTERVAL_OPEN_SUBSET_CLOSED) THEN
          ASM SET_TAC[];
          REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `w:real^1` THEN DISCH_TAC THEN
          SUBGOAL_THEN `drop u < drop w /\ drop w < drop v` STRIP_ASSUME_TAC THENL
           [UNDISCH_TAC `(w:real^1) IN interval(u,v)` THEN REWRITE_TAC[IN_INTERVAL_1];
            ALL_TAC] THEN
          SUBGOAL_THEN `(w:real^1) IN interval[u,v]` ASSUME_TAC THENL
           [REWRITE_TAC[IN_INTERVAL_1] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `(w:real^1) IN interval[vec 0,vec 1]` ASSUME_TAC THENL
           [ASM SET_TAC[]; ALL_TAC] THEN
          SUBGOAL_THEN `~((p:real^1->real^N) w IN S)` ASSUME_TAC THENL
           [DISCH_TAC THEN
            UNDISCH_TAC `!w:real^1. drop u < drop w /\ drop w < drop v ==> ~(w IN ts)` THEN
            DISCH_THEN(MP_TAC o SPEC `w:real^1`) THEN ASM_REWRITE_TAC[] THEN
            EXPAND_TAC "ts" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
            ALL_TAC] THEN
          SUBGOAL_THEN `(p:real^1->real^N) w IN W` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
          ASM SET_TAC[]];
        ALL_TAC] THEN
      USE_THEN "ext" MATCH_MP_TAC THEN EXISTS_TAC `u:real^1` THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      USE_THEN "side" (MP_TAC o SPEC `subpath u v (p:real^1->real^N)`) THEN
      REWRITE_TAC[PATHSTART_SUBPATH; PATHFINISH_SUBPATH] THEN ANTS_TAC THENL
       [ASM_SIMP_TAC[PATH_SUBPATH; PATH_IMAGE_SUBPATH; REAL_LT_IMP_LE] THEN
        SUBGOAL_THEN `interval[u:real^1,v] = interval(u,v) UNION {u,v}` SUBST1_TAC THENL
         [MATCH_MP_TAC CLOSED_OPEN_INTERVAL_1 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
        REWRITE_TAC[IMAGE_UNION; IMAGE_CLAUSES] THEN ASM SET_TAC[];
        DISCH_THEN ACCEPT_TAC]];
    ALL_TAC] THEN
  EXPAND_TAC "gs" THEN REWRITE_TAC[IN_ELIM_THM; SUBPATH_TRIVIAL] THEN
  SUBGOAL_THEN `(p:real^1->real^N)(vec 1) = pathfinish p` SUBST1_TAC THENL
   [REWRITE_TAC[pathfinish]; SIMP_TAC[]]);;

(* ========================================================================= *)
(* Part 8: the two ends of the product chart.  CHART_SLAB: images of        *)
(* E PCROSS J (E SUBSET D, J a set of heights) under f, with membership by  *)
(* coordinates.  LEVEL: a point z of W DIFF S whose vertical segment to the  *)
(* height a misses S (except z) lies on the side of the far end of the      *)
(* segment.  ENDS: with x0, x1 the lowest and highest points of S, either    *)
(* the level of x0 lies on one side and the level of x1 on the other, or    *)
(* both ends of the chart lie on one side and the other side is trapped in  *)
(* the compact slab between the levels of x0 and x1.                         *)
(* ========================================================================= *)

let MOI_S3SJ_CHART_SLAB = prove
 (`!(W:real^3->bool) (D:real^3->bool) (f:real^(3,1)finite_sum->real^3) g E J.
     homeomorphism (D PCROSS {x:real^1 | &0 < drop x /\ drop x < &1},W) (f,g) /\
     E SUBSET D /\ J SUBSET {x:real^1 | &0 < drop x /\ drop x < &1}
     ==> IMAGE f (E PCROSS J) SUBSET W /\
         (!z. z IN W
              ==> (z IN IMAGE f (E PCROSS J) <=> fstcart(g z) IN E /\ sndcart(g z) IN J)) /\
         (connected E /\ connected J ==> connected (IMAGE f (E PCROSS J))) /\
         (compact E /\ compact J ==> compact (IMAGE f (E PCROSS J)))`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `I0 = {x:real^1 | &0 < drop x /\ drop x < &1}` THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(E:real^3->bool) PCROSS (J:real^1->bool) SUBSET D PCROSS I0` ASSUME_TAC THENL
   [MATCH_MP_TAC PCROSS_MONO THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^(3,1)finite_sum->real^3) continuous_on (E PCROSS J)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(D:real^3->bool) PCROSS (I0:real^1->bool)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN EQ_TAC THENL
     [REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^(3,1)finite_sum` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(g:real^3->real^(3,1)finite_sum) z = y` SUBST1_TAC THENL
       [UNDISCH_TAC `z = (f:real^(3,1)finite_sum->real^3) y` THEN DISCH_THEN SUBST1_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `(y:real^(3,1)finite_sum) IN E PCROSS J` THEN
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM PASTECART_FST_SND] THEN
      REWRITE_TAC[PASTECART_IN_PCROSS];
      STRIP_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `(g:real^3->real^(3,1)finite_sum) z` THEN CONJ_TAC THENL
       [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        GEN_REWRITE_TAC LAND_CONV [GSYM PASTECART_FST_SND] THEN
        ASM_REWRITE_TAC[PASTECART_IN_PCROSS]]];
    STRIP_TAC THEN MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
    ASM_SIMP_TAC[CONNECTED_PCROSS];
    STRIP_TAC THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_SIMP_TAC[COMPACT_PCROSS]]);;

let MOI_S3SJ_LEVEL = prove
 (`!(W:real^3->bool) S O O' (D:real^3->bool) (f:real^(3,1)finite_sum->real^3) g z a.
     homeomorphism (D PCROSS {x:real^1 | &0 < drop x /\ drop x < &1},W) (f,g) /\
     W DIFF S SUBSET O UNION O' /\ open O /\ open O' /\ DISJOINT O O' /\
     z IN W /\ &0 < drop a /\ drop a < &1 /\
     (!w. w IN W /\ fstcart(g w) = fstcart(g z) /\ sndcart(g w) IN segment[sndcart(g z),a] /\
          ~(w = z) ==> ~(w IN S)) /\
     f(pastecart (fstcart(g z)) a) IN O
     ==> z IN O UNION S`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC
   `!w. w IN W /\ fstcart((g:real^3->real^(3,1)finite_sum) w) = fstcart(g z) /\
        sndcart(g w) IN segment[sndcart(g z),a] /\ ~(w = z) ==> ~(w IN S)` THEN
  DISCH_THEN(LABEL_TAC "seg") THEN
  ASM_CASES_TAC `(z:real^3) IN S` THEN ASM_REWRITE_TAC[IN_UNION] THEN
  ABBREV_TAC `I0 = {x:real^1 | &0 < drop x /\ drop x < &1}` THEN
  SUBGOAL_THEN `fstcart((g:real^3->real^(3,1)finite_sum) z) IN D /\ sndcart(g z) IN I0`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `homeomorphism ((D:real^3->bool) PCROSS I0,(W:real^3->bool))
                   (f:real^(3,1)finite_sum->real^3,g)` THEN
    REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(g:real^3->real^(3,1)finite_sum) z IN D PCROSS I0` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM PASTECART_FST_SND] THEN
    REWRITE_TAC[PASTECART_IN_PCROSS];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[sndcart((g:real^3->real^(3,1)finite_sum) z),a] SUBSET I0`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `I0 = interval(vec 0:real^1,vec 1)` SUBST1_TAC THENL
       [EXPAND_TAC "I0" THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTERVAL_1; DROP_VEC];
        REWRITE_TAC[CONVEX_INTERVAL]];
      EXPAND_TAC "I0" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`W:real^3->bool`; `D:real^3->bool`; `f:real^(3,1)finite_sum->real^3`;
                 `g:real^3->real^(3,1)finite_sum`;
                 `{fstcart((g:real^3->real^(3,1)finite_sum) z)}`;
                 `segment[sndcart((g:real^3->real^(3,1)finite_sum) z),a]`]
    MOI_S3SJ_CHART_SLAB) THEN
  ASM_REWRITE_TAC[SING_SUBSET; CONNECTED_SING; CONNECTED_SEGMENT; IN_SING] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "vmem")
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  ABBREV_TAC
   `V = IMAGE (f:real^(3,1)finite_sum->real^3)
          ({fstcart((g:real^3->real^(3,1)finite_sum) z)} PCROSS segment[sndcart(g z),a])` THEN
  SUBGOAL_THEN
   `(z:real^3) IN V /\
    (f:real^(3,1)finite_sum->real^3)(pastecart (fstcart((g:real^3->real^(3,1)finite_sum) z)) a)
    IN V`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "vmem" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(z:real^3) IN W`)]) THEN
      REWRITE_TAC[ENDS_IN_SEGMENT];
      EXPAND_TAC "V" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      REWRITE_TAC[PASTECART_IN_PCROSS; IN_SING; ENDS_IN_SEGMENT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `V SUBSET (O:real^3->bool) \/ V SUBSET O'` MP_TAC THENL
   [MATCH_MP_TAC MOI_S3SJ_CONNECTED_OPEN_SPLIT THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(w:real^3) IN W` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~((w:real^3) IN S)` ASSUME_TAC THENL
     [ASM_CASES_TAC `w:real^3 = z` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "seg" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(w:real^3) IN V` THEN
      USE_THEN "vmem" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(w:real^3) IN W`)]);
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC [`W DIFF S SUBSET (O:real^3->bool) UNION O'`;
                           `(w:real^3) IN W`; `~((w:real^3) IN S)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`DISJOINT (O:real^3->bool) O'`; `(z:real^3) IN V`;
    `(f:real^(3,1)finite_sum->real^3)(pastecart (fstcart((g:real^3->real^(3,1)finite_sum) z)) a)
     IN V`;
    `(f:real^(3,1)finite_sum->real^3)(pastecart (fstcart((g:real^3->real^(3,1)finite_sum) z)) a)
     IN O`] THEN
  SET_TAC[]);;

let MOI_S3SJ_ENDS = prove
 (`!(W:real^3->bool) S O1 O2 (D:real^3->bool) (f:real^(3,1)finite_sum->real^3) g.
     homeomorphism (D PCROSS {x:real^1 | &0 < drop x /\ drop x < &1},W) (f,g) /\
     compact D /\ connected D /\
     compact S /\ ~(S = {}) /\ S SUBSET W /\
     open O1 /\ open O2 /\ DISJOINT O1 O2 /\ W DIFF S = O1 UNION O2
     ==> ?x0 x1. x0 IN S /\ x1 IN S /\
           ((!z. z IN W /\ sndcart(g z) = sndcart(g x0) ==> z IN O2 UNION S) /\
            (!z. z IN W /\ sndcart(g z) = sndcart(g x1) ==> z IN O1 UNION S) \/
            (!z. z IN W /\ sndcart(g z) = sndcart(g x0) ==> z IN O1 UNION S) /\
            (!z. z IN W /\ sndcart(g z) = sndcart(g x1) ==> z IN O2 UNION S) \/
            (?M. compact M /\ M SUBSET W /\ (O1 SUBSET M \/ O2 SUBSET M)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `homeomorphism ((D:real^3->bool) PCROSS {x:real^1 | &0 < drop x /\ drop x < &1},
                              (W:real^3->bool)) (f:real^(3,1)finite_sum->real^3,g)` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC(REWRITE_RULE[homeomorphism] th)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "gf") (CONJUNCTS_THEN2 (LABEL_TAC "fim")
    (CONJUNCTS_THEN2 (LABEL_TAC "fco") (CONJUNCTS_THEN2 (LABEL_TAC "fg")
      (CONJUNCTS_THEN2 (LABEL_TAC "gim") (LABEL_TAC "gcont")))))) THEN
  SUBGOAL_THEN
   `!w:real^3. w IN W ==> fstcart((g:real^3->real^(3,1)finite_sum) w) IN D /\
                          &0 < drop(sndcart(g w)) /\ drop(sndcart(g w)) < &1`
  (LABEL_TAC "gco") THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(g:real^3->real^(3,1)finite_sum) w IN
                  D PCROSS {x:real^1 | &0 < drop x /\ drop x < &1}` MP_TAC THENL
     [USE_THEN "gim" (fun th -> REWRITE_TAC[GSYM th]) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM PASTECART_FST_SND] THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_ELIM_THM];
    ALL_TAC] THEN
  (* the lowest and highest points of S *)
  MP_TAC(ISPEC `IMAGE (\z:real^3. sndcart((g:real^3->real^(3,1)finite_sum) z)) S`
    MOI_S3SJ_COMPACT_MAX_MIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IMAGE_EQ_EMPTY] THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SNDCART THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `W:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; FORALL_IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `x1:real^3` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "max")))
    (X_CHOOSE_THEN `x0:real^3` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "min")))) THEN
  MAP_EVERY EXISTS_TAC [`x0:real^3`; `x1:real^3`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(x0:real^3) IN W /\ (x1:real^3) IN W` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `t0 = drop(sndcart((g:real^3->real^(3,1)finite_sum) x0))` THEN
  ABBREV_TAC `t1 = drop(sndcart((g:real^3->real^(3,1)finite_sum) x1))` THEN
  SUBGOAL_THEN `&0 < t0 /\ t0 < &1 /\ &0 < t1 /\ t1 < &1 /\ t0 <= t1` STRIP_ASSUME_TAC THENL
   [USE_THEN "gco" (MP_TAC o C MATCH_MP (ASSUME `(x0:real^3) IN W`)) THEN
    USE_THEN "gco" (MP_TAC o C MATCH_MP (ASSUME `(x1:real^3) IN W`)) THEN
    USE_THEN "max" (MP_TAC o C MATCH_MP (ASSUME `(x0:real^3) IN S`)) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the upper end A, the lower end B and the middle slab M *)
  MP_TAC(ISPECL [`W:real^3->bool`; `D:real^3->bool`; `f:real^(3,1)finite_sum->real^3`;
                 `g:real^3->real^(3,1)finite_sum`; `D:real^3->bool`;
                 `interval(lift t1,vec 1)`] MOI_S3SJ_CHART_SLAB) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_REFL] THEN
    REWRITE_TAC[SUBSET; IN_INTERVAL_1; IN_ELIM_THM; LIFT_DROP; DROP_VEC] THEN
    REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[CONNECTED_INTERVAL; IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "Amem")
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  MP_TAC(ISPECL [`W:real^3->bool`; `D:real^3->bool`; `f:real^(3,1)finite_sum->real^3`;
                 `g:real^3->real^(3,1)finite_sum`; `D:real^3->bool`;
                 `interval(vec 0,lift t0)`] MOI_S3SJ_CHART_SLAB) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_REFL] THEN
    REWRITE_TAC[SUBSET; IN_INTERVAL_1; IN_ELIM_THM; LIFT_DROP; DROP_VEC] THEN
    REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[CONNECTED_INTERVAL; IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "Bmem")
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  MP_TAC(ISPECL [`W:real^3->bool`; `D:real^3->bool`; `f:real^(3,1)finite_sum->real^3`;
                 `g:real^3->real^(3,1)finite_sum`; `D:real^3->bool`;
                 `interval[lift t0,lift t1]`] MOI_S3SJ_CHART_SLAB) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_REFL] THEN
    REWRITE_TAC[SUBSET; IN_INTERVAL_1; IN_ELIM_THM; LIFT_DROP; DROP_VEC] THEN
    REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[COMPACT_INTERVAL; IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "Mmem")
    (CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC))) THEN
  ABBREV_TAC `A = IMAGE (f:real^(3,1)finite_sum->real^3) (D PCROSS interval(lift t1,vec 1))` THEN
  ABBREV_TAC `B = IMAGE (f:real^(3,1)finite_sum->real^3) (D PCROSS interval(vec 0,lift t0))` THEN
  ABBREV_TAC `M = IMAGE (f:real^(3,1)finite_sum->real^3) (D PCROSS interval[lift t0,lift t1])` THEN
  (* each end lies on one side *)
  SUBGOAL_THEN `A SUBSET (O1:real^3->bool) \/ A SUBSET O2` (LABEL_TAC "Aside") THENL
   [MATCH_MP_TAC MOI_S3SJ_CONNECTED_OPEN_SPLIT THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `W DIFF S = (O1:real^3->bool) UNION O2` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[SUBSET; IN_DIFF] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN W` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    USE_THEN "Amem" (MP_TAC o C MATCH_MP (ASSUME `(z:real^3) IN W`)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    USE_THEN "max" (MP_TAC o C MATCH_MP (ASSUME `(z:real^3) IN S`)) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `B SUBSET (O1:real^3->bool) \/ B SUBSET O2` (LABEL_TAC "Bside") THENL
   [MATCH_MP_TAC MOI_S3SJ_CONNECTED_OPEN_SPLIT THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `W DIFF S = (O1:real^3->bool) UNION O2` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[SUBSET; IN_DIFF] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN W` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    USE_THEN "Bmem" (MP_TAC o C MATCH_MP (ASSUME `(z:real^3) IN W`)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    USE_THEN "min" (MP_TAC o C MATCH_MP (ASSUME `(z:real^3) IN S`)) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* points of W outside both ends lie in the slab *)
  SUBGOAL_THEN `!z:real^3. z IN W /\ ~(z IN A) /\ ~(z IN B) ==> z IN M` (LABEL_TAC "mid") THENL
   [X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    USE_THEN "Mmem" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(z:real^3) IN W`)]) THEN
    UNDISCH_TAC `~((z:real^3) IN A)` THEN UNDISCH_TAC `~((z:real^3) IN B)` THEN
    USE_THEN "Amem" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(z:real^3) IN W`)]) THEN
    USE_THEN "Bmem" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(z:real^3) IN W`)]) THEN
    USE_THEN "gco" (MP_TAC o C MATCH_MP (ASSUME `(z:real^3) IN W`)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the levels of x0 and x1 *)
  SUBGOAL_THEN
   `!O O'. open O /\ open O' /\ DISJOINT O O' /\ W DIFF S SUBSET O UNION O' /\ B SUBSET O
           ==> !z:real^3. z IN W /\ sndcart((g:real^3->real^(3,1)finite_sum) z) = sndcart(g x0)
                          ==> z IN O UNION S`
  (LABEL_TAC "low") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_S3SJ_LEVEL THEN
    MAP_EVERY EXISTS_TAC [`W:real^3->bool`; `O':real^3->bool`; `D:real^3->bool`;
                          `f:real^(3,1)finite_sum->real^3`; `g:real^3->real^(3,1)finite_sum`;
                          `lift(t0 / &2)`] THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SEGMENT_1] THEN
      SUBGOAL_THEN `~(drop(sndcart((g:real^3->real^(3,1)finite_sum) x0)) <= drop(lift(t0 / &2)))`
      (fun th -> REWRITE_TAC[th]) THENL
       [ASM_REWRITE_TAC[LIFT_DROP] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN `t0 <= drop(sndcart((g:real^3->real^(3,1)finite_sum) w))` ASSUME_TAC THENL
       [USE_THEN "min" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `sndcart((g:real^3->real^(3,1)finite_sum) w) = sndcart(g z)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[GSYM DROP_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(g:real^3->real^(3,1)finite_sum) w = g z` ASSUME_TAC THENL
       [ONCE_REWRITE_TAC[PASTECART_EQ] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `~(w:real^3 = z)` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `(f:real^(3,1)finite_sum->real^3)(g(w:real^3))` THEN CONJ_TAC THENL
       [CONV_TAC SYM_CONV THEN USE_THEN "fg" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[] THEN USE_THEN "fg" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      SUBGOAL_THEN
       `(f:real^(3,1)finite_sum->real^3)
          (pastecart (fstcart((g:real^3->real^(3,1)finite_sum) z)) (lift(t0 / &2))) IN B`
      MP_TAC THENL
       [EXPAND_TAC "B" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
        USE_THEN "gco" (MP_TAC o C MATCH_MP (ASSUME `(z:real^3) IN W`)) THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        ASM SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!O O'. open O /\ open O' /\ DISJOINT O O' /\ W DIFF S SUBSET O UNION O' /\ A SUBSET O
           ==> !z:real^3. z IN W /\ sndcart((g:real^3->real^(3,1)finite_sum) z) = sndcart(g x1)
                          ==> z IN O UNION S`
  (LABEL_TAC "high") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_S3SJ_LEVEL THEN
    MAP_EVERY EXISTS_TAC [`W:real^3->bool`; `O':real^3->bool`; `D:real^3->bool`;
                          `f:real^(3,1)finite_sum->real^3`; `g:real^3->real^(3,1)finite_sum`;
                          `lift((t1 + &1) / &2)`] THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SEGMENT_1] THEN
      SUBGOAL_THEN `drop(sndcart((g:real^3->real^(3,1)finite_sum) x1)) <= drop(lift((t1 + &1) / &2))`
      (fun th -> REWRITE_TAC[th]) THENL
       [ASM_REWRITE_TAC[LIFT_DROP] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN `drop(sndcart((g:real^3->real^(3,1)finite_sum) w)) <= t1` ASSUME_TAC THENL
       [USE_THEN "max" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `sndcart((g:real^3->real^(3,1)finite_sum) w) = sndcart(g z)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[GSYM DROP_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(g:real^3->real^(3,1)finite_sum) w = g z` ASSUME_TAC THENL
       [ONCE_REWRITE_TAC[PASTECART_EQ] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `~(w:real^3 = z)` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `(f:real^(3,1)finite_sum->real^3)(g(w:real^3))` THEN CONJ_TAC THENL
       [CONV_TAC SYM_CONV THEN USE_THEN "fg" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[] THEN USE_THEN "fg" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      SUBGOAL_THEN
       `(f:real^(3,1)finite_sum->real^3)
          (pastecart (fstcart((g:real^3->real^(3,1)finite_sum) z)) (lift((t1 + &1) / &2))) IN A`
      MP_TAC THENL
       [EXPAND_TAC "A" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
        USE_THEN "gco" (MP_TAC o C MATCH_MP (ASSUME `(z:real^3) IN W`)) THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        ASM SET_TAC[]]];
    ALL_TAC] THEN
  (* the four cases *)
  SUBGOAL_THEN `W DIFF S SUBSET (O1:real^3->bool) UNION O2 /\ W DIFF S SUBSET O2 UNION O1 /\
                DISJOINT (O2:real^3->bool) O1`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `DISJOINT (O1:real^3->bool) O2` THEN
    UNDISCH_TAC `W DIFF S = (O1:real^3->bool) UNION O2` THEN SET_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "Aside" DISJ_CASES_TAC THEN REMOVE_THEN "Bside" DISJ_CASES_TAC THENL
   [DISJ2_TAC THEN DISJ2_TAC THEN EXISTS_TAC `M:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    DISJ2_TAC THEN REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    USE_THEN "mid" MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC [`W DIFF S = (O1:real^3->bool) UNION O2`; `DISJOINT (O1:real^3->bool) O2`;
      `A SUBSET (O1:real^3->bool)`; `B SUBSET (O1:real^3->bool)`; `(z:real^3) IN O2`] THEN
    SET_TAC[];
    DISJ1_TAC THEN CONJ_TAC THENL
     [USE_THEN "low" MATCH_MP_TAC THEN EXISTS_TAC `O1:real^3->bool` THEN ASM_REWRITE_TAC[];
      USE_THEN "high" MATCH_MP_TAC THEN EXISTS_TAC `O2:real^3->bool` THEN ASM_REWRITE_TAC[]];
    DISJ2_TAC THEN DISJ1_TAC THEN CONJ_TAC THENL
     [USE_THEN "low" MATCH_MP_TAC THEN EXISTS_TAC `O2:real^3->bool` THEN ASM_REWRITE_TAC[];
      USE_THEN "high" MATCH_MP_TAC THEN EXISTS_TAC `O1:real^3->bool` THEN ASM_REWRITE_TAC[]];
    DISJ2_TAC THEN DISJ2_TAC THEN EXISTS_TAC `M:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    DISJ1_TAC THEN REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    USE_THEN "mid" MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC [`W DIFF S = (O1:real^3->bool) UNION O2`; `DISJOINT (O1:real^3->bool) O2`;
      `A SUBSET (O2:real^3->bool)`; `B SUBSET (O2:real^3->bool)`; `(z:real^3) IN O1`] THEN
    SET_TAC[]]);;

(* ========================================================================= *)
(* Part 9: assembly.  SIDES: with K inside the interior of the closed set X *)
(* inside the open set N0, W = N0 DIFF K minus frontier X splits into the   *)
(* open sides interior X DIFF K and W DIFF X.  TRAPPED: neither side lies   *)
(* in a compact subset of W (else K, resp. N0, would be a nonempty compact  *)
(* open set).  MAIN: the abstract form of Lemma 10.  S33_SURJ, from         *)
(* TUBE_FACTS, moi_s33_hd and moi_s33_inv (frontier X is the union of the   *)
(* boundary complex, a finite set of simplices).                            *)
(* ========================================================================= *)

let MOI_S3SJ_SIDES = prove
 (`!(N0:real^3->bool) X K.
     open N0 /\ closed X /\ closed K /\ K SUBSET interior X /\ X SUBSET N0
     ==> open (N0 DIFF K) /\ frontier X SUBSET N0 DIFF K /\
         open (interior X DIFF K) /\ open ((N0 DIFF K) DIFF X) /\
         DISJOINT (interior X DIFF K) ((N0 DIFF K) DIFF X) /\
         (N0 DIFF K) DIFF frontier X = (interior X DIFF K) UNION ((N0 DIFF K) DIFF X)`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC OPEN_DIFF THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED] THEN
    MP_TAC(ISPEC `X:real^3->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[];
    MATCH_MP_TAC OPEN_DIFF THEN ASM_REWRITE_TAC[OPEN_INTERIOR];
    MATCH_MP_TAC OPEN_DIFF THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_DIFF THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPEC `X:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[];
    REWRITE_TAC[frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED] THEN
    MP_TAC(ISPEC `X:real^3->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[]]);;

let MOI_S3SJ_TRAPPED = prove
 (`!(N0:real^3->bool) X K M.
     open N0 /\ compact X /\ compact K /\ ~(K = {}) /\ K SUBSET interior X /\ X SUBSET N0 /\
     compact M /\ M SUBSET N0 DIFF K /\
     (interior X DIFF K SUBSET M \/ (N0 DIFF K) DIFF X SUBSET M)
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THENL
   [SUBGOAL_THEN `closure(interior X DIFF K) SUBSET (M:real^3->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
    SUBGOAL_THEN `open(K:real^3->bool)` MP_TAC THENL
     [SUBGOAL_THEN `K = interior X DIFF closure(interior X DIFF (K:real^3->bool))`
      SUBST1_TAC THENL
       [MP_TAC(ISPEC `interior X DIFF (K:real^3->bool)` CLOSURE_SUBSET) THEN ASM SET_TAC[];
        MATCH_MP_TAC OPEN_DIFF THEN REWRITE_TAC[OPEN_INTERIOR; CLOSED_CLOSURE]];
      ASM_MESON_TAC[COMPACT_OPEN]];
    SUBGOAL_THEN `compact(N0:real^3->bool)` ASSUME_TAC THENL
     [SUBGOAL_THEN `N0 = (X:real^3->bool) UNION M` SUBST1_TAC THENL
       [MP_TAC(ISPEC `X:real^3->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[];
        ASM_SIMP_TAC[COMPACT_UNION]];
      ALL_TAC] THEN
    SUBGOAL_THEN `N0:real^3->bool = {}` MP_TAC THENL
     [ASM_MESON_TAC[COMPACT_OPEN]; ALL_TAC] THEN
    MP_TAC(ISPEC `X:real^3->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[]]);;

let MOI_S3SJ_MAIN = prove
 (`!(N0:real^3->bool) X K (D:real^3->bool) (f:real^(3,1)finite_sum->real^3) g ff.
     open N0 /\ compact X /\ compact K /\ ~(K = {}) /\ K SUBSET interior X /\ X SUBSET N0 /\
     compact D /\ connected D /\
     homeomorphism (D PCROSS {x:real^1 | &0 < drop x /\ drop x < &1},N0 DIFF K) (f,g) /\
     FINITE ff /\ (!k. k IN ff ==> compact k /\ convex k) /\ UNIONS ff = frontier X /\
     connected (frontier X)
     ==> ?a. a IN frontier X /\
             !p. path p /\ path_image p SUBSET N0 DIFF K /\ pathstart p = a /\ pathfinish p = a
                 ==> ?q. path q /\ path_image q SUBSET frontier X /\ pathstart q = a /\
                         pathfinish q = a /\ homotopic_paths (N0 DIFF K) p q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`N0:real^3->bool`; `X:real^3->bool`; `K:real^3->bool`] MOI_S3SJ_SIDES) THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN STRIP_TAC THEN
  ABBREV_TAC `W = (N0:real^3->bool) DIFF K` THEN
  ABBREV_TAC `S = frontier(X:real^3->bool)` THEN
  ABBREV_TAC `O1 = interior X DIFF (K:real^3->bool)` THEN
  ABBREV_TAC `O2 = (W:real^3->bool) DIFF X` THEN
  SUBGOAL_THEN `compact(S:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MATCH_MP_TAC COMPACT_FRONTIER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(S:real^3->bool = {})` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[FRONTIER_EQ_EMPTY; DE_MORGAN_THM] THEN CONJ_TAC THENL
     [MP_TAC(ISPEC `X:real^3->bool` INTERIOR_SUBSET) THEN
      MAP_EVERY UNDISCH_TAC [`~(K:real^3->bool = {})`; `K SUBSET interior(X:real^3->bool)`] THEN
      SET_TAC[];
      ASM_MESON_TAC[COMPACT_IMP_BOUNDED; NOT_BOUNDED_UNIV]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. &0 < e
        ==> ?d. &0 < d /\
                !x y. x IN S /\ y IN S /\ dist(x,y) < d
                      ==> ?p. path p /\ path_image p SUBSET S /\
                              path_image p SUBSET ball(x,e) /\
                              pathstart p = x /\ pathfinish p = (y:real^3)`
  (LABEL_TAC "ulpc") THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`ff:(real^3->bool)->bool`; `e:real`] MOI_S3SJ_ULPC) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `path_connected(S:real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[path_connected] THEN
    MAP_EVERY X_GEN_TAC [`a:real^3`; `b:real^3`] THEN STRIP_TAC THEN
    USE_THEN "ulpc" (MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL
     [`\u v:real^3. ?p. path p /\ path_image p SUBSET S /\ pathstart p = u /\ pathfinish p = v`;
      `S:real^3->bool`; `S:real^3->bool`; `a:real^3`; `d:real`] MOI_S3SJ_REL_CONNECTED) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[SUBSET_REFL] THEN CONJ_TAC THENL
       [MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^3`; `v:real^3`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; MESON_TAC[]];
        MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`; `w:real^3`] THEN
        DISCH_THEN(CONJUNCTS_THEN2
          (X_CHOOSE_THEN `p1:real^1->real^3` STRIP_ASSUME_TAC)
          (X_CHOOSE_THEN `p2:real^1->real^3` STRIP_ASSUME_TAC)) THEN
        EXISTS_TAC `(p1:real^1->real^3) ++ p2` THEN
        ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN;
                     UNION_SUBSET]];
      DISCH_THEN(MP_TAC o SPEC `b:real^3`) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `W DIFF S SUBSET (O1:real^3->bool) UNION O2 /\
                W DIFF S SUBSET (O2:real^3->bool) UNION O1 /\
                DISJOINT (O2:real^3->bool) O1`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `DISJOINT (O1:real^3->bool) O2` THEN
    UNDISCH_TAC `W DIFF S = (O1:real^3->bool) UNION O2` THEN SET_TAC[];
    ALL_TAC] THEN
  (* the two extreme points with their levels on opposite sides *)
  SUBGOAL_THEN
   `?xa xb. xa IN S /\ xb IN S /\
            (!z. z IN W /\ sndcart((g:real^3->real^(3,1)finite_sum) z) = sndcart(g xa)
                 ==> z IN O2 UNION S) /\
            (!z. z IN W /\ sndcart(g z) = sndcart(g xb) ==> z IN O1 UNION S)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`W:real^3->bool`; `S:real^3->bool`; `O1:real^3->bool`; `O2:real^3->bool`;
                   `D:real^3->bool`; `f:real^(3,1)finite_sum->real^3`;
                   `g:real^3->real^(3,1)finite_sum`] MOI_S3SJ_ENDS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x0:real^3` (X_CHOOSE_THEN `x1:real^3` STRIP_ASSUME_TAC)) THENL
     [MAP_EVERY EXISTS_TAC [`x0:real^3`; `x1:real^3`] THEN ASM_REWRITE_TAC[];
      MAP_EVERY EXISTS_TAC [`x1:real^3`; `x0:real^3`] THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`N0:real^3->bool`; `X:real^3->bool`; `K:real^3->bool`; `M:real^3->bool`]
        MOI_S3SJ_TRAPPED) THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`N0:real^3->bool`; `X:real^3->bool`; `K:real^3->bool`; `M:real^3->bool`]
        MOI_S3SJ_TRAPPED) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the side property for both sides *)
  SUBGOAL_THEN
   `!r. path r /\ path_image r SUBSET W /\
        (path_image r SUBSET O1 UNION S \/ path_image r SUBSET O2 UNION S) /\
        pathstart r IN S /\ pathfinish r IN S
        ==> ?q. path q /\ path_image q SUBSET S /\ pathstart q = pathstart r /\
                pathfinish q = pathfinish r /\ homotopic_paths W r (q:real^1->real^3)`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:real^1->real^3` THEN STRIP_TAC THENL
     [MP_TAC(ISPECL [`W:real^3->bool`; `S:real^3->bool`; `O1:real^3->bool`; `O2:real^3->bool`;
                     `D:real^3->bool`; `f:real^(3,1)finite_sum->real^3`;
                     `g:real^3->real^(3,1)finite_sum`; `xa:real^3`] MOI_S3SJ_SIDE_PATH) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      MP_TAC(ISPECL [`W:real^3->bool`; `S:real^3->bool`; `O2:real^3->bool`; `O1:real^3->bool`;
                     `D:real^3->bool`; `f:real^(3,1)finite_sum->real^3`;
                     `g:real^3->real^(3,1)finite_sum`; `xb:real^3`] MOI_S3SJ_SIDE_PATH) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  EXISTS_TAC `xa:real^3` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `p:real^1->real^3` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`W:real^3->bool`; `S:real^3->bool`; `O1:real^3->bool`; `O2:real^3->bool`;
                 `p:real^1->real^3`] MOI_S3SJ_DECOMP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]);;

let S33_SURJ = prove
 (MOI_S33_SURJ,
  DISCH_THEN(LABEL_TAC "tube") THEN
  MAP_EVERY X_GEN_TAC [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                       `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                       `x:(real^3->bool)->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `moi_s33_tube t l h` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_s33_hd]; ALL_TAC] THEN
  USE_THEN "tube" (fun th -> MP_TAC(MATCH_MP th (ASSUME `moi_s33_tube t l h`))) THEN
  STRIP_TAC THEN
  UNDISCH_TAC `moi_s33_inv t l h e x` THEN REWRITE_TAC[moi_s33_inv; moi_s33_x2] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!s:real^3->bool. s IN x ==> compact s /\ convex s` ASSUME_TAC THENL
   [X_GEN_TAC `s:real^3->bool` THEN DISCH_TAC THEN
    UNDISCH_TAC `combinatorial_manifold_with_boundary 3 (x:(real^3->bool)->bool)` THEN
    REWRITE_TAC[combinatorial_manifold_with_boundary; lf_simplicial_complex] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real^3->bool` o CONJUNCT1 o CONJUNCT1) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[SIMPLEX_IMP_COMPACT; SIMPLEX_IMP_CONVEX];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS(boundary_complex x) = frontier(UNIONS(x:(real^3->bool)->bool))`
  ASSUME_TAC THENL
   [MP_TAC(MATCH_MP BOUNDARY_COMPLEX_SURFACE
      (ASSUME `combinatorial_manifold_with_boundary 3 (x:(real^3->bool)->bool)`)) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2(CONJUNCT2 th))]) THEN
    MP_TAC(MATCH_MP COMPLEX_BOUNDARY_FRONTIER_3
      (ASSUME `combinatorial_manifold_with_boundary 3 (x:(real^3->bool)->bool)`)) THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(IMAGE (h:real^3->real^3) (UNIONS l) = {})` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s33_tube t l h` THEN REWRITE_TAC[moi_s33_tube] THEN STRIP_TAC THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY; EMPTY_UNIONS; NOT_FORALL_THM; NOT_IMP] THEN
    EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `aff_dim(s:real^3->bool) = &1` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `compact(derived_frontier (t:(real^3->bool)->bool) l)` ASSUME_TAC THENL
   [UNDISCH_TAC `frontier (derived_nbhd (t:(real^3->bool)->bool) l) = derived_frontier t l` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC COMPACT_FRONTIER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`interior(IMAGE (h:real^3->real^3) (derived_nbhd t l))`; `UNIONS(x:(real^3->bool)->bool)`;
    `IMAGE (h:real^3->real^3) (UNIONS l)`; `derived_frontier (t:(real^3->bool)->bool) l`;
    `f:real^(3,1)finite_sum->real^3`; `g:real^3->real^(3,1)finite_sum`;
    `boundary_complex(x:(real^3->bool)->bool)`] MOI_S3SJ_MAIN) THEN
  REWRITE_TAC[GSYM moi_s33_ww] THEN ANTS_TAC THENL
   [REWRITE_TAC[OPEN_INTERIOR] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [MATCH_MP_TAC COMPACT_UNIONS THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC PATH_CONNECTED_IMP_CONNECTED THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[boundary_complex] THEN MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[boundary_complex; IN_ELIM_THM] THEN ASM_SIMP_TAC[]];
    SIMP_TAC[]]);;


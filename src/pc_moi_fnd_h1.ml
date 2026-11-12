(* ========================================================================= *)
(* pc_moi_fnd_h1: foundations of the Moise PL core (Moise GTM 47, Sec 28,    *)
(* p.203: J ~ 0 on T iff J is contractible in T).  Loops in the solid torus *)
(* and torus models are null-homotopic iff the winding numbers of their     *)
(* circle coordinates vanish; spines of solid tori and ends of annuli carry *)
(* all loops; integral H_1 of a solid torus and of an annulus is infinite   *)
(* cyclic with the spine (each end) inducing an isomorphism; H_1 of a torus *)
(* is Z x Z; loops_carried implies carries_h1.                              *)
(* Tools: pc_top_hurewicz (path_simplex, loop classes, ATOP_HUREWICZ1),     *)
(* homology.ml (homotopy invariance, spheres), cauchy.ml (winding numbers). *)
(*                                                                           *)
(* The first section: loop classes of real^1 paths in H_1 of a Euclidean     *)
(* subspace (bridge from homotopic_loops to the real-path tools of           *)
(* pc_top_hurewicz).                                                         *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_stmt.ml";;
needs "src/pc_top_hurewicz.ml";;
needs "src/pc_top_mv.ml";;
needs "src/pc_moi_assembly.ml";;
needs "src/pc_moi_plmap.ml";;

prioritize_real();;
type_invention_error := true;;

let MOI_FH1_HOMOTOPIC_LOOPS_LIFT = prove
 (`!s p q:real^1->real^N.
      homotopic_loops s p q
      ==> homotopic_with (\k. k(&0) = k(&1))
            (subtopology euclideanreal (real_interval[&0,&1]),
             subtopology euclidean s) (p o lift) (q o lift)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopic_loops] THEN DISCH_TAC THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_MAP_RIGHT THEN
  EXISTS_TAC `\r:real^1->real^N. pathfinish r = pathstart r` THEN
  EXISTS_TAC `subtopology euclidean (interval[vec 0:real^1,vec 1])` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
    SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY; CONTINUOUS_MAP_LIFT] THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; IMAGE_LIFT_REAL_INTERVAL] THEN
    REWRITE_TAC[LIFT_NUM; SUBSET_REFL];
    REWRITE_TAC[pathfinish; pathstart; o_THM; LIFT_NUM] THEN MESON_TAC[]]);;

let MOI_FH1_LOOP_CYCLE = prove
 (`!top (g:real->A).
      path_in top g /\ g(&0) = g(&1)
      ==> singular_relcycle (1,top,{}) (frag_of (path_simplex g))`,
  REWRITE_TAC[path_simplex; SINGULAR_RELCYCLE_LOOP]);;

let MOI_FH1_LOOP_CLASS_IN_CARRIER = prove
 (`!top (g:real->A).
      path_in top g /\ g(&0) = g(&1)
      ==> homologous_rel (1,top,{}) (frag_of (path_simplex g)) IN
          group_carrier (homology_group(&1,top))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[homology_group; RELATIVE_HOMOLOGY_GROUP; IN_ELIM_THM] THEN
  EXISTS_TAC `frag_of (path_simplex (g:real->A))` THEN
  ASM_SIMP_TAC[MOI_FH1_LOOP_CYCLE]);;

let MOI_FH1_CONST_LOOP_CLASS = prove
 (`!top (a:A).
      a IN topspace top
      ==> homologous_rel (1,top,{}) (frag_of (path_simplex (\t. a))) =
          group_id (homology_group(&1,top))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[homology_group; RELATIVE_HOMOLOGY_GROUP] THEN
  ASM_SIMP_TAC[HOMOLOGOUS_REL_EQ_RELBOUNDARY; SINGULAR_RELBOUNDARY_CONST_PATH]);;

let MOI_FH1_HOM_INDUCED_LOOP = prove
 (`!top top' (f:A->B) (g:real->A).
      continuous_map (top,top') f /\ path_in top g /\ g(&0) = g(&1)
      ==> hom_induced (&1) (top,{}) (top',{}) f
            (homologous_rel (1,top,{}) (frag_of (path_simplex g))) =
          homologous_rel (1,top',{}) (frag_of (path_simplex (f o g)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`1`; `top:A topology`; `{}:A->bool`; `top':B topology`;
                 `{}:B->bool`; `f:A->B`; `frag_of (path_simplex (g:real->A))`]
                HOM_INDUCED_CHAIN_MAP) THEN
  ASM_SIMP_TAC[IMAGE_CLAUSES; EMPTY_SUBSET; MOI_FH1_LOOP_CYCLE] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[CHAIN_MAP_OF] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[simplex_map; path_simplex; RESTRICTION_EXTENSION] THEN
  SIMP_TAC[o_THM; RESTRICTION]);;

let MOI_FH1_LOOP_CLASS_HOMOTOPIC = prove
 (`!s p q:real^1->real^N.
      homotopic_loops s p q
      ==> homologous_rel (1,subtopology euclidean s,{})
            (frag_of (path_simplex (p o lift))) =
          homologous_rel (1,subtopology euclidean s,{})
            (frag_of (path_simplex (q o lift)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_FH1_HOMOTOPIC_LOOPS_LIFT) THEN
  DISCH_THEN(MP_TAC o MATCH_MP HOMOLOGOUS_REL_HOMOTOPIC_LOOPS) THEN
  REWRITE_TAC[GSYM path_simplex; HOMOLOGOUS_REL_EQ; ETA_AX]);;

let MOI_FH1_JOINPATHS_LIFT = prove
 (`!g h:real^1->real^N.
      (g ++ h) o lift =
      (\t. if t <= &1 / &2 then (g o lift) (&2 * t) else (h o lift) (&2 * t - &1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; joinpaths; LIFT_DROP] THEN
  REWRITE_TAC[LIFT_CMUL; LIFT_SUB; LIFT_NUM]);;

let MOI_FH1_REVERSEPATH_LIFT = prove
 (`!g:real^1->real^N. reversepath g o lift = (\t. (g o lift) (&1 - t))`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; reversepath; LIFT_SUB; LIFT_NUM]);;

let MOI_FH1_LOOP_CLASS_JOIN = prove
 (`!s g h:real^1->real^N.
      path g /\ path_image g SUBSET s /\ path h /\ path_image h SUBSET s /\
      pathfinish g = pathstart g /\ pathstart h = pathstart g /\
      pathfinish h = pathstart g
      ==> homologous_rel (1,subtopology euclidean s,{})
            (frag_of (path_simplex ((g ++ h) o lift))) =
          group_mul (homology_group(&1,subtopology euclidean s))
            (homologous_rel (1,subtopology euclidean s,{})
               (frag_of (path_simplex (g o lift))))
            (homologous_rel (1,subtopology euclidean s,{})
               (frag_of (path_simplex (h o lift))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology euclidean (s:real^N->bool)`; `pathstart(g:real^1->real^N)`;
                 `(g:real^1->real^N) o lift`; `(h:real^1->real^N) o lift`]
                HOMOLOGY_GROUP_MUL_JOINPATHS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM PATH_EUCLIDEAN] THEN
    REWRITE_TAC[o_THM; LIFT_NUM] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
    ASM_REWRITE_TAC[pathstart];
    DISCH_THEN(fun th -> REWRITE_TAC[path_simplex; MOI_FH1_JOINPATHS_LIFT; th])]);;

let MOI_FH1_LOOP_CLASS_REVERSEPATH = prove
 (`!s g:real^1->real^N.
      path g /\ path_image g SUBSET s
      ==> homologous_rel (1,subtopology euclidean s,{})
            (frag_of (path_simplex (reversepath g o lift))) =
          group_inv (homology_group(&1,subtopology euclidean s))
            (homologous_rel (1,subtopology euclidean s,{})
               (frag_of (path_simplex (g o lift))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology euclidean (s:real^N->bool)`;
                 `(g:real^1->real^N) o lift`] HOMOLOGOUS_REL_REVERSEPATH) THEN
  ASM_REWRITE_TAC[GSYM PATH_EUCLIDEAN] THEN
  REWRITE_TAC[homology_group; RELATIVE_HOMOLOGY_GROUP_INV_CLASS] THEN
  REWRITE_TAC[MOI_FH1_REVERSEPATH_LIFT; HOMOLOGOUS_REL_EQ] THEN
  REWRITE_TAC[homologous_rel] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  CONV_TAC FRAG_MODULE);;

(* ------------------------------------------------------------------------- *)
(* Loops in the circle, the solid torus model and the torus model,           *)
(* classified by winding numbers of the circle coordinates (real^2 =         *)
(* complex).                                                                 *)
(* ------------------------------------------------------------------------- *)

let MOI_FH1_ORIGIN_NOT_IN_CIRCLE = prove
 (`~((vec 0:real^2) IN sphere(vec 0,&1))`,
  REWRITE_TAC[IN_SPHERE_0; NORM_0] THEN REAL_ARITH_TAC);;

let MOI_FH1_CIRCLE_HOMOTOPIC_LOOPS_EQ = prove
 (`!g h:real^1->real^2.
      path g /\ pathfinish g = pathstart g /\ path_image g SUBSET sphere(vec 0,&1) /\
      path h /\ pathfinish h = pathstart h /\ path_image h SUBSET sphere(vec 0,&1)
      ==> (homotopic_loops (sphere(vec 0,&1)) g h <=>
           winding_number(g,vec 0) = winding_number(h,vec 0))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sphere(vec 0:real^2,&1) SUBSET (:real^2) DELETE vec 0` ASSUME_TAC THENL
   [MP_TAC MOI_FH1_ORIGIN_NOT_IN_CIRCLE THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~((vec 0:real^2) IN path_image g) /\ ~((vec 0:real^2) IN path_image h)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC MOI_FH1_ORIGIN_NOT_IN_CIRCLE THEN ASM SET_TAC[]; ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC WINDING_NUMBER_HOMOTOPIC_LOOPS THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_SUBSET THEN
    EXISTS_TAC `sphere(vec 0:real^2,&1)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[WINDING_NUMBER_HOMOTOPIC_LOOPS_EQ] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`vec 0:real^2`; `&1`] SPHERE_RETRACT_OF_PUNCTURED_UNIVERSE) THEN
  REWRITE_TAC[REAL_LT_01; retract_of; retraction] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^2->real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `homotopic_loops (sphere(vec 0:real^2,&1)) ((r:real^2->real^2) o (g:real^1->real^2)) (r o (h:real^1->real^2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE THEN
    EXISTS_TAC `(:real^2) DELETE vec 0` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `homotopic_loops (sphere(vec 0:real^2,&1)) g ((r:real^2->real^2) o (g:real^1->real^2)) /\
    homotopic_loops (sphere(vec 0:real^2,&1)) h (r o (h:real^1->real^2))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC HOMOTOPIC_LOOPS_EQ THEN ASM_REWRITE_TAC[o_THM] THEN
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[path_image]) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_MESON_TAC[HOMOTOPIC_LOOPS_TRANS; HOMOTOPIC_LOOPS_SYM]);;

let MOI_FH1_CIRCLE_NULLHOMOTOPIC = prove
 (`!g:real^1->real^2.
      path g /\ pathfinish g = pathstart g /\ path_image g SUBSET sphere(vec 0,&1)
      ==> (homotopic_loops (sphere(vec 0,&1)) g (linepath(pathstart g,pathstart g)) <=>
           winding_number(g,vec 0) = Cx(&0))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `pathstart(g:real^1->real^2) IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^1->real^2`; `linepath(pathstart g:real^2,pathstart g)`]
                MOI_FH1_CIRCLE_HOMOTOPIC_LOOPS_EQ) THEN
  ASM_REWRITE_TAC[PATH_LINEPATH; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                  PATH_IMAGE_LINEPATH; SEGMENT_REFL; SING_SUBSET] THEN
  DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC WINDING_NUMBER_TRIVIAL THEN
  ASM_MESON_TAC[MOI_FH1_ORIGIN_NOT_IN_CIRCLE]);;

let MOI_FH1_HOMOTOPIC_LOOPS_PASTECART = prove
 (`!(s:real^M->bool) (t:real^N->bool) p1 p2 q1 q2.
      homotopic_loops s p1 q1 /\ homotopic_loops t p2 q2
      ==> homotopic_loops (s PCROSS t) (\x. pastecart (p1 x) (p2 x))
                                       (\x. pastecart (q1 x) (q2 x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HOMOTOPIC_LOOPS] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `h1:real^(1,1)finite_sum->real^M` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `h2:real^(1,1)finite_sum->real^N` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `\z. pastecart ((h1:real^(1,1)finite_sum->real^M) z)
                            ((h2:real^(1,1)finite_sum->real^N) z)` THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_PASTECART; ETA_AX] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; FORALL_IN_IMAGE]) THEN ASM_SIMP_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish; o_THM]) THEN
    ASM_SIMP_TAC[pathstart; pathfinish; o_THM; PASTECART_INJ]]);;

let MOI_FH1_IN_PCROSS = prove
 (`!(s:real^M->bool) (t:real^N->bool) z.
      z IN s PCROSS t <=> fstcart z IN s /\ sndcart z IN t`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM PASTECART_FST_SND] THEN
  REWRITE_TAC[PASTECART_IN_PCROSS]);;

let MOI_FH1_COMPOSE_LINEPATH_REFL = prove
 (`!(f:real^M->real^N) a. f o linepath(a,a) = linepath(f a,f a)`,
  REWRITE_TAC[LINEPATH_REFL; o_DEF]);;

let MOI_FH1_LOOP_COMPONENTS = prove
 (`!(p:real^1->real^(M,N)finite_sum) s t.
      path p /\ pathfinish p = pathstart p /\ path_image p SUBSET s PCROSS t
      ==> path (fstcart o p) /\ pathfinish (fstcart o p) = pathstart (fstcart o p) /\
          path_image (fstcart o p) SUBSET s /\
          path (sndcart o p) /\ pathfinish (sndcart o p) = pathstart (sndcart o p) /\
          path_image (sndcart o p) SUBSET t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATH_IMAGE_COMPOSE] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN
      ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART] THEN NO_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; MOI_FH1_IN_PCROSS]) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]);;

let MOI_FH1_HOMOTOPIC_LOOPS_PROJ = prove
 (`!(p:real^1->real^(M,N)finite_sum) q s t.
      homotopic_loops (s PCROSS t) p q
      ==> homotopic_loops s (fstcart o p) (fstcart o q) /\
          homotopic_loops t (sndcart o p) (sndcart o q)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE THEN
  EXISTS_TAC `(s:real^M->bool) PCROSS (t:real^N->bool)` THEN
  ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; MOI_FH1_IN_PCROSS] THEN SIMP_TAC[]);;

let MOI_FH1_CONVEX_NULLHOMOTOPIC = prove
 (`!(g:real^1->real^N) s.
      convex s /\ path g /\ pathfinish g = pathstart g /\ path_image g SUBSET s
      ==> homotopic_loops s g (linepath(pathstart g,pathstart g))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMOTOPIC_LOOPS_LINEAR THEN
  ASM_REWRITE_TAC[PATH_LINEPATH; PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
  REWRITE_TAC[LINEPATH_REFL] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[CONVEX_CONTAINS_SEGMENT]) THEN
  CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[path_image]) THEN ASM SET_TAC[];
    ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; SUBSET]]);;

let SOLID_TORUS_MODEL_NULLHOMOTOPIC_WINDING = prove
 (`!p:real^1->real^(2,2)finite_sum.
     path p /\ pathfinish p = pathstart p /\
     path_image p SUBSET cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)
     ==> (homotopic_loops (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1))
                          p (linepath(pathstart p,pathstart p)) <=>
          winding_number(sndcart o p,vec 0) = Cx(&0))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FH1_LOOP_COMPONENTS) THEN
  MP_TAC(ISPEC `sndcart o (p:real^1->real^(2,2)finite_sum)`
               MOI_FH1_CIRCLE_NULLHOMOTOPIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[PATHSTART_COMPOSE] THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o CONJUNCT2 o MATCH_MP MOI_FH1_HOMOTOPIC_LOOPS_PROJ) THEN
    REWRITE_TAC[MOI_FH1_COMPOSE_LINEPATH_REFL];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`fstcart o (p:real^1->real^(2,2)finite_sum)`; `cball(vec 0:real^2,&1)`]
                MOI_FH1_CONVEX_NULLHOMOTOPIC) THEN
  ASM_REWRITE_TAC[CONVEX_CBALL; PATHSTART_COMPOSE] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`cball(vec 0:real^2,&1)`; `sphere(vec 0:real^2,&1)`;
                 `fstcart o (p:real^1->real^(2,2)finite_sum)`;
                 `sndcart o (p:real^1->real^(2,2)finite_sum)`;
                 `linepath(fstcart(pathstart p):real^2,
                           fstcart(pathstart(p:real^1->real^(2,2)finite_sum)))`;
                 `linepath(sndcart(pathstart p):real^2,
                           sndcart(pathstart(p:real^1->real^(2,2)finite_sum)))`]
                MOI_FH1_HOMOTOPIC_LOOPS_PASTECART) THEN
  ASM_REWRITE_TAC[o_THM; PASTECART_FST_SND; ETA_AX; LINEPATH_REFL]);;

let TORUS_MODEL_NULLHOMOTOPIC_WINDING = prove
 (`!p:real^1->real^(2,2)finite_sum.
     path p /\ pathfinish p = pathstart p /\
     path_image p SUBSET sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)
     ==> (homotopic_loops (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1))
                          p (linepath(pathstart p,pathstart p)) <=>
          winding_number(fstcart o p,vec 0) = Cx(&0) /\
          winding_number(sndcart o p,vec 0) = Cx(&0))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FH1_LOOP_COMPONENTS) THEN
  MP_TAC(ISPEC `fstcart o (p:real^1->real^(2,2)finite_sum)`
               MOI_FH1_CIRCLE_NULLHOMOTOPIC) THEN
  MP_TAC(ISPEC `sndcart o (p:real^1->real^(2,2)finite_sum)`
               MOI_FH1_CIRCLE_NULLHOMOTOPIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[PATHSTART_COMPOSE] THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o MATCH_MP MOI_FH1_HOMOTOPIC_LOOPS_PROJ) THEN
    REWRITE_TAC[MOI_FH1_COMPOSE_LINEPATH_REFL];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`sphere(vec 0:real^2,&1)`; `sphere(vec 0:real^2,&1)`;
                 `fstcart o (p:real^1->real^(2,2)finite_sum)`;
                 `sndcart o (p:real^1->real^(2,2)finite_sum)`;
                 `linepath(fstcart(pathstart p):real^2,
                           fstcart(pathstart(p:real^1->real^(2,2)finite_sum)))`;
                 `linepath(sndcart(pathstart p):real^2,
                           sndcart(pathstart(p:real^1->real^(2,2)finite_sum)))`]
                MOI_FH1_HOMOTOPIC_LOOPS_PASTECART) THEN
  ASM_REWRITE_TAC[o_THM; PASTECART_FST_SND; ETA_AX; LINEPATH_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Spines of solid tori and ends of annuli carry all loops (a straight-line  *)
(* deformation in the model), and loops_carried implies carries_h1 (every    *)
(* H_1 class of a path-connected space is a loop class, ATOP_HUREWICZ1, and  *)
(* loop classes are invariant under free homotopy).                          *)
(* ------------------------------------------------------------------------- *)

let MOI_FH1_LOOPS_CARRIED_DEFORM = prove
 (`!(m:real^M->bool) (s:real^N->bool) k f g r.
      homeomorphism (m,s) (f,g) /\ k SUBSET m /\
      r continuous_on m /\ IMAGE r m SUBSET k /\
      (!x. x IN m ==> segment[x,r x] SUBSET m)
      ==> loops_carried (IMAGE f k) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HOMEOMORPHISM] THEN STRIP_TAC THEN
  REWRITE_TAC[loops_carried] THEN X_GEN_TAC `p:real^1->real^N` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `path ((g:real^N->real^M) o (p:real^1->real^N)) /\
    pathfinish (g o p) = pathstart (g o p) /\ path_image (g o p) SUBSET m`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATH_IMAGE_COMPOSE] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `path ((r:real^M->real^M) o (g:real^N->real^M) o (p:real^1->real^N)) /\
    pathfinish (r o g o p) = pathstart (r o g o p) /\ path_image (r o g o p) SUBSET k`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `m:real^M->bool` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE] THEN
      ASM_REWRITE_TAC[GSYM PATHSTART_COMPOSE; GSYM PATHFINISH_COMPOSE];
      REWRITE_TAC[PATH_IMAGE_COMPOSE] THEN
      UNDISCH_TAC `path_image ((g:real^N->real^M) o (p:real^1->real^N)) SUBSET m` THEN
      UNDISCH_TAC `IMAGE (r:real^M->real^M) m SUBSET k` THEN
      REWRITE_TAC[PATH_IMAGE_COMPOSE] THEN SET_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `(f:real^M->real^N) o (r:real^M->real^M) o (g:real^N->real^M) o
              (p:real^1->real^N)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `m:real^M->bool` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `path_image ((r:real^M->real^M) o (g:real^N->real^M) o
                             (p:real^1->real^N)) SUBSET k` THEN
    UNDISCH_TAC `(k:real^M->bool) SUBSET m` THEN SET_TAC[];
    REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE] THEN
    AP_TERM_TAC THEN ASM_REWRITE_TAC[GSYM PATHSTART_COMPOSE; GSYM PATHFINISH_COMPOSE];
    REWRITE_TAC[PATH_IMAGE_COMPOSE] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    ASM_REWRITE_TAC[GSYM PATH_IMAGE_COMPOSE];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
  EXISTS_TAC `(f:real^M->real^N) o (g:real^N->real^M) o (p:real^1->real^N)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_LOOPS_EQ THEN ASM_REWRITE_TAC[o_THM] THEN
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `path_image (p:real^1->real^N) SUBSET s` THEN
    UNDISCH_TAC `(t:real^1) IN interval[vec 0,vec 1]` THEN
    REWRITE_TAC[path_image] THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE THEN
  EXISTS_TAC `m:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HOMOTOPIC_LOOPS_LINEAR THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `path_image ((g:real^N->real^M) o (p:real^1->real^N)) SUBSET m` THEN
  UNDISCH_TAC `(t:real^1) IN interval[vec 0,vec 1]` THEN
  REWRITE_TAC[path_image; IMAGE_o] THEN SET_TAC[]);;

let MOI_FH1_SPINE_RETRACT = prove
 (`!p:real^2.
      p IN cball(vec 0,&1)
      ==> ({p} PCROSS sphere(vec 0:real^2,&1)) SUBSET
          cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1) /\
          (\y:real^(2,2)finite_sum. pastecart p (sndcart y)) continuous_on
          (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) /\
          IMAGE (\y:real^(2,2)finite_sum. pastecart p (sndcart y))
                (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) SUBSET
          {p} PCROSS sphere(vec 0:real^2,&1) /\
          (!x. x IN {p} PCROSS sphere(vec 0:real^2,&1)
               ==> (\y:real^(2,2)finite_sum. pastecart p (sndcart y)) x = x) /\
          (!x. x IN cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)
               ==> segment[x,(\y:real^(2,2)finite_sum. pastecart p (sndcart y)) x]
                   SUBSET cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1))`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; MOI_FH1_IN_PCROSS; IN_SING] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
    SIMP_TAC[CONTINUOUS_ON_CONST; LINEAR_CONTINUOUS_ON; LINEAR_SNDCART];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; MOI_FH1_IN_PCROSS; IN_SING] THEN
    SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART];
    REWRITE_TAC[FORALL_IN_PCROSS; IN_SING] THEN
    SIMP_TAC[SNDCART_PASTECART];
    REWRITE_TAC[FORALL_IN_PCROSS; SNDCART_PASTECART] THEN
    MAP_EVERY X_GEN_TAC [`a:real^2`; `b:real^2`] THEN STRIP_TAC THEN
    REWRITE_TAC[SUBSET; IN_SEGMENT] THEN X_GEN_TAC `z:real^(2,2)finite_sum` THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[GSYM PASTECART_CMUL; PASTECART_ADD; PASTECART_IN_PCROSS] THEN
    REWRITE_TAC[VECTOR_ARITH `(&1 - u) % b + u % b:real^2 = b`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[convex] CONVEX_CBALL) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let SPINE_LOOPS_CARRIED = prove
 (`!(j:real^N->bool) s. spine j s ==> loops_carried j s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[spine; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`f:real^(2,2)finite_sum->real^N`;
                       `g:real^N->real^(2,2)finite_sum`; `p:real^2`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `p:real^2` MOI_FH1_SPINE_RETRACT) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET]; STRIP_TAC] THEN
  MATCH_MP_TAC MOI_FH1_LOOPS_CARRIED_DEFORM THEN
  MAP_EVERY EXISTS_TAC
   [`cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)`;
    `g:real^N->real^(2,2)finite_sum`;
    `\y:real^(2,2)finite_sum. pastecart (p:real^2) (sndcart y)`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_FH1_SQUARE_ANNULUS_INFNORM = prove
 (`!x:real^2.
      x IN interval[--vector[&2;&2],vector[&2;&2]] DIFF
           interval(--vector[&1;&1],vector[&1;&1]) <=>
      &1 <= infnorm x /\ infnorm x <= &2`,
  REWRITE_TAC[IN_DIFF; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2;
              VECTOR_NEG_COMPONENT; INFNORM_2] THEN
  REAL_ARITH_TAC);;

let MOI_FH1_SQUARE_FRONTIER_INFNORM = prove
 (`!c x:real^2.
      &0 < c
      ==> (x IN relative_frontier(interval[--vector[c;c],vector[c;c]]) <=>
           infnorm x = c)`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RELATIVE_FRONTIER_NONEMPTY_INTERIOR o
    rand o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; INTERVAL_NE_EMPTY] THEN
    REWRITE_TAC[DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_NEG_COMPONENT] THEN
    ASM_REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[FRONTIER_CLOSED_INTERVAL; IN_DIFF; IN_INTERVAL; DIMINDEX_2; FORALL_2;
              VECTOR_2; VECTOR_NEG_COMPONENT; INFNORM_2] THEN
  ASM_REAL_ARITH_TAC);;

let MOI_FH1_CONTINUOUS_ON_INFNORM_SCALE = prove
 (`!c s. (!x:real^N. x IN s ==> ~(infnorm x = &0))
         ==> (\x. (c * inv(infnorm x)) % x) continuous_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
  REWRITE_TAC[CONTINUOUS_ON_ID] THEN
  REWRITE_TAC[o_DEF; LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
  MP_TAC(ISPECL [`infnorm:real^N->real`; `s:real^N->bool`] CONTINUOUS_ON_INV) THEN
  ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
  REWRITE_TAC[REWRITE_RULE[o_DEF] CONTINUOUS_AT_LIFT_INFNORM]);;

let MOI_FH1_INFNORM_SEGMENT = prove
 (`!x:real^2 y c.
      &1 <= infnorm x /\ infnorm x <= &2 /\ &1 <= c /\ c <= &2 /\
      y IN segment[x,(c * inv(infnorm x)) % x]
      ==> &1 <= infnorm y /\ infnorm y <= &2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC))))) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_ASSOC; GSYM VECTOR_ADD_RDISTRIB; INFNORM_MUL] THEN
  ABBREV_TAC `n = infnorm(x:real^2)` THEN
  SUBGOAL_THEN `&0 < n` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs((&1 - u) + u * c * inv n) * n = (&1 - u) * n + u * c`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `&0 <= (&1 - u) + u * c * inv n` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC];
      ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
      UNDISCH_TAC `&0 < n` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= (&1 - u) * (n - &1) /\ &0 <= (&1 - u) * (&2 - n) /\
    &0 <= u * (c - &1) /\ &0 <= u * (&2 - c)`
  MP_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let MOI_FH1_ANNULUS_RETRACT = prove
 (`!c. c = &1 \/ c = &2
       ==> relative_frontier(interval[--vector[c;c],vector[c;c]]) SUBSET
           interval[--vector[&2;&2],vector[&2;&2]] DIFF
           interval(--vector[&1;&1],vector[&1;&1]) /\
           (\x:real^2. (c * inv(infnorm x)) % x) continuous_on
           (interval[--vector[&2;&2],vector[&2;&2]] DIFF
            interval(--vector[&1;&1],vector[&1;&1])) /\
           IMAGE (\x:real^2. (c * inv(infnorm x)) % x)
                 (interval[--vector[&2;&2],vector[&2;&2]] DIFF
                  interval(--vector[&1;&1],vector[&1;&1])) SUBSET
           relative_frontier(interval[--vector[c;c],vector[c;c]]) /\
           (!x. x IN relative_frontier(interval[--vector[c;c],vector[c;c]])
                ==> (\x:real^2. (c * inv(infnorm x)) % x) x = x) /\
           (!x. x IN interval[--vector[&2;&2],vector[&2;&2]] DIFF
                     interval(--vector[&1;&1],vector[&1;&1])
                ==> segment[x,(\x:real^2. (c * inv(infnorm x)) % x) x] SUBSET
                    interval[--vector[&2;&2],vector[&2;&2]] DIFF
                    interval(--vector[&1;&1],vector[&1;&1]))`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < c /\ &1 <= c /\ c <= &2` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; MOI_FH1_SQUARE_FRONTIER_INFNORM;
               MOI_FH1_SQUARE_ANNULUS_INFNORM] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FH1_CONTINUOUS_ON_INFNORM_SCALE THEN
    REWRITE_TAC[MOI_FH1_SQUARE_ANNULUS_INFNORM] THEN REAL_ARITH_TAC;
    X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
    REWRITE_TAC[INFNORM_MUL; REAL_ABS_MUL; REAL_ABS_INV; REAL_ABS_INFNORM] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < c ==> abs c = c`] THEN
    SUBGOAL_THEN `~(infnorm(x:real^2) = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN X_GEN_TAC `y:real^2` THEN
    DISCH_TAC THEN MATCH_MP_TAC MOI_FH1_INFNORM_SEGMENT THEN
    MAP_EVERY EXISTS_TAC [`x:real^2`; `c:real`] THEN ASM_REWRITE_TAC[]]);;

let ANNULUS_LOOPS_CARRIED = prove
 (`!(a:real^N->bool) j0 j1.
     pl_annulus_with_ends a j0 j1 ==> loops_carried j0 a /\ loops_carried j1 a`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[pl_annulus_with_ends; pl_homeomorphism; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`f:real^2->real^N`; `g:real^N->real^2`] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC MOI_FH1_LOOPS_CARRIED_DEFORM THEN
  MAP_EVERY EXISTS_TAC
   [`interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
     interval(--vector[&1;&1]:real^2,vector[&1;&1])`; `g:real^N->real^2`] THENL
   [EXISTS_TAC `\x:real^2. (&1 * inv(infnorm x)) % x` THEN
    MP_TAC(SPEC `&1` MOI_FH1_ANNULUS_RETRACT);
    EXISTS_TAC `\x:real^2. (&2 * inv(infnorm x)) % x` THEN
    MP_TAC(SPEC `&2` MOI_FH1_ANNULUS_RETRACT)] THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let MOI_FH1_H1_LOOP_REPRESENTATIVE = prove
 (`!(s:real^N->bool) a z.
      path_connected s /\ a IN s /\
      z IN group_carrier(homology_group(&1,subtopology euclidean s))
      ==> ?g:real^1->real^N.
            path g /\ path_image g SUBSET s /\ pathstart g = a /\ pathfinish g = a /\
            z = homologous_rel (1,subtopology euclidean s,{})
                  (frag_of (path_simplex (g o lift)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology euclidean (s:real^N->bool)`; `a:real^N`]
    (REWRITE_RULE[ATOP_HUREWICZ1_STATEMENT] ATOP_HUREWICZ1)) THEN
  ASM_REWRITE_TAC[PATH_CONNECTED_SPACE_EUCLIDEAN_SUBTOPOLOGY;
                  TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  DISCH_THEN(MP_TAC o SPEC `z:((num->real)->real^N)frag->bool` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(g:real->real^N) o drop` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PATH_IN_EUCLIDEAN]) THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[pathstart; pathfinish; o_THM; DROP_VEC] THEN
  REWRITE_TAC[path_simplex] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[RESTRICTION_EXTENSION; o_THM; LIFT_DROP]);;

let MOI_FH1_NULLHOMOTOPIC_LOOP_CLASS = prove
 (`!s g:real^1->real^N.
      homotopic_loops s g (linepath(pathstart g,pathstart g))
      ==> homologous_rel (1,subtopology euclidean s,{})
            (frag_of (path_simplex (g o lift))) =
          group_id (homology_group(&1,subtopology euclidean s))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP MOI_FH1_LOOP_CLASS_HOMOTOPIC) THEN
  REWRITE_TAC[LINEPATH_REFL; o_DEF] THEN
  MATCH_MP_TAC MOI_FH1_CONST_LOOP_CLASS THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_SUBSET) THEN
  REWRITE_TAC[PATH_IMAGE_LINEPATH; SEGMENT_REFL] THEN SET_TAC[]);;

let LOOPS_CARRIED_IMP_CARRIES_H1 = prove
 (`!(j:real^N->bool) s.
     j SUBSET s /\ path_connected s /\ loops_carried j s ==> carries_h1 j s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[carries_h1; group_image] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`&1:int`; `subtopology euclidean (j:real^N->bool)`;
                   `subtopology euclidean (s:real^N->bool)`; `\x:real^N. x`]
                  GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY) THEN
    SIMP_TAC[group_homomorphism];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE] THEN
  X_GEN_TAC `z:((num->real)->real^N)frag->bool` THEN DISCH_TAC THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [SUBGOAL_THEN
     `z = group_id (homology_group(&1,subtopology euclidean (s:real^N->bool)))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC ATOP_TRIVIAL_GROUP_ELEMENT THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`&1:int`; `subtopology euclidean (s:real^N->bool)`]
                    TRIVIAL_RELATIVE_HOMOLOGY_GROUP_TOPSPACE) THEN
      ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; homology_group];
      ALL_TAC] THEN
    EXISTS_TAC `group_id (homology_group(&1,subtopology euclidean (j:real^N->bool)))` THEN
    REWRITE_TAC[GROUP_ID] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC ATOP_GROUP_HOM_ID THEN
    REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `a:real^N` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `a:real^N`; `z:((num->real)->real^N)frag->bool`]
                MOI_FH1_H1_LOOP_REPRESENTATIVE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^N` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `loops_carried (j:real^N->bool) s` THEN REWRITE_TAC[loops_carried] THEN
  DISCH_THEN(MP_TAC o SPEC `g:real^1->real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^1->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `homologous_rel (1,subtopology euclidean (j:real^N->bool),{})
                (frag_of (path_simplex ((q:real^1->real^N) o lift)))` THEN
  SUBGOAL_THEN `path_in (subtopology euclidean (j:real^N->bool)) ((q:real^1->real^N) o lift) /\
                (q o lift) (&0) = (q o lift) (&1)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM PATH_EUCLIDEAN; o_THM; LIFT_NUM] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_FH1_LOOP_CLASS_IN_CARRIER] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MOI_FH1_HOM_INDUCED_LOOP o rand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[ATOP_CONTINUOUS_MAP_INCLUSION];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[o_ASSOC; I_O_ID; GSYM I_DEF] THEN
  MATCH_MP_TAC MOI_FH1_LOOP_CLASS_HOMOTOPIC THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* H_1 of the circle is infinite cyclic (homology.ml spheres); a             *)
(* straight-line deformation retraction of the model onto k makes the        *)
(* inclusion of the image of k a homotopy equivalence, hence an H_1          *)
(* isomorphism; spines of solid tori and ends of annuli.                     *)
(* ------------------------------------------------------------------------- *)

let MOI_FH1_H1_CIRCLE = prove
 (`homology_group(&1,subtopology euclidean (sphere(vec 0:real^2,&1)))
   isomorphic_group integer_group`,
  SUBGOAL_THEN
   `nsphere 1 homeomorphic_space subtopology euclidean (sphere(vec 0:real^2,&1))`
  ASSUME_TAC THENL
   [MP_TAC(INST_TYPE [`:2`,`:N`]
     (SPEC `dimindex(:2)` HOMEOMORPHIC_MAPS_NSPHERE_EUCLIDEAN_SPHERE)) THEN
    REWRITE_TAC[GSYM SIMPLE_IMAGE; IN_NUMSEG; SPAN_STDBASIS; LE_REFL; INTER_UNIV] THEN
    REWRITE_TAC[DIMINDEX_2] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[homeomorphic_space] THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(ISPECL
   [`homology_group(&1,subtopology euclidean (sphere(vec 0:real^2,&1)))`;
    `homology_group(&1,nsphere 1)`; `integer_group`] ISOMORPHIC_GROUP_TRANS) THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[ISOMORPHIC_GROUP_SYM] THEN
    MATCH_MP_TAC HOMEOMORPHIC_SPACE_IMP_ISOMORPHIC_HOMOLOGY_GROUPS THEN
    ASM_REWRITE_TAC[];
    MP_TAC(SPEC `1` (CONJUNCT1 REDUCED_HOMOLOGY_GROUP_NSPHERE)) THEN
    SIMP_TAC[UN_REDUCED_HOMOLOGY_GROUP; INT_OF_NUM_EQ; ARITH_EQ]]);;

let MOI_FH1_H1_DEFORM_ISO = prove
 (`!(m:real^M->bool) (s:real^N->bool) k f g r.
      homeomorphism (m,s) (f,g) /\ k SUBSET m /\
      r continuous_on m /\ IMAGE r m SUBSET k /\ (!x. x IN k ==> r x = x) /\
      (!x. x IN m ==> segment[x,r x] SUBSET m)
      ==> group_isomorphism
            (homology_group(&1,subtopology euclidean (IMAGE f k)),
             homology_group(&1,subtopology euclidean s))
            (hom_induced (&1) (subtopology euclidean (IMAGE f k),{})
                              (subtopology euclidean s,{}) (\x. x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HOMEOMORPHISM] THEN STRIP_TAC THEN
  MATCH_MP_TAC HOMOTOPY_EQUIVALENCE_HOMOLOGY_GROUP_ISOMORPHISM THEN
  EXISTS_TAC `(f:real^M->real^N) o (r:real^M->real^M) o (g:real^N->real^M)` THEN
  SUBGOAL_THEN `IMAGE (f:real^M->real^N) k SUBSET s` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^M->real^N) continuous_on k` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((f:real^M->real^N) o (r:real^M->real^M) o (g:real^N->real^M)) continuous_on s /\
    IMAGE (f o r o g) s SUBSET IMAGE f k`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `m:real^M->bool` THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `k:real^M->bool` THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `IMAGE (g:real^N->real^M) s SUBSET m` THEN
        UNDISCH_TAC `IMAGE (r:real^M->real^M) m SUBSET k` THEN
        REWRITE_TAC[IMAGE_o] THEN SET_TAC[]];
      UNDISCH_TAC `IMAGE (g:real^N->real^M) s SUBSET m` THEN
      UNDISCH_TAC `IMAGE (r:real^M->real^M) m SUBSET k` THEN
      REWRITE_TAC[IMAGE_o] THEN SET_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[ATOP_CONTINUOUS_MAP_INCLUSION];
    ASM_REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2];
    MATCH_MP_TAC HOMOTOPIC_WITH_EQ THEN
    MAP_EVERY EXISTS_TAC [`I:real^N->real^N`; `I:real^N->real^N`] THEN
    REWRITE_TAC[HOMOTOPIC_WITH_REFL; I_DEF; CONTINUOUS_MAP_ID] THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; FORALL_IN_IMAGE; o_THM] THEN
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^M) IN m` ASSUME_TAC THENL
     [ASM SET_TAC[]; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_EQ THEN
  MAP_EVERY EXISTS_TAC
   [`((f:real^M->real^N) o (r:real^M->real^M)) o (g:real^N->real^M)`;
    `((f:real^M->real^N) o (\x:real^M. x)) o (g:real^N->real^M)`] THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; o_THM; I_THM] THEN
  ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_MAP_RIGHT THEN
  EXISTS_TAC `\h:real^M->real^N. T` THEN
  EXISTS_TAC `subtopology euclidean (m:real^M->bool)` THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_MAP_LEFT THEN
  EXISTS_TAC `\h:real^M->real^M. T` THEN
  EXISTS_TAC `subtopology euclidean (m:real^M->bool)` THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_LINEAR THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_ID] THEN
  ONCE_REWRITE_TAC[SEGMENT_SYM] THEN ASM_SIMP_TAC[]);;

let MOI_FH1_H1_ISO_CONSEQUENCES = prove
 (`!(j:real^N->bool) s.
      group_isomorphism (homology_group(&1,subtopology euclidean j),
                         homology_group(&1,subtopology euclidean s))
        (hom_induced (&1) (subtopology euclidean j,{})
                          (subtopology euclidean s,{}) (\x. x)) /\
      j homeomorphic sphere(vec 0:real^2,&1)
      ==> homology_group(&1,subtopology euclidean s) isomorphic_group integer_group /\
          carries_h1 j s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC(ISPECL
     [`homology_group(&1,subtopology euclidean (s:real^N->bool))`;
      `homology_group(&1,subtopology euclidean (j:real^N->bool))`;
      `integer_group`] ISOMORPHIC_GROUP_TRANS) THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[ISOMORPHIC_GROUP_SYM] THEN REWRITE_TAC[isomorphic_group] THEN
      ASM_MESON_TAC[];
      MATCH_MP_TAC(ISPECL
       [`homology_group(&1,subtopology euclidean (j:real^N->bool))`;
        `homology_group(&1,subtopology euclidean (sphere(vec 0:real^2,&1)))`;
        `integer_group`] ISOMORPHIC_GROUP_TRANS) THEN
      REWRITE_TAC[MOI_FH1_H1_CIRCLE] THEN
      MATCH_MP_TAC HOMEOMORPHIC_SPACE_IMP_ISOMORPHIC_HOMOLOGY_GROUPS THEN
      ASM_REWRITE_TAC[HOMEOMORPHIC_SPACE_EUCLIDEAN]];
    REWRITE_TAC[carries_h1; group_image] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GROUP_ISOMORPHISM]) THEN
    SIMP_TAC[]]);;

let MOI_FH1_IMAGE_HOMEOMORPHIC = prove
 (`!(m:real^M->bool) (s:real^N->bool) f g k.
      homeomorphism (m,s) (f,g) /\ k SUBSET m ==> IMAGE f k homeomorphic k`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
  REWRITE_TAC[homeomorphic] THEN
  MAP_EVERY EXISTS_TAC [`f:real^M->real^N`; `g:real^N->real^M`] THEN
  MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
  MAP_EVERY EXISTS_TAC [`m:real^M->bool`; `s:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN ASM SET_TAC[]);;

let SPINE_HOMOLOGY_ISOMORPHISM = prove
 (`!(j:real^N->bool) s.
     spine j s
     ==> homology_group(&1,subtopology euclidean s) isomorphic_group integer_group /\
         group_isomorphism (homology_group(&1,subtopology euclidean j),
                            homology_group(&1,subtopology euclidean s))
           (hom_induced (&1) (subtopology euclidean j,{})
                             (subtopology euclidean s,{}) (\x. x)) /\
         carries_h1 j s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `group_isomorphism (homology_group(&1,subtopology euclidean (j:real^N->bool)),
                       homology_group(&1,subtopology euclidean (s:real^N->bool)))
      (hom_induced (&1) (subtopology euclidean j,{})
                        (subtopology euclidean s,{}) (\x. x)) /\
    j homeomorphic sphere(vec 0:real^2,&1)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `spine (j:real^N->bool) s` THEN
    REWRITE_TAC[spine; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`f:real^(2,2)finite_sum->real^N`;
                         `g:real^N->real^(2,2)finite_sum`; `p:real^2`] THEN
    STRIP_TAC THEN
    MP_TAC(SPEC `p:real^2` MOI_FH1_SPINE_RETRACT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FH1_H1_DEFORM_ISO THEN
      MAP_EVERY EXISTS_TAC
       [`cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)`;
        `g:real^N->real^(2,2)finite_sum`;
        `\y:real^(2,2)finite_sum. pastecart (p:real^2) (sndcart y)`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC(ISPECL
       [`IMAGE (f:real^(2,2)finite_sum->real^N) ({p} PCROSS sphere(vec 0:real^2,&1))`;
        `{p:real^2} PCROSS sphere(vec 0:real^2,&1)`;
        `sphere(vec 0:real^2,&1)`] HOMEOMORPHIC_TRANS) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MOI_FH1_IMAGE_HOMEOMORPHIC THEN
        MAP_EVERY EXISTS_TAC
         [`cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)`;
          `s:real^N->bool`; `g:real^N->real^(2,2)finite_sum`] THEN
        ASM_REWRITE_TAC[];
        ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[HOMEOMORPHIC_PCROSS_SING]]];
    MP_TAC(ISPECL [`j:real^N->bool`; `s:real^N->bool`] MOI_FH1_H1_ISO_CONSEQUENCES) THEN
    ASM_REWRITE_TAC[]]);;

let MOI_FH1_SQUARE_FRONTIER_CIRCLE = prove
 (`!c. &0 < c
       ==> relative_frontier(interval[--vector[c;c]:real^2,vector[c;c]]) homeomorphic
           sphere(vec 0:real^2,&1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`interval[--vector[c;c]:real^2,vector[c;c]]`;
                 `cball(vec 0:real^2,&1)`]
                HOMEOMORPHIC_RELATIVE_FRONTIERS_CONVEX_BOUNDED_SETS) THEN
  REWRITE_TAC[CONVEX_INTERVAL; BOUNDED_INTERVAL; CONVEX_CBALL; BOUNDED_CBALL;
              RELATIVE_FRONTIER_CBALL; REAL_OF_NUM_EQ; ARITH_EQ] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  SUBGOAL_THEN
   `~(interior(interval[--vector[c;c]:real^2,vector[c;c]]) = {}) /\
    ~(interior(cball(vec 0:real^2,&1)) = {})`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; INTERVAL_NE_EMPTY; INTERIOR_CBALL;
                BALL_EQ_EMPTY] THEN
    REWRITE_TAC[DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_NEG_COMPONENT] THEN
    ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[AFF_DIM_NONEMPTY_INTERIOR]]);;

let ANNULUS_HOMOLOGY_ISOMORPHISM = prove
 (`!(a:real^N->bool) j0 j1.
     pl_annulus_with_ends a j0 j1
     ==> homology_group(&1,subtopology euclidean a) isomorphic_group integer_group /\
         group_isomorphism (homology_group(&1,subtopology euclidean j0),
                            homology_group(&1,subtopology euclidean a))
           (hom_induced (&1) (subtopology euclidean j0,{})
                             (subtopology euclidean a,{}) (\x. x)) /\
         group_isomorphism (homology_group(&1,subtopology euclidean j1),
                            homology_group(&1,subtopology euclidean a))
           (hom_induced (&1) (subtopology euclidean j1,{})
                             (subtopology euclidean a,{}) (\x. x))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[pl_annulus_with_ends; pl_homeomorphism; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`f:real^2->real^N`; `g:real^N->real^2`] THEN STRIP_TAC THEN
  MP_TAC(SPEC `&1` MOI_FH1_ANNULUS_RETRACT) THEN
  MP_TAC(SPEC `&2` MOI_FH1_ANNULUS_RETRACT) THEN
  REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC) THEN DISCH_THEN(STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `group_isomorphism (homology_group(&1,subtopology euclidean (j0:real^N->bool)),
                       homology_group(&1,subtopology euclidean (a:real^N->bool)))
      (hom_induced (&1) (subtopology euclidean j0,{})
                        (subtopology euclidean a,{}) (\x. x)) /\
    group_isomorphism (homology_group(&1,subtopology euclidean (j1:real^N->bool)),
                       homology_group(&1,subtopology euclidean (a:real^N->bool)))
      (hom_induced (&1) (subtopology euclidean j1,{})
                        (subtopology euclidean a,{}) (\x. x))`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC MOI_FH1_H1_DEFORM_ISO THEN
    MAP_EVERY EXISTS_TAC
     [`interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
       interval(--vector[&1;&1]:real^2,vector[&1;&1])`; `g:real^N->real^2`] THENL
     [EXISTS_TAC `\x:real^2. (&1 * inv(infnorm x)) % x`;
      EXISTS_TAC `\x:real^2. (&2 * inv(infnorm x)) % x`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`j0:real^N->bool`; `a:real^N->bool`] MOI_FH1_H1_ISO_CONSEQUENCES) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(ISPECL
   [`IMAGE (f:real^2->real^N)
       (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`;
    `relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])`;
    `sphere(vec 0:real^2,&1)`] HOMEOMORPHIC_TRANS) THEN
  SIMP_TAC[MOI_FH1_SQUARE_FRONTIER_CIRCLE; REAL_LT_01] THEN
  MATCH_MP_TAC MOI_FH1_IMAGE_HOMEOMORPHIC THEN
  MAP_EVERY EXISTS_TAC
   [`interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
     interval(--vector[&1;&1]:real^2,vector[&1;&1])`;
    `a:real^N->bool`; `g:real^N->real^2`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* H_1 of the torus. In H_1 of the circle the class of a loop is the power   *)
(* of the class of circlepath given by its winding number, and that class    *)
(* has infinite order, so a loop class vanishes iff the winding number does. *)
(* The two projections of the torus model then give an isomorphism of H_1    *)
(* onto H_1(S^1) x H_1(S^1): surjective by pasting loops, injective by       *)
(* ATOP_HUREWICZ1 and TORUS_MODEL_NULLHOMOTOPIC_WINDING.                     *)
(* ------------------------------------------------------------------------- *)

let MOI_FH1_CIRCLEPATH_FACTS = prove
 (`path (circlepath(vec 0,&1)) /\
   pathstart (circlepath(vec 0,&1)) = Cx(&1) /\
   pathfinish (circlepath(vec 0,&1)) = Cx(&1) /\
   path_image (circlepath(vec 0,&1)) = sphere(vec 0:real^2,&1) /\
   winding_number(circlepath(vec 0,&1),vec 0) = Cx(&1) /\
   Cx(&1) IN sphere(vec 0:real^2,&1)`,
  REWRITE_TAC[PATH_CIRCLEPATH; PATHSTART_CIRCLEPATH; PATHFINISH_CIRCLEPATH;
              VECTOR_ADD_LID] THEN
  SIMP_TAC[PATH_IMAGE_CIRCLEPATH; REAL_POS] THEN CONJ_TAC THENL
   [MATCH_MP_TAC WINDING_NUMBER_CIRCLEPATH THEN
    REWRITE_TAC[VECTOR_SUB_REFL; NORM_0; REAL_LT_01];
    REWRITE_TAC[IN_SPHERE_0; COMPLEX_NORM_CX] THEN REAL_ARITH_TAC]);;

let MOI_FH1_CIRCLE_CLASS_WINDING = prove
 (`!g h:real^1->real^2.
      path g /\ pathfinish g = pathstart g /\ path_image g SUBSET sphere(vec 0,&1) /\
      path h /\ pathfinish h = pathstart h /\ path_image h SUBSET sphere(vec 0,&1) /\
      winding_number(g,vec 0) = winding_number(h,vec 0)
      ==> homologous_rel (1,subtopology euclidean (sphere(vec 0:real^2,&1)),{})
            (frag_of (path_simplex (g o lift))) =
          homologous_rel (1,subtopology euclidean (sphere(vec 0:real^2,&1)),{})
            (frag_of (path_simplex (h o lift)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FH1_LOOP_CLASS_HOMOTOPIC THEN
  MP_TAC(ISPECL [`g:real^1->real^2`; `h:real^1->real^2`]
                MOI_FH1_CIRCLE_HOMOTOPIC_LOOPS_EQ) THEN
  ASM_REWRITE_TAC[]);;

let MOI_FH1_CIRCLE_POWERS = prove
 (`!n. ?h:real^1->real^2.
        path h /\ pathstart h = Cx(&1) /\ pathfinish h = Cx(&1) /\
        path_image h SUBSET sphere(vec 0,&1) /\
        winding_number(h,vec 0) = Cx(&n) /\
        homologous_rel (1,subtopology euclidean (sphere(vec 0:real^2,&1)),{})
          (frag_of (path_simplex (h o lift))) =
        group_pow (homology_group(&1,subtopology euclidean (sphere(vec 0:real^2,&1))))
          (homologous_rel (1,subtopology euclidean (sphere(vec 0:real^2,&1)),{})
             (frag_of (path_simplex (circlepath(vec 0,&1) o lift)))) n`,
  STRIP_ASSUME_TAC MOI_FH1_CIRCLEPATH_FACTS THEN
  SUBGOAL_THEN
   `homologous_rel (1,subtopology euclidean (sphere(vec 0:real^2,&1)),{})
      (frag_of (path_simplex (circlepath(vec 0,&1) o lift))) IN
    group_carrier (homology_group(&1,subtopology euclidean (sphere(vec 0:real^2,&1))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FH1_LOOP_CLASS_IN_CARRIER THEN
    ASM_REWRITE_TAC[GSYM PATH_EUCLIDEAN; SUBSET_REFL; o_THM; LIFT_NUM] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  INDUCT_TAC THENL
   [EXISTS_TAC `linepath(Cx(&1),Cx(&1))` THEN
    ASM_REWRITE_TAC[PATH_LINEPATH; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                    PATH_IMAGE_LINEPATH; SEGMENT_REFL; SING_SUBSET; group_pow] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC WINDING_NUMBER_TRIVIAL THEN
      ASM_MESON_TAC[MOI_FH1_ORIGIN_NOT_IN_CIRCLE];
      REWRITE_TAC[LINEPATH_REFL; o_DEF] THEN
      MATCH_MP_TAC MOI_FH1_CONST_LOOP_CLASS THEN
      ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `h:real^1->real^2` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(h:real^1->real^2) ++ circlepath(vec 0,&1)` THEN
  ASM_SIMP_TAC[PATH_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN; PATH_IMAGE_JOIN;
               UNION_SUBSET; SUBSET_REFL] THEN
  CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) WINDING_NUMBER_JOIN o lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MP_TAC MOI_FH1_ORIGIN_NOT_IN_CIRCLE THEN ASM SET_TAC[];
      DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[GSYM CX_ADD; REAL_OF_NUM_ADD; ADD1]];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MOI_FH1_LOOP_CLASS_JOIN o lhand o snd) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[SUBSET_REFL]; DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[ADD1; GROUP_POW_ADD; GROUP_POW_1]);;

let MOI_FH1_COMPLEX_INTEGER_CASES = prove
 (`!z. complex_integer z ==> ?n. z = Cx(&n) \/ z = --Cx(&n)`,
  GEN_TAC THEN REWRITE_TAC[complex_integer; INTEGER_CASES] THEN
  STRIP_TAC THEN EXISTS_TAC `n:num` THEN
  ASM_REWRITE_TAC[COMPLEX_EQ; RE_CX; IM_CX; RE_NEG; IM_NEG] THEN REAL_ARITH_TAC);;

let MOI_FH1_CIRCLE_CLASS_POW = prove
 (`!g:real^1->real^2.
      path g /\ pathfinish g = pathstart g /\ path_image g SUBSET sphere(vec 0,&1)
      ==> ?n. (winding_number(g,vec 0) = Cx(&n) /\
               homologous_rel (1,subtopology euclidean (sphere(vec 0:real^2,&1)),{})
                 (frag_of (path_simplex (g o lift))) =
               group_pow (homology_group(&1,subtopology euclidean (sphere(vec 0:real^2,&1))))
                 (homologous_rel (1,subtopology euclidean (sphere(vec 0:real^2,&1)),{})
                    (frag_of (path_simplex (circlepath(vec 0,&1) o lift)))) n) \/
              (winding_number(g,vec 0) = --Cx(&n) /\
               homologous_rel (1,subtopology euclidean (sphere(vec 0:real^2,&1)),{})
                 (frag_of (path_simplex (g o lift))) =
               group_inv (homology_group(&1,subtopology euclidean (sphere(vec 0:real^2,&1))))
                (group_pow (homology_group(&1,subtopology euclidean (sphere(vec 0:real^2,&1))))
                 (homologous_rel (1,subtopology euclidean (sphere(vec 0:real^2,&1)),{})
                    (frag_of (path_simplex (circlepath(vec 0,&1) o lift)))) n))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~((vec 0:real^2) IN path_image g)` ASSUME_TAC THENL
   [MP_TAC MOI_FH1_ORIGIN_NOT_IN_CIRCLE THEN ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^1->real^2`; `vec 0:real^2`] INTEGER_WINDING_NUMBER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num` o MATCH_MP MOI_FH1_COMPLEX_INTEGER_CASES) THEN
  EXISTS_TAC `n:num` THEN
  X_CHOOSE_THEN `h:real^1->real^2` STRIP_ASSUME_TAC (SPEC `n:num` MOI_FH1_CIRCLE_POWERS) THEN
  SUBGOAL_THEN `~((vec 0:real^2) IN path_image h)` ASSUME_TAC THENL
   [MP_TAC MOI_FH1_ORIGIN_NOT_IN_CIRCLE THEN ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `homologous_rel (1,subtopology euclidean (sphere(vec 0:real^2,&1)),{})
                  (frag_of (path_simplex ((h:real^1->real^2) o lift)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FH1_CIRCLE_CLASS_WINDING THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `homologous_rel (1,subtopology euclidean (sphere(vec 0:real^2,&1)),{})
                  (frag_of (path_simplex (reversepath (h:real^1->real^2) o lift)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FH1_CIRCLE_CLASS_WINDING THEN
      ASM_SIMP_TAC[PATH_REVERSEPATH; PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH;
                   PATH_IMAGE_REVERSEPATH; WINDING_NUMBER_REVERSEPATH];
      ASM_SIMP_TAC[MOI_FH1_LOOP_CLASS_REVERSEPATH]]]);;

let MOI_FH1_CIRCLE_GENERATOR_ORDER = prove
 (`homologous_rel (1,subtopology euclidean (sphere(vec 0:real^2,&1)),{})
     (frag_of (path_simplex (circlepath(vec 0,&1) o lift))) IN
   group_carrier (homology_group(&1,subtopology euclidean (sphere(vec 0:real^2,&1)))) /\
   group_element_order (homology_group(&1,subtopology euclidean (sphere(vec 0:real^2,&1))))
     (homologous_rel (1,subtopology euclidean (sphere(vec 0:real^2,&1)),{})
        (frag_of (path_simplex (circlepath(vec 0,&1) o lift)))) = 0`,
  STRIP_ASSUME_TAC MOI_FH1_CIRCLEPATH_FACTS THEN
  ABBREV_TAC `H = homology_group(&1,subtopology euclidean (sphere(vec 0:real^2,&1)))` THEN
  ABBREV_TAC `x = homologous_rel (1,subtopology euclidean (sphere(vec 0:real^2,&1)),{})
                    (frag_of (path_simplex (circlepath(vec 0,&1) o lift)))` THEN
  SUBGOAL_THEN `(x:((num->real)->real^2)frag->bool) IN group_carrier H` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["x"; "H"] THEN MATCH_MP_TAC MOI_FH1_LOOP_CLASS_IN_CARRIER THEN
    ASM_REWRITE_TAC[GSYM PATH_EUCLIDEAN; SUBSET_REFL; o_THM; LIFT_NUM] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP INFINITE_CYCLIC_SUBGROUP_ORDER th)]) THEN
  MATCH_MP_TAC INFINITE_SUPERSET THEN
  EXISTS_TAC `group_carrier (H:(((num->real)->real^2)frag->bool)group)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`H:(((num->real)->real^2)frag->bool)group`; `integer_group`]
                  ISOMORPHIC_GROUP_INFINITENESS) THEN
    EXPAND_TAC "H" THEN REWRITE_TAC[MOI_FH1_H1_CIRCLE; INFINITE_INTEGER_GROUP];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CARRIER_SUBGROUP_GENERATED_BY_SING] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNIV] THEN
  X_GEN_TAC `z:((num->real)->real^2)frag->bool` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`sphere(vec 0:real^2,&1)`; `Cx(&1)`;
                 `z:((num->real)->real^2)frag->bool`] MOI_FH1_H1_LOOP_REPRESENTATIVE) THEN
  ASM_SIMP_TAC[PATH_CONNECTED_SPHERE; DIMINDEX_2; LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `g:real^1->real^2` MOI_FH1_CIRCLE_CLASS_POW) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (DISJ_CASES_THEN STRIP_ASSUME_TAC)) THENL
   [EXISTS_TAC `&n:int` THEN ASM_REWRITE_TAC[GROUP_NPOW];
    EXISTS_TAC `--(&n):int` THEN ASM_SIMP_TAC[GROUP_ZPOW_NEG; GROUP_NPOW]]);;

let MOI_FH1_CIRCLE_CLASS_ZERO = prove
 (`!g:real^1->real^2.
      path g /\ pathfinish g = pathstart g /\ path_image g SUBSET sphere(vec 0,&1)
      ==> (homologous_rel (1,subtopology euclidean (sphere(vec 0:real^2,&1)),{})
             (frag_of (path_simplex (g o lift))) =
           group_id (homology_group(&1,subtopology euclidean (sphere(vec 0:real^2,&1)))) <=>
           winding_number(g,vec 0) = Cx(&0))`,
  REPEAT STRIP_TAC THEN
  STRIP_ASSUME_TAC MOI_FH1_CIRCLE_GENERATOR_ORDER THEN
  MP_TAC(ISPEC `g:real^1->real^2` MOI_FH1_CIRCLE_CLASS_POW) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (DISJ_CASES_THEN STRIP_ASSUME_TAC)) THEN
  ASM_SIMP_TAC[GROUP_INV_EQ_ID; GROUP_POW; GROUP_POW_EQ_ID; DIVIDES_ZERO] THEN
  REWRITE_TAC[COMPLEX_NEG_EQ_0; CX_INJ; REAL_OF_NUM_EQ]);;

let MOI_FH1_TORUS_PROJ_CONTINUOUS = prove
 (`continuous_map
     (subtopology euclidean (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)),
      subtopology euclidean (sphere(vec 0:real^2,&1)))
     (fstcart:real^(2,2)finite_sum->real^2) /\
   continuous_map
     (subtopology euclidean (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)),
      subtopology euclidean (sphere(vec 0:real^2,&1)))
     (sndcart:real^(2,2)finite_sum->real^2)`,
  REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2] THEN
  SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; MOI_FH1_IN_PCROSS] THEN SIMP_TAC[]);;

let MOI_FH1_PASTECART_LOOP = prove
 (`!(g1:real^1->real^M) (g2:real^1->real^N) s t.
      path g1 /\ path g2 /\ path_image g1 SUBSET s /\ path_image g2 SUBSET t /\
      pathfinish g1 = pathstart g1 /\ pathfinish g2 = pathstart g2
      ==> path_in (subtopology euclidean (s PCROSS t))
                  ((\x. pastecart (g1 x) (g2 x)) o lift) /\
          ((\x. pastecart (g1 x) (g2 x)) o lift) (&0) =
          ((\x. pastecart (g1 x) (g2 x)) o lift) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM PATH_EUCLIDEAN] THEN CONJ_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[path]) THEN REWRITE_TAC[path] THEN
      MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN ASM_REWRITE_TAC[];
      RULE_ASSUM_TAC(REWRITE_RULE[path_image; SUBSET; FORALL_IN_IMAGE]) THEN
      REWRITE_TAC[path_image; SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS] THEN
      ASM_SIMP_TAC[]];
    RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
    ASM_REWRITE_TAC[o_THM; LIFT_NUM]]);;

let MOI_FH1_TORUS_PHI_ISO = prove
 (`group_isomorphism
     (homology_group(&1,subtopology euclidean
                       (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1))),
      prod_group (homology_group(&1,subtopology euclidean (sphere(vec 0:real^2,&1))))
                 (homology_group(&1,subtopology euclidean (sphere(vec 0:real^2,&1)))))
     (\z. hom_induced (&1)
            (subtopology euclidean (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)),{})
            (subtopology euclidean (sphere(vec 0:real^2,&1)),{})
            (fstcart:real^(2,2)finite_sum->real^2) z,
          hom_induced (&1)
            (subtopology euclidean (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)),{})
            (subtopology euclidean (sphere(vec 0:real^2,&1)),{})
            (sndcart:real^(2,2)finite_sum->real^2) z)`,
  STRIP_ASSUME_TAC MOI_FH1_CIRCLEPATH_FACTS THEN
  STRIP_ASSUME_TAC MOI_FH1_TORUS_PROJ_CONTINUOUS THEN
  SUBGOAL_THEN `path_connected(sphere(vec 0:real^2,&1)) /\
                path_connected(sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1))`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[PATH_CONNECTED_PCROSS; PATH_CONNECTED_SPHERE; DIMINDEX_2; LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `group_homomorphism
     (homology_group(&1,subtopology euclidean
                       (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1))),
      prod_group (homology_group(&1,subtopology euclidean (sphere(vec 0:real^2,&1))))
                 (homology_group(&1,subtopology euclidean (sphere(vec 0:real^2,&1)))))
     (\z. hom_induced (&1)
            (subtopology euclidean (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)),{})
            (subtopology euclidean (sphere(vec 0:real^2,&1)),{})
            (fstcart:real^(2,2)finite_sum->real^2) z,
          hom_induced (&1)
            (subtopology euclidean (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)),{})
            (subtopology euclidean (sphere(vec 0:real^2,&1)),{})
            (sndcart:real^(2,2)finite_sum->real^2) z)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GROUP_HOMOMORPHISM_PAIRED; ETA_AX; GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM GROUP_MONOMORPHISM_EPIMORPHISM; GROUP_MONOMORPHISM_ALT;
              group_epimorphism] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:((num->real)->real^(2,2)finite_sum)frag->bool` THEN
    REWRITE_TAC[PROD_GROUP; PAIR_EQ] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)`;
                   `pastecart (Cx(&1)) (Cx(&1)):real^(2,2)finite_sum`;
                   `z:((num->real)->real^(2,2)finite_sum)frag->bool`]
                  MOI_FH1_H1_LOOP_REPRESENTATIVE) THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^1->real^(2,2)finite_sum` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `path_in (subtopology euclidean
                    (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)))
                    ((p:real^1->real^(2,2)finite_sum) o lift) /\
                  (p o lift) (&0) = (p o lift) (&1)`
    STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[GSYM PATH_EUCLIDEAN; o_THM; LIFT_NUM] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `pathfinish (p:real^1->real^(2,2)finite_sum) = pathstart p`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`p:real^1->real^(2,2)finite_sum`; `sphere(vec 0:real^2,&1)`;
                   `sphere(vec 0:real^2,&1)`] MOI_FH1_LOOP_COMPONENTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC
     `hom_induced (&1)
        (subtopology euclidean (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)),{})
        (subtopology euclidean (sphere(vec 0:real^2,&1)),{})
        (fstcart:real^(2,2)finite_sum->real^2) z =
      group_id (homology_group(&1,subtopology euclidean (sphere(vec 0:real^2,&1))))` THEN
    UNDISCH_TAC
     `hom_induced (&1)
        (subtopology euclidean (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)),{})
        (subtopology euclidean (sphere(vec 0:real^2,&1)),{})
        (sndcart:real^(2,2)finite_sum->real^2) z =
      group_id (homology_group(&1,subtopology euclidean (sphere(vec 0:real^2,&1))))` THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[MOI_FH1_HOM_INDUCED_LOOP] THEN
    REWRITE_TAC[o_ASSOC] THEN
    ASM_SIMP_TAC[MOI_FH1_CIRCLE_CLASS_ZERO] THEN REPEAT DISCH_TAC THEN
    MATCH_MP_TAC MOI_FH1_NULLHOMOTOPIC_LOOP_CLASS THEN
    MP_TAC(ISPEC `p:real^1->real^(2,2)finite_sum` TORUS_MODEL_NULLHOMOTOPIC_WINDING) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ASM_MESON_TAC[group_homomorphism]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; PROD_GROUP; FORALL_PAIR_THM; IN_CROSS; IN_IMAGE] THEN
  MAP_EVERY X_GEN_TAC [`z1:((num->real)->real^2)frag->bool`;
                       `z2:((num->real)->real^2)frag->bool`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`sphere(vec 0:real^2,&1)`; `Cx(&1)`;
                 `z1:((num->real)->real^2)frag->bool`] MOI_FH1_H1_LOOP_REPRESENTATIVE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g1:real^1->real^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`sphere(vec 0:real^2,&1)`; `Cx(&1)`;
                 `z2:((num->real)->real^2)frag->bool`] MOI_FH1_H1_LOOP_REPRESENTATIVE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g2:real^1->real^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`g1:real^1->real^2`; `g2:real^1->real^2`; `sphere(vec 0:real^2,&1)`;
                 `sphere(vec 0:real^2,&1)`] MOI_FH1_PASTECART_LOOP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC
   `homologous_rel
      (1,subtopology euclidean (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)),{})
      (frag_of (path_simplex ((\x. pastecart ((g1:real^1->real^2) x)
                                             ((g2:real^1->real^2) x)) o lift)))` THEN
  ASM_SIMP_TAC[MOI_FH1_LOOP_CLASS_IN_CARRIER; MOI_FH1_HOM_INDUCED_LOOP; PAIR_EQ] THEN
  SUBGOAL_THEN
   `(fstcart:real^(2,2)finite_sum->real^2) o
      ((\x. pastecart ((g1:real^1->real^2) x) ((g2:real^1->real^2) x)) o lift) =
    g1 o lift /\
    (sndcart:real^(2,2)finite_sum->real^2) o
      ((\x. pastecart ((g1:real^1->real^2) x) ((g2:real^1->real^2) x)) o lift) =
    g2 o lift`
  (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART]);;

let TORUS_HOMOLOGY_1 = prove
 (`!t:real^N->bool.
     torus_surface t
     ==> homology_group(&1,subtopology euclidean t) isomorphic_group
         prod_group integer_group integer_group`,
  GEN_TAC THEN REWRITE_TAC[torus_surface] THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPECL
   [`homology_group(&1,subtopology euclidean (t:real^N->bool))`;
    `homology_group(&1,subtopology euclidean
                       (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)))`;
    `prod_group integer_group integer_group`] ISOMORPHIC_GROUP_TRANS) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHIC_SPACE_IMP_ISOMORPHIC_HOMOLOGY_GROUPS THEN
    ASM_REWRITE_TAC[HOMEOMORPHIC_SPACE_EUCLIDEAN];
    ALL_TAC] THEN
  MATCH_MP_TAC(ISPECL
   [`homology_group(&1,subtopology euclidean
                       (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)))`;
    `prod_group (homology_group(&1,subtopology euclidean (sphere(vec 0:real^2,&1))))
                (homology_group(&1,subtopology euclidean (sphere(vec 0:real^2,&1))))`;
    `prod_group integer_group integer_group`] ISOMORPHIC_GROUP_TRANS) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[isomorphic_group] THEN MESON_TAC[MOI_FH1_TORUS_PHI_ISO];
    MATCH_MP_TAC ISOMORPHIC_GROUP_PROD_GROUPS THEN REWRITE_TAC[MOI_FH1_H1_CIRCLE]]);;

(* ------------------------------------------------------------------------- *)
(* The p.203 sentence in the models: a loop in the torus model (solid torus  *)
(* model) is zero in H_1 iff it is null-homotopic. Corollaries of the        *)
(* winding-number classification and of H_1 of the torus, for the Sec 28     *)
(* arguments.                                                                *)
(* ------------------------------------------------------------------------- *)

let MOI_FH1_TORUS_MODEL_LOOP_CLASS_ZERO = prove
 (`!p:real^1->real^(2,2)finite_sum.
     path p /\ pathfinish p = pathstart p /\
     path_image p SUBSET sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)
     ==> (homologous_rel
            (1,subtopology euclidean
                 (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)),{})
            (frag_of (path_simplex (p o lift))) =
          group_id (homology_group(&1,subtopology euclidean
                      (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)))) <=>
          homotopic_loops (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1))
                          p (linepath(pathstart p,pathstart p)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN EQ_TAC THENL
   [ALL_TAC; MESON_TAC[MOI_FH1_NULLHOMOTOPIC_LOOP_CLASS]] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FH1_LOOP_COMPONENTS) THEN
  ASM_SIMP_TAC[TORUS_MODEL_NULLHOMOTOPIC_WINDING] THEN
  ASM_SIMP_TAC[GSYM MOI_FH1_CIRCLE_CLASS_ZERO] THEN
  STRIP_ASSUME_TAC MOI_FH1_TORUS_PROJ_CONTINUOUS THEN
  SUBGOAL_THEN `path_in (subtopology euclidean
                  (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)))
                  ((p:real^1->real^(2,2)finite_sum) o lift) /\
                (p o lift) (&0) = (p o lift) (&1)`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
    ASM_REWRITE_TAC[GSYM PATH_EUCLIDEAN; o_THM; LIFT_NUM] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM o_ASSOC] THEN
  SUBGOAL_THEN
   `hom_induced (&1)
      (subtopology euclidean (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)),{})
      (subtopology euclidean (sphere(vec 0:real^2,&1)),{})
      (fstcart:real^(2,2)finite_sum->real^2)
      (homologous_rel
         (1,subtopology euclidean
              (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)),{})
         (frag_of (path_simplex ((p:real^1->real^(2,2)finite_sum) o lift)))) =
    homologous_rel (1,subtopology euclidean (sphere(vec 0:real^2,&1)),{})
      (frag_of (path_simplex (fstcart o p o lift))) /\
    hom_induced (&1)
      (subtopology euclidean (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)),{})
      (subtopology euclidean (sphere(vec 0:real^2,&1)),{})
      (sndcart:real^(2,2)finite_sum->real^2)
      (homologous_rel
         (1,subtopology euclidean
              (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)),{})
         (frag_of (path_simplex ((p:real^1->real^(2,2)finite_sum) o lift)))) =
    homologous_rel (1,subtopology euclidean (sphere(vec 0:real^2,&1)),{})
      (frag_of (path_simplex (sndcart o p o lift)))`
  (CONJUNCTS_THEN (SUBST1_TAC o SYM)) THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_FH1_HOM_INDUCED_LOOP THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN CONJ_TAC THEN
  MATCH_MP_TAC ATOP_GROUP_HOM_ID THEN
  REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY]);;

let MOI_FH1_SOLID_TORUS_MODEL_LOOP_CLASS_ZERO = prove
 (`!p:real^1->real^(2,2)finite_sum.
     path p /\ pathfinish p = pathstart p /\
     path_image p SUBSET cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)
     ==> (homologous_rel
            (1,subtopology euclidean
                 (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)),{})
            (frag_of (path_simplex (p o lift))) =
          group_id (homology_group(&1,subtopology euclidean
                      (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)))) <=>
          homotopic_loops (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1))
                          p (linepath(pathstart p,pathstart p)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN EQ_TAC THENL
   [ALL_TAC; MESON_TAC[MOI_FH1_NULLHOMOTOPIC_LOOP_CLASS]] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FH1_LOOP_COMPONENTS) THEN
  ASM_SIMP_TAC[SOLID_TORUS_MODEL_NULLHOMOTOPIC_WINDING] THEN
  ASM_SIMP_TAC[GSYM MOI_FH1_CIRCLE_CLASS_ZERO] THEN
  SUBGOAL_THEN
   `continuous_map
     (subtopology euclidean (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)),
      subtopology euclidean (sphere(vec 0:real^2,&1)))
     (sndcart:real^(2,2)finite_sum->real^2)`
  ASSUME_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2] THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; MOI_FH1_IN_PCROSS] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `path_in (subtopology euclidean
                  (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)))
                  ((p:real^1->real^(2,2)finite_sum) o lift) /\
                (p o lift) (&0) = (p o lift) (&1)`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
    ASM_REWRITE_TAC[GSYM PATH_EUCLIDEAN; o_THM; LIFT_NUM] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM o_ASSOC] THEN
  SUBGOAL_THEN
   `hom_induced (&1)
      (subtopology euclidean (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)),{})
      (subtopology euclidean (sphere(vec 0:real^2,&1)),{})
      (sndcart:real^(2,2)finite_sum->real^2)
      (homologous_rel
         (1,subtopology euclidean
              (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)),{})
         (frag_of (path_simplex ((p:real^1->real^(2,2)finite_sum) o lift)))) =
    homologous_rel (1,subtopology euclidean (sphere(vec 0:real^2,&1)),{})
      (frag_of (path_simplex (sndcart o p o lift)))`
  (SUBST1_TAC o SYM) THENL
   [MATCH_MP_TAC MOI_FH1_HOM_INDUCED_LOOP THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC ATOP_GROUP_HOM_ID THEN
  REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY]);;


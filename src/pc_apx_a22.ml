(* ========================================================================= *)
(* pc_apx_a22: MT Claim A.22: there is no infinite chain of (C,eps)-caps C0  *)
(* SUBSET C1 SUBSET ... such that the closed core of each C(n+1) meets the   *)
(* frontier of C n.  Main theorem APX_A22 |- !u. APX_A22_STATEMENT u         *)
(* (unconditional).  Method: MT's quantity d_n = dist(x0, M - C_n) grows by  *)
(* a fixed amount and stays below the cap diameter; the step uses the end    *)
(* structure of the complement neck of a cap (L1), the small frontier of a   *)
(* cap (L2), the distance from the core to the outer half of the complement  *)
(* neck (L3), and hence that C_n lies on the core side of the central sphere *)
(* of the complement neck of C(n+1) (L4).  This replaces MT's three-case     *)
(* analysis with A.11, whose first case (p. 510) needs the unstated fact     *)
(* that a cap cannot lie inside a neck.                                      *)
(* ========================================================================= *)

needs "src/pc_apx_chain.ml";;
needs "src/pc_grg_distcont.ml";;

prioritize_real();;
type_invention_error := true;;

let APX22_UNFOLD_ASM_TAC name (def:thm) =
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[def] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = name)) (concl th)));;

(* ------------------------------------------------------------------------- *)
(* Radial invariance of radial sets, and the data of a cap used              *)
(* below (both kinds): complement neck e with e(dom) = U - K, closed core K   *)
(* (compact, containing the closure of the core), collar of the boundary     *)
(* neck e' outside K, the core with half the collar open, and its closure.   *)
(* ------------------------------------------------------------------------- *)

(* Radial extensions of sphere diffeomorphisms preserve radial sets. *)

let APX22_RADIAL_IMAGE = prove
 (`!(f:real^3->real^3) f' (P:real->bool).
     sphere_diffeo f f'
     ==> IMAGE (radial_ext f) {y | P(norm y)} = {y:real^3 | P(norm y)}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(!y:real^3. norm(radial_ext f y) = norm y) /\
                (!y:real^3. norm(radial_ext f' y) = norm y) /\
                (!y:real^3. radial_ext f (radial_ext f' y) = y)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `sphere_diffeo (f:real^3->real^3) f'` THEN REWRITE_TAC[sphere_diffeo] THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THEN GEN_TAC THENL
     [MATCH_MP_TAC SMT_RADIAL_EXT_NORM THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC SMT_RADIAL_EXT_NORM THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC SMT_RADIAL_EXT_INVERSE THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `w:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN EXISTS_TAC `radial_ext (f':real^3->real^3) w` THEN ASM_REWRITE_TAC[]]);;

let APX22_RADIAL_ANNULUS = prove
 (`!(f:real^3->real^3) f' r1 r2.
     sphere_diffeo f f'
     ==> IMAGE (radial_ext f) (annulus r1 r2) = annulus r1 r2 /\
         IMAGE (radial_ext f) {y | r1 < norm y /\ norm y <= r2} =
         {y:real^3 | r1 < norm y /\ norm y <= r2} /\
         IMAGE (radial_ext f) (sphere(vec 0,r2)) = sphere(vec 0,r2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[annulus] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`f:real^3->real^3`; `f':real^3->real^3`; `\t. r1 < t /\ t < r2`]
      APX22_RADIAL_IMAGE);
    MP_TAC(ISPECL [`f:real^3->real^3`; `f':real^3->real^3`; `\t. r1 < t /\ t <= r2`]
      APX22_RADIAL_IMAGE);
    MP_TAC(ISPECL [`f:real^3->real^3`; `f':real^3->real^3`; `\t:real. t = r2`]
      APX22_RADIAL_IMAGE) THEN
    REWRITE_TAC[GSYM IN_SPHERE_0; SET_RULE `{y:real^3 | y IN s} = s`]] THEN
  ASM_REWRITE_TAC[]);;

(* The data of a ball cap used below: closed core K = b(cball 1), the collar *)
(* of the boundary neck e' outside K, and the core with half the collar as   *)
(* an open set whose closure adds only collar points.                        *)

let APX22_BALL_DATA = prove
 (`!top atlas (b:real^3->A) e' f f'.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     mfd_ball_chart top atlas b /\ sphere_diffeo f f' /\
     (!y. y IN annulus (&1) (&2) ==> b y = e'(radial_ext f y))
     ==> compact_in top (IMAGE b (cball(vec 0,&1))) /\
         top closure_of (IMAGE b (ball(vec 0,&1))) SUBSET IMAGE b (cball(vec 0,&1)) /\
         IMAGE e' (annulus (&1) (&2)) = IMAGE b (annulus (&1) (&2)) /\
         DISJOINT (IMAGE b (annulus (&1) (&2))) (IMAGE b (cball(vec 0,&1))) /\
         open_in top (IMAGE b (cball(vec 0,&1)) UNION IMAGE e' (annulus (&1) (&3 / &2))) /\
         top closure_of (IMAGE e' (annulus (&1) (&3 / &2))) SUBSET
         IMAGE b (cball(vec 0,&1)) UNION IMAGE e' {y | &1 < norm y /\ norm y <= &3 / &2}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_param top atlas (ball(vec 0,&2)) (b:real^3->A)` ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_ball_chart]; ALL_TAC] THEN
  SUBGOAL_THEN `!s. s SUBSET annulus (&1) (&2) /\ IMAGE (radial_ext f) s = s
                    ==> IMAGE (e':real^3->A) s = IMAGE (b:real^3->A) s` ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) o
      check (fun th -> concl th = `IMAGE (radial_ext (f:real^3->real^3)) s = s`)) THEN
    REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC IMAGE_EQ THEN
    REWRITE_TAC[o_THM] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `f':real^3->real^3`; `&1`; `&2`] APX22_RADIAL_ANNULUS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `f':real^3->real^3`; `&1`; `&3 / &2`]
    APX22_RADIAL_ANNULUS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (e':real^3->A) (annulus (&1) (&2)) = IMAGE (b:real^3->A) (annulus (&1) (&2)) /\
                IMAGE (e':real^3->A) (annulus (&1) (&3 / &2)) = IMAGE (b:real^3->A) (annulus (&1) (&3 / &2)) /\
                IMAGE (e':real^3->A) {y | &1 < norm y /\ norm y <= &3 / &2} =
                IMAGE (b:real^3->A) {y | &1 < norm y /\ norm y <= &3 / &2}` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
    REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in top (IMAGE (b:real^3->A) (cball(vec 0,&1))) /\
                compact_in top (IMAGE (b:real^3->A) {y | &1 <= norm y /\ norm y <= &3 / &2})`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `{y:real^3 | &1 <= norm y /\ norm y <= &3 / &2} =
                  cball(vec 0,&3 / &2) DIFF ball(vec 0,&1)` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THEN MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `ball(vec 0:real^3,&2)`] THEN
    ASM_SIMP_TAC[COMPACT_CBALL; COMPACT_DIFF; OPEN_BALL; SUBSET; IN_CBALL_0; IN_BALL_0;
                 IN_DIFF] THEN
    GEN_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN ASM_SIMP_TAC[COMPACT_IN_IMP_CLOSED_IN] THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[BALL_SUBSET_CBALL];
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    X_GEN_TAC `q:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `u:real^3 = v` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_INJ THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `ball(vec 0:real^3,&2)`; `b:real^3->A`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `(u:real^3) IN annulus (&1) (&2)` THEN
        REWRITE_TAC[IN_BALL_0; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `(v:real^3) IN cball(vec 0,&1)` THEN
        REWRITE_TAC[IN_BALL_0; IN_CBALL_0] THEN REAL_ARITH_TAC;
        ASM_MESON_TAC[]];
      UNDISCH_TAC `(v:real^3) IN annulus (&1) (&2)` THEN
      UNDISCH_TAC `(v:real^3) IN cball(vec 0,&1)` THEN
      REWRITE_TAC[IN_CBALL_0; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC];
    SUBGOAL_THEN `IMAGE (b:real^3->A) (cball(vec 0,&1)) UNION IMAGE (b:real^3->A) (annulus (&1) (&3 / &2)) =
                  IMAGE (b:real^3->A) (ball(vec 0,&3 / &2))` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_UNION] THEN AP_TERM_TAC THEN
      REWRITE_TAC[EXTENSION; IN_UNION; IN_CBALL_0; IN_BALL_0; annulus; IN_ELIM_THM] THEN
      GEN_TAC THEN REAL_ARITH_TAC;
      MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `ball(vec 0:real^3,&2)`] THEN
      ASM_REWRITE_TAC[OPEN_BALL; SUBSET; IN_BALL_0] THEN REAL_ARITH_TAC];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (b:real^3->A) {y | &1 <= norm y /\ norm y <= &3 / &2}` THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN ASM_SIMP_TAC[COMPACT_IN_IMP_CLOSED_IN] THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_UNION] THEN
      X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
      ASM_CASES_TAC `norm(y:real^3) = &1` THENL
       [DISJ1_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_CBALL_0; REAL_LE_REFL];
        DISJ2_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_ELIM_THM] THEN
        ASM_REAL_ARITH_TAC]]]);;

(* The same data for a twisted cap: closed core K = p(1/2 <= norm <= 2), the *)
(* collar e'(annulus(1,2)) = p(annulus(2,4)).                                *)

let APX22_TWIST_NORM = prove
 (`!y:real^3. ~(y = vec 0) ==> norm(rfs_twist y) = inv(norm y)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[rfs_twist; NORM_NEG; NORM_MUL; REAL_ABS_INV; REAL_ABS_POW; REAL_ABS_NORM] THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` MP_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; CONV_TAC REAL_FIELD]);;

let APX22_TWISTED_DATA = prove
 (`!top atlas (p:real^3->A) e' f f'.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     rfs_twisted_chart top atlas p /\ sphere_diffeo f f' /\
     (!y. y IN annulus (&2) (&4) ==> p y = e'(radial_ext f (inv(&2) % y)))
     ==> compact_in top (IMAGE p {y | &1 / &2 <= norm y /\ norm y <= &2}) /\
         top closure_of (IMAGE p (annulus (&1 / &2) (&2))) SUBSET
         IMAGE p {y | &1 / &2 <= norm y /\ norm y <= &2} /\
         IMAGE e' (annulus (&1) (&2)) = IMAGE p (annulus (&2) (&4)) /\
         DISJOINT (IMAGE p (annulus (&2) (&4)))
                  (IMAGE p {y | &1 / &2 <= norm y /\ norm y <= &2}) /\
         open_in top (IMAGE p {y | &1 / &2 <= norm y /\ norm y <= &2} UNION
                      IMAGE e' (annulus (&1) (&3 / &2))) /\
         top closure_of (IMAGE e' (annulus (&1) (&3 / &2))) SUBSET
         IMAGE p {y | &1 / &2 <= norm y /\ norm y <= &2} UNION
         IMAGE e' {y | &1 < norm y /\ norm y <= &3 / &2}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `rfs_twisted_chart top atlas (p:real^3->A)` THEN
  REWRITE_TAC[rfs_twisted_chart] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "id") (LABEL_TAC "loc")) THEN
  SUBGOAL_THEN `continuous_map (subtopology euclidean (annulus (&1 / &4) (&4)),top)
                               (p:real^3->A)` ASSUME_TAC THENL
   [MATCH_MP_TAC TOPC_CONTINUOUS_MAP_LOCAL THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "loc" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `ball(y:real^3,r)` THEN
    ASM_SIMP_TAC[OPEN_IN_OPEN_EQ; OPEN_ANNULUS; OPEN_BALL; CENTRE_IN_BALL] THEN
    REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
    ASM_SIMP_TAC[SET_RULE `(s:real^3->bool) SUBSET t ==> t INTER s = s`] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `ball(y:real^3,r)`; `p:real^3->A`] GRGD_PARAM_FACTS) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. open s /\ s SUBSET annulus (&1 / &4) (&4)
                    ==> open_in top (IMAGE (p:real^3->A) s)` ASSUME_TAC THENL
   [X_GEN_TAC `s:real^3->bool` THEN STRIP_TAC THEN
    GEN_REWRITE_TAC I [OPEN_IN_SUBOPEN] THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "loc" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `IMAGE (p:real^3->A) (ball(y,r) INTER s)` THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `ball(y:real^3,r)`] THEN
      ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL; INTER_SUBSET];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL];
      MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTER_SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN annulus (&1 / &4) (&4)
                    ==> rfs_twist y IN annulus (&1 / &4) (&4) /\
                        (p:real^3->A) (rfs_twist y) = p y /\
                        norm(rfs_twist y) = inv(norm y)` ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(y:real^3 = vec 0) /\ &1 / &4 < norm y /\ norm y < &4` STRIP_ASSUME_TAC
    THENL
     [UNDISCH_TAC `(y:real^3) IN annulus (&1 / &4) (&4)` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM; GSYM NORM_POS_LT] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `c /\ a /\ (a ==> b) ==> a /\ b /\ c`) THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[APX22_TWIST_NORM]; ALL_TAC] THEN CONJ_TAC THENL
     [REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_SIMP_TAC[APX22_TWIST_NORM] THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN `inv(&4) < inv(norm(y:real^3))` MP_TAC THENL
         [MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC;
          CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC];
        SUBGOAL_THEN `inv(norm(y:real^3)) < inv(&1 / &4)` MP_TAC THENL
         [MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC;
          CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC]];
      DISCH_TAC THEN USE_THEN "id" (MP_TAC o SPECL [`y:real^3`; `rfs_twist y`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(ACCEPT_TAC o SYM o REWRITE_RULE[])];
    ALL_TAC] THEN
  (* collar images: e' on radial sets in annulus(1,2) is p on the doubled sets *)
  SUBGOAL_THEN `!Q. (!t. Q t ==> &1 < t /\ t < &2)
                    ==> IMAGE (e':real^3->A) {w | Q(norm w)} =
                        IMAGE (p:real^3->A) {y | Q(inv(&2) * norm y)}` ASSUME_TAC THENL
   [X_GEN_TAC `Q:real->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `IMAGE (p:real^3->A) {y | Q(inv(&2) * norm y)} =
                  IMAGE ((e':real^3->A) o radial_ext f o (\y. inv(&2) % y))
                        {y | Q(inv(&2) * norm y)}` SUBST1_TAC THENL
     [MATCH_MP_TAC IMAGE_EQ THEN X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_ELIM_THM; o_THM] THEN
      DISCH_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `annulus (&2) (&4):real^3->bool`)) (concl th))) THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `inv(&2) * norm(y:real^3)`) THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IMAGE_o] THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `IMAGE (\y:real^3. inv(&2) % y) {y | Q(inv(&2) * norm y)} = {w | Q(norm w)}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `w:real^3` THEN
      EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NUM];
        DISCH_TAC THEN EXISTS_TAC `&2 % w:real^3` THEN
        REWRITE_TAC[VECTOR_MUL_ASSOC; NORM_MUL; REAL_ABS_NUM; REAL_MUL_ASSOC] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[VECTOR_MUL_LID; REAL_MUL_LID]];
      ALL_TAC] THEN
    MATCH_MP_TAC(GSYM APX22_RADIAL_IMAGE) THEN EXISTS_TAC `f':real^3->real^3` THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (e':real^3->A) (annulus (&1) (&2)) = IMAGE (p:real^3->A) (annulus (&2) (&4)) /\
                IMAGE (e':real^3->A) (annulus (&1) (&3 / &2)) = IMAGE (p:real^3->A) (annulus (&2) (&3)) /\
                IMAGE (e':real^3->A) {y | &1 < norm y /\ norm y <= &3 / &2} =
                IMAGE (p:real^3->A) {y | &2 < norm y /\ norm y <= &3}` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[annulus] THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `\t. &1 < t /\ t < &2`);
      FIRST_X_ASSUM(MP_TAC o SPEC `\t. &1 < t /\ t < &3 / &2`);
      FIRST_X_ASSUM(MP_TAC o SPEC `\t. &1 < t /\ t <= &3 / &2`)] THEN
    (ANTS_TAC THENL [REWRITE_TAC[] THEN REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o BETA_RULE)]) THEN
    AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `compact_in top (IMAGE (p:real^3->A) {y | &1 / &2 <= norm y /\ norm y <= &2}) /\
                compact_in top (IMAGE (p:real^3->A) {y | &2 <= norm y /\ norm y <= &3})`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `{y:real^3 | &1 / &2 <= norm y /\ norm y <= &2} =
                  cball(vec 0,&2) DIFF ball(vec 0,&1 / &2) /\
                  {y:real^3 | &2 <= norm y /\ norm y <= &3} = cball(vec 0,&3) DIFF ball(vec 0,&2)`
    (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN
      CONJ_TAC THEN GEN_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THEN MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology euclidean (annulus (&1 / &4) (&4):real^3->bool)` THEN
    ASM_SIMP_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN; COMPACT_DIFF; COMPACT_CBALL;
                 OPEN_BALL] THEN
    REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN
    GEN_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN ASM_SIMP_TAC[COMPACT_IN_IMP_CLOSED_IN] THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `q:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)) THEN
    USE_THEN "id" (MP_TAC o SPECL [`u:real^3`; `v:real^3`]) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `(u:real^3) IN annulus (&2) (&4)` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(p:real^3->A) u = p v` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    STRIP_TAC THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `v:real^3 = u`)) THEN
      UNDISCH_TAC `(u:real^3) IN annulus (&2) (&4)` THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN
      ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `norm(v:real^3) = inv(norm(u:real^3))` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APX22_TWIST_NORM THEN
        UNDISCH_TAC `(u:real^3) IN annulus (&2) (&4)` THEN
        REWRITE_TAC[annulus; IN_ELIM_THM; GSYM NORM_POS_LT] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `inv(norm(u:real^3)) < inv(&2)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV2 THEN UNDISCH_TAC `(u:real^3) IN annulus (&2) (&4)` THEN
        REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
        CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC]];
    SUBGOAL_THEN `IMAGE (p:real^3->A) {y | &1 / &2 <= norm y /\ norm y <= &2} UNION
                  IMAGE (p:real^3->A) (annulus (&2) (&3)) = IMAGE (p:real^3->A) (annulus (&1 / &3) (&3))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM IMAGE_UNION] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
        REWRITE_TAC[SUBSET; IN_UNION; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNION] THEN X_GEN_TAC `y:real^3` THEN
        REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
        ASM_CASES_TAC `&1 / &2 <= norm(y:real^3)` THENL
         [ASM_CASES_TAC `norm(y:real^3) <= &2` THENL
           [DISJ1_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_ELIM_THM];
            DISJ2_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN
            ASM_REAL_ARITH_TAC];
          DISJ2_TAC THEN
          FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th -> is_forall(concl th) &&
            can (find_term (fun t -> t = `rfs_twist`)) (concl th))) THEN
          ANTS_TAC THENL [REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          STRIP_TAC THEN
          FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
            `(p:real^3->A) (rfs_twist y) = p y`)) THEN
          MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN
          ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
           [SUBGOAL_THEN `inv(&1 / &2) < inv(norm(y:real^3))` MP_TAC THENL
             [MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC;
              CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC];
            SUBGOAL_THEN `inv(norm(y:real^3)) < inv(&1 / &3)` MP_TAC THENL
             [MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC;
              CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC]]]];
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[OPEN_ANNULUS; SUBSET; annulus; IN_ELIM_THM] THEN
      REAL_ARITH_TAC];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (p:real^3->A) {y | &2 <= norm y /\ norm y <= &3}` THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN ASM_SIMP_TAC[COMPACT_IN_IMP_CLOSED_IN] THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_UNION] THEN
      X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
      ASM_CASES_TAC `norm(y:real^3) = &2` THENL
       [DISJ1_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_ELIM_THM] THEN
        ASM_REAL_ARITH_TAC;
        DISJ2_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_ELIM_THM] THEN
        ASM_REAL_ARITH_TAC]]]);;

(* Both kinds of caps: the complement neck e (e(dom) = U - K), the boundary *)
(* neck e' whose collar e'(annulus(1,2)) lies in U - K, and the closed core *)
(* K (compact, containing the closure of the core Y).                       *)

let APX22_CAP_DATA = prove
 (`!top atlas (g:A->real^3^3) C eps U Y.
     hausdorff_space top /\ rfs_cap (top,atlas) g C eps U Y
     ==> smooth_manifold_atlas top atlas /\ open_in top U /\ ~(Y = {}) /\
         ?e z e' z' K.
           rfs_neck (top,atlas) g eps z e /\ rfs_neck (top,atlas) g eps z' e' /\
           IMAGE e (rfs_neck_dom eps) = U DIFF K /\
           compact_in top K /\ K SUBSET U /\ top closure_of Y SUBSET K /\ Y SUBSET K /\
           IMAGE e' (annulus (&1) (&2)) SUBSET U DIFF K /\
           open_in top (K UNION IMAGE e' (annulus (&1) (&3 / &2))) /\
           top closure_of (IMAGE e' (annulus (&1) (&3 / &2))) SUBSET
           K UNION IMAGE e' {y | &1 < norm y /\ norm y <= &3 / &2}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL APX_CAP_CORE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `rfs_cap (top,atlas) (g:A->real^3^3) C eps U Y` THEN REWRITE_TAC[rfs_cap] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 MP_TAC (K ALL_TAC)))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `b:real^3->A`;
                   `e'':real^3->A`; `f:real^3->real^3`; `f':real^3->real^3`] APX22_BALL_DATA) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MAP_EVERY EXISTS_TAC [`e:real^3->A`; `z:A`; `e'':real^3->A`; `z'':A`;
                          `IMAGE (b:real^3->A) (cball(vec 0,&1))`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (b:real^3->A) (ball(vec 0,&2))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[BALL_SUBSET_CBALL];
      SUBGOAL_THEN `IMAGE (b:real^3->A) (annulus (&1) (&2)) SUBSET U` MP_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (b:real^3->A) (ball(vec 0,&2))` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
        REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM; IN_BALL_0] THEN REAL_ARITH_TAC;
        UNDISCH_TAC `DISJOINT (IMAGE (b:real^3->A) (annulus (&1) (&2)))
                              (IMAGE b (cball(vec 0,&1)))` THEN SET_TAC[]]];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `p:real^3->A`;
                   `e'':real^3->A`; `f:real^3->real^3`; `f':real^3->real^3`]
                  APX22_TWISTED_DATA) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MAP_EVERY EXISTS_TAC [`e:real^3->A`; `z:A`; `e'':real^3->A`; `z'':A`;
                          `IMAGE (p:real^3->A) {y | &1 / &2 <= norm y /\ norm y <= &2}`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (p:real^3->A) (annulus (&1 / &4) (&4))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN
      REAL_ARITH_TAC;
      SUBGOAL_THEN `IMAGE (p:real^3->A) (annulus (&2) (&4)) SUBSET U` MP_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `IMAGE (p:real^3->A) (annulus (&1 / &4) (&4))` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
        REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
        UNDISCH_TAC `DISJOINT (IMAGE (p:real^3->A) (annulus (&2) (&4)))
                              (IMAGE p {y | &1 / &2 <= norm y /\ norm y <= &2})` THEN
        SET_TAC[]]]]);;

(* ------------------------------------------------------------------------- *)
(* L1 CAP_ENDS.  The collar sphere S = e'(sphere 3/2) of a cap               *)
(* is a section of the complement neck e (N4); the collar C' =               *)
(* e'(annulus(1,3/2)) is clopen in the complement of S in the neck, so it    *)
(* contains a side of S, hence an end of e; orient e so that this is the     *)
(* low end.  By N2 the collar has small level span, so it lies at levels     *)
(* below -1/eps + 11.  Consequences: W = K + e0(levels < 0) is open with     *)
(* closure inside W + e0(sphere 1), and the frontier of U lies in the        *)
(* closure of the top slab of e0.                                            *)
(* ------------------------------------------------------------------------- *)

(* The collar annuli lie in the neck domain. *)

let APX22_COLLAR_DOM = prove
 (`!eps. &0 < eps /\ eps <= &1 / &1024
         ==> exp(--(inv(sqrt(&2) * eps))) < &1 / &4 /\ &4 < exp(inv(sqrt(&2) * eps)) /\
             {y:real^3 | &1 / &4 <= norm y /\ norm y <= &4} SUBSET rfs_neck_dom eps`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(&2) /\ sqrt(&2) <= &3 / &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH];
      MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 <= inv(sqrt(&2) * eps)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`sqrt(&2) * eps`; `&1 / &4`] REAL_LE_INV2) THEN ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 / &2 * &1 / &1024` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 < exp(inv(sqrt(&2) * eps))` ASSUME_TAC THENL
   [MP_TAC(SPEC `inv(sqrt(&2) * eps)` REAL_EXP_LE_X) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `exp(--(inv(sqrt(&2) * eps))) < &1 / &4` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_NEG] THEN
    MP_TAC(SPECL [`&4`; `exp(inv(sqrt(&2) * eps))`] REAL_LT_INV2) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[rfs_neck_dom; SUBSET; annulus; IN_ELIM_THM] THEN
  GEN_TAC THEN ASM_REAL_ARITH_TAC);;

(* A connected set meeting an open set Q, and missing the frontier points of *)
(* Q, lies in Q.                                                             *)

let APX22_CLOPEN_SPLIT = prove
 (`!top N Q:A->bool.
     connected_in top N /\ open_in top Q /\ N INTER top closure_of Q SUBSET Q
     ==> N SUBSET Q \/ DISJOINT N Q`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `Q:A->bool`;
                 `topspace top DIFF top closure_of (Q:A->bool)`; `N:A->bool`]
                CONNECTED_IN_SUBSET_SEPARATED_UNION) THEN
  SUBGOAL_THEN `(Q:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(Q:A->bool) SUBSET top closure_of Q` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CLOSURE_OF_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(Q:A->bool) SUBSET top interior_of (top closure_of Q)` ASSUME_TAC THENL
   [MATCH_MP_TAC INTERIOR_OF_MAXIMAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(N:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONNECTED_IN_SUBSET_TOPSPACE]; ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[separated_in; CLOSURE_OF_COMPLEMENT] THEN ASM SET_TAC[];
    ASM SET_TAC[]]);;

(* A connected set inside the union of two disjoint open sets, meeting the *)
(* first, lies in the first.                                               *)

let APX22_CONNECTED_TWO = prove
 (`!top C A B:A->bool.
     connected_in top C /\ open_in top A /\ open_in top B /\ DISJOINT A B /\
     C SUBSET A UNION B /\ ~DISJOINT C A
     ==> C SUBSET A`,
  REWRITE_TAC[CONNECTED_IN; NOT_EXISTS_THM] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`A:A->bool`; `B:A->bool`]) THEN ASM_REWRITE_TAC[] THEN
  ASM SET_TAC[]);;

(* The two sides of a section contain the two ends of the neck domain. *)

let APX22_SIDE_ENDS = prove
 (`!(u:real^3->real) eps.
     &0 < eps /\
     (\x. lift(u x)) continuous_on sphere(vec 0,&1) /\
     (!x. x IN sphere(vec 0,&1)
          ==> exp(--inv eps / sqrt(&2)) < u x /\ u x < exp(inv eps / sqrt(&2)))
     ==> ?d. &0 < d /\ d <= &1 /\
             apx_slab (--inv eps) (--inv eps + d) SUBSET
             {z | ~(z = vec 0) /\ exp(--inv eps / sqrt(&2)) < norm z /\
                  norm z < u(inv(norm z) % z)} /\
             apx_slab (inv eps - d) (inv eps) SUBSET
             {z | ~(z = vec 0) /\ u(inv(norm z) % z) < norm z /\
                  norm z < exp(inv eps / sqrt(&2))}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bd"))) THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `compact(sphere(vec 0:real^3,&1)) /\ ~(sphere(vec 0:real^3,&1) = {}) /\
                (lift o (u:real^3->real)) continuous_on sphere(vec 0,&1)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[COMPACT_SPHERE; SPHERE_EQ_EMPTY; o_DEF] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^3->real`; `sphere(vec 0:real^3,&1)`] CONTINUOUS_ATTAINS_INF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:real^3` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "mn"))) THEN
  MP_TAC(ISPECL [`u:real^3->real`; `sphere(vec 0:real^3,&1)`] CONTINUOUS_ATTAINS_SUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w2:real^3` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "mx"))) THEN
  USE_THEN "bd" (fun th -> MP_TAC(MATCH_MP th (ASSUME `w1:real^3 IN sphere(vec 0,&1)`)) THEN
                           MP_TAC(MATCH_MP th (ASSUME `w2:real^3 IN sphere(vec 0,&1)`))) THEN
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `m = (u:real^3->real) w1` THEN ABBREV_TAC `M = (u:real^3->real) w2` THEN
  SUBGOAL_THEN `&0 < m /\ &0 < M` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `--inv eps / sqrt(&2)` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--inv eps < sqrt(&2) * log m /\ sqrt(&2) * log M < inv eps`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `exp(--inv eps / sqrt(&2)) < exp(log m) /\
                  exp(log M) < exp(inv eps / sqrt(&2))` MP_TAC THENL
     [ASM_SIMP_TAC[EXP_LOG];
      REWRITE_TAC[REAL_EXP_MONO_LT] THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `min (&1) (min (sqrt(&2) * log m + inv eps) (inv eps - sqrt(&2) * log M))` THEN
  ABBREV_TAC `d = min (&1) (min (sqrt(&2) * log m + inv eps) (inv eps - sqrt(&2) * log M))` THEN
  SUBGOAL_THEN `&0 < d /\ d <= &1 /\ d <= sqrt(&2) * log m + inv eps /\
                d <= inv eps - sqrt(&2) * log M` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `exp((--inv eps + d) / sqrt(&2)) <= m /\ M <= exp((inv eps - d) / sqrt(&2))`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `exp((--inv eps + d) / sqrt(&2)) <= exp(log m) /\
                  exp(log M) <= exp((inv eps - d) / sqrt(&2))` MP_TAC THENL
     [REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[EXP_LOG]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. ~(z = vec 0) ==> inv(norm z) % z IN sphere(vec 0,&1)`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[apx_slab; SUBSET; annulus; IN_ELIM_THM] THEN CONJ_TAC THEN
  X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
  (SUBGOAL_THEN `~(z:real^3 = vec 0)` ASSUME_TAC THENL
    [REWRITE_TAC[GSYM NORM_EQ_0] THEN
     MP_TAC(SPEC `--inv eps / sqrt(&2)` REAL_EXP_POS_LT) THEN
     MP_TAC(SPEC `(inv eps - d) / sqrt(&2)` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC;
     ALL_TAC]) THEN
  ASM_REWRITE_TAC[] THEN
  (SUBGOAL_THEN `inv(norm(z:real^3)) % z IN sphere(vec 0,&1)` ASSUME_TAC THENL
    [ASM_SIMP_TAC[]; ALL_TAC]) THEN
  USE_THEN "mn" (fun th ->
    MP_TAC(MATCH_MP th (ASSUME `inv(norm(z:real^3)) % z IN sphere(vec 0,&1)`))) THEN
  USE_THEN "mx" (fun th ->
    MP_TAC(MATCH_MP th (ASSUME `inv(norm(z:real^3)) % z IN sphere(vec 0,&1)`))) THEN
  ASM_REAL_ARITH_TAC);;

(* N2 in both necks: two points of the collar region of e' (norms in        *)
(* [1,3/2]) have e-levels within 10 of each other, unless both are near the *)
(* ends of e (the min term of the N2 lower bound).                          *)

let APX22_LEVEL_SPAN = prove
 (`!top atlas (g:A->real^3^3) eps z (e:real^3->A) z' (e':real^3->A) v1 v2 y1 y2.
     &0 < eps /\ eps <= &1 / &1024 /\
     apx_eng_n2 top atlas g eps (&1 / &100) /\
     rfs_neck (top,atlas) g eps z e /\ rfs_neck (top,atlas) g eps z' e' /\
     inv(sqrt(mfd_scalar atlas g z')) <= &3 / &2 * inv(sqrt(mfd_scalar atlas g z)) /\
     &1 <= norm v1 /\ norm v1 <= &3 / &2 /\ &1 <= norm v2 /\ norm v2 <= &3 / &2 /\
     y1 IN rfs_neck_dom eps /\ y2 IN rfs_neck_dom eps /\
     e y1 = e' v1 /\ e y2 = e' v2
     ==> min (abs(apx_sval y1 - apx_sval y2))
             (&2 * inv eps - abs(apx_sval y1) - abs(apx_sval y2)) < &10`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(v1:real^3) IN rfs_neck_dom eps /\ (v2:real^3) IN rfs_neck_dom eps`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` APX22_COLLAR_DOM) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN STRIP_TAC THEN CONJ_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&2) /\ sqrt(&2) <= &3 / &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH];
      MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^3. &1 <= norm v /\ norm v <= &3 / &2
                           ==> &0 <= apx_sval v /\ apx_sval v <= &3 / &4`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[apx_sval] THEN
    SUBGOAL_THEN `&0 <= log(norm(v:real^3)) /\ log(norm v) <= &1 / &2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[];
        MP_TAC(SPEC `norm(v:real^3) - &1` LOG_LE) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[REAL_ARITH `&1 + x - &1 = x`] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 / &2 * &1 / &2` THEN
      CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= apx_sval(v1:real^3) /\ apx_sval v1 <= &3 / &4 /\
                &0 <= apx_sval(v2:real^3) /\ apx_sval v2 <= &3 / &4` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`z':A`; `e':real^3->A`; `v1:real^3`; `v2:real^3`] o
    REWRITE_RULE[apx_eng_n2] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_eng_n2")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`z:A`; `e:real^3->A`; `y1:real^3`; `y2:real^3`] o
    REWRITE_RULE[apx_eng_n2] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_eng_n2")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `h = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) z))` THEN
  ABBREV_TAC `h' = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) z'))` THEN
  ABBREV_TAC `mn = min (abs(apx_sval(y1:real^3) - apx_sval y2))
                       (&2 * inv eps - abs(apx_sval y1) - abs(apx_sval y2))` THEN
  ABBREV_TAC `dd = mfd_dist (top,atlas) (g:A->real^3^3) (e'(v1:real^3)) (e' v2)` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 < h /\ &0 < h'` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "h'"] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN
    MATCH_MP_TAC SQRT_POS_LT THEN ASM_MESON_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt(&2) * pi` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `h' * (abs(apx_sval(v1:real^3) - apx_sval v2) + sqrt(&2) * pi) <=
                (&3 / &2 * h) * (&111 / &20)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN MP_TAC APX_SQRT2_PI THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `h * &10 <= h * mn` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* If the low end of a neck e0 lies in the collar of e', the whole collar  *)
(* region e'(1 < |y| <= 3/2) lies at e0-levels below -1/eps + 11.          *)

let APX22_ENDS_FROM_SIDE = prove
 (`!top atlas (g:A->real^3^3) eps z (e0:real^3->A) z' (e':real^3->A) d.
     apx_ch_ctx top atlas g eps /\
     rfs_neck (top,atlas) g eps z e0 /\ rfs_neck (top,atlas) g eps z' e' /\
     IMAGE e' (annulus (&1) (&2)) SUBSET IMAGE e0 (rfs_neck_dom eps) /\
     &0 < d /\ d <= &1 /\
     IMAGE e0 (apx_slab (--inv eps) (--inv eps + d)) SUBSET IMAGE e' (annulus (&1) (&3 / &2))
     ==> IMAGE e' {y | &1 < norm y /\ norm y <= &3 / &2} SUBSET
         IMAGE e0 (apx_slab (--inv eps) (--inv eps + &11))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  APX22_UNFOLD_ASM_TAC "apx_ch_ctx" apx_ch_ctx THEN
  SUBGOAL_THEN `&1024 <= inv eps` ASSUME_TAC THENL
   [MP_TAC(SPECL [`eps:real`; `&1 / &1024`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `eps:real` APX22_COLLAR_DOM) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_param top atlas (rfs_neck_dom eps) (e0:real^3->A) /\
                mfd_param top atlas (rfs_neck_dom eps) (e':real^3->A)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  (* the scale comparison *)
  SUBGOAL_THEN `&5 / &4 % basis 1:real^3 IN annulus (&1) (&2) /\
                &5 / &4 % basis 1:real^3 IN rfs_neck_dom eps` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `norm(&5 / &4 % basis 1:real^3) = &5 / &4` ASSUME_TAC THENL
     [SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term (fun t -> t = `&1 / &4`)) (concl th) &&
        can (find_term (fun t -> t = `rfs_neck_dom eps`)) (concl th))) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(sqrt(mfd_scalar atlas g z')) <=
                &3 / &2 * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) z))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `&3 / &2 * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x1))`))
          (concl th))) THEN
    MAP_EVERY EXISTS_TAC [`e0:real^3->A`; `e':real^3->A`; `&5 / &4 % basis 1:real^3`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (find_term (fun t -> t = `annulus (&1) (&2):real^3->bool`)) (concl th) &&
      not (can (find_term (fun t -> t = `&3 / &2`)) (concl th)))) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the reference point at the low end *)
  ABBREV_TAC `y0 = exp((--inv eps + d / &2) / sqrt(&2)) % basis 1:real^3` THEN
  SUBGOAL_THEN `~(y0:real^3 = vec 0) /\ apx_sval y0 = --inv eps + d / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "y0" THEN
    MP_TAC(SPECL [`--inv eps + d / &2`; `&1`] APX_SVAL_SCALED_BASIS) THEN
    REWRITE_TAC[REAL_LT_01; VECTOR_MUL_LID; LOG_1; REAL_MUL_RZERO; REAL_ADD_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y0:real^3) IN apx_slab (--inv eps) (--inv eps + d) /\
                (y0:real^3) IN apx_slab (--inv eps) (--inv eps + &21 / &2) /\
                (y0:real^3) IN rfs_neck_dom eps` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[APX_SLAB_SVAL; APX_SLAB_NECK_DOM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?v0:real^3. v0 IN annulus (&1) (&3 / &2) /\ (e0:real^3->A) y0 = e' v0`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (e0:real^3->A) (apx_slab (--inv eps) (--inv eps + d)) SUBSET
                 IMAGE (e':real^3->A) (annulus (&1) (&3 / &2))` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `y0:real^3`) THEN ASM_REWRITE_TAC[IN_IMAGE] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  (* every point of the collar region is at a low or a high level *)
  SUBGOAL_THEN
   `IMAGE (e':real^3->A) {y | &1 < norm y /\ norm y <= &3 / &2} SUBSET
    IMAGE e0 (apx_slab (--inv eps) (--inv eps + &21 / &2)) UNION
    IMAGE e0 (apx_slab (inv eps - &10) (inv eps))` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `?y:real^3. y IN rfs_neck_dom eps /\ (e':real^3->A) v = e0 y`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `IMAGE (e':real^3->A) (annulus (&1) (&2)) SUBSET
                   IMAGE e0 (rfs_neck_dom eps)` THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      DISCH_THEN(MP_TAC o SPEC `v:real^3`) THEN
      ANTS_TAC THENL [REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `z:A`; `e0:real^3->A`; `z':A`; `e':real^3->A`;
                   `v0:real^3`; `v:real^3`; `y0:real^3`; `y:real^3`] APX22_LEVEL_SPAN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(v0:real^3) IN annulus (&1) (&3 / &2)` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      DISCH_TAC] THEN
    MP_TAC(SPECL [`eps:real`; `y:real^3`] APX_SVAL_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[IN_UNION] THEN
    SUBGOAL_THEN `apx_sval(y:real^3) < --inv eps + &21 / &2 \/ inv eps - &10 < apx_sval y`
    MP_TAC THENL
     [UNDISCH_TAC `min (abs(apx_sval(y0:real^3) - apx_sval(y:real^3)))
                       (&2 * inv eps - abs(apx_sval y0) - abs(apx_sval y)) < &10` THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `abs(--inv eps + d / &2) = inv eps - d / &2` SUBST1_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_MIN_LT] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    STRIP_TAC THENL
     [DISJ1_TAC; DISJ2_TAC] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* connectedness *)
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `IMAGE (e0:real^3->A) (apx_slab (--inv eps) (--inv eps + &21 / &2))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC APX_SLAB_SUBSET THEN REAL_ARITH_TAC] THEN
  MATCH_MP_TAC APX22_CONNECTED_TWO THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`;
                        `IMAGE (e0:real^3->A) (apx_slab (inv eps - &10) (inv eps))`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`vec 0:real^3`; `&1`; `&3 / &2`] (CONJUNCT1(CONJUNCT2 CONNECTED_ANNULUS))) THEN
      REWRITE_TAC[VECTOR_SUB_RZERO; DIMINDEX_3; ARITH];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
        `!a b c:real^3->bool. a SUBSET b ==> c SUBSET a ==> c SUBSET b`) o check (fun th ->
        can (find_term (fun t -> t = `&1 / &4`)) (concl th) && not(is_forall(concl th)) &&
        can (find_term (fun t -> t = `rfs_neck_dom eps`)) (concl th))) THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC];
    MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
    ASM_REWRITE_TAC[apx_slab; OPEN_ANNULUS] THEN
    REWRITE_TAC[GSYM apx_slab] THEN MATCH_MP_TAC APX_SLAB_SUB_DOM THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
    ASM_REWRITE_TAC[apx_slab; OPEN_ANNULUS] THEN
    REWRITE_TAC[GSYM apx_slab] THEN MATCH_MP_TAC APX_SLAB_SUB_DOM THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC APX_IMAGE_SLABS_DISJOINT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `eps:real`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC APX_SLAB_SUB_DOM) THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `(e0:real^3->A) y0` THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      UNDISCH_TAC `(v0:real^3) IN annulus (&1) (&3 / &2)` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]]);;

(* L1 core: the collar sphere e'(sphere 3/2) is a section of the complement *)
(* neck e; the collar contains one of its sides, hence an end of e.  Orient *)
(* e (e or apx_rev e) so that this is the low end.                           *)

let APX22_CAP_ENDS_RAW = prove
 (`!top atlas (g:A->real^3^3) eps z (e:real^3->A) z' (e':real^3->A) K U.
     apx_ch_ctx top atlas g eps /\ apx_ch_n4r top atlas g eps /\
     rfs_neck (top,atlas) g eps z e /\ rfs_neck (top,atlas) g eps z' e' /\
     IMAGE e (rfs_neck_dom eps) = U DIFF K /\
     IMAGE e' (annulus (&1) (&2)) SUBSET U DIFF K /\
     top closure_of (IMAGE e' (annulus (&1) (&3 / &2))) SUBSET
       K UNION IMAGE e' {y | &1 < norm y /\ norm y <= &3 / &2}
     ==> ?e0 d. (e0 = e \/ e0 = apx_rev e) /\ &0 < d /\ d <= &1 /\
               IMAGE e0 (apx_slab (--inv eps) (--inv eps + d)) SUBSET
                 IMAGE e' (annulus (&1) (&3 / &2)) /\
               IMAGE e' {y | &1 < norm y /\ norm y <= &3 / &2} SUBSET
                 IMAGE e0 (apx_slab (--inv eps) (--inv eps + &11))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  APX22_UNFOLD_ASM_TAC "apx_ch_ctx" apx_ch_ctx THEN
  MP_TAC(SPEC `eps:real` APX22_COLLAR_DOM) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_param top atlas (rfs_neck_dom eps) (e:real^3->A) /\
                mfd_param top atlas (rfs_neck_dom eps) (e':real^3->A)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  (* facts about the collar of e' *)
  SUBGOAL_THEN `annulus (&1) (&2) SUBSET rfs_neck_dom eps /\
                annulus (&1) (&3 / &2) SUBSET rfs_neck_dom eps /\
                sphere(vec 0:real^3,&3 / &2) SUBSET rfs_neck_dom eps`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
      `!a b c:real^3->bool. a SUBSET b ==> c SUBSET a ==> c SUBSET b`) o check (fun th ->
      can (find_term (fun t -> t = `&1 / &4`)) (concl th) &&
      can (find_term (fun t -> t = `rfs_neck_dom eps`)) (concl th))) THEN
    REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM; IN_SPHERE_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (e':real^3->A) (sphere(vec 0,&3 / &2)) SUBSET U DIFF K /\
                IMAGE (e':real^3->A) (annulus (&1) (&3 / &2)) SUBSET U DIFF K`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (e':real^3->A) (annulus (&1) (&2))` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM; IN_SPHERE_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (IMAGE (e':real^3->A) (annulus (&1) (&3 / &2)))
                         (IMAGE e' (sphere(vec 0,&3 / &2)))` ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    X_GEN_TAC `q:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `v1:real^3` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `v2:real^3` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `v1:real^3 = v2` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_INJ THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `rfs_neck_dom eps`; `e':real^3->A`] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `(v1:real^3) IN annulus (&1) (&3 / &2)` THEN
        UNDISCH_TAC `annulus (&1) (&3 / &2) SUBSET rfs_neck_dom eps` THEN SET_TAC[];
        UNDISCH_TAC `(v2:real^3) IN sphere(vec 0,&3 / &2)` THEN
        UNDISCH_TAC `sphere(vec 0:real^3,&3 / &2) SUBSET rfs_neck_dom eps` THEN SET_TAC[];
        UNDISCH_TAC `q = (e':real^3->A) v1` THEN UNDISCH_TAC `q = (e':real^3->A) v2` THEN
        MESON_TAC[]];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC [`(v2:real^3) IN annulus (&1) (&3 / &2)`;
                           `(v2:real^3) IN sphere(vec 0,&3 / &2)`] THEN
    REWRITE_TAC[annulus; IN_ELIM_THM; IN_SPHERE_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (e':real^3->A) {y | &1 < norm y /\ norm y <= &3 / &2} =
                IMAGE e' (annulus (&1) (&3 / &2)) UNION IMAGE e' (sphere(vec 0,&3 / &2))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_UNION] THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_UNION; annulus; IN_ELIM_THM; IN_SPHERE_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (IMAGE (e':real^3->A) (annulus (&1) (&3 / &2)))` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
    ASM_REWRITE_TAC[OPEN_ANNULUS] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `annulus (&1) (&2):real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(IMAGE (e':real^3->A) (annulus (&1) (&3 / &2)) = {})` ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_EQ_EMPTY] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `&5 / &4 % basis 1:real^3` THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN
    SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the section and its sides *)
  SUBGOAL_THEN `apx_section (e:real^3->A) (exp(--(inv(sqrt(&2) * eps))))
                            (exp(inv(sqrt(&2) * eps)))
                            (IMAGE (e':real^3->A) (sphere(vec 0,&3 / &2)))`
  MP_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[apx_ch_n4r] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_ch_n4r")) (concl th))) THEN
    MAP_EVERY EXISTS_TAC [`z:A`; `z':A`] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP APX_SECTION_DATA) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `e:real^3->A`;
                 `exp(--inv eps / sqrt(&2))`; `exp(inv eps / sqrt(&2))`; `u:real^3->real`]
                APX_SECTION_SPLIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_EXP_POS_LT; GSYM(REWRITE_RULE[apx_slab] APX_SLAB_NECK_DOM)];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM(REWRITE_RULE[apx_slab] APX_SLAB_NECK_DOM)] THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
      lhs(concl th) = `IMAGE (e':real^3->A) (sphere(vec 0,&3 / &2))`
    then REWRITE_TAC[GSYM th] else failwith "no") THEN
  REWRITE_TAC[ASSUME `IMAGE (e:real^3->A) (rfs_neck_dom eps) = U DIFF K`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`u:real^3->real`; `eps:real`] APX22_SIDE_ENDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `Cl = IMAGE (e':real^3->A) (annulus (&1) (&3 / &2))` THEN
  ABBREV_TAC `S = IMAGE (e':real^3->A) (sphere(vec 0,&3 / &2))` THEN
  ABBREV_TAC `Nin = IMAGE (e:real^3->A)
                     {z | ~(z = vec 0) /\ exp(--inv eps / sqrt(&2)) < norm z /\
                          norm z < u(inv(norm z) % z)}` THEN
  ABBREV_TAC `Nout = IMAGE (e:real^3->A)
                     {z | ~(z = vec 0) /\ u(inv(norm z) % z) < norm z /\
                          norm z < exp(inv eps / sqrt(&2))}` THEN
  (* the clopen dichotomy for the two sides *)
  SUBGOAL_THEN `!N:A->bool. connected_in top N /\ N SUBSET U DIFF K /\ DISJOINT S N
                            ==> N SUBSET Cl \/ DISJOINT N Cl` ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC APX22_CLOPEN_SPLIT THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`top closure_of (Cl:A->bool) SUBSET
       K UNION IMAGE (e':real^3->A) {y | &1 < norm y /\ norm y <= &3 / &2}`;
      `IMAGE (e':real^3->A) {y | &1 < norm y /\ norm y <= &3 / &2} = Cl UNION S`;
      `(N:A->bool) SUBSET U DIFF K`; `DISJOINT (S:A->bool) N`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Nin:A->bool) SUBSET Cl \/ (Nout:A->bool) SUBSET Cl` MP_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `Nin:A->bool`) THEN
    FIRST_ASSUM(MP_TAC o SPEC `Nout:A->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN
    MAP_EVERY UNDISCH_TAC
     [`(Nin:A->bool) SUBSET Cl \/ DISJOINT Nin Cl`;
      `(Nout:A->bool) SUBSET Cl \/ DISJOINT Nout Cl`;
      `U DIFF K:A->bool = S UNION Nin UNION Nout`;
      `(Cl:A->bool) SUBSET U DIFF K`; `DISJOINT (Cl:A->bool) S`; `~(Cl:A->bool = {})`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [(* the low side lies in the collar: e itself *)
    SUBGOAL_THEN `IMAGE (e:real^3->A) (apx_slab (--inv eps) (--inv eps + d)) SUBSET Cl`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `Nin:A->bool` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "Nin" THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`e:real^3->A`; `d:real`] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `z:A`; `e:real^3->A`; `z':A`; `e':real^3->A`; `d:real`]
                  APX22_ENDS_FROM_SIDE) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `IMAGE (e':real^3->A) (annulus (&1) (&2)) SUBSET U DIFF K` THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    (* the high side lies in the collar: the reversed neck *)
    SUBGOAL_THEN `IMAGE (apx_rev (e:real^3->A)) (apx_slab (--inv eps) (--inv eps + d)) =
                  IMAGE e (apx_slab (inv eps - d) (inv eps))` ASSUME_TAC THENL
     [REWRITE_TAC[APX_REV_IMAGE_SLAB; REAL_NEG_NEG; REAL_ARITH `--(--a + b) = a - b`];
      ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (e:real^3->A) (apx_slab (inv eps - d) (inv eps)) SUBSET Cl`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `Nout:A->bool` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "Nout" THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (apx_rev (e:real^3->A)) (apx_slab (--inv eps) (--inv eps + d)) SUBSET Cl`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `rfs_neck (top,atlas) (g:A->real^3^3) eps z (apx_rev e) /\
                  IMAGE (apx_rev (e:real^3->A)) (rfs_neck_dom eps) = U DIFF K`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[APX_REV_NECK; APX_REV_IMAGE_DOM]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`apx_rev(e:real^3->A)`; `d:real`] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `z:A`; `apx_rev(e:real^3->A)`; `z':A`; `e':real^3->A`; `d:real`]
                  APX22_ENDS_FROM_SIDE) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `IMAGE (e':real^3->A) (annulus (&1) (&2)) SUBSET U DIFF K` THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]]]);;

(* Images of closed shells inside the neck domain are closed. *)

let APX22_SHELL_CLOSED = prove
 (`!top atlas (e:real^3->A) eps a b.
     hausdorff_space top /\ mfd_param top atlas (rfs_neck_dom eps) e /\
     exp(--inv eps / sqrt(&2)) < a /\ b < exp(inv eps / sqrt(&2))
     ==> closed_in top (IMAGE e {y:real^3 | a <= norm y /\ norm y <= b})`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE THEN
  MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `{y:real^3 | a <= norm y /\ norm y <= b} = cball(vec 0,b) DIFF ball(vec 0,a)`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC;
      SIMP_TAC[COMPACT_DIFF; COMPACT_CBALL; OPEN_BALL]];
    REWRITE_TAC[APX_SLAB_NECK_DOM; apx_slab; SUBSET; annulus; IN_ELIM_THM] THEN
    GEN_TAC THEN ASM_REAL_ARITH_TAC]);;

(* L1 CAP_ENDS.  For a cap U with closed core K, the complement neck e0      *)
(* (oriented) satisfies: W = K + e0(levels < 0) is open, its closure adds    *)
(* only points of the central sphere, and the frontier of U lies in the      *)
(* closure of the top slab (levels > 1/eps - 1).                             *)

let APX22_CAP_ENDS = prove
 (`!top atlas (g:A->real^3^3) C eps U Y.
     apx_ch_ctx top atlas g eps /\ apx_ch_n4r top atlas g eps /\
     rfs_cap (top,atlas) g C eps U Y
     ==> open_in top U /\ ~(Y = {}) /\
         ?e0 z K.
           rfs_neck (top,atlas) g eps z e0 /\
           IMAGE e0 (rfs_neck_dom eps) = U DIFF K /\
           compact_in top K /\ K SUBSET U /\ top closure_of Y SUBSET K /\ Y SUBSET K /\
           open_in top (K UNION IMAGE e0 (apx_slab (--inv eps) (&0))) /\
           top closure_of (K UNION IMAGE e0 (apx_slab (--inv eps) (&0))) SUBSET
             K UNION IMAGE e0 (apx_slab (--inv eps) (&0)) UNION IMAGE e0 (sphere(vec 0,&1)) /\
           top frontier_of U SUBSET
             top closure_of (IMAGE e0 (apx_slab (inv eps - &1) (inv eps)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  APX22_UNFOLD_ASM_TAC "apx_ch_ctx" apx_ch_ctx THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`] APX22_CAP_DATA) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `z:A`; `e:real^3->A`; `z':A`; `e':real^3->A`; `K:A->bool`;
                 `U:A->bool`] APX22_CAP_ENDS_RAW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real^3->A` (X_CHOOSE_THEN `d:real`
    (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `rfs_neck (top,atlas) (g:A->real^3^3) eps z e0 /\
                IMAGE (e0:real^3->A) (rfs_neck_dom eps) = U DIFF K` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN
    ASM_SIMP_TAC[APX_REV_NECK; APX_REV_IMAGE_DOM];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`e0:real^3->A`; `z:A`; `K:A->bool`] THEN ASM_REWRITE_TAC[] THEN
  (* basic facts *)
  SUBGOAL_THEN `&1024 <= inv eps` ASSUME_TAC THENL
   [MP_TAC(SPECL [`eps:real`; `&1 / &1024`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param top atlas (rfs_neck_dom eps) (e0:real^3->A)` ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  SUBGOAL_THEN `closed_in top (K:A->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `exp(--inv eps / sqrt(&2)) < exp((--inv eps + d / &2) / sqrt(&2)) /\
    exp((--inv eps + d / &2) / sqrt(&2)) <= exp((--inv eps + d) / sqrt(&2)) /\
    exp(&0 / sqrt(&2)) = &1 /\ &1 < exp(inv eps / sqrt(&2)) /\
    exp((inv eps - &1) / sqrt(&2)) < exp(inv eps / sqrt(&2))` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_MONO_LT; REAL_EXP_MONO_LE] THEN
    ASM_SIMP_TAC[REAL_LT_DIV2_EQ; REAL_LE_DIV2_EQ] THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_EXP_0] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EXP_LT_1 THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `Cl = IMAGE (e':real^3->A) (annulus (&1) (&3 / &2))` THEN
  ABBREV_TAC `CS = IMAGE (e':real^3->A) {y | &1 < norm y /\ norm y <= &3 / &2}` THEN
  SUBGOAL_THEN `(Cl:A->bool) SUBSET CS /\ (Cl:A->bool) SUBSET topspace top` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["Cl"; "CS"] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET_UNION; SUBSET_TRANS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(CS:A->bool) SUBSET IMAGE e0 (apx_slab (--inv eps) (&0)) /\
                IMAGE (e0:real^3->A) (apx_slab (--inv eps) (&0)) SUBSET U DIFF K`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (e0:real^3->A) (apx_slab (--inv eps) (--inv eps + &11))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC APX_SLAB_SUBSET THEN
      ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(fun th -> if concl th = `IMAGE (e0:real^3->A) (rfs_neck_dom eps) = U DIFF K`
        then REWRITE_TAC[SYM th] THEN ASSUME_TAC th else failwith "no") THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC APX_SLAB_SUB_DOM THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `top closure_of (Cl:A->bool) SUBSET K UNION IMAGE e0 (apx_slab (--inv eps) (&0))`
  ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`top closure_of (Cl:A->bool) SUBSET K UNION CS`;
                           `(CS:A->bool) SUBSET IMAGE e0 (apx_slab (--inv eps) (&0))`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the middle shells *)
  ABBREV_TAC `Mi = {y:real^3 | exp((--inv eps + d / &2) / sqrt(&2)) <= norm y /\ norm y <= &1}` THEN
  ABBREV_TAC `Mo = {y:real^3 | exp((--inv eps + d / &2) / sqrt(&2)) <= norm y /\
                               norm y <= exp((inv eps - &1) / sqrt(&2))}` THEN
  SUBGOAL_THEN `closed_in top (IMAGE (e0:real^3->A) Mi) /\ closed_in top (IMAGE (e0:real^3->A) Mo)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Mi"; "Mo"] THEN CONJ_TAC THEN MATCH_MP_TAC APX22_SHELL_CLOSED THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `eps:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `apx_slab (--inv eps) (&0) SUBSET apx_slab (--inv eps) (--inv eps + d) UNION Mi /\
    Mi SUBSET apx_slab (--inv eps) (&0) UNION sphere(vec 0,&1) /\
    rfs_neck_dom eps SUBSET apx_slab (--inv eps) (--inv eps + d) UNION Mo UNION
                            apx_slab (inv eps - &1) (inv eps) /\
    Mo SUBSET rfs_neck_dom eps`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Mi"; "Mo"] THEN
    REWRITE_TAC[APX_SLAB_NECK_DOM] THEN
    REWRITE_TAC[apx_slab; SUBSET; annulus; IN_ELIM_THM; IN_UNION; IN_SPHERE_0] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* W is open *)
    SUBGOAL_THEN `K UNION IMAGE (e0:real^3->A) (apx_slab (--inv eps) (&0)) =
                  (K UNION Cl) UNION IMAGE e0 (apx_slab (--inv eps) (&0))` SUBST1_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`(Cl:A->bool) SUBSET CS`;
                             `(CS:A->bool) SUBSET IMAGE e0 (apx_slab (--inv eps) (&0))`] THEN
      SET_TAC[];
      MATCH_MP_TAC OPEN_IN_UNION THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[apx_slab; OPEN_ANNULUS];
        MATCH_MP_TAC APX_SLAB_SUB_DOM THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* the closure of W *)
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `K UNION top closure_of (Cl:A->bool) UNION IMAGE (e0:real^3->A) Mi` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN
      ASM_SIMP_TAC[CLOSED_IN_UNION; CLOSED_IN_CLOSURE_OF] THEN
      MP_TAC(ISPECL [`top:A topology`; `Cl:A->bool`] CLOSURE_OF_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `IMAGE (e0:real^3->A) (apx_slab (--inv eps) (&0)) SUBSET
                    IMAGE e0 (apx_slab (--inv eps) (--inv eps + d)) UNION IMAGE e0 Mi`
      MP_TAC THENL
       [REWRITE_TAC[GSYM IMAGE_UNION] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
        MAP_EVERY UNDISCH_TAC
         [`IMAGE (e0:real^3->A) (apx_slab (--inv eps) (--inv eps + d)) SUBSET Cl`;
          `(Cl:A->bool) SUBSET top closure_of Cl`] THEN
        SET_TAC[]];
      SUBGOAL_THEN `IMAGE (e0:real^3->A) Mi SUBSET
                    IMAGE e0 (apx_slab (--inv eps) (&0)) UNION IMAGE e0 (sphere(vec 0,&1))`
      MP_TAC THENL
       [REWRITE_TAC[GSYM IMAGE_UNION] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `top closure_of (Cl:A->bool) SUBSET
                     K UNION IMAGE e0 (apx_slab (--inv eps) (&0))` THEN
        SET_TAC[]]];
    ALL_TAC] THEN
  (* the frontier of U *)
  SUBGOAL_THEN `top frontier_of U = top closure_of U DIFF (U:A->bool)` SUBST1_TAC THENL
   [MATCH_MP_TAC FRONTIER_OF_OPEN_IN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `top closure_of (U:A->bool) SUBSET
    K UNION top closure_of Cl UNION IMAGE (e0:real^3->A) Mo UNION
    top closure_of (IMAGE e0 (apx_slab (inv eps - &1) (inv eps)))` MP_TAC THENL
   [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN
    ASM_SIMP_TAC[CLOSED_IN_UNION; CLOSED_IN_CLOSURE_OF] THEN
    MP_TAC(ISPECL [`top:A topology`; `Cl:A->bool`] CLOSURE_OF_SUBSET) THEN
    MP_TAC(ISPECL [`top:A topology`;
                   `IMAGE (e0:real^3->A) (apx_slab (inv eps - &1) (inv eps))`]
                  CLOSURE_OF_SUBSET) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_IMAGE_SUBSET THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APX_SLAB_SUB_DOM THEN ASM_REAL_ARITH_TAC;
      DISCH_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `IMAGE (e0:real^3->A) (rfs_neck_dom eps) SUBSET
                  IMAGE e0 (apx_slab (--inv eps) (--inv eps + d)) UNION IMAGE e0 Mo UNION
                  IMAGE e0 (apx_slab (inv eps - &1) (inv eps))` MP_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_UNION] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`IMAGE (e0:real^3->A) (rfs_neck_dom eps) = U DIFF K`; `(K:A->bool) SUBSET U`;
      `IMAGE (e0:real^3->A) (apx_slab (--inv eps) (--inv eps + d)) SUBSET Cl`;
      `(Cl:A->bool) SUBSET top closure_of Cl`;
      `IMAGE (e0:real^3->A) (apx_slab (inv eps - &1) (inv eps)) SUBSET
       top closure_of (IMAGE e0 (apx_slab (inv eps - &1) (inv eps)))`] THEN
    MATCH_ACCEPT_TAC(SET_RULE
     `!U K D A B C Cl cCl cC:A->bool.
        C SUBSET cC ==> Cl SUBSET cCl ==> A SUBSET Cl ==> K SUBSET U ==> D = U DIFF K ==>
        D SUBSET A UNION B UNION C ==> U SUBSET K UNION cCl UNION B UNION cC`);
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (e0:real^3->A) Mo SUBSET U` MP_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (e0:real^3->A) (rfs_neck_dom eps)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `IMAGE (e0:real^3->A) (rfs_neck_dom eps) = U DIFF K` THEN
      MATCH_ACCEPT_TAC(SET_RULE `!D U K:A->bool. D = U DIFF K ==> D SUBSET U`)];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`top closure_of (Cl:A->bool) SUBSET K UNION IMAGE e0 (apx_slab (--inv eps) (&0))`;
    `IMAGE (e0:real^3->A) (apx_slab (--inv eps) (&0)) SUBSET U DIFF K`;
    `(K:A->bool) SUBSET U`] THEN
  MATCH_ACCEPT_TAC(SET_RULE
   `!K U S0 cCl Mo cU cT:A->bool.
      K SUBSET U ==> S0 SUBSET U DIFF K ==> cCl SUBSET K UNION S0 ==> Mo SUBSET U ==>
      cU SUBSET K UNION cCl UNION Mo UNION cT ==> cU DIFF U SUBSET cT`));;

(* ------------------------------------------------------------------------- *)
(* L2 SMALL_FRONTIER and the crossing of curves.  Two points of              *)
(* the closure of the top slab of a neck are joinable and at distance at     *)
(* most (1 + 1/100) h (1 + sqrt 2 pi) (N2 and the continuity of the          *)
(* distance); with L1 this bounds the frontier of a cap.  A curve from an    *)
(* open set W to its complement passes through a point of the closure of W   *)
(* outside W.                                                                *)
(* ------------------------------------------------------------------------- *)

let APX22_TOP_CLOSURE_DIST = prove
 (`!top atlas (g:A->real^3^3) eps z (e:real^3->A) f1 f2.
     apx_ch_ctx top atlas g eps /\ rfs_neck (top,atlas) g eps z e /\
     f1 IN top closure_of (IMAGE e (apx_slab (inv eps - &1) (inv eps))) /\
     f2 IN top closure_of (IMAGE e (apx_slab (inv eps - &1) (inv eps)))
     ==> mfd_joinable (top,atlas) f1 f2 /\
         mfd_dist (top,atlas) g f1 f2 <=
         (&1 + &1 / &100) * inv(sqrt(mfd_scalar atlas g z)) * (&1 + sqrt(&2) * pi)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  APX22_UNFOLD_ASM_TAC "apx_ch_ctx" apx_ch_ctx THEN
  SUBGOAL_THEN `&1024 <= inv eps` ASSUME_TAC THENL
   [MP_TAC(SPECL [`eps:real`; `&1 / &1024`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `A = IMAGE (e:real^3->A) (apx_slab (inv eps - &1) (inv eps))` THEN
  ABBREV_TAC `c = (&1 + &1 / &100) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) z)) *
                  (&1 + sqrt(&2) * pi)` THEN
  SUBGOAL_THEN `apx_slab (inv eps - &1) (inv eps) SUBSET rfs_neck_dom eps` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_SLAB_SUB_DOM THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(A:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN MATCH_MP_TAC MFD_PARAM_IMAGE_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[rfs_neck];
    ALL_TAC] THEN
  (* pairs of points of the slab *)
  SUBGOAL_THEN `!a1 a2:A. a1 IN A /\ a2 IN A
                          ==> mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) a1 a2 /\
                              mfd_dist (top,atlas) (g:A->real^3^3) a1 a2 <= c`
  ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `y1:real^3` THEN DISCH_TAC THEN X_GEN_TAC `y2:real^3` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL [`z:A`; `e:real^3->A`; `y1:real^3`; `y2:real^3`] o
      REWRITE_RULE[apx_eng_n2] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_eng_n2")) (concl th) &&
        can (find_term (fun t -> t = `&1 / &100`)) (concl th))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
      UNDISCH_TAC `apx_slab (inv eps - &1) (inv eps) SUBSET rfs_neck_dom eps` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o CONJUNCT1)) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN EXPAND_TAC "c" THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SQRT_POS_LE THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_MESON_TAC[rfs_neck];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= &1 ==> x + p <= &1 + p`) THEN
    MAP_EVERY UNDISCH_TAC [`(y1:real^3) IN apx_slab (inv eps - &1) (inv eps)`;
                           `(y2:real^3) IN apx_slab (inv eps - &1) (inv eps)`] THEN
    REWRITE_TAC[APX_SLAB_SVAL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the distance bound passes to the closure *)
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^3^3) f1 f2 <= c` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`]
                  MFD_DIST_CONTINUOUS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\(x,y). mfd_dist (top,atlas) (g:A->real^3^3) x y`;
                   `prod_topology (top:A topology) top`; `euclideanreal`;
                   `{r:real | r <= c}`] CLOSED_IN_CONTINUOUS_MAP_PREIMAGE) THEN
    ASM_REWRITE_TAC[GSYM REAL_CLOSED_IN; REAL_CLOSED_HALFSPACE_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `prod_topology (top:A topology) top closure_of ((A:A->bool) CROSS A) SUBSET
      {x | x IN topspace(prod_topology top top) /\
           (\(x,y). mfd_dist (top,atlas) (g:A->real^3^3) x y) x IN {r | r <= c}}`
    MP_TAC THENL
     [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_CROSS; IN_ELIM_THM; TOPSPACE_PROD_TOPOLOGY] THEN
      CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
      MAP_EVERY X_GEN_TAC [`a1:A`; `a2:A`] THEN STRIP_TAC THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[CLOSURE_OF_CROSS; SUBSET; FORALL_PAIR_THM; IN_CROSS; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`f1:A`; `f2:A`]) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* joinability of the limit points *)
  SUBGOAL_THEN `!f:A. f IN top closure_of A
                      ==> ?a. a IN A /\
                              mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) f a`
  ASSUME_TAC THENL
   [X_GEN_TAC `f:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `f:A`]
                  MFD_JOINABLE_OPEN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `(f:A) IN top closure_of A` THEN REWRITE_TAC[IN_CLOSURE_OF] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (MP_TAC o SPEC `{y:A | mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) f y}`)) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; MFD_JOINABLE_REFL] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(f1:A) IN top closure_of A`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:A` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(f2:A) IN top closure_of A`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `a2:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) (a1:A) a2`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `a1:A` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `a2:A` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[MFD_JOINABLE_SYM]);;

(* L2 for caps: two frontier points of a cap are joinable and close. *)

let APX22_SMALL_FRONTIER = prove
 (`!top atlas (g:A->real^3^3) eps z (e0:real^3->A) U f1 f2.
     apx_ch_ctx top atlas g eps /\ rfs_neck (top,atlas) g eps z e0 /\
     top frontier_of U SUBSET
       top closure_of (IMAGE e0 (apx_slab (inv eps - &1) (inv eps))) /\
     f1 IN top frontier_of U /\ f2 IN top frontier_of U
     ==> mfd_joinable (top,atlas) f1 f2 /\
         mfd_dist (top,atlas) g f1 f2 <=
         (&1 + &1 / &100) * inv(sqrt(mfd_scalar atlas g z)) * (&1 + sqrt(&2) * pi)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC APX22_TOP_CLOSURE_DIST THEN
  MAP_EVERY EXISTS_TAC [`eps:real`; `e0:real^3->A`] THEN ASM SET_TAC[]);;

(* A curve from an open set W to a point outside W meets the closure of W *)
(* outside W.                                                             *)

let APX22_CURVE_CROSS = prove
 (`!top atlas (gamma:real->A) a b W.
     mfd_c1_curve (top,atlas:((A->bool)#(A->real^3))->bool) gamma a b /\
     open_in top W /\ gamma a IN W /\ ~(gamma b IN W)
     ==> ?t. a <= t /\ t <= b /\ gamma t IN top closure_of W /\ ~(gamma t IN W)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  APX22_UNFOLD_ASM_TAC "mfd_c1_curve" mfd_c1_curve THEN
  SUBGOAL_THEN `connected_in top (IMAGE (gamma:real->A) (real_interval[a,b]))` ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
    EXISTS_TAC `subtopology euclideanreal (real_interval[a,b])` THEN
    ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; SUBSET_REFL; CONNECTED_IN_EUCLIDEANREAL_INTERVAL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `IMAGE (gamma:real->A) (real_interval[a,b])`; `W:A->bool`]
                CONNECTED_IN_INTER_FRONTIER_OF) THEN
  ASM_SIMP_TAC[FRONTIER_OF_OPEN_IN] THEN ANTS_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_DIFF; IN_IMAGE; IN_REAL_INTERVAL] THEN
    CONJ_TAC THENL
     [EXISTS_TAC `(gamma:real->A) a` THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `a:real` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      EXISTS_TAC `(gamma:real->A) b` THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `b:real` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_DIFF; IN_IMAGE; IN_REAL_INTERVAL] THEN
    MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* L3 CORE_FAR and L4 DEEP.  With the data of L1 for a cap U                 *)
(* (W = K + e0(levels < 0), closure W inside W + e0(sphere 1)): a curve     *)
(* from the closed core K to a point outside W passes through the central   *)
(* sphere, so its length is at least (99/100) h / eps (the N2 curve bound   *)
(* in the form APX_FRONTIER_LOWER); likewise for a curve from W to a point  *)
(* outside U.  If a cap U' inside U has a frontier point in K, its frontier *)
(* lies in W: otherwise L2 for U' and L3 for U conflict, the scales of the  *)
(* two complement necks being comparable (apx_ch_ctx).                      *)
(* ------------------------------------------------------------------------- *)

let APX22_SIGMA_CROSS = prove
 (`!top atlas (gamma:real->A) a b W Sg.
     mfd_c1_curve (top,atlas:((A->bool)#(A->real^3))->bool) gamma a b /\
     open_in top W /\ top closure_of W SUBSET W UNION Sg /\
     gamma a IN W /\ ~(gamma b IN W)
     ==> ?t. a <= t /\ t <= b /\ gamma t IN Sg`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `gamma:real->A`;
                 `a:real`; `b:real`; `W:A->bool`] APX22_CURVE_CROSS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* A point of the central sphere of a neck: in the domain, at level 0. *)

let APX22_SIGMA_POINT = prove
 (`!eps (e0:real^3->A) q.
     &0 < eps /\ q IN IMAGE e0 (sphere(vec 0,&1))
     ==> ?y. y IN rfs_neck_dom eps /\ apx_sval y = &0 /\ q = e0 y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    MATCH_MP_TAC APX_SVAL_UNIT THEN ASM_MESON_TAC[IN_SPHERE_0]]);;

(* L3: the closed core is far from the complement of W. *)

let APX22_CORE_FAR = prove
 (`!top atlas (g:A->real^3^3) eps z (e0:real^3->A) K p f.
     apx_ch_ctx top atlas g eps /\ rfs_neck (top,atlas) g eps z e0 /\
     DISJOINT K (IMAGE e0 (rfs_neck_dom eps)) /\
     open_in top (K UNION IMAGE e0 (apx_slab (--inv eps) (&0))) /\
     top closure_of (K UNION IMAGE e0 (apx_slab (--inv eps) (&0))) SUBSET
       K UNION IMAGE e0 (apx_slab (--inv eps) (&0)) UNION IMAGE e0 (sphere(vec 0,&1)) /\
     p IN K /\ ~(f IN K UNION IMAGE e0 (apx_slab (--inv eps) (&0))) /\
     mfd_joinable (top,atlas) p f
     ==> &99 / &100 * inv(sqrt(mfd_scalar atlas g z)) * inv eps <=
         mfd_dist (top,atlas) g p f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  APX22_UNFOLD_ASM_TAC "apx_ch_ctx" apx_ch_ctx THEN
  MATCH_MP_TAC APX_DIST_GE_CURVES THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `gamma:real->A` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `gamma:real->A`;
                 `&0`; `&1`; `K UNION IMAGE (e0:real^3->A) (apx_slab (--inv eps) (&0))`;
                 `IMAGE (e0:real^3->A) (sphere(vec 0,&1))`] APX22_SIGMA_CROSS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[UNION_ASSOC] THEN ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[IN_UNION];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`eps:real`; `e0:real^3->A`; `(gamma:real->A) t`] APX22_SIGMA_POINT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `gamma:real->A`; `&0`; `t:real`; `&1`] MFD_LENGTH_COMBINE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `gamma:real->A`; `t:real`; `&1`] MFD_LENGTH_POS_LE) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `gamma:real->A`; `&0`; `t:real`] MFD_DIST_LE_LENGTH) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `gamma:real->A`; `&0`; `t:real`] MFD_C1_CURVE_JOINABLE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `z:A`; `e0:real^3->A`; `p:A`; `y:real^3`] APX_FRONTIER_LOWER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `DISJOINT (K:A->bool) (IMAGE (e0:real^3->A) (rfs_neck_dom eps))` THEN
    UNDISCH_TAC `(p:A) IN K` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_ABS_NUM; REAL_SUB_RZERO] THEN DISCH_TAC THEN
  ASM_REAL_ARITH_TAC);;

(* L4, curve form: a curve from W to a point outside U is long. *)

let APX22_EXIT_FAR = prove
 (`!top atlas (g:A->real^3^3) eps z (e0:real^3->A) K U (gamma:real->A) a b.
     apx_ch_ctx top atlas g eps /\ rfs_neck (top,atlas) g eps z e0 /\
     IMAGE e0 (rfs_neck_dom eps) SUBSET U /\
     K UNION IMAGE e0 (apx_slab (--inv eps) (&0)) SUBSET U /\
     open_in top (K UNION IMAGE e0 (apx_slab (--inv eps) (&0))) /\
     top closure_of (K UNION IMAGE e0 (apx_slab (--inv eps) (&0))) SUBSET
       K UNION IMAGE e0 (apx_slab (--inv eps) (&0)) UNION IMAGE e0 (sphere(vec 0,&1)) /\
     mfd_c1_curve (top,atlas) gamma a b /\
     gamma a IN K UNION IMAGE e0 (apx_slab (--inv eps) (&0)) /\ ~(gamma b IN U)
     ==> &99 / &100 * inv(sqrt(mfd_scalar atlas g z)) * inv eps <=
         mfd_length atlas g gamma a b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  APX22_UNFOLD_ASM_TAC "apx_ch_ctx" apx_ch_ctx THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `gamma:real->A`;
                 `a:real`; `b:real`; `K UNION IMAGE (e0:real^3->A) (apx_slab (--inv eps) (&0))`;
                 `IMAGE (e0:real^3->A) (sphere(vec 0,&1))`] APX22_SIGMA_CROSS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[UNION_ASSOC] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((gamma:real->A) b IN U)` THEN
    UNDISCH_TAC `K UNION IMAGE (e0:real^3->A) (apx_slab (--inv eps) (&0)) SUBSET U` THEN
    SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`eps:real`; `e0:real^3->A`; `(gamma:real->A) t`] APX22_SIGMA_POINT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `gamma:real->A`; `a:real`; `t:real`; `b:real`] MFD_LENGTH_COMBINE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `gamma:real->A`; `a:real`; `t:real`] MFD_LENGTH_POS_LE) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `gamma:real->A`; `t:real`; `b:real`] MFD_DIST_LE_LENGTH) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `gamma:real->A`; `t:real`; `b:real`] MFD_C1_CURVE_JOINABLE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `z:A`; `e0:real^3->A`; `(gamma:real->A) b`; `y:real^3`]
                APX_FRONTIER_LOWER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (e0:real^3->A) (rfs_neck_dom eps) SUBSET U` THEN
      UNDISCH_TAC `~((gamma:real->A) b IN U)` THEN SET_TAC[];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `(gamma:real->A) b`; `(e0:real^3->A) y`] MFD_JOINABLE_SYM) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `(gamma:real->A) b`; `(e0:real^3->A) y`] MFD_DIST_SYM) THEN
  ASM_REWRITE_TAC[REAL_ABS_NUM; REAL_SUB_RZERO] THEN DISCH_THEN SUBST1_TAC THEN
  DISCH_TAC THEN ASM_REAL_ARITH_TAC);;

(* L4: if a cap U' inside the cap U has a frontier point in the closed core *)
(* K of U, then the frontier of U' lies on the core side W of U.           *)

let APX22_DEEP_FRONTIER = prove
 (`!top atlas (g:A->real^3^3) eps z (e0:real^3->A) K U z' (e0':real^3->A) K' U' p.
     apx_ch_ctx top atlas g eps /\
     rfs_neck (top,atlas) g eps z e0 /\ IMAGE e0 (rfs_neck_dom eps) = U DIFF K /\
     compact_in top K /\ K SUBSET U /\
     open_in top (K UNION IMAGE e0 (apx_slab (--inv eps) (&0))) /\
     top closure_of (K UNION IMAGE e0 (apx_slab (--inv eps) (&0))) SUBSET
       K UNION IMAGE e0 (apx_slab (--inv eps) (&0)) UNION IMAGE e0 (sphere(vec 0,&1)) /\
     rfs_neck (top,atlas) g eps z' e0' /\ IMAGE e0' (rfs_neck_dom eps) = U' DIFF K' /\
     compact_in top K' /\ K' SUBSET U' /\ open_in top U' /\
     top frontier_of U' SUBSET
       top closure_of (IMAGE e0' (apx_slab (inv eps - &1) (inv eps))) /\
     U' SUBSET U /\ p IN top frontier_of U' /\ p IN K
     ==> top frontier_of U' SUBSET K UNION IMAGE e0 (apx_slab (--inv eps) (&0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  APX22_UNFOLD_ASM_TAC "apx_ch_ctx" apx_ch_ctx THEN
  SUBGOAL_THEN `&1024 <= inv eps` ASSUME_TAC THENL
   [MP_TAC(SPECL [`eps:real`; `&1 / &1024`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `f:A` THEN DISCH_TAC THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  (* L2 for U' *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `z':A`; `e0':real^3->A`; `U':A->bool`; `p:A`; `f:A`]
                APX22_SMALL_FRONTIER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  (* L3 for U *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `z:A`; `e0:real^3->A`; `K:A->bool`; `p:A`; `f:A`]
                APX22_CORE_FAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (e0:real^3->A) (rfs_neck_dom eps) = U DIFF K` THEN SET_TAC[];
    DISCH_TAC] THEN
  (* the two complement necks overlap near f, so their scales compare *)
  SUBGOAL_THEN `?q:A. q IN U' /\ ~(q IN K) /\ ~(q IN K')` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(f:A) IN top closure_of U' /\ ~(f IN U')` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(f:A) IN top frontier_of U'` THEN ASM_SIMP_TAC[FRONTIER_OF_OPEN_IN; IN_DIFF];
      ALL_TAC] THEN
    SUBGOAL_THEN `closed_in top (K:A->bool) /\ closed_in top (K':A->bool)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(f:A) IN top closure_of U'` THEN REWRITE_TAC[IN_CLOSURE_OF] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (MP_TAC o SPEC `topspace top DIFF ((K:A->bool) UNION K')`)) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`(f:A) IN topspace top`; `~((f:A) IN U')`; `(K':A->bool) SUBSET U'`;
          `~((f:A) IN K UNION IMAGE (e0:real^3->A) (apx_slab (--inv eps) (&0)))`] THEN
        SET_TAC[];
        MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_SIMP_TAC[OPEN_IN_TOPSPACE; CLOSED_IN_UNION]];
      REWRITE_TAC[IN_DIFF; IN_UNION] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?v. v IN rfs_neck_dom eps /\ (e0':real^3->A) v = q` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (e0':real^3->A) (rfs_neck_dom eps) = U' DIFF K'` THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DIFF] THEN DISCH_THEN(MP_TAC o SPEC `q:A`) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(sqrt(mfd_scalar atlas g z')) <=
                &3 / &2 * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) z))` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `&3 / &2 * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x1))`))
          (concl th))) THEN
    MAP_EVERY EXISTS_TAC [`e0:real^3->A`; `e0':real^3->A`; `v:real^3`] THEN
    ASM_REWRITE_TAC[IN_DIFF] THEN
    MAP_EVERY UNDISCH_TAC [`(U':A->bool) SUBSET U`; `(q:A) IN U'`] THEN SET_TAC[];
    ALL_TAC] THEN
  (* the arithmetic contradiction *)
  ABBREV_TAC `h = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) z))` THEN
  ABBREV_TAC `h' = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) z'))` THEN
  SUBGOAL_THEN `&0 < h /\ &0 < h'` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "h'"] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN
    MATCH_MP_TAC SQRT_POS_LT THEN ASM_MESON_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt(&2) * pi` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN MP_TAC PI_POS THEN
    SIMP_TAC[SQRT_POS_LE; REAL_POS] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `h' * (&1 + sqrt(&2) * pi) <= (&3 / &2 * h) * (&29 / &5)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN MP_TAC APX_SQRT2_PI THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `h * &1024 <= h * inv eps` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* L4 for caps: a curve from the frontier of U' to a point outside U is at *)
(* least (99/100) R(z)^(-1/2) / eps long, for a point z of U.              *)

let APX22_STEP = prove
 (`!top atlas (g:A->real^3^3) C eps U Y U' Y' (gamma:real->A) a b.
     apx_ch_ctx top atlas g eps /\ apx_ch_n4r top atlas g eps /\
     rfs_cap (top,atlas) g C eps U Y /\ rfs_cap (top,atlas) g C eps U' Y' /\
     U' SUBSET U /\ ~(top frontier_of U' INTER top closure_of Y = {}) /\
     mfd_c1_curve (top,atlas) gamma a b /\ gamma a IN top frontier_of U' /\
     ~(gamma b IN U)
     ==> ?z. z IN U /\ &0 < mfd_scalar atlas g z /\
             &99 / &100 * inv(sqrt(mfd_scalar atlas g z)) * inv eps <=
             mfd_length atlas g gamma a b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`] APX22_CAP_ENDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `e0:real^3->A` (X_CHOOSE_THEN `z:A`
      (X_CHOOSE_THEN `K:A->bool` STRIP_ASSUME_TAC))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `U':A->bool`; `Y':A->bool`] APX22_CAP_ENDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `e0':real^3->A` (X_CHOOSE_THEN `z':A`
      (X_CHOOSE_THEN `K':A->bool` STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `p:A` STRIP_ASSUME_TAC o
    REWRITE_RULE[GSYM MEMBER_NOT_EMPTY; IN_INTER] o check (fun th ->
      concl th = `~(top frontier_of (U':A->bool) INTER top closure_of (Y:A->bool) = {})`)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `z:A`; `e0:real^3->A`; `K:A->bool`; `U:A->bool`;
                 `z':A`; `e0':real^3->A`; `K':A->bool`; `U':A->bool`; `p:A`]
                APX22_DEEP_FRONTIER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `top closure_of (Y:A->bool) SUBSET K` THEN
    UNDISCH_TAC `(p:A) IN top closure_of Y` THEN SET_TAC[];
    DISCH_TAC] THEN
  SUBGOAL_THEN `IMAGE (e0:real^3->A) (apx_slab (--inv eps) (&0)) SUBSET
                IMAGE e0 (rfs_neck_dom eps) /\
                IMAGE (e0:real^3->A) (sphere(vec 0,&1)) SUBSET IMAGE e0 (rfs_neck_dom eps)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THENL
     [MATCH_MP_TAC APX_SLAB_SUB_DOM THEN
      SUBGOAL_THEN `&0 < inv eps` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN ASM_MESON_TAC[rfs_neck]; REAL_ARITH_TAC];
      MATCH_MP_TAC APX_UNIT_SPHERE_NECK_DOM THEN ASM_MESON_TAC[rfs_neck]];
    ALL_TAC] THEN
  EXISTS_TAC `z:A` THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `(z:A) IN IMAGE (e0:real^3->A) (sphere(vec 0,&1))` MP_TAC THENL
     [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`IMAGE (e0:real^3->A) (sphere(vec 0,&1)) SUBSET IMAGE e0 (rfs_neck_dom eps)`;
      `IMAGE (e0:real^3->A) (rfs_neck_dom eps) = U DIFF K`] THEN
    SET_TAC[];
    ASM_MESON_TAC[rfs_neck];
    MATCH_MP_TAC APX22_EXIT_FAR THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `e0:real^3->A`; `K:A->bool`; `U:A->bool`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [SET_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`IMAGE (e0:real^3->A) (apx_slab (--inv eps) (&0)) SUBSET IMAGE e0 (rfs_neck_dom eps)`;
        `IMAGE (e0:real^3->A) (rfs_neck_dom eps) = U DIFF K`; `(K:A->bool) SUBSET U`] THEN
      SET_TAC[];
      UNDISCH_TAC `top frontier_of (U':A->bool) SUBSET
                   K UNION IMAGE (e0:real^3->A) (apx_slab (--inv eps) (&0))` THEN
      UNDISCH_TAC `(gamma:real->A) a IN top frontier_of U'` THEN SET_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* L5, MT Claim A.22.  Take x0 in the first core and R0 = R(x0).             *)
(* By the ratio clause R < C R0 on every cap of the chain, so each step of   *)
(* L4 adds at least delta = (99/100) (C R0)^(-1/2) / eps to the length of a  *)
(* curve from x0 to the complement of the n-th cap: such curves have length  *)
(* at least n delta.  The diameter clause gives, for every n, a curve from   *)
(* x0 to a point of the frontier of the n-th cap (lying in the next cap) of  *)
(* length below C R0^(-1/2).  This is impossible for n large.                *)
(* ------------------------------------------------------------------------- *)

let APX22_CAP_OPEN = prove
 (`!top atlas (g:A->real^3^3) C eps U Y.
     rfs_cap (top,atlas) g C eps U Y ==> open_in top U`,
  SIMP_TAC[rfs_cap]);;

let APX22_CAP_SMOOTH = prove
 (`!top atlas (g:A->real^3^3) C eps U Y.
     rfs_cap (top,atlas) g C eps U Y ==> smooth_manifold_atlas top atlas`,
  SIMP_TAC[rfs_cap]);;

(* The ratio clause of a cap, and positivity of R on it. *)

let APX22_CAP_RATIO = prove
 (`!top atlas (g:A->real^3^3) C eps U Y (w1:A) w2.
     rfs_cap (top,atlas) g C eps U Y /\ w1 IN U /\ w2 IN U
     ==> &0 < mfd_scalar atlas g w1 /\
         mfd_scalar atlas g w2 < C * mfd_scalar atlas g w1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_cap; rfs_sup_lt; IN_ELIM_THM] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) w1` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
      aconv (concl th) `!y:A. y IN U ==> &0 < mfd_scalar atlas (g:A->real^3^3) y`)) THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC o check (fun th ->
    can (find_term (fun t -> t = `mfd_scalar atlas (g:A->real^3^3) y2 /
                                  mfd_scalar atlas g y1`)) (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `mfd_scalar atlas (g:A->real^3^3) w2 / mfd_scalar atlas g w1`) THEN
  ANTS_TAC THENL [MAP_EVERY EXISTS_TAC [`w2:A`; `w1:A`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `mfd_scalar atlas (g:A->real^3^3) w2 / mfd_scalar atlas g w1 < C` MP_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ]]);;

(* The diameter clause of a cap: points of a cap are joinable, at distance  *)
(* below C R(w1)^(-1/2).                                                     *)

let APX22_CAP_DIAM = prove
 (`!top atlas (g:A->real^3^3) C eps U Y (w1:A) w2.
     riemannian_metric atlas g /\ &0 < C /\
     rfs_cap (top,atlas) g C eps U Y /\ w1 IN U /\ w2 IN U
     ==> mfd_joinable (top,atlas) w1 w2 /\
         mfd_dist (top,atlas) g w1 w2 < C * inv(sqrt(mfd_scalar atlas g w1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`] APX_CAP_JOINABLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`w1:A`; `w2:A`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC APX22_CAP_SMOOTH THEN
    MAP_EVERY EXISTS_TAC [`g:A->real^3^3`; `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_IN_IMP]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `mfd_dist_in (top,atlas) (g:A->real^3^3) U w1 w2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC MFD_DIST_LE_DIST_IN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the bound for R on U and the supremum *)
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) w1 /\
                !y. y IN U ==> mfd_scalar atlas g y < C * mfd_scalar atlas g w1`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`;
                     `w1:A`; `w1:A`] APX22_CAP_RATIO) THEN
      ASM_SIMP_TAC[];
      X_GEN_TAC `y:A` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`;
                     `w1:A`; `y:A`] APX22_CAP_RATIO) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar atlas (g:A->real^3^3) w1 <=
                sup(IMAGE (mfd_scalar atlas g) U)` ASSUME_TAC THENL
   [MATCH_MP_TAC ELEMENT_LE_SUP THEN CONJ_TAC THENL
     [EXISTS_TAC `C * mfd_scalar atlas (g:A->real^3^3) w1` THEN
      REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_MESON_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(sqrt(sup(IMAGE (mfd_scalar atlas (g:A->real^3^3)) U))) <=
                inv(sqrt(mfd_scalar atlas g w1))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SQRT_MONO_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  UNDISCH_TAC `rfs_cap (top,atlas) (g:A->real^3^3) C eps U Y` THEN
  REWRITE_TAC[rfs_cap; rfs_sup_lt; IN_ELIM_THM] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_dist_in")) (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `mfd_dist_in (top,atlas) (g:A->real^3^3) U w1 w2`) THEN
  ANTS_TAC THENL [MAP_EVERY EXISTS_TAC [`w1:A`; `w2:A`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `C * inv(sqrt(sup(IMAGE (mfd_scalar atlas (g:A->real^3^3)) U))) <=
                C * inv(sqrt(mfd_scalar atlas g w1))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `C * inv(sqrt(sup(IMAGE (mfd_scalar atlas (g:A->real^3^3)) U)))` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `d:real` THEN
  ASM_REWRITE_TAC[]);;

(* The length bound along the chain, by induction. *)

let APX22_CHAIN_BOUND = prove
 (`!top atlas (g:A->real^3^3) C eps (U:num->A->bool) Y x0 delta.
     apx_ch_ctx top atlas g eps /\ apx_ch_n4r top atlas g eps /\
     (!n. rfs_cap (top,atlas) g C eps (U n) (Y n) /\ U n SUBSET U(SUC n) /\
          ~(top frontier_of (U n) INTER top closure_of (Y(SUC n)) = {})) /\
     (!n. x0 IN U n) /\
     (!n z. z IN U n
            ==> delta <= &99 / &100 * inv(sqrt(mfd_scalar atlas g z)) * inv eps)
     ==> !n (gamma:real->A) a b.
            mfd_c1_curve (top,atlas) gamma a b /\ gamma a = x0 /\ ~(gamma b IN U n)
            ==> &n * delta <= mfd_length atlas g gamma a b`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "ch") (CONJUNCTS_THEN2 (LABEL_TAC "x0") (LABEL_TAC "dl"))))) THEN
  APX22_UNFOLD_ASM_TAC "apx_ch_ctx" apx_ch_ctx THEN
  INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_MUL_LZERO] THEN
    MATCH_MP_TAC MFD_LENGTH_POS_LE THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`gamma:real->A`; `a:real`; `b:real`] THEN STRIP_TAC THEN
  USE_THEN "ch" (MP_TAC o SPEC `n:num`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  USE_THEN "ch" (MP_TAC o SPEC `SUC n`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)) THEN
  SUBGOAL_THEN `open_in top ((U:num->A->bool) n)` ASSUME_TAC THENL
   [MATCH_MP_TAC APX22_CAP_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                          `C:real`; `eps:real`; `(Y:num->A->bool) n`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((gamma:real->A) b IN (U:num->A->bool) n) /\ (gamma:real->A) a IN U n`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "x0" (MP_TAC o SPEC `n:num`) THEN
    MAP_EVERY UNDISCH_TAC [`~((gamma:real->A) b IN U(SUC n))`;
                           `(U:num->A->bool) n SUBSET U(SUC n)`;
                           `(gamma:real->A) a = x0`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `gamma:real->A`;
                 `a:real`; `b:real`; `(U:num->A->bool) n`] APX22_CURVE_CROSS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(gamma:real->A) t IN top frontier_of ((U:num->A->bool) n)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FRONTIER_OF_OPEN_IN; IN_DIFF]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `gamma:real->A`; `a:real`; `t:real`; `b:real`] MFD_LENGTH_COMBINE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`gamma:real->A`; `a:real`; `t:real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `(U:num->A->bool)(SUC n)`; `(Y:num->A->bool)(SUC n)`;
                 `(U:num->A->bool) n`; `(Y:num->A->bool) n`; `gamma:real->A`; `t:real`;
                 `b:real`] APX22_STEP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `zz:A` STRIP_ASSUME_TAC) THEN
  USE_THEN "dl" (fun th ->
    MP_TAC(MATCH_MP th (ASSUME `(zz:A) IN (U:num->A->bool)(SUC n)`))) THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_ADD_RDISTRIB; REAL_MUL_LID] THEN
  ASM_REAL_ARITH_TAC);;

(* No infinite chain, for eps where the chain context and N4 hold. *)

let APX22_NO_CHAIN = prove
 (`!top atlas (g:A->real^3^3) C eps (U:num->A->bool) Y.
     apx_ch_ctx top atlas g eps /\ apx_ch_n4r top atlas g eps /\ &0 < C
     ==> ~(!n. rfs_cap (top,atlas) g C eps (U n) (Y n) /\ U n SUBSET U(SUC n) /\
               ~(top frontier_of (U n) INTER top closure_of (Y(SUC n)) = {}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_THEN(LABEL_TAC "ch") THEN
  APX22_UNFOLD_ASM_TAC "apx_ch_ctx" apx_ch_ctx THEN
  SUBGOAL_THEN `!n. rfs_cap (top,atlas) (g:A->real^3^3) C eps ((U:num->A->bool) n) (Y n)`
    (LABEL_TAC "cap")
  THENL [USE_THEN "ch" (fun th -> MESON_TAC[th]); ALL_TAC] THEN
  SUBGOAL_THEN `!n. (U:num->A->bool) 0 SUBSET U n` (LABEL_TAC "mono") THENL
   [INDUCT_TAC THEN REWRITE_TAC[SUBSET_REFL] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(U:num->A->bool) n` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "ch" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  (* a point x0 of the first core *)
  SUBGOAL_THEN `?x0:A. x0 IN U 0` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `C:real`; `eps:real`; `(U:num->A->bool) 0`;
                   `(Y:num->A->bool) 0`] APX22_CAP_DATA) THEN
    USE_THEN "cap" (fun th -> ASM_REWRITE_TAC[th]) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN STRIP_TAC THEN EXISTS_TAC `x:A` THEN
    MAP_EVERY UNDISCH_TAC [`(x:A) IN Y 0`; `(Y:num->A->bool) 0 SUBSET K`;
                           `(K:A->bool) SUBSET U 0`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. (x0:A) IN (U:num->A->bool) n` (LABEL_TAC "x0") THENL
   [GEN_TAC THEN USE_THEN "mono" (MP_TAC o SPEC `n:num`) THEN
    UNDISCH_TAC `(x0:A) IN U 0` THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `R0 = mfd_scalar atlas (g:A->real^3^3) x0` THEN
  SUBGOAL_THEN `&0 < R0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `C:real`; `eps:real`; `(U:num->A->bool) 0`;
                   `(Y:num->A->bool) 0`; `x0:A`; `x0:A`] APX22_CAP_RATIO) THEN
    USE_THEN "cap" (fun th -> ASM_REWRITE_TAC[th]) THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `delta = &99 / &100 * inv(sqrt(C * R0)) * inv eps` THEN
  SUBGOAL_THEN `&0 < delta` ASSUME_TAC THENL
   [EXPAND_TAC "delta" THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN
    ASM_SIMP_TAC[SQRT_POS_LT; REAL_LT_MUL];
    ALL_TAC] THEN
  (* each cap of the chain has R < C R0 *)
  SUBGOAL_THEN `!n z. z IN (U:num->A->bool) n
                      ==> delta <= &99 / &100 *
                                   inv(sqrt(mfd_scalar atlas (g:A->real^3^3) z)) * inv eps`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `z:A`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `C:real`; `eps:real`; `(U:num->A->bool) n`;
                   `(Y:num->A->bool) n`; `x0:A`; `z:A`] APX22_CAP_RATIO) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `C:real`; `eps:real`; `(U:num->A->bool) n`;
                   `(Y:num->A->bool) n`; `z:A`; `z:A`] APX22_CAP_RATIO) THEN
    USE_THEN "cap" (fun th -> USE_THEN "x0" (fun th' -> ASM_REWRITE_TAC[th; th'])) THEN
    REPEAT STRIP_TAC THEN EXPAND_TAC "delta" THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC SQRT_MONO_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
      MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `U:num->A->bool`; `Y:num->A->bool`; `x0:A`;
                 `delta:real`] APX22_CHAIN_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  (* each frontier is reached from x0 by a short curve *)
  SUBGOAL_THEN `!n. &n * delta < C * inv(sqrt R0)` ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN USE_THEN "ch" (MP_TAC o SPEC `n:num`) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(p:A) IN U(SUC n) /\ ~(p IN U n)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `C:real`; `eps:real`; `(U:num->A->bool)(SUC n)`;
                       `(Y:num->A->bool)(SUC n)`] APX22_CAP_DATA) THEN
        USE_THEN "cap" (fun th -> ASM_REWRITE_TAC[th]) THEN STRIP_TAC THEN
        MAP_EVERY UNDISCH_TAC [`(p:A) IN top closure_of (Y(SUC n))`;
                               `top closure_of ((Y:num->A->bool)(SUC n)) SUBSET K`;
                               `(K:A->bool) SUBSET U(SUC n)`] THEN
        SET_TAC[];
        UNDISCH_TAC `(p:A) IN top frontier_of ((U:num->A->bool) n)` THEN
        SUBGOAL_THEN `open_in top ((U:num->A->bool) n)` MP_TAC THENL
         [MATCH_MP_TAC APX22_CAP_OPEN THEN
          MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                                `C:real`; `eps:real`; `(Y:num->A->bool) n`] THEN
          USE_THEN "cap" (fun th -> REWRITE_TAC[th]);
          SIMP_TAC[FRONTIER_OF_OPEN_IN; IN_DIFF]]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `C:real`; `eps:real`; `(U:num->A->bool)(SUC n)`;
                   `(Y:num->A->bool)(SUC n)`; `x0:A`; `p:A`] APX22_CAP_DIAM) THEN
    USE_THEN "cap" (fun th -> USE_THEN "x0" (fun th' -> ASM_REWRITE_TAC[th; th'])) THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `x0:A`; `p:A`; `C * inv(sqrt R0)`]
                  APX_DIST_SHORT_CURVE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `gamma:real->A`; `&0`; `&1`] o check (fun th ->
      can (find_term (fun t -> t = `delta:real`)) (concl th) && is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_length")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `delta:real` REAL_ARCH) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num` o SPEC `C * inv(sqrt R0)`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> t = `C * inv(sqrt R0)`)) (concl th))) THEN
  ASM_REAL_ARITH_TAC);;

(* MT Claim A.22, unconditional. *)

let APX_A22 = prove
 (`!u:A->bool. APX_A22_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[APX_A22_STATEMENT] THEN
  MP_TAC APX_CH_CTX_HOLDS THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ctx"))) THEN
  MP_TAC APX_CH_N4R_HOLDS THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "n4r"))) THEN
  EXISTS_TAC `min e1 e2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `top:A topology`;
                       `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                       `U:num->A->bool`; `Y:num->A->bool`] THEN
  STRIP_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool)`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `0` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_cap")) (concl th))) THEN
    SIMP_TAC[rfs_cap];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `U:num->A->bool`; `Y:num->A->bool`] APX22_NO_CHAIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "ctx" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                      `g:A->real^3^3`; `eps:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      USE_THEN "n4r" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                      `g:A->real^3^3`; `eps:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ASM_REWRITE_TAC[]]);;


(* ========================================================================= *)
(* Unit pc_p2b_conelib: general bad-tube and neck lemmas, used by the cone   *)
(* units (pc_p2b_cone, ...), by pc_p2b_tubelim3 and by Part 2C units:        *)
(*                                                                           *)
(* - the data of a bad tube (P2BK_TUBE_FACTS) and the time slice of an       *)
(*   evolving neck (P2BK_EVOLVING_NECK_SLICE);                               *)
(* - the two sides of a separating set in a connected, locally connected     *)
(*   space (P2BK_COMPONENT_MEETS, P2BK_COMPONENT_HALF, P2BK_TWO_SIDES_TOP);  *)
(* - the two halves of a neck minus its central sphere (P2BK_NECK_HALVES,    *)
(*   P2BK_NECK_SIDES);                                                       *)
(* - the distance gained across a neck, MT Claim A (P2BK_CURVE_MEETS_SEP,    *)
(*   P2BK_GAIN_ARITH, P2BK_CROSS_GAIN).                                      *)
(* ========================================================================= *)

needs "src/pc_p2b_defs.ml";;
needs "src/pc_apx_neck.ml";;

prioritize_real();;
type_invention_error := true;;


(* ========================================================================= *)
(* The data of a bad tube in a usable form.  The slice of an evolving neck   *)
(* is a neck; at time 0 the view is (top,atlas,g), so every point H y with   *)
(* r1 < |y| < 2 is the centre of a time-0 2eps-neck whose central sphere     *)
(* separates the two ends.                                                   *)
(* ========================================================================= *)

let P2BK_EVOLVING_NECK_SLICE = prove
 (`!V eps (x:B) t len e.
     rfs_evolving_neck V eps x t len e
     ==> rfs_neck (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) eps x e`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_evolving_neck; rfs_vtop; rfs_vatlas; rfs_vmetric] THEN
  SIMP_TAC[]);;

let P2BK_TUBE_FACTS = prove
 (`!eps top atlas (g:B->real^3^3) V H.
     p2b_bad_tube eps (top,atlas) g V H
     ==> hausdorff_space top /\ smooth_manifold_atlas top atlas /\
         riemannian_metric atlas g /\ connected_space top /\ apx_sphere_sep top atlas /\
         mfd_param top atlas (annulus (&1) (&2)) H /\
         IMAGE H (annulus (&1) (&2)) = topspace top /\
         (?D. !x y. x IN topspace top /\ y IN topspace top
                    ==> mfd_joinable (top,atlas) x y /\ mfd_dist (top,atlas) g x y <= D) /\
         (!B0. ?r. r < &2 /\
                   !y. r < norm y /\ norm y < &2 ==> B0 <= mfd_scalar atlas g (H y)) /\
         (!x. x IN topspace top ==> &0 < mfd_scalar atlas g x) /\
         p2c_regular_view V /\
         rfs_vtop V (&0) = top /\ rfs_vatlas V (&0) = atlas /\ rfs_vmetric V (&0) = g /\
         (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                  ==> &0 <= mfd_sectional atlas g x u v) /\
         (?r1. &1 < r1 /\ r1 < &2 /\
               !y. r1 < norm y /\ norm y < &2
                   ==> ?e. rfs_neck (top,atlas) g (&2 * eps) (H y) e /\
                           rfs_evolving_neck V (&2 * eps) (H y) (&0) (&1 / &2) e /\
                           ?r2 r3. &1 < r2 /\ r2 < r3 /\ r3 < &2 /\
                                   !w1 w2. &1 < norm w1 /\ norm w1 < r2 /\
                                           r3 < norm w2 /\ norm w2 < &2
                                           ==> apx_separates top
                                                 (IMAGE e (sphere(vec 0,&1)))
                                                 (H w1) (H w2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2b_bad_tube] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `&0` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "mfd_sectional"
                               with Failure _ -> false)) (concl th))) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC o check (fun th ->
    is_exists(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "rfs_evolving_neck"
                             with Failure _ -> false)) (concl th))) THEN
  EXISTS_TAC `r1:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "rfs_evolving_neck"
                             with Failure _ -> false)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^3->B` (CONJUNCTS_THEN ASSUME_TAC)) THEN
  EXISTS_TAC `e:real^3->B` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`V:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                    (real->B->real^3^3)`;
                 `&2 * eps`; `(H:real^3->B) y`; `&0`; `&1 / &2`; `e:real^3->B`]
    P2BK_EVOLVING_NECK_SLICE) THEN
  ASM_REWRITE_TAC[]);;


(* ========================================================================= *)
(* The two sides of a separating sphere (pure topology).  In a connected,    *)
(* locally connected space, let S be closed and nonempty, N an open          *)
(* neighbourhood of S with N - S the union of two nonempty connected sets    *)
(* Nm, Np, and let S separate p0 from q0.  Every component of top - S meets  *)
(* Nm or Np (otherwise it would be clopen in top), so top - S has exactly    *)
(* the two components of p0 and q0, one containing Nm and the other Np.      *)
(* ========================================================================= *)

let P2BK_COMPONENT_MEETS = prove
 (`!top (S:B->bool) N Nm Np p.
     connected_space top /\ locally_connected_space top /\
     closed_in top S /\ ~(S = {}) /\ open_in top N /\ S SUBSET N /\
     N DIFF S = Nm UNION Np /\ p IN topspace top DIFF S
     ==> ~(connected_component_of (subtopology top (topspace top DIFF S)) p INTER
           (Nm UNION Np) = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `X = subtopology top (topspace top DIFF (S:B->bool))` THEN
  ABBREV_TAC `C = connected_component_of (X:B topology) p` THEN
  SUBGOAL_THEN `open_in top (topspace top DIFF (S:B->bool))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_TOPSPACE]; ALL_TAC] THEN
  SUBGOAL_THEN `topspace (X:B topology) = topspace top DIFF S` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(C:B->bool) SUBSET topspace top DIFF S /\ (p:B) IN C` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`X:B topology`; `p:B`] CONNECTED_COMPONENT_OF_SUBSET_TOPSPACE) THEN
      ASM_REWRITE_TAC[];
      GEN_REWRITE_TAC I [IN] THEN REWRITE_TAC[CONNECTED_COMPONENT_OF_REFL] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (X:B topology) C` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN
    MATCH_MP_TAC OPEN_IN_CONNECTED_COMPONENT_OF_LOCALLY_CONNECTED_SPACE THEN
    EXPAND_TAC "X" THEN MATCH_MP_TAC LOCALLY_CONNECTED_SPACE_OPEN_SUBSET THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (C:B->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN
    EXISTS_TAC `topspace top DIFF (S:B->bool)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed_in (X:B topology) C` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN REWRITE_TAC[CLOSED_IN_CONNECTED_COMPONENT_OF]; ALL_TAC] THEN
  SUBGOAL_THEN `top closure_of (C:B->bool) SUBSET C` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:B` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~((z:B) IN S)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `(z:B) IN top closure_of C` THEN REWRITE_TAC[IN_CLOSURE_OF] THEN
      DISCH_THEN(MP_TAC o SPEC `N:B->bool` o CONJUNCT2) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(S:B->bool) SUBSET N` THEN UNDISCH_TAC `(z:B) IN S` THEN SET_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:B` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `(C:B->bool) INTER (Nm UNION Np) = {}` THEN
      REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_INTER] THEN
      DISCH_THEN(MP_TAC o SPEC `y:B`) THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(y:B) IN N DIFF S` MP_TAC THENL
       [UNDISCH_TAC `(C:B->bool) SUBSET topspace top DIFF S` THEN
        UNDISCH_TAC `(y:B) IN C` THEN UNDISCH_TAC `(y:B) IN N` THEN SET_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:B) IN (X:B topology) closure_of C` MP_TAC THENL
     [UNDISCH_THEN `subtopology top (topspace top DIFF (S:B->bool)) = X`
        (SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC[CLOSURE_OF_SUBTOPOLOGY; IN_INTER] THEN
      SUBGOAL_THEN `(z:B) IN topspace top` MP_TAC THENL
       [MP_TAC(ISPECL [`top:B topology`; `C:B->bool`] CLOSURE_OF_SUBSET_TOPSPACE) THEN
        UNDISCH_TAC `(z:B) IN top closure_of C` THEN SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(topspace top DIFF (S:B->bool)) INTER C = C` SUBST1_TAC THENL
       [UNDISCH_TAC `(C:B->bool) SUBSET topspace top DIFF S` THEN SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_DIFF];
      ASM_SIMP_TAC[CLOSURE_OF_CLOSED_IN]];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed_in top (C:B->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM CLOSURE_OF_SUBSET_EQ] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(C:B->bool) SUBSET topspace top DIFF S` THEN SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `connected_space (top:B topology)` THEN
  REWRITE_TAC[CONNECTED_SPACE_CLOPEN_IN] THEN
  DISCH_THEN(MP_TAC o SPEC `C:B->bool`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THENL
   [UNDISCH_TAC `(p:B) IN C` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY]; ALL_TAC] THEN
  UNDISCH_TAC `closed_in top (S:B->bool)` THEN
  DISCH_THEN(MP_TAC o MATCH_MP CLOSED_IN_SUBSET) THEN
  UNDISCH_TAC `(C:B->bool) SUBSET topspace top DIFF S` THEN
  UNDISCH_TAC `~((S:B->bool) = {})` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let P2BK_COMPONENT_HALF = prove
 (`!top (S:B->bool) N Nm Np p.
     connected_space top /\ locally_connected_space top /\
     closed_in top S /\ ~(S = {}) /\ open_in top N /\ S SUBSET N /\
     N DIFF S = Nm UNION Np /\ connected_in top Nm /\ connected_in top Np /\
     p IN topspace top DIFF S
     ==> Nm SUBSET connected_component_of (subtopology top (topspace top DIFF S)) p \/
         Np SUBSET connected_component_of (subtopology top (topspace top DIFF S)) p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `S:B->bool`; `N:B->bool`; `Nm:B->bool`; `Np:B->bool`;
                 `p:B`] P2BK_COMPONENT_MEETS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `X = subtopology top (topspace top DIFF (S:B->bool))` THEN
  SUBGOAL_THEN `(Nm:B->bool) SUBSET topspace top DIFF S /\ Np SUBSET topspace top DIFF S`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `N:B->bool`] OPEN_IN_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(N:B->bool) DIFF S = Nm UNION Np` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected_in (X:B topology) Nm /\ connected_in X Np` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY]; ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_UNION] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:B` STRIP_ASSUME_TAC) THENL
   [DISJ1_TAC; DISJ2_TAC] THEN
  (SUBGOAL_THEN `connected_component_of (X:B topology) p = connected_component_of X y`
   SUBST1_TAC THENL
    [REWRITE_TAC[CONNECTED_COMPONENT_OF_EQ] THEN DISJ2_TAC THEN
     UNDISCH_TAC `(y:B) IN connected_component_of X p` THEN
     GEN_REWRITE_TAC LAND_CONV [IN] THEN
     MESON_TAC[CONNECTED_COMPONENT_IN_TOPSPACE];
     MATCH_MP_TAC CONNECTED_COMPONENT_OF_MAXIMAL THEN ASM_REWRITE_TAC[]]));;

let P2BK_TWO_SIDES_TOP = prove
 (`!top (S:B->bool) N Nm Np p0 q0.
     connected_space top /\ locally_connected_space top /\
     closed_in top S /\ ~(S = {}) /\ open_in top N /\ S SUBSET N /\
     N DIFF S = Nm UNION Np /\ connected_in top Nm /\ connected_in top Np /\
     ~(Nm = {}) /\ ~(Np = {}) /\ apx_separates top S p0 q0
     ==> (!p. p IN topspace top DIFF S
              ==> connected_component_of (subtopology top (topspace top DIFF S)) p p0 \/
                  connected_component_of (subtopology top (topspace top DIFF S)) p q0) /\
         (Nm SUBSET connected_component_of (subtopology top (topspace top DIFF S)) p0 /\
          Np SUBSET connected_component_of (subtopology top (topspace top DIFF S)) q0 \/
          Np SUBSET connected_component_of (subtopology top (topspace top DIFF S)) p0 /\
          Nm SUBSET connected_component_of (subtopology top (topspace top DIFF S)) q0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [apx_separates]) THEN
  MP_TAC(ISPECL [`top:B topology`; `S:B->bool`; `N:B->bool`; `Nm:B->bool`; `Np:B->bool`]
    P2BK_COMPONENT_HALF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `X = subtopology top (topspace top DIFF (S:B->bool))` THEN
  SUBGOAL_THEN `topspace (X:B topology) = topspace top DIFF S` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (connected_component_of (X:B topology) p0)
                         (connected_component_of X q0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CONNECTED_COMPONENT_OF_DISJOINT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(Nm:B->bool) SUBSET connected_component_of (X:B topology) p0 /\
    Np SUBSET connected_component_of X q0 \/
    Np SUBSET connected_component_of X p0 /\ Nm SUBSET connected_component_of X q0`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `p0:B`) THEN FIRST_X_ASSUM(MP_TAC o SPEC `q0:B`) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `DISJOINT (connected_component_of (X:B topology) p0)
                          (connected_component_of X q0)` THEN
    UNDISCH_TAC `~((Nm:B->bool) = {})` THEN UNDISCH_TAC `~((Np:B->bool) = {})` THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `p:B` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p:B`) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!z:B. z IN topspace top DIFF S /\
          ~(connected_component_of (X:B topology) p INTER connected_component_of X z = {})
          ==> connected_component_of X p z`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:B` THEN REWRITE_TAC[GSYM DISJOINT; CONNECTED_COMPONENT_OF_DISJOINT] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_disj o concl)) THEN
  ASM_MESON_TAC[SET_RULE `!A B C:B->bool. ~(A = {}) /\ A SUBSET B /\ A SUBSET C
                                          ==> ~(B INTER C = {})`]);;


(* ========================================================================= *)
(* The two sides of a separating neck sphere.  For a neck e with central     *)
(* sphere S = e(sphere 1) separating p0 from q0 in a connected Hausdorff     *)
(* manifold, top - S has exactly the components of p0 and q0, and the two    *)
(* halves of the neck (|y| < 1 and |y| > 1) lie in different ones.           *)
(* ========================================================================= *)

let P2BK_NECK_HALVES = prove
 (`!top atlas (g:B->real^3^3) eps (x:B) e.
     hausdorff_space top /\ rfs_neck (top,atlas) g eps x e
     ==> closed_in top (IMAGE e (sphere(vec 0,&1))) /\
         ~(IMAGE e (sphere(vec 0,&1)) = {}) /\
         open_in top (IMAGE e (rfs_neck_dom eps)) /\
         IMAGE e (sphere(vec 0,&1)) SUBSET IMAGE e (rfs_neck_dom eps) /\
         IMAGE e (rfs_neck_dom eps) DIFF IMAGE e (sphere(vec 0,&1)) =
         IMAGE e (annulus (exp(--inv eps / sqrt(&2))) (&1)) UNION
         IMAGE e (annulus (&1) (exp(inv eps / sqrt(&2)))) /\
         connected_in top (IMAGE e (annulus (exp(--inv eps / sqrt(&2))) (&1))) /\
         connected_in top (IMAGE e (annulus (&1) (exp(inv eps / sqrt(&2))))) /\
         ~(IMAGE e (annulus (exp(--inv eps / sqrt(&2))) (&1)) = {}) /\
         ~(IMAGE e (annulus (&1) (exp(inv eps / sqrt(&2)))) = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck]) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  DISCH_THEN(X_CHOOSE_THEN `e':B->real^3` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `a = exp(--inv eps / sqrt(&2))` THEN
  ABBREV_TAC `b = exp(inv eps / sqrt(&2))` THEN
  SUBGOAL_THEN `&0 < a /\ a < &1 /\ &1 < b` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a"; "b"] THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
    SUBGOAL_THEN `&0 < inv eps / sqrt(&2)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_LT_INV_EQ; SQRT_POS_LT; REAL_OF_NUM_LT;
                                                 ARITH];
      ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_MUL_LNEG] THEN
    MESON_TAC[REAL_EXP_LT_1; REAL_EXP_0; REAL_EXP_MONO_LT; REAL_ARITH
      `&0 < x ==> --x < &0`];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_neck_dom eps = annulus a b` ASSUME_TAC THENL
   [REWRITE_TAC[APX_SLAB_NECK_DOM; apx_slab] THEN MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    REWRITE_TAC[real_div; REAL_MUL_LNEG];
    ALL_TAC] THEN
  SUBGOAL_THEN `sphere(vec 0:real^3,&1) SUBSET rfs_neck_dom eps` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_UNIT_SPHERE_NECK_DOM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `sphere(vec 0:real^3,&1) SUBSET annulus a b` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `annulus a (&1) SUBSET rfs_neck_dom eps /\
                annulus (&1) b SUBSET rfs_neck_dom eps`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[annulus; SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology euclidean (rfs_neck_dom eps)` THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN; COMPACT_SPHERE];
    REWRITE_TAC[IMAGE_EQ_EMPTY; SPHERE_EQ_EMPTY] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[IMAGE_SUBSET];
    UNDISCH_TAC `!x:real^3. x IN rfs_neck_dom eps ==> e'((e:real^3->B) x) = x` THEN
    UNDISCH_TAC `rfs_neck_dom eps = annulus a b` THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNION; IN_IMAGE; IN_SPHERE_0; annulus;
                IN_ELIM_THM] THEN
    DISCH_TAC THEN X_GEN_TAC `p:B` THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
      ASM_CASES_TAC `norm(y:real^3) = &1` THENL
       [UNDISCH_TAC `~(?x:real^3. p = (e:real^3->B) x /\ norm x = &1)` THEN
        REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_CASES_TAC `norm(y:real^3) < &1` THENL
       [DISJ1_TAC THEN EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        DISJ2_TAC THEN EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC];
      DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)) THEN
      (CONJ_TAC THENL
       [EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
        FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `z:real^3` th) THEN MP_TAC(SPEC `y:real^3` th)) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
        SUBGOAL_THEN `y:real^3 = z` (fun th -> ASM_MESON_TAC[th; REAL_LT_REFL]) THEN
        ASM_MESON_TAC[]])];
    MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `rfs_neck_dom eps`] THEN
    ASM_REWRITE_TAC[APX_CONNECTED_ANNULUS3];
    MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `rfs_neck_dom eps`] THEN
    ASM_REWRITE_TAC[APX_CONNECTED_ANNULUS3];
    REWRITE_TAC[IMAGE_EQ_EMPTY] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `((a + &1) / &2) % basis 1:real^3` THEN
    SIMP_TAC[annulus; IN_ELIM_THM; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[IMAGE_EQ_EMPTY] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `((b + &1) / &2) % basis 1:real^3` THEN
    SIMP_TAC[annulus; IN_ELIM_THM; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
    ASM_REAL_ARITH_TAC]);;

let P2BK_NECK_SIDES = prove
 (`!top atlas (g:B->real^3^3) eps (x:B) e p0 q0.
     hausdorff_space top /\ connected_space top /\ rfs_neck (top,atlas) g eps x e /\
     apx_separates top (IMAGE e (sphere(vec 0,&1))) p0 q0
     ==> (!p. p IN topspace top DIFF IMAGE e (sphere(vec 0,&1))
              ==> connected_component_of
                    (subtopology top (topspace top DIFF IMAGE e (sphere(vec 0,&1)))) p p0 \/
                  connected_component_of
                    (subtopology top (topspace top DIFF IMAGE e (sphere(vec 0,&1)))) p q0) /\
         (IMAGE e (annulus (exp(--inv eps / sqrt(&2))) (&1)) SUBSET
          connected_component_of
            (subtopology top (topspace top DIFF IMAGE e (sphere(vec 0,&1)))) p0 /\
          IMAGE e (annulus (&1) (exp(inv eps / sqrt(&2)))) SUBSET
          connected_component_of
            (subtopology top (topspace top DIFF IMAGE e (sphere(vec 0,&1)))) q0 \/
          IMAGE e (annulus (&1) (exp(inv eps / sqrt(&2)))) SUBSET
          connected_component_of
            (subtopology top (topspace top DIFF IMAGE e (sphere(vec 0,&1)))) p0 /\
          IMAGE e (annulus (exp(--inv eps / sqrt(&2))) (&1)) SUBSET
          connected_component_of
            (subtopology top (topspace top DIFF IMAGE e (sphere(vec 0,&1)))) q0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:B->real^3^3`; `eps:real`; `x:B`; `e:real^3->B`] P2BK_NECK_HALVES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC P2BK_TWO_SIDES_TOP THEN
  EXISTS_TAC `IMAGE (e:real^3->B) (rfs_neck_dom eps)` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck]) THEN
  ASM_MESON_TAC[GEO_MANIFOLD_LOCALLY_PATH_CONNECTED;
                LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED_SPACE]);;


(* ========================================================================= *)
(* The distance gained across a neck (Claim A).  A curve from p to q on      *)
(* different sides of the central sphere S of an eps-neck meets S; if q lies *)
(* outside the neck it must then leave the neck, which costs sqrt(1 - eps) h *)
(* / eps (APX_NECK_EXIT), while S has diameter at most sqrt(1 + eps) h sqrt  *)
(* 2 pi (APX_NECK_DIST_UPPER).  For eps <= 1/100 the net gain is at least h  *)
(* / (2 eps), h = R(x)^(-1/2).                                               *)
(* ========================================================================= *)

let P2BK_CURVE_MEETS_SEP = prove
 (`!top atlas (gamma:real->B) a b S.
     mfd_c1_curve (top,atlas:((B->bool)#(B->real^3))->bool) gamma a b /\ a <= b /\
     ~(connected_component_of (subtopology top (topspace top DIFF S)) (gamma a) (gamma b))
     ==> ?t. a <= t /\ t <= b /\ gamma t IN S`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  UNDISCH_TAC `~(connected_component_of (subtopology top (topspace top DIFF S))
                  ((gamma:real->B) a) (gamma b))` THEN
  REWRITE_TAC[connected_component_of] THEN
  EXISTS_TAC `IMAGE (gamma:real->B) (real_interval[a,b])` THEN
  REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `mfd_c1_curve (top,atlas:((B->bool)#(B->real^3))->bool) gamma a b` THEN
    REWRITE_TAC[mfd_c1_curve] THEN STRIP_TAC THEN
    MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
    EXISTS_TAC `subtopology euclideanreal (real_interval[a,b])` THEN
    ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; SUBSET_REFL;
                    CONNECTED_IN_EUCLIDEANREAL_INTERVAL];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF] THEN X_GEN_TAC `t:real` THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `gamma:real->B`; `a:real`; `b:real`; `t:real`]
        MFD_C1_CURVE_IN_TOPSPACE) THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `t IN real_interval[a,b]` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      ASM_MESON_TAC[]];
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `a:real` THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `b:real` THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC]);;

let P2BK_GAIN_ARITH = prove
 (`!eps h d0 d1 l1 l2.
     &0 < eps /\ eps <= &1 / &100 /\ &0 <= h /\
     d0 <= d1 + sqrt(&1 + eps) * h * (sqrt(&2) * pi) /\
     d1 <= l1 /\ sqrt(&1 - eps) * h * (inv eps - &0) <= l2
     ==> d0 + h * inv(&2 * eps) <= l1 + l2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&99 / &100 <= sqrt(&1 - eps) /\ sqrt(&1 + eps) <= &2 /\
                sqrt(&2) <= &3 / &2 /\ pi <= &4`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      MP_TAC PI2_BOUNDS THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv eps /\ inv(&2 * eps) = inv eps / &2` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&100 <= inv eps` ASSUME_TAC THENL
   [SUBGOAL_THEN `inv(&1 / &100) <= inv eps` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&1 + eps) * h * (sqrt(&2) * pi) <= &12 * h` ASSUME_TAC THENL
   [SUBGOAL_THEN `sqrt(&1 + eps) * (sqrt(&2) * pi) <= &12` MP_TAC THENL
     [SUBGOAL_THEN `&0 <= sqrt(&1 + eps) /\ &0 <= sqrt(&2) /\ &0 <= pi`
      STRIP_ASSUME_TAC THENL
       [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC SQRT_POS_LE) THEN
        MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * (&3 / &2 * &4)` THEN
      CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN
      SUBGOAL_THEN `sqrt(&1 + eps) * h * (sqrt(&2) * pi) =
                    (sqrt(&1 + eps) * (sqrt(&2) * pi)) * h` SUBST1_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&99 / &100 * h * inv eps <= sqrt(&1 - eps) * h * (inv eps - &0)`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_SUB_RZERO; REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&12 * h + h * inv eps / &2 <= &99 / &100 * h * inv eps` ASSUME_TAC THENL
   [SUBGOAL_THEN `&12 * h <= (&49 / &100 * inv eps) * h` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P2BK_CROSS_GAIN = prove
 (`!top atlas (g:B->real^3^3) eps (x:B) e p q.
     hausdorff_space top /\ riemannian_metric atlas g /\
     rfs_neck (top,atlas) g eps x e /\ eps <= &1 / &100 /\
     p IN topspace top DIFF IMAGE e (sphere(vec 0,&1)) /\
     ~(connected_component_of
         (subtopology top (topspace top DIFF IMAGE e (sphere(vec 0,&1)))) p q) /\
     ~(q IN IMAGE e (rfs_neck_dom eps)) /\ mfd_joinable (top,atlas) p q
     ==> mfd_dist (top,atlas) g p x + inv(sqrt(mfd_scalar atlas g x)) * inv(&2 * eps)
         <= mfd_dist (top,atlas) g p q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck]) THEN
  SUBGOAL_THEN `sphere(vec 0:real^3,&1) SUBSET rfs_neck_dom eps` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_UNIT_SPHERE_NECK_DOM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC APX_DIST_GE_CURVES THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `gamma:real->B` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `gamma:real->B`; `&0`; `&1`; `IMAGE (e:real^3->B) (sphere(vec 0,&1))`]
    P2BK_CURVE_MEETS_SEP) THEN
  ASM_REWRITE_TAC[REAL_POS] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(gamma:real->B) t1 IN IMAGE (e:real^3->B) (sphere(vec 0,&1))` THEN
  REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  UNDISCH_TAC `(x:B) IN IMAGE (e:real^3->B) (sphere(vec 0,&1))` THEN
  REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `u0:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  SUBGOAL_THEN `(u0:real^3) IN rfs_neck_dom eps /\ (u1:real^3) IN rfs_neck_dom eps`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    ASM_REWRITE_TAC[IN_SPHERE_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `t1 < &1` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `~((q:B) IN IMAGE (e:real^3->B) (rfs_neck_dom eps))` THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `(q:B) = e(u1:real^3)` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `gamma:real->B`; `&0`; `t1:real`; `&1`] MFD_LENGTH_COMBINE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `eps:real`; `x:B`; `e:real^3->B`; `u0:real^3`; `u1:real^3`]
    APX_NECK_DIST_UPPER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[APX_SVAL_UNIT; REAL_SUB_REFL; REAL_ABS_0; REAL_ADD_LID] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `eps:real`; `x:B`; `e:real^3->B`; `u1:real^3`; `gamma:real->B`;
                 `t1:real`; `&1`] APX_NECK_EXIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[APX_SVAL_UNIT; REAL_ABS_0; REAL_SUB_RZERO] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `gamma:real->B`; `&0`; `t1:real`] MFD_DIST_LE_LENGTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `p:B`; `(gamma:real->B) t1`; `x:B`] MFD_DIST_TRIANGLE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(gamma:real->B)(&0) = p`)) THEN
      MATCH_MP_TAC MFD_C1_CURVE_JOINABLE THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[MFD_JOINABLE_SYM]];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `(e:real^3->B) u0`; `(e:real^3->B) u1`] MFD_DIST_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC P2BK_GAIN_ARITH THEN
  EXISTS_TAC `mfd_dist (top,atlas) (g:B->real^3^3) p ((gamma:real->B) t1)` THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC[REAL_LT_INV_EQ] THEN
    MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `mfd_dist (top,atlas) (g:B->real^3^3) p x <=
               mfd_dist (top,atlas) g p ((gamma:real->B) t1) +
               mfd_dist (top,atlas) g ((gamma:real->B) t1) x` THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;


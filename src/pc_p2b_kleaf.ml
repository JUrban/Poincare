(* ========================================================================= *)
(* Unit pc_p2b_kleaf (Part 2B, a step of the proof of                        *)
(* P2B_SPLIT_ROUND_STATEMENT): the compact leaf L of the split ancient flow  *)
(* is a smooth 2-sphere whose induced metrics form a 2-d Ricci flow with     *)
(* R_L = R > 0, pinched at arbitrarily negative times, and                   *)
(* (y,r) |-> Phi_r(y) is a bijection L x R -> M: the hypotheses of           *)
(* P2B_REQ_S2_ENTROPY_STATEMENT for the leaf; with that statement R is       *)
(* constant on L at every time.  The generic leaf geometry is in the unit    *)
(* pc_p2b_kleafg.                                                            *)
(*                                                                           *)
(* Main theorems: P2BKL_SHELL_LEVEL_SPHERE (shell leaves are spheres),       *)
(* P2BKL_SHELLS_PINCHED (pinched thick shells from the asymptotic soliton),  *)
(* P2BKL_LEAF_DATA (the leaf data), P2BKL_LEAF_ROUND (with                   *)
(* P2B_REQ_S2_ENTROPY_STATEMENT).                                            *)
(* ========================================================================= *)

needs "src/pc_p2b_kleafg.ml";;
needs "src/pc_p2b_kshell.ml";;
needs "src/pc_p2b_p946i.ml";;
needs "src/pc_lim_curv.ml";;
needs "src/pc_lrg_stab.ml";;
needs "src/pc_p2b_979s.ml";;
needs "src/pc_p2b_979.ml";;
needs "src/pc_mfd_restrict.ml";;
needs "src/pc_p2b_s2entreq.ml";;

prioritize_real();;
type_invention_error := true;;


(* P2BKL.L6 A level set of a shell function is a smooth 2-sphere: for an   *)
(* mfd_param psi on an open s0 containing the closed shell                 *)
(* inv(e) <= norm z <= e, a function h on M whose pullback Fn = h o psi    *)
(* satisfies the radial-graph condition p2bx46_shell Fn A0 (A0/10), the     *)
(* whole leaf lvs_set (psi(annulus(1/e,e))) h (h(psi w0)) is diffeomorphic  *)
(* to the round sphere with sphere2_atlas (P2BX46_NECK_LEVEL_SPHERE with a  *)
(* shell parametrization in place of the neck chart).                      *)

let P2BKL_SHELL_LEVEL_SPHERE = prove
 (`!top atlas (psi:real^3->A) s0 (h:A->real) (Fn:real^3->real) A0 w0.
     smooth_manifold_atlas top atlas /\ open s0 /\
     (!z. inv(exp(&1)) <= norm z /\ norm z <= exp(&1) ==> z IN s0) /\
     mfd_param top atlas s0 psi /\
     lvs_regular atlas (IMAGE psi (annulus (inv(exp(&1))) (exp(&1)))) h (h(psi w0)) /\
     smooth_map_on s0 (\z. lift(Fn z)) /\ (!z. z IN s0 ==> Fn z = h(psi z)) /\
     p2bx46_shell Fn A0 (A0 / &10) /\ &0 < A0 /\ norm w0 = &1
     ==> ?psi1 psi1'.
           mfd_diffeo (subtopology euclidean (sphere(vec 0:real^3,&1))) sphere2_atlas
                      (sphere(vec 0,&1))
                      (subtopology top (lvs_set (IMAGE psi (annulus (inv(exp(&1))) (exp(&1))))
                                                h (h(psi w0))))
                      (lvs_atlas top atlas (IMAGE psi (annulus (inv(exp(&1))) (exp(&1))))
                                 h (h(psi w0)))
                      (lvs_set (IMAGE psi (annulus (inv(exp(&1))) (exp(&1)))) h (h(psi w0)))
                      psi1 psi1'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  STRIP_ASSUME_TAC P2BX46_E_PI_BOUNDS THEN
  SUBGOAL_THEN
   `annulus (inv(exp(&1))) (exp(&1)) SUBSET (s0:real^3->bool) /\
    open(annulus (inv(exp(&1))) (exp(&1)):real^3->bool) /\
    (!z:real^3. z IN annulus (inv(exp(&1))) (exp(&1)) ==> ~(z = vec 0))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[OPEN_ANNULUS; SUBSET] THEN CONJ_TAC THENL
     [X_GEN_TAC `z:real^3` THEN DISCH_THEN(MP_TAC o MATCH_MP P2BX46_ANNULUS_E) THEN
      STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `z:real^3` THEN DISCH_THEN(MP_TAC o MATCH_MP P2BX46_ANNULUS_E) THEN
      SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `Sh = annulus (inv(exp(&1))) (exp(&1)):real^3->bool` THEN
  ABBREV_TAC `u = (h:A->real)((psi:real^3->A) w0)` THEN
  SUBGOAL_THEN `(Fn:real^3->real) w0 = u` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the radial graph *)
  MP_TAC(ISPECL [`Fn:real^3->real`; `A0:real`; `A0 / &10`; `s0:real^3->bool`;
                 `u:real`; `w0:real^3`] P2BX46_RADIAL_GRAPH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `O:real^3->bool` (X_CHOOSE_THEN `sig:real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  (* the parametrization *)
  FIRST_ASSUM(X_CHOOSE_THEN `ei:A->real^3` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS o
    check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_param"))
                         (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo] o
    check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_diffeo"))
                         (concl th))) THEN
  SUBGOAL_THEN `IMAGE (psi:real^3->A) s0 SUBSET topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_IMAGE_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `s0:real^3->bool`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (IMAGE (psi:real^3->A) Sh)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `s0:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `V = IMAGE (psi:real^3->A) Sh` THEN
  ABBREV_TAC `N = lvs_set V (h:A->real) u` THEN
  SUBGOAL_THEN `(N:A->bool) SUBSET V /\ N SUBSET topspace top`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN REWRITE_TAC[lvs_set] THEN
    SUBGOAL_THEN `(V:A->bool) SUBSET topspace top` MP_TAC THENL
     [EXPAND_TAC "V" THEN ASM SET_TAC[]; SET_TAC[]];
    ALL_TAC] THEN
  (* the two inverse maps *)
  SUBGOAL_THEN
   `!w:real^3. w IN sphere(vec 0,&1)
               ==> (sig:real^3->real^3) w IN Sh /\ (psi:real^3->A)(sig w) IN N /\
                   (ei:A->real^3)(psi(sig w)) = sig w /\ inv(norm(sig w)) % sig w = w`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `sig:real^3->real^3`)) (concl th) &&
      can (find_term ((=) `sphere(vec 0:real^3,&1)`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(sig:real^3->real^3) w IN s0` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    EXPAND_TAC "N" THEN REWRITE_TAC[lvs_set; IN_ELIM_THM] THEN CONJ_TAC THENL
     [EXPAND_TAC "V" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `(sig:real^3->real^3) w` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `Fn:real^3->real`)) (concl th) &&
        can (find_term ((=) `h:A->real`)) (concl th))) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p:A. p IN N
          ==> (ei:A->real^3) p IN Sh /\ inv(norm(ei p)) % ei p IN sphere(vec 0:real^3,&1) /\
              (psi:real^3->A)((sig:real^3->real^3)(inv(norm(ei p)) % ei p)) = p`
  ASSUME_TAC THENL
   [X_GEN_TAC `p:A` THEN EXPAND_TAC "N" THEN REWRITE_TAC[lvs_set; IN_ELIM_THM] THEN
    EXPAND_TAC "V" THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    SUBGOAL_THEN `(z:real^3) IN s0` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `p:A`)) THEN
    SUBGOAL_THEN `~(z:real^3 = vec 0)` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `inv(norm z) % z IN sphere(vec 0:real^3,&1)` ASSUME_TAC THENL
     [REWRITE_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
      MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[NORM_EQ_0];
      ALL_TAC] THEN
    SUBGOAL_THEN `(Fn:real^3->real) z = u` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `Fn:real^3->real`)) (concl th) &&
        can (find_term ((=) `h:A->real`)) (concl th))) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* continuity *)
  SUBGOAL_THEN `(sig:real^3->real^3) continuous_on sphere(vec 0,&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `O:real^3->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (subtopology euclidean (sphere(vec 0:real^3,&1)),top)
                               ((psi:real^3->A) o (sig:real^3->real^3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean (s0:real^3->bool)` THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `V SUBSET IMAGE (psi:real^3->A) s0` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!p:A. p IN V ==> (ei:A->real^3) p IN Sh` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^3` THEN
    DISCH_TAC THEN SUBGOAL_THEN `(z:real^3) IN s0` ASSUME_TAC THENL
     [ASM SET_TAC[]; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z:real^3. inv(norm z) % z) continuous_on Sh` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `{x:real^3 | ~(x = vec 0)}` THEN
    SIMP_TAC[SMOOTH_MAP_ON_NORMALIZE; SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `continuous_map (subtopology top V,subtopology euclidean (sphere(vec 0:real^3,&1)))
                   (\p:A. inv(norm((ei:A->real^3) p)) % ei p)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\p:A. inv(norm((ei:A->real^3) p)) % ei p) = (\z. inv(norm z) % z) o ei`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean (Sh:real^3->bool)` THEN CONJ_TAC THENL
     [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
        EXISTS_TAC `IMAGE (psi:real^3->A) s0` THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN
        ASM_SIMP_TAC[]];
      REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0] THEN X_GEN_TAC `z:real^3` THEN
      DISCH_TAC THEN REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
      MATCH_MP_TAC REAL_MUL_LINV THEN ASM_SIMP_TAC[NORM_EQ_0]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`(psi:real^3->A) o (sig:real^3->real^3)`;
                        `\p:A. inv(norm((ei:A->real^3) p)) % ei p`] THEN
  REWRITE_TAC[mfd_diffeo] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN; SUBSET_UNIV];
    REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN EXISTS_TAC `V:A->bool` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ASM SET_TAC[]];
    REWRITE_TAC[homeomorphic_maps; SUBTOPOLOGY_SUBTOPOLOGY; INTER_IDEMPOT] THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN; INTER_UNIV] THEN
    SUBGOAL_THEN `topspace top INTER (N:A->bool) = N` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN EXISTS_TAC `V:A->bool` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[];
      REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[]];
    (* smooth from the sphere into the leaf *)
    MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^3,&1))`; `sphere2_atlas`;
                   `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `V:A->bool`; `h:A->real`; `u:real`;
                   `sphere(vec 0:real^3,&1)`; `(psi:real^3->A) o (sig:real^3->real^3)`]
      P2BX46_LEAF_INTO) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[SPHERE2_ATLAS; OPEN_IN_TOPSPACE; OPEN_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN;
                SUBSET_UNIV; SUBTOPOLOGY_SUBTOPOLOGY; INTER_IDEMPOT] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^3,&1))`; `sphere2_atlas`;
                     `euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                     `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `sphere(vec 0:real^3,&1)`; `s0:real^3->bool`;
                     `sig:real^3->real^3`; `psi:real^3->A`] MFD_SMOOTH_MAP_COMPOSE) THEN
      DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[SPHERE2_ATLAS; MFD_EUCLIDEAN_ATLAS; OPEN_IN_SUBTOPOLOGY_REFL;
                      TOPSPACE_EUCLIDEAN; SUBSET_UNIV; GSYM OPEN_IN;
                      SUBTOPOLOGY_SUBTOPOLOGY; INTER_IDEMPOT] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM SET_TAC[];
        REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN] THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC P2BX46_SPHERE_SMOOTH_IN THEN EXISTS_TAC `O:real^3->bool` THEN
        ASM_REWRITE_TAC[]];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN ASM_SIMP_TAC[]];
    (* smooth from the leaf onto the sphere *)
    SUBGOAL_THEN `(N:A->bool) INTER V = N` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `subtopology euclidean (sphere(vec 0:real^3,&1))`; `sphere2_atlas`;
                   `V:A->bool`; `h:A->real`; `u:real`; `V:A->bool`;
                   `\p:A. inv(norm((ei:A->real^3) p)) % ei p`] P2BX46_LEAF_FROM) THEN
    ASM_REWRITE_TAC[SPHERE2_ATLAS] THEN DISCH_THEN MATCH_MP_TAC THEN
    SUBGOAL_THEN `(\p:A. inv(norm((ei:A->real^3) p)) % ei p) = (\z. inv(norm z) % z) o ei`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                   `subtopology euclidean (sphere(vec 0:real^3,&1))`; `sphere2_atlas`;
                   `V:A->bool`; `Sh:real^3->bool`;
                   `ei:A->real^3`; `\z:real^3. inv(norm z) % z`] MFD_SMOOTH_MAP_COMPOSE) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[SPHERE2_ATLAS; MFD_EUCLIDEAN_ATLAS; GSYM OPEN_IN] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
      EXISTS_TAC `IMAGE (psi:real^3->A) s0` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0] THEN X_GEN_TAC `z:real^3` THEN
      DISCH_TAC THEN REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
      MATCH_MP_TAC REAL_MUL_LINV THEN ASM_SIMP_TAC[NORM_EQ_0];
      MATCH_MP_TAC MFD_SMOOTH_MAP_SUBSET THEN
      EXISTS_TAC `IMAGE (psi:real^3->A) s0` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2BX46_SPHERE_SMOOTH_OUT THEN ASM_REWRITE_TAC[]]]);;


(* P2BKL.L7 The soliton slice has constant scalar curvature 1/lam on the     *)
(* image of the model map p of P2B_SHRINKER_SPLIT_CYL; the shell at one      *)
(* index on annulus(e^-2, e^2): primitive with the logarithmic estimate, and *)
(* the form estimate itself (a = 2 version of P2BKS_SHELL_AT_INDEX).         *)

let P2BKL_U4_SCALAR = prove
 (`!top atlas (g0:B->real^3^3) (p:real^3->B) lam y.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g0 /\ &0 < lam /\
     (!y. ~(y = vec 0) ==> ?r. &0 < r /\ r < norm y /\ mfd_param top atlas (ball(y,r)) p) /\
     (!y. ~(y = vec 0) ==> rfs_pullback atlas p g0 y = lam %% cylinder_flow (&0) y) /\
     ~(y = vec 0)
     ==> mfd_scalar atlas g0 (p y) = inv lam`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "par")
      (CONJUNCTS_THEN2 (LABEL_TAC "pb") ASSUME_TAC))))) THEN
  USE_THEN "par" (MP_TAC o C MATCH_MP (ASSUME `~(y:real^3 = vec 0)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g0:B->real^3^3`; `ball(y:real^3,r)`; `p:real^3->B`;
                 `&1`; `y:real^3`] P2B9_PARAM_LSCALAR_SCALED) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CENTRE_IN_BALL; REAL_LT_01]; REWRITE_TAC[REAL_DIV_1]] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN
   `lscalar (\z. &1 %% rfs_pullback atlas (p:real^3->B) (g0:B->real^3^3) z) y =
    lscalar (\z. lam %% cylinder_flow (&0) z) y`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LSCALAR_LOCAL THEN EXISTS_TAC `ball(y:real^3,r)` THEN
    ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL; MATRIX_CMUL_LID] THEN
    X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_BALL] THEN DISCH_TAC THEN
    USE_THEN "pb" MATCH_MP_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `dist(y:real^3,z) < r` THEN ASM_REWRITE_TAC[DIST_0] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `cylinder_flow (&0)`; `lam:real`; `y:real^3`]
    LSCALAR_SCALE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD; IN_DELETE; IN_UNIV; REAL_LT_01];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`&0`; `y:real^3`] RFB_CYL_SCALAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LT_01]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[REAL_SUB_RZERO; REAL_DIV_1; real_div; REAL_MUL_LID; REAL_INV_1]);;

let P2BKL_SHELL_AT_INDEX2 = prove
 (`?C. &0 < C /\
       !top atlas (g0:B->real^3^3) (Y:B->real^3) top1 atlas1 (g1:A->real^3^3) (X:A->real^3)
        (phi:B->A) phi' W (p:real^3->B) lam Q eta m.
         smooth_manifold_atlas top atlas /\ riemannian_metric atlas g0 /\
         smooth_manifold_atlas top1 atlas1 /\ riemannian_metric atlas1 g1 /\
         p2b_parallel_on atlas1 g1 (topspace top1) X /\
         mfd_diffeo top atlas W top1 atlas1 (IMAGE phi W) phi phi' /\
         mfd_param top atlas (annulus (exp(--(&2))) (exp(&2))) p /\
         IMAGE p (annulus (exp(--(&2))) (exp(&2))) SUBSET W /\
         &0 < lam /\ &0 < Q /\ &0 <= eta /\
         (!y. y IN annulus (exp(--(&2))) (exp(&2))
              ==> rfs_pullback atlas p g0 y = lam %% cylinder_flow (&0) y /\
                  Y(p y) = frechet_derivative (\z. SND(chart_at atlas (p y)) (p z)) (at y)
                                              (inv(sqrt(&2 * lam)) % y) /\
                  Y(p y) dot (g0(p y) ** Y(p y)) = &1 /\
                  (?zz. mfd_differential atlas atlas1 phi (p y) zz = X(phi(p y)) /\
                        (inv(sqrt Q) % zz - Y(p y)) dot
                        (g0(p y) ** (inv(sqrt Q) % zz - Y(p y))) <= eta) /\
                  lck_dist2 m (metric_local atlas (chart_at atlas (p y)) g0)
                              (metric_local atlas (chart_at atlas (p y))
                                 (\x. Q %% mfd_pullback_metric atlas atlas1 phi g1 x))
                              (SND(chart_at atlas (p y)) (p y)) <= eta)
         ==> (!y. y IN annulus (exp(--(&2))) (exp(&2))
                  ==> norm(p2bkg_pform atlas1 g1 X (phi o p) y -
                           (sqrt(&2 * lam / Q) / norm y pow 2) % y) <=
                      &3 * (inv(sqrt Q) * (sqrt(&3 * eta) + sqrt(eta * eta) + sqrt eta) *
                            sqrt(&2 * lam) / norm y)) /\
             ?h c0. p2bkg_prim atlas1 g1 X (IMAGE (phi o p) (annulus (exp(--(&2))) (exp(&2)))) h /\
                    !y. y IN annulus (exp(--(&2))) (exp(&2))
                        ==> abs((h((phi o p) y) - c0) - sqrt(&2 * lam / Q) * log(norm y)) <=
                            C * (&3 * (inv(sqrt Q) *
                                       (sqrt(&3 * eta) + sqrt(eta * eta) + sqrt eta) *
                                       sqrt(&2 * lam) * exp(&2)))`,
  MP_TAC(SPEC `&2` P2BKS_SHELL_FROM_FORM) THEN
  REWRITE_TAC[REAL_ARITH `&0 < &2`] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sff"))) THEN
  EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN LABEL_TAC "dat"
    (funpow 11 CONJUNCT2 th)) THEN
  ABBREV_TAC `S = annulus (exp(--(&2))) (exp(&2)):real^3->bool` THEN
  SUBGOAL_THEN `mfd_param top1 atlas1 S ((phi:B->A) o (p:real^3->B))` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BKS_PARAM_DIFFEO_COMPOSE THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                          `phi':A->B`; `W:B->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Bd = sqrt(&3 * eta) + sqrt(eta * eta) + sqrt eta` THEN
  SUBGOAL_THEN `&0 <= Bd` ASSUME_TAC THENL
   [EXPAND_TAC "Bd" THEN MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LE THEN
    ASM_SIMP_TAC[REAL_LE_MUL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN S
        ==> norm(p2bkg_pform atlas1 (g1:A->real^3^3) (X:A->real^3) ((phi:B->A) o (p:real^3->B)) y -
                 (sqrt(&2 * lam / Q) / norm y pow 2) % y) <=
            &3 * (inv(sqrt Q) * Bd * sqrt(&2 * lam) / norm y)`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "dat" (MP_TAC o C MATCH_MP (ASSUME `(y:real^3) IN S`)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `zz:real^3` STRIP_ASSUME_TAC) ASSUME_TAC)))) THEN
    SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `(y:real^3) IN S` THEN EXPAND_TAC "S" THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REWRITE_TAC[NORM_0] THEN
      MP_TAC(SPEC `--(&2)` REAL_EXP_POS_LT) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "Bd" THEN
    MATCH_MP_TAC(ISPECL
     [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `Y:B->real^3`;
      `top1:A topology`; `atlas1:((A->bool)#(A->real^3))->bool`; `g1:A->real^3^3`;
      `X:A->real^3`; `phi:B->A`; `phi':A->B`; `W:B->bool`; `p:real^3->B`; `S:real^3->bool`;
      `lam:real`; `Q:real`; `y:real^3`; `zz:real^3`; `eta:real`; `eta:real`; `m:num`]
     P2BKS_PFORM_CLOSE_POINT) THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    EXPAND_TAC "S" THEN REWRITE_TAC[P2BPC_ANNULUS_OPEN];
    ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  USE_THEN "sff" (MP_TAC o SPECL
   [`top1:A topology`; `atlas1:((A->bool)#(A->real^3))->bool`; `g1:A->real^3^3`;
    `X:A->real^3`; `topspace top1:A->bool`; `(phi:B->A) o (p:real^3->B)`;
    `sqrt(&2 * lam / Q)`;
    `&3 * (inv(sqrt Q) * Bd * sqrt(&2 * lam) * exp(&2))`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_IN_TOPSPACE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_IMAGE_SUBSET THEN
      MAP_EVERY EXISTS_TAC [`atlas1:((A->bool)#(A->real^3))->bool`; `S:real^3->bool`] THEN
      ASM_REWRITE_TAC[SUBSET_REFL];
      ALL_TAC] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `exp(--(&2)) < norm(y:real^3)` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN S` THEN EXPAND_TAC "S" THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&3 * (inv(sqrt Q) * Bd * sqrt(&2 * lam) / norm(y:real^3))` THEN
    CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [REWRITE_TAC[REAL_LE_INV_EQ; SQRT_POS_LE] THEN
                    MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `exp(&2) = inv(exp(--(&2)))` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_EXP_NEG; REAL_NEG_NEG]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_EXP_POS_LT];
    ALL_TAC] THEN
  REWRITE_TAC[o_THM]);;


(* P2BKL.L8 The radial-graph condition from the form estimate, and an      *)
(* arithmetic fact: pinching from closeness to a positive constant.        *)

let P2BKL_PFORM_SHELL = prove
 (`!(Fn:real^3->real) (pf:real^3->real^3) kappa eps1.
     &0 < kappa /\ &0 <= eps1 /\ &11 * eps1 <= &1 /\
     (!z. inv(exp(&1)) <= norm z /\ norm z <= exp(&1)
          ==> ((\v. lift(Fn v)) has_derivative (\v. lift(pf z dot v))) (at z) /\
              norm(pf z - (kappa / norm z pow 2) % z) <= eps1 * kappa / norm z)
     ==> p2bx46_shell Fn (kappa * (&1 - eps1)) ((kappa * (&1 - eps1)) / &10)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[p2bx46_shell] THEN
  X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(z:real^3)` ASSUME_TAC THENL
   [MP_TAC P2BX46_E_PI_BOUNDS THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `d = (pf:real^3->real^3) z - (kappa / norm(z:real^3) pow 2) % z` THEN
  SUBGOAL_THEN `!v:real^3. pf z dot v = d dot v + (kappa / norm(z:real^3) pow 2) * (z dot v)`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "d" THEN REWRITE_TAC[DOT_LSUB; DOT_LMUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^3. abs(d dot v) <= (eps1 * kappa / norm(z:real^3)) * norm v`
  (LABEL_TAC "cs") THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm(d:real^3) * norm(v:real^3)` THEN
    REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[differentiable] THEN ASM_MESON_TAC[];
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    REWRITE_TAC[LIFT_DROP] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[DOT_SQUARE_NORM] THEN
    SUBGOAL_THEN `kappa / norm(z:real^3) pow 2 * norm z pow 2 = kappa` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_DIV_RMUL THEN
      ASM_SIMP_TAC[REAL_POW_EQ_0; REAL_LT_IMP_NZ; ARITH_EQ];
      ALL_TAC] THEN
    USE_THEN "cs" (MP_TAC o SPEC `z:real^3`) THEN
    SUBGOAL_THEN `(eps1 * kappa / norm(z:real^3)) * norm z = eps1 * kappa` SUBST1_TAC THENL
     [MATCH_MP_TAC(REAL_FIELD `~(n = &0) ==> (e * k / n) * n = e * k`) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_NZ];
      ALL_TAC] THEN
    REAL_ARITH_TAC;
    X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    REWRITE_TAC[LIFT_DROP] THEN ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(eps1 * kappa / norm(z:real^3)) * norm(v:real^3)` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= kappa * inv(norm(z:real^3)) * norm(v:real^3)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[NORM_POS_LE; REAL_LE_INV_EQ];
      ALL_TAC] THEN
    MP_TAC(SPECL [`eps1:real`; `(&1 - eps1) * inv(&10)`;
                  `kappa * inv(norm(z:real^3)) * norm(v:real^3)`] REAL_LE_RMUL) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC]);;

let P2BKL_PINCH_ARITH = prove
 (`!R0 e Q a b.
     &0 < R0 /\ &0 < e /\ &0 < Q /\
     abs(a / Q - R0) <= e * R0 / (&2 * (&2 + e)) /\
     abs(b / Q - R0) <= e * R0 / (&2 * (&2 + e))
     ==> a <= (&1 + e) * b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `al = e * R0 / (&2 * (&2 + e))` THEN
  SUBGOAL_THEN `al * (&2 + e) = e * R0 / &2` ASSUME_TAC THENL
   [EXPAND_TAC "al" THEN
    MATCH_MP_TAC(REAL_FIELD `~(&2 + e = &0) ==> (e * r / (&2 * (&2 + e))) * (&2 + e) = e * r / &2`) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < e * R0` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN `a <= Q * (R0 + al) /\ Q * (R0 - al) <= b` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `a / Q <= R0 + al /\ R0 - al <= b / Q` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `R0 + al <= (&1 + e) * (R0 - al)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Q * (R0 + al)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 + e) * Q * (R0 - al)` THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`Q:real`; `R0 + al`; `(&1 + e) * (R0 - al)`] REAL_LE_LMUL) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;


(* P2BKL.L9 Pinched shells of every thickness from the asymptotic soliton (a *)
(* strengthened form of P2BKS_SHELLS_FROM_LIMIT): for every tk, e > 0 and Tm *)
(* there is an index k with t k < Tm and a shell psi on annulus(e^-2, e^2)   *)
(* carrying a primitive h for gs with the logarithmic estimate, tk + delta < *)
(* 2 kappa, the radial-graph condition for h o psi, and scalar curvature of  *)
(* the slice at index k pinched by 1 + e on psi(shell).                      *)

let P2BKL_SHELLS_PINCHED = prove
 (`!V x t Q top atlas (g0:B->real^3^3) xl W (phi:num->B->A) (top1:A topology) atlas1
    (gs:A->real^3^3) (X:A->real^3) sub (Y:B->real^3) (p:real^3->B) lam.
     p2c_slice_limit_with V x t Q (top,atlas) g0 xl W phi /\
     (!n. rfs_vtop (V n) (t n) = top1 /\ rfs_vatlas (V n) (t n) = atlas1) /\
     hausdorff_space top1 /\ smooth_manifold_atlas top1 atlas1 /\
     (!n. riemannian_metric atlas1 (rfs_vmetric (V n) (t n)) /\
          p2b_parallel_on atlas1 (rfs_vmetric (V n) (t n)) (topspace top1) X /\
          (!y. y IN topspace top1 ==> rfs_vmetric (V n) (t n) y ** X y = gs y ** X y)) /\
     (!e. &0 < e ==> ?n0. !n. n0 <= n ==> Q n < e) /\
     (!Tm. ?n0. !n. n0 <= n ==> t n < Tm) /\
     p3_subseq sub /\
     (!y. y IN topspace top ==> Y y dot (g0 y ** Y y) = &1) /\
     (!K e. compact_in top K /\ &0 < e
            ==> ?n0. !n. n0 <= n
                         ==> !y. y IN K
                                 ==> ?z. mfd_differential atlas atlas1 (phi (sub n)) y z =
                                         X (phi (sub n) y) /\
                                         (inv(sqrt(Q(sub n))) % z - Y y) dot
                                         (g0 y ** (inv(sqrt(Q(sub n))) % z - Y y)) < e) /\
     &0 < lam /\
     (!y. ~(y = vec 0) ==> ?r. &0 < r /\ r < norm y /\ mfd_param top atlas (ball(y,r)) p) /\
     (!y z. ~(y = vec 0) /\ ~(z = vec 0) ==> (p y = p z <=> z = y)) /\
     (!y. ~(y = vec 0) ==> rfs_pullback atlas p g0 y = lam %% cylinder_flow (&0) y) /\
     (!y. ~(y = vec 0)
          ==> Y(p y) = mfd_differential (open_set_atlas {z:real^3 | ~(z = vec 0)}) atlas p y
                                        (inv(sqrt(&2 * lam)) % y))
     ==> !tk e Tm. &0 < e
            ==> ?k psi h kappa delta c0 A0.
                  t k < Tm /\
                  mfd_param top1 atlas1 (annulus (exp(--(&2))) (exp(&2))) psi /\
                  p2bkg_prim atlas1 gs X (IMAGE psi (annulus (exp(--(&2))) (exp(&2)))) h /\
                  &0 < kappa /\ &0 <= delta /\ tk + delta < kappa * &2 /\
                  (!y. y IN annulus (exp(--(&2))) (exp(&2))
                       ==> abs((h(psi y) - c0) - kappa * log(norm y)) <= delta) /\
                  &0 < A0 /\ p2bx46_shell (\z. h(psi z)) A0 (A0 / &10) /\
                  (!y1 y2. y1 IN IMAGE psi (annulus (exp(--(&2))) (exp(&2))) /\
                           y2 IN IMAGE psi (annulus (exp(--(&2))) (exp(&2)))
                           ==> mfd_scalar atlas1 (rfs_vmetric (V k) (t k)) y1 <=
                               (&1 + e) * mfd_scalar atlas1 (rfs_vmetric (V k) (t k)) y2)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN
     LABEL_TAC "qz" (CONJUNCT1(funpow 5 CONJUNCT2 th)) THEN
     LABEL_TAC "tz" (CONJUNCT1(funpow 6 CONJUNCT2 th)) THEN
     LABEL_TAC "pf" (CONJUNCT1(funpow 9 CONJUNCT2 th))) THEN
  MAP_EVERY X_GEN_TAC [`tk:real`; `e:real`; `Tm:real`] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2c_slice_limit_with]) THEN
  MP_TAC P2BKL_SHELL_AT_INDEX2 THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sai"))) THEN
  MP_TAC(SPEC `min (inv(&6 * C * exp(&2))) (inv(&33))` P2BKS_ETA_CHOICE) THEN ANTS_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`lam:real`; `tk:real`] P2BKS_KAPPA_BIG) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "kb"))) THEN
  SUBGOAL_THEN `!S. open S /\ ~(vec 0 IN S) ==> mfd_param top atlas S (p:real^3->B)`
  (LABEL_TAC "par") THENL
   [GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC P2BKS_U4_PARAM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `S = annulus (exp(--(&2))) (exp(&2)):real^3->bool` THEN
  ABBREV_TAC `K0 = cball(vec 0:real^3,exp(&2)) DIFF ball(vec 0,exp(--(&2)))` THEN
  SUBGOAL_THEN `compact_in top (IMAGE (p:real^3->B) K0) /\ S SUBSET K0 /\
                mfd_param top atlas S p /\ (!z:real^3. z IN K0 ==> ~(z = vec 0))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`;
                            `annulus (exp(--(&3))) (exp(&3)):real^3->bool`] THEN
      REPEAT CONJ_TAC THENL
       [USE_THEN "par" MATCH_MP_TAC THEN
        REWRITE_TAC[P2BPC_ANNULUS_OPEN; annulus; IN_ELIM_THM; NORM_0] THEN
        MP_TAC(SPEC `--(&3)` REAL_EXP_POS_LT) THEN REAL_ARITH_TAC;
        EXPAND_TAC "K0" THEN SIMP_TAC[COMPACT_DIFF; COMPACT_CBALL; OPEN_BALL];
        EXPAND_TAC "K0" THEN
        REWRITE_TAC[SUBSET; IN_DIFF; IN_CBALL_0; IN_BALL_0; annulus; IN_ELIM_THM; REAL_NOT_LT] THEN
        GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `exp(--(&2))` THEN
          ASM_REWRITE_TAC[REAL_EXP_MONO_LT] THEN REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `exp(&2)` THEN
          ASM_REWRITE_TAC[REAL_EXP_MONO_LT] THEN REAL_ARITH_TAC]];
      EXPAND_TAC "S" THEN EXPAND_TAC "K0" THEN
      REWRITE_TAC[SUBSET; IN_DIFF; IN_CBALL_0; IN_BALL_0; annulus; IN_ELIM_THM] THEN
      REAL_ARITH_TAC;
      EXPAND_TAC "S" THEN USE_THEN "par" MATCH_MP_TAC THEN
      REWRITE_TAC[P2BPC_ANNULUS_OPEN; annulus; IN_ELIM_THM; NORM_0] THEN
      MP_TAC(SPEC `--(&2)` REAL_EXP_POS_LT) THEN REAL_ARITH_TAC;
      EXPAND_TAC "K0" THEN REWRITE_TAC[IN_DIFF; IN_CBALL_0; IN_BALL_0; REAL_NOT_LT] THEN
      GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
      UNDISCH_TAC `exp(--(&2)) <= norm(z:real^3)` THEN ASM_REWRITE_TAC[NORM_0] THEN
      MP_TAC(SPEC `--(&2)` REAL_EXP_POS_LT) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `K = IMAGE (p:real^3->B) K0` THEN
  (* constants for the scalar curvature closeness *)
  MP_TAC(ISPECL [`0`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
                 `K:B->bool`] P2B9S_RMD2_COMPACT_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `Bk:real`) THEN
  SUBGOAL_THEN `!y. y IN K ==> rfa_rmd2 0 atlas (g0:B->real^3^3) y <= (abs Bk + &1) pow 2`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:B` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `Bk:real` THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= abs b + &1 /\ abs b + &1 <= (abs b + &1) pow 2
                             ==> b <= (abs b + &1) pow 2`) THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_2] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 * a <= a * a ==> a <= a * a`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `al = e * inv lam / (&2 * (&2 + e))` THEN
  SUBGOAL_THEN `&0 < al` ASSUME_TAC THENL
   [EXPAND_TAC "al" THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_LT_INV] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`abs Bk + &1`; `al:real`] (INST_TYPE [`:3`,`:N`] LCK_CURVATURE_STABILITY)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `etc:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lcs"))) THEN
  (* the indices *)
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`; `x:num->A`; `t:num->real`; `Q:num->real`;
                 `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
                 `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `K:B->bool`; `0`; `eta:real`]
                P2BPL_SLICE_CLOSE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n1:num` (LABEL_TAC "sc")) THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`; `x:num->A`; `t:num->real`; `Q:num->real`;
                 `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
                 `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `K:B->bool`; `2`; `etc pow 2`]
                P2BPL_SLICE_CLOSE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n5:num` (LABEL_TAC "sc2")) THEN
  USE_THEN "pf" (MP_TAC o SPECL [`K:B->bool`; `eta:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n2:num` (LABEL_TAC "pfn")) THEN
  USE_THEN "qz" (MP_TAC o C MATCH_MP (ASSUME `&0 < q0`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `n3:num` (LABEL_TAC "qn")) THEN
  USE_THEN "tz" (MP_TAC o SPEC `Tm:real`) THEN
  DISCH_THEN(X_CHOOSE_THEN `n4:num` (LABEL_TAC "tn")) THEN
  SUBGOAL_THEN `!n. n <= (sub:num->num) n` ASSUME_TAC THENL
   [MATCH_MP_TAC MONOTONE_BIGGER THEN ASM_MESON_TAC[p3_subseq]; ALL_TAC] THEN
  ABBREV_TAC `N = n1 + n2 + n3 + n4 + n5:num` THEN
  SUBGOAL_THEN `N <= (sub:num->num) N` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `k = (sub:num->num) N` THEN
  SUBGOAL_THEN `n1 <= (k:num) /\ n2 <= (N:num) /\ n3 <= (k:num) /\ n4 <= (k:num) /\
                n5 <= (k:num)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `n1 + n2 + n3 + n4 + n5 = (N:num)` THEN UNDISCH_TAC `(N:num) <= k` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "sc" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sck")) THEN
  USE_THEN "sc2" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "sck2" o CONJUNCT2) THEN
  USE_THEN "pfn" (MP_TAC o SPEC `N:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "pfk") THEN
  USE_THEN "qn" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  USE_THEN "tn" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(SPEC `k:num` (ASSUME
   `!k. ?psi. mfd_diffeo top (atlas:((B->bool)#(B->real^3))->bool) ((W:num->B->bool) k)
                (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) k) (t k))
                (rfs_vatlas (V k) (t k)) (IMAGE ((phi:num->B->A) k) (W k)) (phi k) psi`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `phi':A->B` MP_TAC) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `IMAGE (p:real^3->B) S SUBSET (W:num->B->bool) k` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `K:B->bool` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "K" THEN ASM_SIMP_TAC[IMAGE_SUBSET];
    ALL_TAC] THEN
  ABBREV_TAC `g1 = rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) k) (t k)` THEN
  SUBGOAL_THEN `riemannian_metric atlas1 (g1:A->real^3^3) /\
                p2b_parallel_on atlas1 g1 (topspace top1) (X:A->real^3) /\
                (!y. y IN topspace top1 ==> g1 y ** X y = (gs:A->real^3^3) y ** X y)`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "g1" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the shell at index k *)
  USE_THEN "sai" (MP_TAC o SPECL
   [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `Y:B->real^3`;
    `top1:A topology`; `atlas1:((A->bool)#(A->real^3))->bool`; `g1:A->real^3^3`;
    `X:A->real^3`; `(phi:num->B->A) k`; `phi':A->B`; `(W:num->B->bool) k`; `p:real^3->B`;
    `lam:real`; `(Q:num->real) k`; `eta:real`; `0`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(y:real^3 = vec 0) /\ (p:real^3->B) y IN K` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [ASM SET_TAC[];
        EXPAND_TAC "K" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(p:real^3->B) y IN topspace top` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `S:real^3->bool`;
                     `p:real^3->B`; `S:real^3->bool`] MFD_PARAM_IMAGE_SUBSET) THEN
      ASM_REWRITE_TAC[SUBSET_REFL] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[];
      ALL_TAC;
      ASM_SIMP_TAC[];
      USE_THEN "pfk" (MP_TAC o C MATCH_MP (ASSUME `(p:real^3->B) y IN K`)) THEN
      MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[REAL_LT_IMP_LE];
      USE_THEN "sck" (MP_TAC o C MATCH_MP (ASSUME `(p:real^3->B) y IN K`)) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_LT_IMP_LE]] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(p:real^3->B) y`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `S:real^3->bool`;
                   `p:real^3->B`; `chart_at (atlas:((B->bool)#(B->real^3))->bool) ((p:real^3->B) y)`]
                  P2BKG_PARAM_CHART_SMOOTH) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [EXPAND_TAC "S" THEN REWRITE_TAC[P2BPC_ANNULUS_OPEN]; STRIP_TAC] THEN
    SUBGOAL_THEN `(\z. SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) ((p:real^3->B) y)) (p z))
                  differentiable at y` ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `{z:real^3 | z IN S /\
                     (p:real^3->B) z IN FST(chart_at (atlas:((B->bool)#(B->real^3))->bool) (p y))}` THEN
      ASM_REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`{z:real^3 | ~(z = vec 0)}`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `p:real^3->B`; `y:real^3`] P2BKS_MDIFF_OPEN_SET_LOCAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      SUBGOAL_THEN `{z:real^3 | ~(z = vec 0)} = (:real^3) DELETE vec 0` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DELETE; IN_UNIV]; ALL_TAC] THEN
      SIMP_TAC[OPEN_DELETE; OPEN_UNIV];
      ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "pfb")
    (X_CHOOSE_THEN `h:A->real` (X_CHOOSE_THEN `c0:real` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `mfd_param top1 atlas1 S ((phi:num->B->A) k o (p:real^3->B))` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BKS_PARAM_DIFFEO_COMPOSE THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                          `phi':A->B`; `(W:num->B->bool) k`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `psi = (phi:num->B->A) k o (p:real^3->B)` THEN
  ABBREV_TAC `Bd = sqrt(&3 * eta) + sqrt(eta * eta) + sqrt eta` THEN
  SUBGOAL_THEN `&0 <= Bd` ASSUME_TAC THENL
   [EXPAND_TAC "Bd" THEN MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LE THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt((Q:num->real) k) /\ &0 < sqrt(&2 * lam)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `kappa = sqrt(&2 * lam / (Q:num->real) k)` THEN
  SUBGOAL_THEN `&0 < kappa` ASSUME_TAC THENL
   [EXPAND_TAC "kappa" THEN
    MATCH_MP_TAC SQRT_POS_LT THEN MATCH_MP_TAC REAL_LT_MUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`k:num`; `psi:real^3->A`; `h:A->real`; `kappa:real`;
    `C * (&3 * (inv(sqrt((Q:num->real) k)) * Bd * sqrt(&2 * lam) * exp(&2)))`;
    `c0:real`; `kappa * (&1 - &3 * Bd)`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    (* the primitive for gs *)
    MATCH_MP_TAC P2BKS_PRIM_INVARIANT THEN EXISTS_TAC `top1:A topology` THEN
    EXISTS_TAC `g1:A->real^3^3` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`atlas1:((A->bool)#(A->real^3))->bool`; `S:real^3->bool`] THEN
      ASM_REWRITE_TAC[SUBSET_REFL] THEN EXPAND_TAC "S" THEN REWRITE_TAC[P2BPC_ANNULUS_OPEN];
      X_GEN_TAC `xx:A` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(xx:A) IN topspace top1` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`top1:A topology`; `atlas1:((A->bool)#(A->real^3))->bool`;
                       `S:real^3->bool`; `psi:real^3->A`; `S:real^3->bool`]
                      MFD_PARAM_IMAGE_SUBSET) THEN
        ASM_REWRITE_TAC[SUBSET_REFL] THEN ASM SET_TAC[];
        ASM_SIMP_TAC[]]];
    ASM_REWRITE_TAC[];
    (* delta >= 0 *)
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_INV_EQ; REAL_EXP_POS_LE] THEN REAL_ARITH_TAC;
    (* thickness *)
    MP_TAC(ISPECL [`C:real`; `exp(&2)`; `Bd:real`;
                   `inv(sqrt((Q:num->real) k))`; `sqrt(&2 * lam)`] P2BKS_DELTA_HALF) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_EXP_POS_LT; REAL_LE_INV_EQ; REAL_LT_IMP_LE]; ALL_TAC] THEN
    USE_THEN "kb" (MP_TAC o SPEC `(Q:num->real) k`) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(SPECL [`lam:real`; `(Q:num->real) k`] P2BKS_KAPPA_SPLIT) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    (* the logarithmic estimate *)
    ASM_REWRITE_TAC[];
    (* A0 > 0 *)
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    (* the radial-graph condition *)
    MATCH_MP_TAC P2BKL_PFORM_SHELL THEN
    EXISTS_TAC `p2bkg_pform atlas1 (g1:A->real^3^3) (X:A->real^3) (psi:real^3->A)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN S` ASSUME_TAC THENL
     [EXPAND_TAC "S" THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN
      STRIP_ASSUME_TAC P2BX46_E_PI_BOUNDS THEN
      SUBGOAL_THEN `exp(--(&2)) < inv(exp(&1)) /\ exp(&1) < exp(&2)` MP_TAC THENL
       [REWRITE_TAC[GSYM REAL_EXP_NEG; REAL_EXP_MONO_LT] THEN REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2BKS_PRIM_PARAM_DERIV THEN
      MAP_EVERY EXISTS_TAC [`top1:A topology`; `IMAGE (psi:real^3->A) S`; `S:real^3->bool`] THEN
      ASM_REWRITE_TAC[SUBSET_REFL] THEN CONJ_TAC THENL
       [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
        MAP_EVERY EXISTS_TAC [`atlas1:((A->bool)#(A->real^3))->bool`; `S:real^3->bool`] THEN
        ASM_REWRITE_TAC[SUBSET_REFL] THEN EXPAND_TAC "S" THEN REWRITE_TAC[P2BPC_ANNULUS_OPEN];
        EXPAND_TAC "S" THEN REWRITE_TAC[P2BPC_ANNULUS_OPEN]];
      ALL_TAC] THEN
    USE_THEN "pfb" (MP_TAC o C MATCH_MP (ASSUME `(z:real^3) IN S`)) THEN
    MP_TAC(SPECL [`lam:real`; `(Q:num->real) k`] P2BKS_KAPPA_SPLIT) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `y = x ==> a <= y ==> a <= x`) THEN
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* pinching *)
  SUBGOAL_THEN
   `!z. z IN S
        ==> abs(mfd_scalar atlas1 (g1:A->real^3^3) ((psi:real^3->A) z) / (Q:num->real) k -
                inv lam) <= al`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(z:real^3 = vec 0) /\ (p:real^3->B) z IN K` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [ASM SET_TAC[];
        EXPAND_TAC "K" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
                   `p:real^3->B`; `lam:real`; `z:real^3`] P2BKL_U4_SCALAR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    EXPAND_TAC "psi" THEN REWRITE_TAC[o_THM] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
                   `top1:A topology`; `atlas1:((A->bool)#(A->real^3))->bool`; `g1:A->real^3^3`;
                   `(W:num->B->bool) k`; `IMAGE ((phi:num->B->A) k) (W k)`; `(phi:num->B->A) k`;
                   `phi':A->B`; `(Q:num->real) k`; `abs Bk + &1`; `al:real`; `etc:real`;
                   `(p:real^3->B) z`] LIM_POINT_CURV) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
       [ASM SET_TAC[];
        ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[];
        USE_THEN "sck2" (MP_TAC o C MATCH_MP (ASSUME `(p:real^3->B) z IN K`)) THEN
        ASM_REWRITE_TAC[]];
      SIMP_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`y1:A`; `y2:A`] THEN REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z1:real^3` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `z2:real^3` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BKL_PINCH_ARITH THEN
  MAP_EVERY EXISTS_TAC [`inv lam`; `(Q:num->real) k`] THEN
  ASM_SIMP_TAC[REAL_LT_INV]);;


(* P2BKL.L10 Assembly helpers for the main leaf: restriction of             *)
(* primitives, smoothness of h o psi, compactness and connectedness of a    *)
(* diffeomorphic image of the sphere, the main leaf of a pinched shell, and *)
(* pinching transported along the X-orbits (leaf transport and isometry     *)
(* invariance of the scalar curvature).                                     *)

let P2BKL_PRIM_SUBSET = prove
 (`!atlas (g:A->real^3^3) (X:A->real^3) V V' h.
     p2bkg_prim atlas g X V h /\ V' SUBSET V ==> p2bkg_prim atlas g X V' h`,
  REWRITE_TAC[p2bkg_prim] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC MFD_SMOOTH_ON_SUBSET THEN EXISTS_TAC `V:A->bool` THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

let P2BKL_SHELL_FN_SMOOTH = prove
 (`!top atlas (psi:real^3->A) s (h:A->real) V.
     smooth_manifold_atlas top atlas /\ mfd_param top atlas s psi /\ open_in top V /\
     IMAGE psi s SUBSET V /\ mfd_smooth_on atlas V (\x. lift(h x))
     ==> smooth_map_on s (\z. lift(h(psi z)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `mfd_param top (atlas:((A->bool)#(A->real^3))->bool) s (psi:real^3->A)` THEN
  REWRITE_TAC[mfd_param] THEN DISCH_THEN(X_CHOOSE_TAC `e':A->real^3`) THEN
  SUBGOAL_THEN `(\z. lift((h:A->real)((psi:real^3->A) z))) = (\x. lift(h x)) o psi`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC LVS_PARAM_SMOOTH_COMPOSE THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `V:A->bool`;
                        `e':A->real^3`] THEN
  ASM_REWRITE_TAC[]);;

let P2BKL_SPHERE_IMAGE_FACTS = prove
 (`!top (L:A->bool) (atlasL:((A->bool)#(A->real^2))->bool) (psi1:real^3->A) psi1'.
     mfd_diffeo (subtopology euclidean (sphere(vec 0:real^3,&1))) sphere2_atlas (sphere(vec 0,&1))
                (subtopology top L) atlasL L psi1 psi1' /\ L SUBSET topspace top
     ==> compact_in top L /\ connected_in top L /\ ~(L = {})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_diffeo] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> is_const t &&
    fst(dest_const t) = "homeomorphic_maps")) (concl th))) THEN
  REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY; INTER_IDEMPOT] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HOMEOMORPHIC_MAPS_IMP_MAP) THEN
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP HOMEOMORPHIC_IMP_SURJECTIVE_MAP th) THEN
                       ASSUME_TAC(MATCH_MP HOMEOMORPHIC_IMP_CONTINUOUS_MAP th)) THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY] THEN
  SUBGOAL_THEN `topspace top INTER (L:A->bool) = L` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `compact_in (subtopology top (L:A->bool)) (IMAGE (psi1:real^3->A) (sphere(vec 0,&1))) /\
    connected_in (subtopology top L) (IMAGE psi1 (sphere(vec 0,&1)))`
  MP_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_COMPACT_IN THEN
      EXISTS_TAC `subtopology euclidean (sphere(vec 0:real^3,&1))` THEN
      ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; SUBSET_REFL; COMPACT_IN_EUCLIDEAN; COMPACT_SPHERE];
      MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
      EXISTS_TAC `subtopology euclidean (sphere(vec 0:real^3,&1))` THEN
      ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; SUBSET_REFL; CONNECTED_IN_EUCLIDEAN] THEN
      MATCH_MP_TAC CONNECTED_SPHERE THEN REWRITE_TAC[DIMINDEX_3] THEN ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; CONNECTED_IN_SUBTOPOLOGY] THEN
  SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    can (find_term ((=) `sphere(vec 0:real^3,&1)`)) (concl th))) THEN
  REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `basis 1:real^3` THEN
  SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH]);;

let P2BKL_MAIN_LEAF = prove
 (`!top atlas (gs:A->real^3^3) (X:A->real^3) (psi:real^3->A) h A0.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas gs /\
     (!x. x IN topspace top ==> X x dot (gs x ** X x) = &1) /\
     mfd_param top atlas (annulus (exp(--(&2))) (exp(&2))) psi /\
     p2bkg_prim atlas gs X (IMAGE psi (annulus (exp(--(&2))) (exp(&2)))) h /\
     &0 < A0 /\ p2bx46_shell (\z. h(psi z)) A0 (A0 / &10)
     ==> ?V0 u0 psi1 psi1'.
            open_in top V0 /\ p2bkg_prim atlas gs X V0 h /\ lvs_regular atlas V0 h u0 /\
            V0 SUBSET IMAGE psi (annulus (exp(--(&2))) (exp(&2))) /\
            mfd_diffeo (subtopology euclidean (sphere(vec 0:real^3,&1))) sphere2_atlas
                       (sphere(vec 0,&1)) (subtopology top (lvs_set V0 h u0))
                       (lvs_atlas top atlas V0 h u0) (lvs_set V0 h u0) psi1 psi1' /\
            compact_in top (lvs_set V0 h u0) /\ connected_in top (lvs_set V0 h u0) /\
            ~(lvs_set V0 h u0 = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  STRIP_ASSUME_TAC P2BX46_E_PI_BOUNDS THEN
  ABBREV_TAC `S2 = annulus (exp(--(&2))) (exp(&2)):real^3->bool` THEN
  ABBREV_TAC `Sh = annulus (inv(exp(&1))) (exp(&1)):real^3->bool` THEN
  SUBGOAL_THEN `exp(--(&2)) < inv(exp(&1)) /\ exp(&1) < exp(&2)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_NEG; REAL_EXP_MONO_LT] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `open (S2:real^3->bool) /\ open (Sh:real^3->bool) /\ Sh SUBSET S2 /\
                (!z:real^3. inv(exp(&1)) <= norm z /\ norm z <= exp(&1) ==> z IN S2)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["S2"; "Sh"] THEN REWRITE_TAC[P2BPC_ANNULUS_OPEN] THEN
    REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN CONJ_TAC THEN GEN_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `V0 = IMAGE (psi:real^3->A) Sh` THEN
  SUBGOAL_THEN `open_in top (V0:A->bool) /\ V0 SUBSET IMAGE (psi:real^3->A) S2 /\
                V0 SUBSET topspace top /\ open_in top (IMAGE (psi:real^3->A) S2)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "V0" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `S2:real^3->bool`] THEN
      ASM_REWRITE_TAC[];
      ASM SET_TAC[];
      MATCH_MP_TAC MFD_PARAM_IMAGE_SUBSET THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `S2:real^3->bool`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `S2:real^3->bool`] THEN
      ASM_REWRITE_TAC[SUBSET_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2bkg_prim atlas (gs:A->real^3^3) (X:A->real^3) V0 (h:A->real)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BKL_PRIM_SUBSET THEN
    EXISTS_TAC `IMAGE (psi:real^3->A) S2` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `u0 = (h:A->real)((psi:real^3->A)(basis 1))` THEN
  SUBGOAL_THEN `lvs_regular atlas V0 (h:A->real) u0` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BKG_LEVEL_REGULAR THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `gs:A->real^3^3`; `X:A->real^3`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `p2bkg_prim atlas (gs:A->real^3^3) (X:A->real^3) V0 (h:A->real)` THEN
    REWRITE_TAC[p2bkg_prim] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `psi:real^3->A`;
                 `S2:real^3->bool`; `h:A->real`; `\z:real^3. (h:A->real)((psi:real^3->A) z)`;
                 `A0:real`; `basis 1:real^3`] P2BKL_SHELL_LEVEL_SPHERE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN
    MATCH_MP_TAC P2BKL_SHELL_FN_SMOOTH THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `IMAGE (psi:real^3->A) S2`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN
    UNDISCH_TAC `p2bkg_prim atlas (gs:A->real^3^3) (X:A->real^3) (IMAGE (psi:real^3->A) S2)
                            (h:A->real)` THEN
    SIMP_TAC[p2bkg_prim];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi1:real^3->A` (X_CHOOSE_TAC `psi1':A->real^3`)) THEN
  MAP_EVERY EXISTS_TAC [`V0:A->bool`; `u0:real`; `psi1:real^3->A`; `psi1':A->real^3`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2BKL_SPHERE_IMAGE_FACTS THEN
  MAP_EVERY EXISTS_TAC [`lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) V0 (h:A->real) u0`;
                        `psi1:real^3->A`; `psi1':A->real^3`] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[lvs_set] THEN ASM SET_TAC[]);;

let P2BKL_LEAF_PINCH = prove
 (`!top atlas (gs:A->real^3^3) (g1:A->real^3^3) (X:A->real^3) V0 h0 u0 V1 h1 c1 e.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas gs /\
     mfd_complete (top,atlas) gs /\ p2b_parallel_on atlas gs (topspace top) X /\
     (!x. x IN topspace top ==> X x dot (gs x ** X x) = &1) /\
     riemannian_metric atlas g1 /\ p2b_parallel_on atlas g1 (topspace top) X /\
     open_in top V0 /\ p2bkg_prim atlas gs X V0 h0 /\ connected_in top (lvs_set V0 h0 u0) /\
     (!x. x IN topspace top
          ==> ?r y. y IN lvs_set V0 h0 u0 /\ p2bkf_phi (top,atlas) gs X r y = x) /\
     open_in top V1 /\ p2bkg_prim atlas gs X V1 h1 /\ closed_in top (lvs_set V1 h1 c1) /\
     ~(lvs_set V1 h1 c1 = {}) /\
     (!y1 y2. y1 IN V1 /\ y2 IN V1
              ==> mfd_scalar atlas g1 y1 <= (&1 + e) * mfd_scalar atlas g1 y2)
     ==> !x y. x IN lvs_set V0 h0 u0 /\ y IN lvs_set V0 h0 u0
               ==> mfd_scalar atlas g1 x <= (&1 + e) * mfd_scalar atlas g1 y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `z1:A` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  SUBGOAL_THEN `(z1:A) IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `(z1:A) IN lvs_set V1 h1 c1` THEN REWRITE_TAC[lvs_set; IN_ELIM_THM] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(z1:A) IN topspace top`) o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2bkf_phi")) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `y0:A` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `!y. y IN lvs_set V0 h0 u0
        ==> p2bkf_phi (top,atlas) (gs:A->real^3^3) (X:A->real^3) r y IN lvs_set V1 h1 c1`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BKG_LEAF_TRANSPORT THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `y0:A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN topspace top
        ==> mfd_scalar atlas (g1:A->real^3^3) x =
            mfd_scalar atlas g1 (p2bkf_phi (top,atlas) (gs:A->real^3^3) (X:A->real^3) r x)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN MATCH_MP_TAC MFD_ISOMETRY_SCALAR THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `top:A topology`;
                          `p2bkf_phi (top,atlas) (gs:A->real^3^3) (X:A->real^3) (--r)`] THEN
    ASM_REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC P2BKF_PHI_ISOMETRY THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top /\ (y:A) IN topspace top` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:A) IN lvs_set V0 h0 u0` THEN UNDISCH_TAC `(y:A) IN lvs_set V0 h0 u0` THEN
    REWRITE_TAC[lvs_set; IN_ELIM_THM] THEN ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  SUBGOAL_THEN `lvs_set V1 (h1:A->real) c1 SUBSET V1` MP_TAC THENL
   [REWRITE_TAC[lvs_set] THEN SET_TAC[]; ALL_TAC] THEN
  ASM SET_TAC[]);;


(* P2BKL.L11 The leaf data: from the asymptotic-soliton slice limit of a    *)
(* split ancient flow (the data of P2BKS_SHELLS_FROM_LIMIT), a compact leaf *)
(* L of the reference metric g s1 which is a smooth 2-sphere, whose induced *)
(* metrics form a 2-d Ricci flow with R_L = R > 0, pinched at arbitrarily   *)
(* negative times, and such that (y,r) |-> Phi_r(y) is a bijection L x R -> *)
(* M.                                                                       *)

let P2BKL_SHELL2_LEAF = prove
 (`!top atlas (psi:real^3->A) (h:A->real) kappa delta c0 (gs:A->real^3^3) (X:A->real^3).
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     mfd_param top atlas (annulus (exp(--(&2))) (exp(&2))) psi /\
     p2bkg_prim atlas gs X (IMAGE psi (annulus (exp(--(&2))) (exp(&2)))) h /\
     &0 < kappa /\ &0 <= delta /\ delta < kappa * &2 /\
     (!y. y IN annulus (exp(--(&2))) (exp(&2))
          ==> abs((h(psi y) - c0) - kappa * log(norm y)) <= delta)
     ==> open_in top (IMAGE psi (annulus (exp(--(&2))) (exp(&2)))) /\
         closed_in top (lvs_set (IMAGE psi (annulus (exp(--(&2))) (exp(&2)))) h c0) /\
         ~(lvs_set (IMAGE psi (annulus (exp(--(&2))) (exp(&2)))) h c0 = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_smooth_on (atlas:((A->bool)#(A->real^3))->bool)
                              (IMAGE (psi:real^3->A) (annulus (exp(--(&2))) (exp(&2))))
                              (\x. lift((h:A->real) x))` ASSUME_TAC THENL
   [UNDISCH_TAC `p2bkg_prim atlas (gs:A->real^3^3) (X:A->real^3)
                   (IMAGE (psi:real^3->A) (annulus (exp(--(&2))) (exp(&2)))) h` THEN
    SIMP_TAC[p2bkg_prim];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`;
                          `annulus (exp(--(&2))) (exp(&2)):real^3->bool`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL; P2BPC_ANNULUS_OPEN];
    MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `psi:real^3->A`;
                   `h:A->real`; `&2`; `kappa:real`; `delta:real`; `c0:real`] P2BKG_LEAF_COMPACT) THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC P2BKG_SHELL_LEVEL_NONEMPTY THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `kappa:real`; `delta:real`] THEN
    ASM_REWRITE_TAC[]]);;

let P2BKL_LEAF_FLOW_GS = prove
 (`!top atlas (g:real->A->real^3^3) (gs:A->real^3^3) b (X:A->real^3) V h u.
     (!a. a < b ==> ricci_flow_on (top,atlas) a b g) /\ smooth_manifold_atlas top atlas /\
     open_in top V /\ p2bkg_prim atlas gs X V h /\
     (!s. s < b ==> p2b_parallel_on atlas (g s) (topspace top) X) /\
     (!s y. s < b /\ y IN topspace top ==> g s y ** X y = gs y ** X y) /\
     (!y. y IN topspace top ==> X y dot (gs y ** X y) = &1)
     ==> (!s. s < b ==> p2bkg_prim atlas (g s) X V h) /\
         (!a. a < b ==> ricci_flow_on (subtopology top (lvs_set V h u),lvs_atlas top atlas V h u)
                                      a b (\t. lvs_metric top atlas (g t) V h u)) /\
         (!t y. t < b /\ y IN lvs_set V h u
                ==> mfd_scalar (lvs_atlas top atlas V h u) (lvs_metric top atlas (g t) V h u) y =
                    mfd_scalar atlas (g t) y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s. s < b ==> p2bkg_prim atlas ((g:real->A->real^3^3) s) (X:A->real^3) V h`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN MATCH_MP_TAC P2BKS_PRIM_INVARIANT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `gs:A->real^3^3`] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BKL_LEAF_FLOW_ALL THEN EXISTS_TAC `X:A->real^3` THEN
  ASM_SIMP_TAC[]);;


(* P2BKL.L12 Main theorem: the leaf data.                                   *)

let P2BKL_LEAF_DATA = prove
 (`!V x t Q top atlas (g0:B->real^3^3) xl W (phi:num->B->A) (top1:A topology) atlas1
    (g:real->A->real^3^3) (gs:A->real^3^3) b (X:A->real^3) sub (Y:B->real^3) (p:real^3->B) lam.
     p2c_slice_limit_with V x t Q (top,atlas) g0 xl W phi /\
     (!n. rfs_vtop (V n) (t n) = top1 /\ rfs_vatlas (V n) (t n) = atlas1 /\
          rfs_vmetric (V n) (t n) = g (t n) /\ t n < b) /\
     hausdorff_space top1 /\ connected_space top1 /\ smooth_manifold_atlas top1 atlas1 /\
     (!a. a < b ==> ricci_flow_on (top1,atlas1) a b g) /\
     riemannian_metric atlas1 gs /\ mfd_complete (top1,atlas1) gs /\
     p2b_parallel_on atlas1 gs (topspace top1) X /\
     (!y. y IN topspace top1 ==> X y dot (gs y ** X y) = &1) /\
     (!s. s < b ==> p2b_parallel_on atlas1 (g s) (topspace top1) X) /\
     (!s y. s < b /\ y IN topspace top1 ==> g s y ** X y = gs y ** X y) /\
     (!s y. s < b /\ y IN topspace top1 ==> &0 < mfd_scalar atlas1 (g s) y) /\
     (!e. &0 < e ==> ?n0. !n. n0 <= n ==> Q n < e) /\
     (!Tm. ?n0. !n. n0 <= n ==> t n < Tm) /\
     p3_subseq sub /\
     (!y. y IN topspace top ==> Y y dot (g0 y ** Y y) = &1) /\
     (!K e. compact_in top K /\ &0 < e
            ==> ?n0. !n. n0 <= n
                         ==> !y. y IN K
                                 ==> ?z. mfd_differential atlas atlas1 (phi (sub n)) y z =
                                         X (phi (sub n) y) /\
                                         (inv(sqrt(Q(sub n))) % z - Y y) dot
                                         (g0 y ** (inv(sqrt(Q(sub n))) % z - Y y)) < e) /\
     &0 < lam /\
     (!y. ~(y = vec 0) ==> ?r. &0 < r /\ r < norm y /\ mfd_param top atlas (ball(y,r)) p) /\
     (!y z. ~(y = vec 0) /\ ~(z = vec 0) ==> (p y = p z <=> z = y)) /\
     (!y. ~(y = vec 0) ==> rfs_pullback atlas p g0 y = lam %% cylinder_flow (&0) y) /\
     (!y. ~(y = vec 0)
          ==> Y(p y) = mfd_differential (open_set_atlas {z:real^3 | ~(z = vec 0)}) atlas p y
                                        (inv(sqrt(&2 * lam)) % y))
     ==> ?V0 h0 u0 psi1 psi1'.
            open_in top1 V0 /\ p2bkg_prim atlas1 gs X V0 h0 /\
            (!s. s < b ==> p2bkg_prim atlas1 (g s) X V0 h0) /\
            compact_in top1 (lvs_set V0 h0 u0) /\ connected_in top1 (lvs_set V0 h0 u0) /\
            mfd_diffeo (subtopology euclidean (sphere(vec 0:real^3,&1))) sphere2_atlas
                       (sphere(vec 0,&1)) (subtopology top1 (lvs_set V0 h0 u0))
                       (lvs_atlas top1 atlas1 V0 h0 u0)
                       (topspace (subtopology top1 (lvs_set V0 h0 u0))) psi1 psi1' /\
            hausdorff_space (subtopology top1 (lvs_set V0 h0 u0)) /\
            (!a. a < b ==> ricci_flow_on (subtopology top1 (lvs_set V0 h0 u0),
                                          lvs_atlas top1 atlas1 V0 h0 u0) a b
                                         (\t. lvs_metric top1 atlas1 (g t) V0 h0 u0)) /\
            (!t y. t < b /\ y IN lvs_set V0 h0 u0
                   ==> mfd_scalar (lvs_atlas top1 atlas1 V0 h0 u0)
                                  (lvs_metric top1 atlas1 (g t) V0 h0 u0) y =
                       mfd_scalar atlas1 (g t) y) /\
            (!t y. t < b /\ y IN topspace (subtopology top1 (lvs_set V0 h0 u0))
                   ==> &0 < mfd_scalar (lvs_atlas top1 atlas1 V0 h0 u0)
                                       (lvs_metric top1 atlas1 (g t) V0 h0 u0) y) /\
            (!e Tm. &0 < e
                    ==> ?t. t < Tm /\ t < b /\
                            !y z. y IN topspace (subtopology top1 (lvs_set V0 h0 u0)) /\
                                  z IN topspace (subtopology top1 (lvs_set V0 h0 u0))
                                  ==> mfd_scalar (lvs_atlas top1 atlas1 V0 h0 u0)
                                                 (lvs_metric top1 atlas1 (g t) V0 h0 u0) y <=
                                      (&1 + e) *
                                      mfd_scalar (lvs_atlas top1 atlas1 V0 h0 u0)
                                                 (lvs_metric top1 atlas1 (g t) V0 h0 u0) z) /\
            (!y. y IN topspace top1
                 ==> ?r z. z IN lvs_set V0 h0 u0 /\ p2bkf_phi (top1,atlas1) gs X r z = y) /\
            (!z z' r r'. z IN lvs_set V0 h0 u0 /\ z' IN lvs_set V0 h0 u0 /\
                         p2bkf_phi (top1,atlas1) gs X r z = p2bkf_phi (top1,atlas1) gs X r' z'
                         ==> z = z' /\ r = r')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* the pinched shells *)
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`; `x:num->A`; `t:num->real`; `Q:num->real`;
                 `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
                 `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `top1:A topology`;
                 `atlas1:((A->bool)#(A->real^3))->bool`; `gs:A->real^3^3`; `X:A->real^3`;
                 `sub:num->num`; `Y:B->real^3`; `p:real^3->B`; `lam:real`]
                P2BKL_SHELLS_PINCHED) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    X_GEN_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(t:num->real) n < b` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2BKL_RF_RIEMANNIAN THEN
      MAP_EVERY EXISTS_TAC [`top1:A topology`; `b:real`] THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[];
      ASM_SIMP_TAC[]];
    DISCH_THEN(LABEL_TAC "sp")] THEN
  (* the main leaf *)
  USE_THEN "sp" (MP_TAC o SPECL [`&0`; `&1`; `&0`]) THEN REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (X_CHOOSE_THEN `psi0:real^3->A` (X_CHOOSE_THEN `hh:A->real`
    (X_CHOOSE_THEN `kappa0:real` (X_CHOOSE_THEN `delta0:real` (X_CHOOSE_THEN `cc0:real`
    (X_CHOOSE_THEN `A00:real` STRIP_ASSUME_TAC))))))) THEN
  MP_TAC(ISPECL [`top1:A topology`; `atlas1:((A->bool)#(A->real^3))->bool`; `gs:A->real^3^3`;
                 `X:A->real^3`; `psi0:real^3->A`; `hh:A->real`; `A00:real`] P2BKL_MAIN_LEAF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V0:A->bool` (X_CHOOSE_THEN `u0:real` (X_CHOOSE_THEN `psi1:real^3->A`
    (X_CHOOSE_THEN `psi1':A->real^3` STRIP_ASSUME_TAC)))) THEN
  (* thick leaves and the orbit bijection *)
  MP_TAC(ISPECL [`top1:A topology`; `atlas1:((A->bool)#(A->real^3))->bool`; `gs:A->real^3^3`;
                 `X:A->real^3`] P2BKG_SHELL_THICK_FAMILY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `tk:real` THEN
    USE_THEN "sp" (MP_TAC o SPECL [`tk:real`; `&1`; `&0`]) THEN REWRITE_TAC[REAL_LT_01] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `psi:real^3->A` (X_CHOOSE_THEN `h:A->real`
      (X_CHOOSE_THEN `kappa:real` (X_CHOOSE_THEN `delta:real` (X_CHOOSE_THEN `c0:real`
      (X_CHOOSE_THEN `A0:real` STRIP_ASSUME_TAC))))))) THEN
    MAP_EVERY EXISTS_TAC [`psi:real^3->A`; `h:A->real`; `&2`; `kappa:real`; `delta:real`;
                          `c0:real`] THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(LABEL_TAC "thick")] THEN
  MP_TAC(ISPECL [`top1:A topology`; `atlas1:((A->bool)#(A->real^3))->bool`; `gs:A->real^3^3`;
                 `X:A->real^3`; `V0:A->bool`; `hh:A->real`; `u0:real`] P2BKG_ORBIT_BIJECTIVE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "surj") (LABEL_TAC "inj")) THEN
  (* the leaf flow *)
  MP_TAC(ISPECL [`top1:A topology`; `atlas1:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `gs:A->real^3^3`; `b:real`; `X:A->real^3`; `V0:A->bool`; `hh:A->real`;
                 `u0:real`] P2BKL_LEAF_FLOW_GS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "pt") (CONJUNCTS_THEN2 (LABEL_TAC "rf") (LABEL_TAC "rl"))) THEN
  SUBGOAL_THEN `lvs_set V0 (hh:A->real) u0 SUBSET topspace top1` ASSUME_TAC THENL
   [REWRITE_TAC[lvs_set] THEN
    MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top1 (V0:A->bool)`)) THEN SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`V0:A->bool`; `hh:A->real`; `u0:real`; `psi1:real^3->A`;
                        `psi1':A->real^3`] THEN
  REWRITE_TAC[MP (ISPECL [`top1:A topology`; `V0:A->bool`; `hh:A->real`; `u0:real`] LVS_TOPSPACE)
                 (ASSUME `open_in top1 (V0:A->bool)`)] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `hausdorff_space (subtopology top1 (lvs_set V0 (hh:A->real) u0))`
  (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC LVS_HAUSDORFF THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
    USE_THEN "rl" (fun th -> REWRITE_TAC[MATCH_MP th (CONJ (ASSUME `s < b:real`)
                                       (ASSUME `(y:A) IN lvs_set V0 hh u0`))]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:A) IN lvs_set V0 hh u0` THEN
    UNDISCH_TAC `lvs_set V0 (hh:A->real) u0 SUBSET topspace top1` THEN SET_TAC[];
    ALL_TAC] THEN
  (* pinching *)
  MAP_EVERY X_GEN_TAC [`e:real`; `Tm:real`] THEN DISCH_TAC THEN
  USE_THEN "sp" (MP_TAC o C MATCH_MP (ASSUME `&0 < e`) o SPECL [`&0`; `e:real`; `min Tm b`]) THEN
  REWRITE_TAC[REAL_LT_MIN] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `psi:real^3->A` (X_CHOOSE_THEN `h:A->real`
    (X_CHOOSE_THEN `kappa:real` (X_CHOOSE_THEN `delta:real` (X_CHOOSE_THEN `c0:real`
    (X_CHOOSE_THEN `A0:real` STRIP_ASSUME_TAC))))))) THEN
  EXISTS_TAC `(t:num->real) k` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`y:A`; `z:A`] THEN STRIP_TAC THEN
  USE_THEN "rl" (fun th -> REWRITE_TAC[MATCH_MP th (CONJ (ASSUME `(t:num->real) k < b`)
                                     (ASSUME `(y:A) IN lvs_set V0 hh u0`))]) THEN
  USE_THEN "rl" (fun th -> REWRITE_TAC[MATCH_MP th (CONJ (ASSUME `(t:num->real) k < b`)
                                     (ASSUME `(z:A) IN lvs_set V0 hh u0`))]) THEN
  MP_TAC(ISPECL [`top1:A topology`; `atlas1:((A->bool)#(A->real^3))->bool`; `psi:real^3->A`;
                 `h:A->real`; `kappa:real`; `delta:real`; `c0:real`; `gs:A->real^3^3`;
                 `X:A->real^3`] P2BKL_SHELL2_LEAF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas1 ((g:real->A->real^3^3) ((t:num->real) k)) /\
                p2b_parallel_on atlas1 (g (t k)) (topspace top1) (X:A->real^3)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC P2BKL_RF_RIEMANNIAN THEN
      MAP_EVERY EXISTS_TAC [`top1:A topology`; `b:real`] THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top1:A topology`; `atlas1:((A->bool)#(A->real^3))->bool`; `gs:A->real^3^3`;
                 `(g:real->A->real^3^3) ((t:num->real) k)`; `X:A->real^3`; `V0:A->bool`;
                 `hh:A->real`; `u0:real`;
                 `IMAGE (psi:real^3->A) (annulus (exp(--(&2))) (exp(&2)))`; `h:A->real`;
                 `c0:real`; `e:real`] P2BKL_LEAF_PINCH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC
     `!y1 y2. y1 IN IMAGE (psi:real^3->A) (annulus (exp(--(&2))) (exp(&2))) /\
              y2 IN IMAGE psi (annulus (exp(--(&2))) (exp(&2)))
              ==> mfd_scalar atlas1
                    (rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                         (real->A->real^3^3)) k) (t k)) y1 <=
                  (&1 + e) * mfd_scalar atlas1 (rfs_vmetric (V k) (t k)) y2` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;


(* P2BKL.L13 With P2B_REQ_S2_ENTROPY_STATEMENT: the leaf flow has spatially *)
(* constant scalar curvature at every time, so R is constant on L at every  *)
(* time.                                                                    *)

let P2BKL_LEAF_ROUND = prove
 (`!(w:A->bool) V x t Q top atlas (g0:B->real^3^3) xl W (phi:num->B->A) (top1:A topology)
    atlas1 (g:real->A->real^3^3) (gs:A->real^3^3) b (X:A->real^3) sub (Y:B->real^3)
    (p:real^3->B) lam.
     P2B_REQ_S2_ENTROPY_STATEMENT w /\
     p2c_slice_limit_with V x t Q (top,atlas) g0 xl W phi /\
     (!n. rfs_vtop (V n) (t n) = top1 /\ rfs_vatlas (V n) (t n) = atlas1 /\
          rfs_vmetric (V n) (t n) = g (t n) /\ t n < b) /\
     hausdorff_space top1 /\ connected_space top1 /\ smooth_manifold_atlas top1 atlas1 /\
     (!a. a < b ==> ricci_flow_on (top1,atlas1) a b g) /\
     riemannian_metric atlas1 gs /\ mfd_complete (top1,atlas1) gs /\
     p2b_parallel_on atlas1 gs (topspace top1) X /\
     (!y. y IN topspace top1 ==> X y dot (gs y ** X y) = &1) /\
     (!s. s < b ==> p2b_parallel_on atlas1 (g s) (topspace top1) X) /\
     (!s y. s < b /\ y IN topspace top1 ==> g s y ** X y = gs y ** X y) /\
     (!s y. s < b /\ y IN topspace top1 ==> &0 < mfd_scalar atlas1 (g s) y) /\
     (!e. &0 < e ==> ?n0. !n. n0 <= n ==> Q n < e) /\
     (!Tm. ?n0. !n. n0 <= n ==> t n < Tm) /\
     p3_subseq sub /\
     (!y. y IN topspace top ==> Y y dot (g0 y ** Y y) = &1) /\
     (!K e. compact_in top K /\ &0 < e
            ==> ?n0. !n. n0 <= n
                         ==> !y. y IN K
                                 ==> ?z. mfd_differential atlas atlas1 (phi (sub n)) y z =
                                         X (phi (sub n) y) /\
                                         (inv(sqrt(Q(sub n))) % z - Y y) dot
                                         (g0 y ** (inv(sqrt(Q(sub n))) % z - Y y)) < e) /\
     &0 < lam /\
     (!y. ~(y = vec 0) ==> ?r. &0 < r /\ r < norm y /\ mfd_param top atlas (ball(y,r)) p) /\
     (!y z. ~(y = vec 0) /\ ~(z = vec 0) ==> (p y = p z <=> z = y)) /\
     (!y. ~(y = vec 0) ==> rfs_pullback atlas p g0 y = lam %% cylinder_flow (&0) y) /\
     (!y. ~(y = vec 0)
          ==> Y(p y) = mfd_differential (open_set_atlas {z:real^3 | ~(z = vec 0)}) atlas p y
                                        (inv(sqrt(&2 * lam)) % y))
     ==> ?V0 h0 u0 psi1 psi1'.
            open_in top1 V0 /\ p2bkg_prim atlas1 gs X V0 h0 /\
            (!s. s < b ==> p2bkg_prim atlas1 (g s) X V0 h0) /\
            compact_in top1 (lvs_set V0 h0 u0) /\ connected_in top1 (lvs_set V0 h0 u0) /\
            mfd_diffeo (subtopology euclidean (sphere(vec 0:real^3,&1))) sphere2_atlas
                       (sphere(vec 0,&1)) (subtopology top1 (lvs_set V0 h0 u0))
                       (lvs_atlas top1 atlas1 V0 h0 u0)
                       (topspace (subtopology top1 (lvs_set V0 h0 u0))) psi1 psi1' /\
            (!a. a < b ==> ricci_flow_on (subtopology top1 (lvs_set V0 h0 u0),
                                          lvs_atlas top1 atlas1 V0 h0 u0) a b
                                         (\t. lvs_metric top1 atlas1 (g t) V0 h0 u0)) /\
            (!t y. t < b /\ y IN lvs_set V0 h0 u0
                   ==> mfd_scalar (lvs_atlas top1 atlas1 V0 h0 u0)
                                  (lvs_metric top1 atlas1 (g t) V0 h0 u0) y =
                       mfd_scalar atlas1 (g t) y) /\
            (!t y z. t < b /\ y IN lvs_set V0 h0 u0 /\ z IN lvs_set V0 h0 u0
                     ==> mfd_scalar atlas1 (g t) y = mfd_scalar atlas1 (g t) z) /\
            (!y. y IN topspace top1
                 ==> ?r z. z IN lvs_set V0 h0 u0 /\ p2bkf_phi (top1,atlas1) gs X r z = y) /\
            (!z z' r r'. z IN lvs_set V0 h0 u0 /\ z' IN lvs_set V0 h0 u0 /\
                         p2bkf_phi (top1,atlas1) gs X r z = p2bkf_phi (top1,atlas1) gs X r' z'
                         ==> z = z' /\ r = r')`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ent") MP_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP P2BKL_LEAF_DATA) THEN
  DISCH_THEN(X_CHOOSE_THEN `V0:A->bool` (X_CHOOSE_THEN `h0:A->real` (X_CHOOSE_THEN `u0:real`
    (X_CHOOSE_THEN `psi1:real^3->A` (X_CHOOSE_THEN `psi1':A->real^3` STRIP_ASSUME_TAC))))) THEN
  MAP_EVERY EXISTS_TAC [`V0:A->bool`; `h0:A->real`; `u0:real`; `psi1:real^3->A`;
                        `psi1':A->real^3`] THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "ent" (MP_TAC o
    SPECL [`subtopology top1 (lvs_set V0 (h0:A->real) u0)`;
           `lvs_atlas top1 (atlas1:((A->bool)#(A->real^3))->bool) V0 (h0:A->real) u0`;
           `\t. lvs_metric top1 (atlas1:((A->bool)#(A->real^3))->bool)
                           ((g:real->A->real^3^3) t) V0 (h0:A->real) u0`;
           `b:real`; `psi1:real^3->A`; `psi1':A->real^3`] o
    GEN_REWRITE_RULE I [P2B_REQ_S2_ENTROPY_STATEMENT]) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MP (ISPECL [`top1:A topology`; `V0:A->bool`; `h0:A->real`; `u0:real`] LVS_TOPSPACE)
                 (ASSUME `open_in top1 (V0:A->bool)`)] THEN
  DISCH_THEN(LABEL_TAC "const") THEN MAP_EVERY X_GEN_TAC [`s:real`; `y:A`; `z:A`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `mfd_scalar (lvs_atlas top1 atlas1 V0 h0 u0)
               (lvs_metric top1 atlas1 ((g:real->A->real^3^3) s) V0 (h0:A->real) u0) y =
    mfd_scalar atlas1 (g s) y /\
    mfd_scalar (lvs_atlas top1 atlas1 V0 h0 u0) (lvs_metric top1 atlas1 (g s) V0 h0 u0) z =
    mfd_scalar atlas1 (g s) z`
  (fun th -> REWRITE_TAC[GSYM th]) THENL
   [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "const" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;


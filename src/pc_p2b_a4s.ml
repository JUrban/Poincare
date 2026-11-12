(* ========================================================================= *)
(* Unit pc_p2b_a4s (Part 2B): the statement A4 of Part 2C in slice form from *)
(* Prop 2.19 (sep).                                                          *)
(*   P2B_NONNEG_BOUNDED_SLICE_ROUTE |- !w. P2_PROP_2_19_SEP_STATEMENT w     *)
(*     ==> P2C_REQ_NONNEG_BOUNDED_SLICE_STATEMENT w                          *)
(* Route (MT p. 243 with the separating Prop 2.19): on a complete connected  *)
(* slice with sec >= 0 and separating neck spheres, the scalar curvature at  *)
(* neck centres is at most B (P2_PROP_2_19_SEP); a point with R > 4 has a    *)
(* canonical neighbourhood: a neck centred at it (R <= B), a cap (its own    *)
(* neck centre z lies in the cap and R(x) < C R(z) by the ratio bound of     *)
(* rfs_cap, P2BA4_CAP_FACTS), or a C-component or eps-round component, which *)
(* makes the connected slice compact, where R is bounded by continuity       *)
(* (MFD_SCALAR_CONTINUOUS).  Then abs Rm <= R / 2                            *)
(* (P2BX0_RM_NORM_LE_HALF_SCALAR).  The FIX form follows with                *)
(* P2B_NONNEG_BOUNDED_SLICE_IMP_FIX of pc_p2b_defs.                          *)
(* ========================================================================= *)

needs "src/pc_p2b_kreq.ml";;
needs "src/pc_apx_scal.ml";;
needs "src/pc_p2b_rmhalf.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The slice form of A4 from Prop 2.19 (sep).                                *)
(* ========================================================================= *)

(* A cap contains the centre of its neck, and its points satisfy the        *)
(* curvature ratio bound R(y2) < C R(y1).                                    *)

let P2BA4_CAP_FACTS = prove
 (`!top atlas (g:B->real^3^3) C eps U Y x.
     rfs_cap (top,atlas) g C eps U Y /\ x IN Y
     ==> x IN U /\ (?z e. rfs_neck (top,atlas) g eps z e /\ z IN U) /\
         (!y1 y2. y1 IN U /\ y2 IN U
                  ==> &0 < mfd_scalar atlas g y1 /\
                      mfd_scalar atlas g y2 < C * mfd_scalar atlas g y1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_cap; rfs_sup_lt] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "alt") (CONJUNCTS_THEN2 (LABEL_TAC "pos")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "ratio") ASSUME_TAC))))))
    ASSUME_TAC) THEN
  SUBGOAL_THEN `!z e. rfs_neck (top,atlas) (g:B->real^3^3) eps z e
                      ==> z IN IMAGE e (rfs_neck_dom eps)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
    UNDISCH_TAC `(z:B) IN IMAGE (e:real^3->B) (sphere(vec 0,&1))` THEN
    MATCH_MP_TAC(SET_RULE `(s:real^3->bool) SUBSET t ==> (x:B) IN IMAGE (f:real^3->B) s ==> x IN IMAGE f t`) THEN
    REWRITE_TAC[SUBSET; IN_SPHERE_0; rfs_neck_dom; annulus; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `&0 < inv(sqrt(&2) * eps)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `exp(--a) < exp(&0) /\ exp(&0) = &1 ==> exp(--a) < &1`) THEN
      REWRITE_TAC[REAL_EXP_0; REAL_EXP_MONO_LT] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `exp(&0) < exp a /\ exp(&0) = &1 ==> &1 < exp a`) THEN
      REWRITE_TAC[REAL_EXP_0; REAL_EXP_MONO_LT] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "alt" (DISJ_CASES_THEN (X_CHOOSE_THEN `b:real^3->B` STRIP_ASSUME_TAC)) THEN
    REPEAT(FIRST_X_ASSUM(CHOOSE_THEN STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
    UNDISCH_TAC `(x:B) IN Y` THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `ball(vec 0:real^3,&1) SUBSET ball(vec 0,&2)` MP_TAC THENL
       [MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC; ALL_TAC];
      SUBGOAL_THEN `annulus (&1 / &2) (&2) SUBSET (annulus (&1 / &4) (&4):real^3->bool)`
      MP_TAC THENL
       [REWRITE_TAC[annulus; SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC]] THEN
    MATCH_MP_TAC(SET_RULE `IMAGE (f:real^3->B) t SUBSET u
                           ==> s SUBSET t ==> (x:B) IN IMAGE f s ==> x IN u`) THEN
    FIRST_ASSUM ACCEPT_TAC;
    USE_THEN "alt" (DISJ_CASES_THEN (X_CHOOSE_THEN `b:real^3->B` STRIP_ASSUME_TAC)) THEN
    REPEAT(FIRST_X_ASSUM(CHOOSE_THEN STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
    MAP_EVERY EXISTS_TAC [`z:B`; `e:real^3->B`] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`z:B`; `e:real^3->B`] o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> t = `rfs_neck_dom`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    MAP_EVERY X_GEN_TAC [`y1:B`; `y2:B`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < mfd_scalar atlas (g:B->real^3^3) y1` ASSUME_TAC THENL
     [USE_THEN "pos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "ratio" (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `mfd_scalar atlas (g:B->real^3^3) y2 / mfd_scalar atlas g y1` o
      check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "real_div")) (concl th))) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN MAP_EVERY EXISTS_TAC [`y2:B`; `y1:B`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    MATCH_MP_TAC(REAL_ARITH `d * r < C * r ==> x <= d * r ==> x < C * r`) THEN
    MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[]]);;

(* The route: Prop 2.19 (sep) bounds R at neck centres; caps through their *)
(* necks and the ratio bound; component alternatives make the space compact. *)

let P2B_NONNEG_BOUNDED_SLICE_ROUTE = prove
 (`!w:B->bool. P2_PROP_2_19_SEP_STATEMENT w ==> P2C_REQ_NONNEG_BOUNDED_SLICE_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2_PROP_2_19_SEP_STATEMENT; P2C_REQ_NONNEG_BOUNDED_SLICE_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sep"))) THEN
  EXISTS_TAC `eps1:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `top:B topology`;
                       `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "can"))))))))))) THEN
  USE_THEN "sep" (MP_TAC o SPECL [`eps:real`; `top:B topology`;
                                  `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` (LABEL_TAC "nb")) THEN
  SUBGOAL_THEN `?M. !x. x IN topspace top ==> mfd_scalar atlas (g:B->real^3^3) x <= M`
  (X_CHOOSE_THEN `M:real` (LABEL_TAC "M")) THENL
   [ASM_CASES_TAC `compact_space (top:B topology)` THENL
     [MP_TAC(ISPECL [`top:B topology`; `euclideanreal`; `mfd_scalar atlas (g:B->real^3^3)`;
                     `topspace top:B->bool`] IMAGE_COMPACT_IN) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[GSYM compact_space] THEN MATCH_MP_TAC MFD_SCALAR_CONTINUOUS THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[COMPACT_IN_EUCLIDEANREAL; MBOUNDED_REAL_EUCLIDEAN_METRIC; real_bounded;
                  FORALL_IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_TAC `M0:real` o CONJUNCT1) THEN EXISTS_TAC `M0:real` THEN
      ASM_MESON_TAC[REAL_ARITH `abs x <= b ==> x <= b`];
      ALL_TAC] THEN
    EXISTS_TAC `max (&4) (C * abs B)` THEN X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    ASM_CASES_TAC `mfd_scalar atlas (g:B->real^3^3) x <= &4` THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "can" (MP_TAC o SPEC `x:B`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `U:B->bool` MP_TAC) THEN REWRITE_TAC[rfs_canonical_nbhd] THEN
    STRIP_TAC THENL
     [USE_THEN "nb" (MP_TAC o SPECL [`x:B`; `e:real^3->B`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `abs B <= C * abs B` MP_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&1 * b <= C * b ==> b <= C * b`) THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                     `C:real`; `eps:real`; `U:B->bool`; `Y:B->bool`; `x:B`] P2BA4_CAP_FACTS) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `z:B` (X_CHOOSE_THEN `e:real^3->B` STRIP_ASSUME_TAC)) (LABEL_TAC "rat"))) THEN
      USE_THEN "nb" (MP_TAC o SPECL [`z:B`; `e:real^3->B`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      USE_THEN "rat" (MP_TAC o SPECL [`z:B`; `x:B`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      SUBGOAL_THEN `C * mfd_scalar atlas (g:B->real^3^3) z <= C * abs B` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rfs_c_component; rfs_round_component] o
      check (fun th -> can (find_term (fun t -> is_const t &&
        mem (fst(dest_const t)) ["rfs_c_component"; "rfs_round_component"])) (concl th))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC (MP_TAC o CONJUNCT1))) THEN
    ASM_SIMP_TAC[CONNECTED_COMPONENTS_OF_CONNECTED_SPACE] THEN
    COND_CASES_TAC THEN REWRITE_TAC[NOT_IN_EMPTY; IN_SING] THEN
    DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (term_match [] `compact_in (top:B topology) s`) (concl th))) THEN
    ASM_REWRITE_TAC[GSYM compact_space];
    ALL_TAC] THEN
  EXISTS_TAC `abs M / &2` THEN X_GEN_TAC `x:B` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `mfd_scalar atlas (g:B->real^3^3) x / &2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2BX0_RM_NORM_LE_HALF_SCALAR THEN EXISTS_TAC `top:B topology` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    USE_THEN "M" (MP_TAC o SPEC `x:B`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; REAL_ARITH_TAC]]);;


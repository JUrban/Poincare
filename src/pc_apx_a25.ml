(* ========================================================================= *)
(* pc_apx_a25: MT Prop A.25 (given in MT without proof), separating case,    *)
(* from the smooth Schoenflies statement: APX_A25_FROM_SCHREQ |- !u.         *)
(* APX_SCHOENFLIES_REQ_STATEMENT u ==> APX_A25_STATEMENT u.  A compact       *)
(* component V all of whose points are neck centres or cap cores is two      *)
(* balls glued radially or contains a twisted chart.  Method: no caps        *)
(* contradicts A19; from a ball cap U1 grow a chain of necks from the copy   *)
(* of its boundary neck at level 1/(2 eps) (the region growth of             *)
(* pc_apx_class, in the outer side of that sphere); it stops at another ball *)
(* cap (two balls), unless the start sphere meets the extended core of a     *)
(* ball cap U, where the Schoenflies statement bounds a ball by it (two      *)
(* balls, or a switch to the base cap U; finitely many switches by a         *)
(* disjoint-necks card bound).                                               *)
(* ========================================================================= *)

needs "src/pc_apx_class.ml";;
needs "src/pc_smt_leafsep.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Components and the two sides of a neck sphere in a                        *)
(* component V (V = inner side + sphere + outer side; closures add only     *)
(* sphere points).                                                           *)
(* ------------------------------------------------------------------------- *)

(* A connected set meeting a component lies in it. *)

let APX_A25_IN_COMPONENT = prove
 (`!top V K:A->bool.
     V IN connected_components_of top /\ connected_in top K /\ ~DISJOINT K V
     ==> K SUBSET V`,
  REPEAT GEN_TAC THEN REWRITE_TAC[connected_components_of; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x0:A` STRIP_ASSUME_TAC) MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(K:A->bool) SUBSET connected_component_of top y` MP_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPONENT_OF_MAXIMAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `connected_component_of top (y:A) = connected_component_of top x0`
  (fun th -> ASM_REWRITE_TAC[th]) THEN
  UNDISCH_TAC `(y:A) IN V` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[CONNECTED_COMPONENT_OF_EQ] THEN
  ASM_MESON_TAC[IN; CONNECTED_COMPONENT_OF_SYM; CONNECTED_COMPONENT_OF_EQUIV;
                CONNECTED_COMPONENT_IN_TOPSPACE; SUBSET]);;

(* The two sides of a neck sphere inside a component V: V is the union of  *)
(* the inner side, the sphere and the outer side, and the closure of each    *)
(* side only adds sphere points.                                             *)

let APX_A25_SIDES = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) e V.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ apx_sphere_sep top atlas /\
     V IN connected_components_of top /\ mfd_neck_chart top atlas e /\
     ~DISJOINT V (IMAGE e (annulus (&1 / &2) (&2)))
     ==> IMAGE e (annulus (&1 / &2) (&2)) SUBSET V /\
         lsp_side top e (&3 / &4) SUBSET V /\ lsp_side top e (&4 / &3) SUBSET V /\
         V = lsp_side top e (&3 / &4) UNION IMAGE e (sphere(vec 0,&1)) UNION
             lsp_side top e (&4 / &3) /\
         top closure_of (lsp_side top e (&3 / &4)) SUBSET
         lsp_side top e (&3 / &4) UNION IMAGE e (sphere(vec 0,&1)) /\
         top closure_of (lsp_side top e (&4 / &3)) SUBSET
         lsp_side top e (&4 / &3) UNION IMAGE e (sphere(vec 0,&1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `e:real^3->A`]
    LSP_NECK_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `e:real^3->A`]
    LSP_SIDES) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (fun th ->
    MP_TAC(SPEC `&3 / &4` th) THEN MP_TAC(SPEC `&4 / &3` th))) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `e:real^3->A`]
    LSP_SIDE_HALVES) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `S = IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
  ABBREV_TAC `I0 = lsp_side top (e:real^3->A) (&3 / &4)` THEN
  ABBREV_TAC `O0 = lsp_side top (e:real^3->A) (&4 / &3)` THEN
  SUBGOAL_THEN `IMAGE (e:real^3->A) (annulus (&1 / &2) (&2)) SUBSET V` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_A25_IN_COMPONENT THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[DISJOINT_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^3->A)(&3 / &4 % basis 1) IN V /\ (e:real^3->A)(&4 / &3 % basis 1) IN V`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      concl th = `IMAGE (e:real^3->A) (annulus (&1 / &2) (&2)) SUBSET V`)) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN
    SIMP_TAC[annulus; IN_ELIM_THM; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `(I0:A->bool) SUBSET V /\ (O0:A->bool) SUBSET V` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC APX_A25_IN_COMPONENT THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THENL
     [EXISTS_TAC `(e:real^3->A)(&3 / &4 % basis 1)`;
      EXISTS_TAC `(e:real^3->A)(&4 / &3 % basis 1)`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p:A. p IN topspace top DIFF S
                ==> open_in top (connected_component_of (subtopology top (topspace top DIFF S)) p) /\
                    p IN connected_component_of (subtopology top (topspace top DIFF S)) p`
  ASSUME_TAC THENL
   [X_GEN_TAC `p:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `S:A->bool`;
                   `p:A`] LSP_SIDE) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!K:A->bool. K = I0 \/ K = O0
                ==> top closure_of K SUBSET K UNION S`
  ASSUME_TAC THENL
   [X_GEN_TAC `K:A->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?q:A. K = connected_component_of (subtopology top (topspace top DIFF S)) q`
    (X_CHOOSE_TAC `q:A`) THENL
     [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THENL
       [EXPAND_TAC "I0" THEN REWRITE_TAC[lsp_side] THEN
        EXISTS_TAC `(e:real^3->A)(&3 / &4 % basis 1)` THEN EXPAND_TAC "S" THEN REWRITE_TAC[];
        EXPAND_TAC "O0" THEN REWRITE_TAC[lsp_side] THEN
        EXISTS_TAC `(e:real^3->A)(&4 / &3 % basis 1)` THEN EXPAND_TAC "S" THEN REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_UNION] THEN X_GEN_TAC `p:A` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(p:A) IN S` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(p:A) IN topspace top DIFF S` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[IN_DIFF] THEN
      UNDISCH_TAC `(p:A) IN top closure_of K` THEN REWRITE_TAC[IN_CLOSURE_OF] THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(p:A) IN top closure_of K` THEN REWRITE_TAC[IN_CLOSURE_OF] THEN
    DISCH_THEN(MP_TAC o SPEC
      `connected_component_of (subtopology top (topspace top DIFF S)) (p:A)` o CONJUNCT2) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `~(connected_component_of (subtopology top (topspace top DIFF S)) (p:A) INTER
                    connected_component_of (subtopology top (topspace top DIFF S)) q = {})`
    MP_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `y:A` THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(y:A) IN K` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[CONNECTED_COMPONENT_OF_OVERLAP] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      can (find_term (fun t -> t = `p:A`)) (lhs(concl th)))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ALL_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[]] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC APX_CONNECTED_CLOPEN_EQ THEN
  EXISTS_TAC `top:A topology` THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `V IN connected_components_of (top:A topology)` THEN
    REWRITE_TAC[connected_components_of; IN_ELIM_THM] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[CONNECTED_IN_CONNECTED_COMPONENT_OF];
    UNDISCH_TAC `IMAGE (e:real^3->A) (annulus (&1 / &2) (&2)) SUBSET V` THEN
    UNDISCH_TAC `(S:A->bool) SUBSET IMAGE (e:real^3->A) (annulus (&1 / &2) (&2))` THEN
    UNDISCH_TAC `(I0:A->bool) SUBSET V` THEN UNDISCH_TAC `(O0:A->bool) SUBSET V` THEN
    SET_TAC[];
    SUBGOAL_THEN `I0 UNION S UNION O0 = I0 UNION IMAGE (e:real^3->A) (annulus (&1 / &2) (&2))
                                       UNION O0` SUBST1_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!a b c d. b SUBSET d /\ d SUBSET a UNION b UNION c ==>
                              a UNION b UNION c = a UNION (d:A->bool) UNION c`) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `annulus (&1 / &2) (&2) = annulus (&1 / &2) (&1) UNION sphere(vec 0,&1) UNION
                                             annulus (&1) (&2):real^3->bool` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_UNION; annulus; IN_ELIM_THM; IN_SPHERE_0] THEN REAL_ARITH_TAC;
        REWRITE_TAC[IMAGE_UNION] THEN ASM SET_TAC[]];
      MATCH_MP_TAC OPEN_IN_UNION THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC OPEN_IN_UNION THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_UNION] THEN
    EXISTS_TAC `(e:real^3->A)(&3 / &4 % basis 1)` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[CLOSURE_OF_UNION] THEN
    SUBGOAL_THEN `top closure_of (S:A->bool) = S` SUBST1_TAC THENL
     [ASM_SIMP_TAC[CLOSURE_OF_EQ]; ALL_TAC] THEN
    MP_TAC(SPEC `I0:A->bool` (ASSUME `!K:A->bool. K = I0 \/ K = O0
                ==> top closure_of K SUBSET K UNION S`)) THEN
    MP_TAC(SPEC `O0:A->bool` (ASSUME `!K:A->bool. K = I0 \/ K = O0
                ==> top closure_of K SUBSET K UNION S`)) THEN
    REWRITE_TAC[] THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The start annulus near a ball cap (the configuration where the            *)
(* Schoenflies statement APX_SCHOENFLIES_REQ_STATEMENT is used).             *)
(* ------------------------------------------------------------------------- *)

(* The middle annulus lies in every neck domain of scale at most 1/8. *)

let APX_A25_MID_NECK_DOM = prove
 (`!d. &0 < d /\ d <= &1 / &8 ==> annulus (&1 / &2) (&2) SUBSET rfs_neck_dom d`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `d:real` APX_BEXT_RADIUS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[APX_NECK_DOM_ANNULUS; SUBSET; annulus; IN_ELIM_THM] THEN
  REWRITE_TAC[real_div; REAL_MUL_LNEG; REAL_EXP_NEG] THEN
  REWRITE_TAC[GSYM real_div] THEN
  ABBREV_TAC `R = exp(inv d / sqrt(&2))` THEN DISCH_TAC THEN
  SUBGOAL_THEN `inv R < &1 / &2` ASSUME_TAC THENL
   [MP_TAC(SPECL [`&2`; `R:real`] REAL_LT_INV2) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `y:real^3` THEN ASM_REAL_ARITH_TAC);;

(* The start annulus near a ball cap: if the middle annulus of an ep-neck    *)
(* meets the extended core of a ball cap up to level 4/ep, it lies in the     *)
(* extended core up to level 1/(4 eps) (its diameter is about 12 h, while    *)
(* the levels 4/ep and 1/(4 eps) of the cap neck are far apart).            *)

let APX_A25_START_GEOM = prove
 (`!top atlas (g:A->real^3^3) C eps ep U (bb:real^3->A) e' f x0 (N0:real^3->A).
     hausdorff_space top /\ riemannian_metric atlas g /\ &0 < eps /\
     &580 * eps <= ep /\ ep <= &1 / &1024 /\
     apx_ch_ctx top atlas g ep /\ apx_ch_ctx top atlas g eps /\ apx_cl_rat top atlas g ep /\
     apx_bcap (top,atlas) g C eps U bb e' f /\ rfs_neck (top,atlas) g ep x0 N0 /\
     ~DISJOINT (IMAGE N0 (annulus (&1 / &2) (&2)))
               (IMAGE (apx_bext bb e' f) (ball(vec 0,exp((&4 * inv ep) / sqrt(&2)))))
     ==> IMAGE N0 (annulus (&1 / &2) (&2)) SUBSET
         IMAGE (apx_bext bb e' f) (ball(vec 0,exp(inv(&4 * eps) / sqrt(&2))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  APX_UNFOLD_ASM_TAC "apx_bcap" apx_bcap THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
                mfd_param top atlas (rfs_neck_dom eps) (e':real^3->A) /\
                mfd_param top atlas (rfs_neck_dom ep) (N0:real^3->A)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  SUBGOAL_THEN `eps <= &1 / &8 /\ &1024 <= inv ep /\ &580 * inv ep <= inv eps /\ &0 < ep /\
                &1024 * &580 <= inv eps`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < ep` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&1024 <= inv ep` ASSUME_TAC THENL
     [MP_TAC(SPECL [`ep:real`; `&1 / &1024`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&580 * inv ep <= inv eps` ASSUME_TAC THENL
     [SUBGOAL_THEN `inv ep <= inv(&580 * eps)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_INV_MUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `bb:real^3->A`;
                 `e':real^3->A`; `f:real^3->real^3`; `f':real^3->real^3`; `eps:real`]
                APX_BEXT_FACTS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[mfd_ball_chart]; STRIP_TAC] THEN
  MP_TAC(SPEC `eps:real` APX_BEXT_RADIUS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `R = exp(inv eps / sqrt(&2))` THEN
  ABBREV_TAC `r4 = exp((&4 * inv ep) / sqrt(&2))` THEN
  ABBREV_TAC `rho = exp(inv(&4 * eps) / sqrt(&2))` THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(&4 * eps) = inv eps / &4` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 < r4 /\ r4 < rho /\ rho < R` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["r4"; "rho"; "R"] THEN
    REWRITE_TAC[GSYM REAL_EXP_0; REAL_EXP_MONO_LT] THEN
    ASM_SIMP_TAC[REAL_LT_DIV2_EQ] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `A0 = IMAGE (N0:real^3->A) (annulus (&1 / &2) (&2))` THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `q0:A` THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `annulus (&1 / &2) (&2) SUBSET rfs_neck_dom ep` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_A25_MID_NECK_DOM THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `connected_in top (A0:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "A0" THEN MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom ep`] THEN
    ASM_REWRITE_TAC[APX_CONNECTED_ANNULUS3];
    ALL_TAC] THEN
  (* crossing points on the level spheres r4 and rho of the cap neck *)
  SUBGOAL_THEN
   `!r. &1 < r /\ r < R /\ ~DISJOINT (A0:A->bool) (IMAGE (apx_bext (bb:real^3->A) e' f) (ball(vec 0,r))) /\
        ~(A0 SUBSET IMAGE (apx_bext bb e' f) (ball(vec 0,r)))
        ==> ?v y. v IN annulus (&1 / &2) (&2) /\ y IN sphere(vec 0,r) /\
                  (N0:real^3->A) v = e' y`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `apx_bext (bb:real^3->A) e' f`; `R:real`; `r:real`] APX_PARAM_BALL_FRONTIER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MP_TAC(ISPECL [`bb:real^3->A`; `e':real^3->A`; `f:real^3->real^3`; `f':real^3->real^3`;
                   `r:real`] APX_BEXT_SPHERE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `A0:A->bool`;
                   `IMAGE (apx_bext (bb:real^3->A) e' f) (ball(vec 0,r))`]
                  CONNECTED_IN_INTER_FRONTIER_OF) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[GSYM DISJOINT] THEN
      UNDISCH_TAC `~((A0:A->bool) SUBSET IMAGE (apx_bext (bb:real^3->A) e' f) (ball(vec 0,r)))` THEN
      SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(p:A) IN IMAGE (e':real^3->A) (sphere(vec 0,r))` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(p:A) IN A0` THEN EXPAND_TAC "A0" THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`v:real^3`; `y:real^3`] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((A0:A->bool) SUBSET IMAGE (apx_bext (bb:real^3->A) e' f) (ball(vec 0,rho))) /\
                ~(A0 SUBSET IMAGE (apx_bext bb e' f) (ball(vec 0,r4))) /\
                ~DISJOINT A0 (IMAGE (apx_bext bb e' f) (ball(vec 0,r4))) /\
                ~DISJOINT A0 (IMAGE (apx_bext bb e' f) (ball(vec 0,rho)))`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `IMAGE (apx_bext (bb:real^3->A) e' f) (ball(vec 0,r4)) SUBSET
                  IMAGE (apx_bext bb e' f) (ball(vec 0,rho))` MP_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `~DISJOINT (A0:A->bool)
                  (IMAGE (apx_bext (bb:real^3->A) e' f) (ball(vec 0,r4)))` THEN
    UNDISCH_TAC `(q0:A) IN A0` THEN
    UNDISCH_TAC `~((q0:A) IN IMAGE (apx_bext (bb:real^3->A) e' f) (ball(vec 0,rho)))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `r4:real`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:real^3` (X_CHOOSE_THEN `y1:real^3` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `rho:real`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v2:real^3` (X_CHOOSE_THEN `y2:real^3` STRIP_ASSUME_TAC)) THEN
  (* the levels of the crossing points in the cap neck *)
  SUBGOAL_THEN `norm(y1:real^3) = r4 /\ norm(y2:real^3) = rho` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y1:real^3) IN sphere(vec 0,r4)` THEN
    UNDISCH_TAC `(y2:real^3) IN sphere(vec 0,rho)` THEN SIMP_TAC[IN_SPHERE_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y1:real^3) IN rfs_neck_dom eps /\ apx_sval y1 = &4 * inv ep /\
                (y2:real^3) IN rfs_neck_dom eps /\ apx_sval y2 = inv eps / &4`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        concl th = `annulus (&1) R SUBSET rfs_neck_dom eps`)) THEN
      REWRITE_TAC[annulus; IN_ELIM_THM; ASSUME `norm(y1:real^3) = r4`] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[apx_sval; ASSUME `norm(y1:real^3) = r4`] THEN
      REWRITE_TAC[GSYM(ASSUME `exp((&4 * inv ep) / sqrt(&2)) = r4`); LOG_EXP] THEN
      UNDISCH_TAC `&0 < sqrt(&2)` THEN CONV_TAC REAL_FIELD;
      FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        concl th = `annulus (&1) R SUBSET rfs_neck_dom eps`)) THEN
      REWRITE_TAC[annulus; IN_ELIM_THM; ASSUME `norm(y2:real^3) = rho`] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[apx_sval; ASSUME `norm(y2:real^3) = rho`] THEN
      REWRITE_TAC[GSYM(ASSUME `exp(inv(&4 * eps) / sqrt(&2)) = rho`); LOG_EXP] THEN
      REWRITE_TAC[ASSUME `inv(&4 * eps) = inv eps / &4`] THEN
      UNDISCH_TAC `&0 < sqrt(&2)` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v1:real^3) IN rfs_neck_dom ep /\ (v2:real^3) IN rfs_neck_dom ep`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  (* scales *)
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) x0 /\ &0 < mfd_scalar atlas g z'`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(mfd_scalar atlas (g:A->real^3^3) ((N0:real^3->A) v1) /
                    mfd_scalar atlas g x0 - &1) <= &1 / &1000 /\
                abs(mfd_scalar atlas g ((e':real^3->A) y1) / mfd_scalar atlas g z' - &1)
                <= &1 / &1000`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(REWRITE_RULE[apx_cl_rat] (ASSUME `apx_cl_rat top atlas (g:A->real^3^3) ep`)) THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`ep:real`; `x0:A`; `N0:real^3->A`; `v1:real^3`]);
      FIRST_X_ASSUM(MP_TAC o SPECL [`eps:real`; `z':A`; `e':real^3->A`; `y1:real^3`])] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[];
                    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) ((e':real^3->A) y1)` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) ((e':real^3->A) y1) /
                       mfd_scalar atlas g z'` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_MUL_LZERO]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`mfd_scalar atlas (g:A->real^3^3) x0`; `mfd_scalar atlas (g:A->real^3^3) z'`;
                `mfd_scalar atlas (g:A->real^3^3) ((e':real^3->A) y1)`] APX_RATIO_SQRT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `abs(mfd_scalar atlas (g:A->real^3^3) ((N0:real^3->A) v1) /
                     mfd_scalar atlas g x0 - &1) <= &1 / &1000` THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  ABBREV_TAC `hx = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x0))` THEN
  ABBREV_TAC `hz = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) z'))` THEN
  SUBGOAL_THEN `&0 < hx /\ &0 < hz` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["hx"; "hz"] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN
    MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the distance of the two crossing points, through the centre x0 *)
  SUBGOAL_THEN `apx_eng_n2 top atlas (g:A->real^3^3) ep (&1 / &100) /\
                apx_eng_n2 top atlas g eps (&1 / &100)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `apx_ch_ctx top atlas (g:A->real^3^3) ep` THEN
    UNDISCH_TAC `apx_ch_ctx top atlas (g:A->real^3^3) eps` THEN
    SIMP_TAC[apx_ch_ctx];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `ep:real`; `x0:A`; `N0:real^3->A`; `v1:real^3`] APX_CENTRE_DIST) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `ep:real`; `x0:A`; `N0:real^3->A`; `v2:real^3`] APX_CENTRE_DIST) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`ep:real`; `v1:real^3`] APX_SVAL_NECK_DOM) THEN
  MP_TAC(SPECL [`ep:real`; `v2:real^3`] APX_SVAL_NECK_DOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC APX_SQRT2_PI THEN DISCH_TAC THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas) ((e':real^3->A) y1) (e' y2) /\
                mfd_dist (top,atlas) (g:A->real^3^3) (e' y1) (e' y2) <=
                hz * (&203 / &100 * (inv ep + &24 / &5))`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) ((e':real^3->A) y1) x0 /\
                  mfd_joinable (top,atlas) x0 ((e':real^3->A) y2)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [ASM_MESON_TAC[MFD_JOINABLE_SYM]; ASM_MESON_TAC[]];
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_TRANS]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_dist (top,atlas) (g:A->real^3^3) ((e':real^3->A) y1) x0 +
                mfd_dist (top,atlas) g x0 (e' y2)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^3^3) ((e':real^3->A) y1) x0 =
                  mfd_dist (top,atlas) g x0 ((N0:real^3->A) v1) /\
                  mfd_dist (top,atlas) g x0 (e' y2) = mfd_dist (top,atlas) g x0 (N0 v2)`
    (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MFD_DIST_SYM]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&101 / &100 * hx * (abs(apx_sval(v1:real^3)) + sqrt(&2) * pi) +
                &101 / &100 * hx * (abs(apx_sval(v2:real^3)) + sqrt(&2) * pi)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `hx * ((abs(apx_sval(v1:real^3)) + sqrt(&2) * pi) +
                        (abs(apx_sval(v2:real^3)) + sqrt(&2) * pi)) <=
                  (&1002 / &1000 * hz) * (&2 * (inv ep + &24 / &5))` MP_TAC THENL
     [SUBGOAL_THEN `&0 <= sqrt(&2) * pi` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[SQRT_POS_LE; REAL_POS; PI_POS; REAL_LT_IMP_LE];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MP_TAC(SPEC `apx_sval(v1:real^3)` REAL_ABS_POS) THEN
      MP_TAC(SPEC `apx_sval(v2:real^3)` REAL_ABS_POS) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= hz * inv ep` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&0 < hz` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the near-level estimate in the cap neck from e' y1 *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `z':A`; `e':real^3->A`; `y1:real^3`; `(e':real^3->A) y2`]
                APX_NEAR_LEVEL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `hz * (&203 / &100 * (inv ep + &24 / &5))` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&99 / &100 * hz * (inv eps - abs(&4 * inv ep)) =
                  hz * (&99 / &100 * (inv eps - abs(&4 * inv ep)))` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LMUL_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y':real^3` (STRIP_ASSUME_TAC o
    REWRITE_RULE[ASSUME `inv(sqrt(mfd_scalar atlas (g:A->real^3^3) z')) = hz`])) THEN
  SUBGOAL_THEN `y':real^3 = y2` SUBST_ALL_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MFD_PARAM_INJ THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `rfs_neck_dom eps`; `e':real^3->A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `hz * (&99 / &100 * abs(inv eps / &4 - &4 * inv ep)) <=
                hz * (&203 / &100 * (inv ep + &24 / &5))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_dist (top,atlas) (g:A->real^3^3) ((e':real^3->A) y1) (e' y2)` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t ->
      t = `apx_sval(y2:real^3) - apx_sval(y1:real^3)`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Two balls from two ball charts; the base neck N0 of a ball                *)
(* cap U1 at radius r0 and its two sides inside the component V.             *)
(* ------------------------------------------------------------------------- *)

(* Two balls in M with images in an open V give two balls in V. *)

let APX_A25_TWO_BALLS_INTRO = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) V b1 b2 f f' r.
     smooth_manifold_atlas top atlas /\ open_in top V /\
     mfd_ball_chart top atlas b1 /\ mfd_ball_chart top atlas b2 /\
     IMAGE b1 (ball(vec 0,&2)) SUBSET V /\ IMAGE b2 (ball(vec 0,&2)) SUBSET V /\
     sphere_diffeo f f' /\ &1 < r /\
     V = IMAGE b1 (cball(vec 0,&1)) UNION IMAGE b2 (cball(vec 0,&1)) /\
     DISJOINT (IMAGE b1 (ball(vec 0,&1))) (IMAGE b2 (ball(vec 0,&1))) /\
     (!x. x IN annulus (&1) r ==> b1 x = b2(inv(norm x) % f(inv(norm x) % x)))
     ==> apx_two_balls (subtopology top V) (restrict_atlas atlas V)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `V:A->bool`)) THEN
  SUBGOAL_THEN `topspace(subtopology top V) = (V:A->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[apx_two_balls] THEN
  MAP_EVERY EXISTS_TAC [`b1:real^3->A`; `b2:real^3->A`; `f:real^3->real^3`;
                        `f':real^3->real^3`; `r:real`] THEN
  ASM_REWRITE_TAC[mfd_ball_chart] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mfd_ball_chart]) THEN
  ASM_SIMP_TAC[APX_PARAM_RESTRICT_EQ]);;

(* Points of the boundary neck beyond its unit sphere are points of the     *)
(* extended ball chart at the same radius.                                   *)

let APX_A25_BEXT_E = prove
 (`!(bb:real^3->A) e' f f' v.
     sphere_diffeo f f' /\ &1 < norm v /\
     (!x. &1 < norm x ==> apx_bext bb e' f x = e'(radial_ext f x))
     ==> norm(radial_ext f' v) = norm v /\ e' v = apx_bext bb e' f (radial_ext f' v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `norm(radial_ext (f':real^3->real^3) v) = norm v` ASSUME_TAC THENL
   [MATCH_MP_TAC SMT_RADIAL_EXT_NORM THEN ASM_MESON_TAC[sphere_diffeo]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC SMT_RADIAL_EXT_INVERSE THEN ASM_MESON_TAC[sphere_diffeo]);;

(* The base cap: the copy N0 of its boundary neck at level 1/(2 eps), its   *)
(* sphere S0 = e1(sphere r0), the inner side B1(ball r0) and the outer side  *)
(* (B1 the extended ball chart of the cap).                                  *)

let APX_A25_BASE_SETUP = prove
 (`!top atlas (g:A->real^3^3) C eps ep V U1 (bb1:real^3->A) e1 f1 r0 y0 N0 B1.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     apx_sphere_sep top atlas /\ V IN connected_components_of top /\
     &0 < eps /\ apx_kc * eps <= ep /\ ep <= &1 / &1024 /\
     apx_bcap (top,atlas) g C eps U1 bb1 e1 f1 /\ ~DISJOINT V (IMAGE bb1 (ball(vec 0,&1))) /\
     r0 = exp(inv(&2 * eps) / sqrt(&2)) /\ y0 = r0 % basis 1 /\ N0 = apx_cp e1 y0 /\
     B1 = apx_bext bb1 e1 f1
     ==> rfs_neck (top,atlas) g ep (e1 y0) N0 /\ mfd_neck_chart top atlas N0 /\
         (!w. N0 w = e1(r0 % w)) /\
         IMAGE N0 (sphere(vec 0,&1)) = IMAGE B1 (sphere(vec 0,r0)) /\
         IMAGE B1 (ball(vec 0,exp(inv eps / sqrt(&2)))) SUBSET V /\
         IMAGE N0 (annulus (&1 / &2) (&2)) SUBSET V /\
         lsp_side top N0 (&3 / &4) = IMAGE B1 (ball(vec 0,r0)) /\
         V = IMAGE B1 (cball(vec 0,r0)) UNION lsp_side top N0 (&4 / &3) /\
         DISJOINT (IMAGE B1 (cball(vec 0,r0))) (lsp_side top N0 (&4 / &3)) /\
         top closure_of (lsp_side top N0 (&4 / &3)) SUBSET
         lsp_side top N0 (&4 / &3) UNION IMAGE N0 (sphere(vec 0,&1)) /\
         &1 < r0 /\ &2 * r0 <= exp(inv eps / sqrt(&2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&580 * eps <= ep /\ eps <= &1 / &8 /\ &0 < ep` STRIP_ASSUME_TAC THENL
   [MP_TAC APX_KC_GE THEN DISCH_TAC THEN
    SUBGOAL_THEN `&580 * eps <= apx_kc * eps` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  APX_UNFOLD_ASM_TAC "apx_bcap" apx_bcap THEN
  SUBGOAL_THEN `mfd_param top atlas (rfs_neck_dom eps) (e1:real^3->A)` ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `bb1:real^3->A`;
                 `e1:real^3->A`; `f1:real^3->real^3`; `f':real^3->real^3`; `eps:real`]
                APX_BEXT_FACTS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[mfd_ball_chart]; STRIP_TAC] THEN
  MP_TAC(SPEC `eps:real` APX_BEXT_RADIUS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `R1 = exp(inv eps / sqrt(&2))` THEN
  ABBREV_TAC `rr = exp(inv(&2 * eps) / sqrt(&2))` THEN
  ABBREV_TAC `yy:real^3 = rr % basis 1` THEN
  ABBREV_TAC `NN = apx_cp (e1:real^3->A) yy` THEN
  ABBREV_TAC `BB = apx_bext (bb1:real^3->A) e1 f1` THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 < rr /\ &2 * rr <= R1 /\ norm(yy:real^3) = rr /\
                apx_sval(yy:real^3) = inv(&2 * eps) /\ (yy:real^3) IN rfs_neck_dom eps`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&8 <= inv eps` ASSUME_TAC THENL
     [MP_TAC(SPECL [`eps:real`; `&1 / &8`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&1 < rr` ASSUME_TAC THENL
     [EXPAND_TAC "rr" THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_EXP_0] THEN
      REWRITE_TAC[REAL_EXP_MONO_LT] THEN MATCH_MP_TAC REAL_LT_DIV THEN
      ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&2 * rr <= R1` ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["rr"; "R1"] THEN
      SUBGOAL_THEN `&2 = exp(log(&2))` (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [th])
      THENL [SIMP_TAC[EXP_LOG; REAL_ARITH `&0 < &2`]; ALL_TAC] THEN
      REWRITE_TAC[GSYM REAL_EXP_ADD; REAL_EXP_MONO_LE] THEN
      SUBGOAL_THEN `log(&2) <= &1` ASSUME_TAC THENL
       [GEN_REWRITE_TAC RAND_CONV [GSYM LOG_EXP] THEN
        MP_TAC(SPECL [`&2`; `exp(&1)`] LOG_MONO_LE) THEN
        REWRITE_TAC[REAL_EXP_POS_LT; REAL_ARITH `&0 < &2`] THEN DISCH_THEN SUBST1_TAC THEN
        MP_TAC(SPEC `&1` REAL_EXP_LE_X) THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `inv eps / sqrt(&2) = inv(&2 * eps) / sqrt(&2) + inv(&2 * eps) / sqrt(&2)`
      SUBST1_TAC THENL
       [REWRITE_TAC[REAL_INV_MUL] THEN UNDISCH_TAC `&0 < sqrt(&2)` THEN CONV_TAC REAL_FIELD;
        ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `a <= &1 /\ &1 <= b ==> a + b <= b + b`) THEN
      ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LID] THEN
      SUBGOAL_THEN `sqrt(&2) <= &3 / &2` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV;
        REWRITE_TAC[REAL_INV_MUL] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `norm(yy:real^3) = rr` ASSUME_TAC THENL
     [EXPAND_TAC "yy" THEN SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[apx_sval] THEN
      REWRITE_TAC[GSYM(ASSUME `exp(inv(&2 * eps) / sqrt(&2)) = rr`); LOG_EXP] THEN
      UNDISCH_TAC `&0 < sqrt(&2)` THEN CONV_TAC REAL_FIELD;
      FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        concl th = `annulus (&1) R1 SUBSET rfs_neck_dom eps`)) THEN
      ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 < rr` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM(ASSUME `exp(inv(&2 * eps) / sqrt(&2)) = rr`)] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&1 + inv(&2 * eps) / sqrt(&2)` THEN
    REWRITE_TAC[REAL_EXP_LE_X] THEN
    SUBGOAL_THEN `&8 <= inv eps /\ sqrt(&2) <= &3 / &2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC(SPECL [`eps:real`; `&1 / &8`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 < x ==> &2 < &1 + x`) THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_INV_MUL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the copy NN *)
  SUBGOAL_THEN `rfs_neck (top,atlas) (g:A->real^3^3) ep ((e1:real^3->A) yy) NN` ASSUME_TAC THENL
   [EXPAND_TAC "NN" THEN MATCH_MP_TAC APX_CP_NECK THEN
    MAP_EVERY EXISTS_TAC [`eps:real`; `z':A`] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_INV_MUL; real_div] THEN
    SUBGOAL_THEN `&0 < inv eps` MP_TAC THENL
     [ASM_REWRITE_TAC[REAL_LT_INV_EQ]; CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param top atlas (rfs_neck_dom ep) (NN:real^3->A)` ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  SUBGOAL_THEN `annulus (&1 / &2) (&2) SUBSET rfs_neck_dom ep` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_A25_MID_NECK_DOM THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_neck_chart top atlas (NN:real^3->A)` ASSUME_TAC THENL
   [REWRITE_TAC[mfd_neck_chart] THEN MATCH_MP_TAC MFD_PARAM_RESTRICT THEN
    EXISTS_TAC `rfs_neck_dom ep` THEN ASM_REWRITE_TAC[OPEN_ANNULUS];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. (NN:real^3->A) w = e1(rr % w)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`e1:real^3->A`; `yy:real^3`; `eps:real`] APX_CP_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (NN:real^3->A) (sphere(vec 0,&1)) = IMAGE (e1:real^3->A) (sphere(vec 0,rr)) /\
                IMAGE (BB:real^3->A) (sphere(vec 0,rr)) = IMAGE (e1:real^3->A) (sphere(vec 0,rr))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_REWRITE_TAC[EXTENSION; IN_IMAGE; IN_SPHERE_0] THEN X_GEN_TAC `p:A` THEN
      EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THENL
       [EXISTS_TAC `rr % w:real^3` THEN ASM_REWRITE_TAC[NORM_MUL] THEN ASM_REAL_ARITH_TAC;
        EXISTS_TAC `inv rr % w:real^3` THEN
        ASM_SIMP_TAC[NORM_MUL; VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_ARITH `&1 < r ==> ~(r = &0)`;
                     VECTOR_MUL_LID; REAL_ABS_INV] THEN
        ASM_SIMP_TAC[REAL_ARITH `&1 < r ==> abs r = r`; REAL_MUL_LINV;
                     REAL_ARITH `&1 < r ==> ~(r = &0)`]];
      EXPAND_TAC "BB" THEN MATCH_MP_TAC APX_BEXT_SPHERE THEN
      EXISTS_TAC `f':real^3->real^3` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `!x. &1 < norm x ==> (BB:real^3->A) x = e1 (radial_ext f1 x)` THEN
      EXPAND_TAC "BB" THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^3. &1 < norm v
                ==> norm(radial_ext f' v) = norm v /\ (e1:real^3->A) v = BB(radial_ext f' v)`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`bb1:real^3->A`; `e1:real^3->A`; `f1:real^3->real^3`; `f':real^3->real^3`;
                   `v:real^3`] APX_A25_BEXT_E) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [UNDISCH_TAC `!x. &1 < norm x ==> (BB:real^3->A) x = e1 (radial_ext f1 x)` THEN
      EXPAND_TAC "BB" THEN REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (BB:real^3->A) (ball(vec 0,R1)) SUBSET V` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_A25_IN_COMPONENT THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `ball(vec 0:real^3,R1)`] THEN
      ASM_REWRITE_TAC[CONNECTED_BALL; SUBSET_REFL];
      UNDISCH_TAC `~DISJOINT V (IMAGE (bb1:real^3->A) (ball(vec 0,&1)))` THEN
      MATCH_MP_TAC(SET_RULE `!a b c. b SUBSET c ==> ~DISJOINT (a:A->bool) b ==> ~DISJOINT c a`) THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_BALL_0] THEN X_GEN_TAC `w:real^3` THEN
      DISCH_TAC THEN REWRITE_TAC[IN_IMAGE; IN_BALL_0] THEN EXISTS_TAC `w:real^3` THEN
      CONJ_TAC THENL
       [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          is_forall(concl th) && can (find_term ((=) `bb1:real^3->A`)) (concl th) &&
          can (find_term ((=) `BB:real^3->A`)) (concl th))) THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (NN:real^3->A) (annulus (&1 / &2) (&2)) SUBSET V` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (BB:real^3->A) (ball(vec 0,R1))` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; annulus; IN_ELIM_THM] THEN
    X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&1 < norm(rr % w:real^3) /\ norm(rr % w:real^3) < R1` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[NORM_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&1 < r ==> abs r = r`] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `rr * &1 / &2` THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
        SUBGOAL_THEN `rr * norm(w:real^3) < rr * &2` MP_TAC THENL
         [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `rr % w:real^3` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `radial_ext (f':real^3->real^3)`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_BALL_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `NN:real^3->A`;
                 `V:A->bool`] APX_A25_SIDES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (NN:real^3->A) (annulus (&1 / &2) (&2)) SUBSET V` THEN
    MATCH_MP_TAC(SET_RULE `~(s = {}) ==> s SUBSET v ==> ~DISJOINT v (s:A->bool)`) THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `basis 1:real^3` THEN
    SIMP_TAC[annulus; IN_ELIM_THM; NORM_BASIS; DIMINDEX_3; ARITH] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `NN:real^3->A`]
    LSP_SIDES) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (fun th -> MP_TAC(SPEC `&3 / &4` th))) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `S0 = IMAGE (NN:real^3->A) (sphere(vec 0,&1))` THEN
  ABBREV_TAC `I0 = lsp_side top (NN:real^3->A) (&3 / &4)` THEN
  FIRST_X_ASSUM(fun th -> if concl th = `S0 = IMAGE (e1:real^3->A) (sphere(vec 0,rr))`
    then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN ASSUME_TAC th else failwith "no") THEN
  SUBGOAL_THEN `DISJOINT (IMAGE (BB:real^3->A) (ball(vec 0,rr))) S0` ASSUME_TAC THENL
   [SUBGOAL_THEN `S0 = IMAGE (BB:real^3->A) (sphere(vec 0,rr))` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC APX_PARAM_IMAGE_DISJOINT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `ball(vec 0:real^3,R1)`] THEN
    ASM_REWRITE_TAC[SUBSET; IN_BALL_0; IN_SPHERE_0; DISJOINT; EXTENSION; IN_INTER;
                    NOT_IN_EMPTY] THEN
    REPEAT CONJ_TAC THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(NN:real^3->A)(&3 / &4 % basis 1) IN IMAGE (BB:real^3->A) (ball(vec 0,rr))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `&1 < norm((rr * &3 / &4) % basis 1:real^3) /\
                  norm((rr * &3 / &4) % basis 1:real^3) < rr` STRIP_ASSUME_TAC THENL
     [SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(rr * &3 / &4) % basis 1:real^3` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `radial_ext (f':real^3->real^3)`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_BALL_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `I0 = IMAGE (BB:real^3->A) (ball(vec 0,rr))` ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC APX_CONNECTED_CLOPEN_EQ THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "connected_in")) (concl th))) THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
        MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `ball(vec 0:real^3,R1)`] THEN
        ASM_REWRITE_TAC[CONNECTED_BALL; SUBSET; IN_BALL_0] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `IMAGE (BB:real^3->A) (ball(vec 0,rr)) SUBSET topspace top` MP_TAC THENL
         [MATCH_MP_TAC MFD_PARAM_IMAGE_SUBSET THEN
          MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `ball(vec 0:real^3,R1)`] THEN
          ASM_REWRITE_TAC[SUBSET; IN_BALL_0] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
          UNDISCH_TAC `DISJOINT (IMAGE (BB:real^3->A) (ball(vec 0,rr))) S0` THEN
          MATCH_ACCEPT_TAC(SET_RULE `!Q T S. DISJOINT (Q:A->bool) S ==> Q SUBSET T ==>
                                         Q SUBSET T DIFF S`)];
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
        EXISTS_TAC `(NN:real^3->A)(&3 / &4 % basis 1)` THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `ball(vec 0:real^3,R1)`] THEN
      ASM_REWRITE_TAC[OPEN_BALL; SUBSET; IN_BALL_0] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `(NN:real^3->A)(&3 / &4 % basis 1) IN IMAGE (BB:real^3->A) (ball(vec 0,rr))` THEN
      MATCH_ACCEPT_TAC(SET_RULE `!x Q. (x:A) IN Q ==> ~(Q = {})`);
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `BB:real^3->A`;
                     `R1:real`; `rr:real`] APX_PARAM_BALL_FRONTIER) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      SUBGOAL_THEN `IMAGE (BB:real^3->A) (cball(vec 0,rr)) =
                    IMAGE BB (ball(vec 0,rr)) UNION S0` ASSUME_TAC THENL
       [REWRITE_TAC[GSYM(ASSUME `IMAGE (BB:real^3->A) (sphere(vec 0,rr)) = S0`);
                    GSYM IMAGE_UNION] THEN AP_TERM_TAC THEN
        REWRITE_TAC[EXTENSION; IN_UNION; IN_BALL_0; IN_CBALL_0; IN_SPHERE_0] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC
       [`(I0:A->bool) SUBSET topspace top DIFF S0`;
        `IMAGE (BB:real^3->A) (cball(vec 0,rr)) = IMAGE BB (ball(vec 0,rr)) UNION S0`;
        `top closure_of IMAGE (BB:real^3->A) (ball(vec 0,rr)) SUBSET IMAGE BB (cball(vec 0,rr))`] THEN
      MATCH_ACCEPT_TAC(SET_RULE `!C K Q S I T. (C:A->bool) SUBSET K ==> K = Q UNION S ==>
                                            I SUBSET T DIFF S ==> I INTER C SUBSET Q`)];
    ALL_TAC] THEN
  SUBGOAL_THEN `lsp_side top (NN:real^3->A) (&4 / &3) SUBSET topspace top DIFF S0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `NN:real^3->A`]
      LSP_SIDES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `&4 / &3` o CONJUNCT2) THEN
    REWRITE_TAC[ASSUME `IMAGE (NN:real^3->A) (sphere(vec 0,&1)) = S0`] THEN
    STRIP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (BB:real^3->A) (cball(vec 0,rr)) = I0 UNION S0` SUBST1_TAC THENL
   [REWRITE_TAC[ASSUME `I0 = IMAGE (BB:real^3->A) (ball(vec 0,rr))`;
                GSYM(ASSUME `IMAGE (BB:real^3->A) (sphere(vec 0,rr)) = S0`);
                GSYM IMAGE_UNION] THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_UNION; IN_BALL_0; IN_CBALL_0; IN_SPHERE_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM(ASSUME `S0 = IMAGE (e1:real^3->A) (sphere(vec 0,rr))`)] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE `!I S O T. DISJOINT I O /\ O SUBSET T DIFF S
     ==> I UNION S UNION O = (I UNION S) UNION O /\ DISJOINT ((I:A->bool) UNION S) O`) THEN
  EXISTS_TAC `topspace top:A->bool` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The Schoenflies case.  When the base neck N0 meets the                    *)
(* extended core of a ball cap U (up to level 4/ep), the Schoenflies         *)
(* statement gives either two balls for V or the inclusion of the inner      *)
(* side of N0 in the core of U up to level 1/(4 eps).                        *)
(* ------------------------------------------------------------------------- *)

(* A ball chart whose unit sphere is the central sphere of a neck chart and *)
(* whose open unit ball meets one side of the neck is that side.           *)

let APX_A25_CBALL_SIDE = prove
 (`!top atlas (e:real^3->A) c r.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ apx_sphere_sep top atlas /\
     mfd_neck_chart top atlas e /\ mfd_ball_chart top atlas c /\
     (r = &3 / &4 \/ r = &4 / &3) /\
     IMAGE c (sphere(vec 0,&1)) = IMAGE e (sphere(vec 0,&1)) /\
     ~DISJOINT (IMAGE c (ball(vec 0,&1))) (lsp_side top e r)
     ==> IMAGE c (ball(vec 0,&1)) = lsp_side top e r`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `mfd_param top atlas (ball(vec 0,&2)) (c:real^3->A)` ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_ball_chart]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `e:real^3->A`]
    LSP_SIDES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `r:real` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `c:real^3->A`;
                 `&2`; `&1`] APX_PARAM_BALL_FRONTIER) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [REAL_ARITH_TAC; STRIP_TAC] THEN
  ABBREV_TAC `S = IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
  ABBREV_TAC `P = lsp_side top (e:real^3->A) r` THEN
  ABBREV_TAC `Q = IMAGE (c:real^3->A) (ball(vec 0,&1))` THEN
  SUBGOAL_THEN `DISJOINT (Q:A->bool) S` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN
    FIRST_X_ASSUM(fun th -> if concl th = `IMAGE (c:real^3->A) (sphere(vec 0,&1)) = S`
      then REWRITE_TAC[SYM th] else failwith "no") THEN
    MATCH_MP_TAC APX_PARAM_IMAGE_DISJOINT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `ball(vec 0:real^3,&2)`] THEN
    ASM_REWRITE_TAC[SUBSET; IN_BALL_0; IN_SPHERE_0; DISJOINT; EXTENSION; IN_INTER;
                    NOT_IN_EMPTY] THEN
    REPEAT CONJ_TAC THEN GEN_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(Q:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN MATCH_MP_TAC MFD_PARAM_IMAGE_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `ball(vec 0:real^3,&2)`] THEN
    ASM_REWRITE_TAC[SUBSET; IN_BALL_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (c:real^3->A) (cball(vec 0,&1)) = Q UNION S` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN
    FIRST_X_ASSUM(fun th -> if concl th = `IMAGE (c:real^3->A) (sphere(vec 0,&1)) = S`
      then REWRITE_TAC[SYM th] else failwith "no") THEN
    REWRITE_TAC[GSYM IMAGE_UNION] THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_UNION; IN_BALL_0; IN_CBALL_0; IN_SPHERE_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC APX_CONNECTED_CLOPEN_EQ THEN EXISTS_TAC `top:A topology` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "connected_in")) (concl th))) THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "Q" THEN MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `ball(vec 0:real^3,&2)`] THEN
      ASM_REWRITE_TAC[CONNECTED_BALL; SUBSET; IN_BALL_0] THEN REAL_ARITH_TAC;
      MAP_EVERY UNDISCH_TAC [`(Q:A->bool) SUBSET topspace top`; `DISJOINT (Q:A->bool) S`] THEN
      MATCH_ACCEPT_TAC(SET_RULE `!Q T S. DISJOINT (Q:A->bool) S ==> Q SUBSET T ==>
                                         Q SUBSET T DIFF S`);
      UNDISCH_TAC `~DISJOINT (Q:A->bool) P` THEN
      MATCH_ACCEPT_TAC(SET_RULE `!Q P. ~DISJOINT (Q:A->bool) P ==> ~(Q INTER P = {})`)];
    EXPAND_TAC "Q" THEN REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `vec 0:real^3` THEN
    REWRITE_TAC[CENTRE_IN_BALL] THEN REAL_ARITH_TAC;
    MAP_EVERY UNDISCH_TAC
     [`(P:A->bool) SUBSET topspace top DIFF S`;
      `IMAGE (c:real^3->A) (cball(vec 0,&1)) = Q UNION S`;
      `top closure_of (Q:A->bool) SUBSET IMAGE (c:real^3->A) (cball(vec 0,&1))`] THEN
    MATCH_ACCEPT_TAC(SET_RULE `!C K Q S I T. (C:A->bool) SUBSET K ==> K = Q UNION S ==>
                                          I SUBSET T DIFF S ==> I INTER C SUBSET Q`)]);;

(* The point at level t on the first axis. *)

let APX_A25_LEVEL_PT = prove
 (`!eps t. &0 < eps /\ eps <= &1 / &8 /\ &0 < t /\ t <= inv(&2 * eps)
     ==> norm(exp(t / sqrt(&2)) % basis 1:real^3) = exp(t / sqrt(&2)) /\
         &1 < exp(t / sqrt(&2)) /\
         apx_sval(exp(t / sqrt(&2)) % basis 1:real^3) = t /\
         exp(t / sqrt(&2)) % basis 1:real^3 IN rfs_neck_dom eps /\
         &2 * exp(t / sqrt(&2)) <= exp(inv eps / sqrt(&2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(&2) /\ sqrt(&2) <= &3 / &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH];
      MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN `&8 <= inv eps` ASSUME_TAC THENL
   [MP_TAC(SPECL [`eps:real`; `&1 / &8`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(&2 * eps) = inv eps / &2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `norm(exp(t / sqrt(&2)) % basis 1:real^3) = exp(t / sqrt(&2))` ASSUME_TAC THENL
   [SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID; REAL_ABS_EXP]; ALL_TAC] THEN
  SUBGOAL_THEN `apx_sval(exp(t / sqrt(&2)) % basis 1:real^3) = t` ASSUME_TAC THENL
   [MP_TAC(SPECL [`t:real`; `&1`] APX_SVAL_SCALED_BASIS) THEN
    REWRITE_TAC[REAL_LT_01; VECTOR_MUL_LID; LOG_1; REAL_MUL_RZERO; REAL_ADD_RID] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LT] THEN
    ASM_SIMP_TAC[REAL_LT_DIV];
    REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[VECTOR_MUL_EQ_0; REAL_EXP_NZ] THEN
      SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH];
      ASM_REAL_ARITH_TAC];
    SUBGOAL_THEN `&2 = exp(log(&2))` (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [th])
    THENL [SIMP_TAC[EXP_LOG; REAL_ARITH `&0 < &2`]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_EXP_ADD; REAL_EXP_MONO_LE] THEN
    SUBGOAL_THEN `log(&2) <= &1` ASSUME_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM LOG_EXP] THEN
      MP_TAC(SPECL [`&2`; `exp(&1)`] LOG_MONO_LE) THEN
      REWRITE_TAC[REAL_EXP_POS_LT; REAL_ARITH `&0 < &2`] THEN DISCH_THEN SUBST1_TAC THEN
      MP_TAC(SPEC `&1` REAL_EXP_LE_X) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `t / sqrt(&2) + &1 <= inv eps / sqrt(&2)` MP_TAC THENL
     [SUBGOAL_THEN `t / sqrt(&2) + &1 = (t + sqrt(&2)) / sqrt(&2)` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < sqrt(&2)` THEN CONV_TAC REAL_FIELD;
        ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC]]);;

(* The ball chart c of the Schoenflies statement agrees with the neck on   *)
(* its sphere.                                                             *)

let APX_A25_C_SPHERE = prove
 (`!(c:real^3->A) e.
     (!x. x IN annulus (&3 / &4) (&2) ==> c x = e x) \/
     (!x. x IN annulus (&3 / &4) (&2) ==> c x = e(inv(norm x pow 2) % x))
     ==> IMAGE c (sphere(vec 0,&1)) = IMAGE e (sphere(vec 0,&1))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC IMAGE_EQ THEN
  X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_SPHERE_0] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^3) IN annulus (&3 / &4) (&2)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM DISJ_CASES_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[VECTOR_MUL_LID]);;

(* The Schoenflies statement applied to the base neck N0 inside the        *)
(* extended core of another ball cap U: either V is two balls (the outer   *)
(* side of N0 is the ball of the Schoenflies statement) or the inner side  *)
(* of N0 lies in that core up                                              *)
(* to level 1/(4 eps) (switch the base cap to U).                          *)

let APX_A25_SCHREQ_CASE = prove
 (`!u top atlas (g:A->real^3^3) C eps ep V U1 (bb1:real^3->A) e1 f1 r0 y0 N0 B1
    U (bb:real^3->A) e' f.
     APX_SCHOENFLIES_REQ_STATEMENT (u:A->bool) /\
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     apx_sphere_sep top atlas /\ V IN connected_components_of top /\
     &0 < eps /\ apx_kc * eps <= ep /\ ep <= &1 / &1024 /\
     apx_ch_ctx top atlas g ep /\ apx_ch_ctx top atlas g eps /\ apx_cl_rat top atlas g ep /\
     apx_bcap (top,atlas) g C eps U1 bb1 e1 f1 /\ ~DISJOINT V (IMAGE bb1 (ball(vec 0,&1))) /\
     r0 = exp(inv(&2 * eps) / sqrt(&2)) /\ y0 = r0 % basis 1 /\ N0 = apx_cp e1 y0 /\
     B1 = apx_bext bb1 e1 f1 /\
     apx_bcap (top,atlas) g C eps U bb e' f /\
     ~DISJOINT (IMAGE N0 (annulus (&1 / &2) (&2)))
               (IMAGE (apx_bext bb e' f) (ball(vec 0,exp((&4 * inv ep) / sqrt(&2)))))
     ==> apx_two_balls (subtopology top V) (restrict_atlas atlas V) \/
         IMAGE B1 (ball(vec 0,r0)) SUBSET
         IMAGE (apx_bext bb e' f) (ball(vec 0,exp(inv(&4 * eps) / sqrt(&2))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `ep:real`; `V:A->bool`; `U1:A->bool`; `bb1:real^3->A`;
                 `e1:real^3->A`; `f1:real^3->real^3`; `r0:real`; `y0:real^3`;
                 `N0:real^3->A`; `B1:real^3->A`] APX_A25_BASE_SETUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `&580 * eps <= ep /\ eps <= &1 / &8 /\ &0 < ep` STRIP_ASSUME_TAC THENL
   [MP_TAC APX_KC_GE THEN DISCH_TAC THEN
    SUBGOAL_THEN `&580 * eps <= apx_kc * eps` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `ep:real`; `U:A->bool`; `bb:real^3->A`; `e':real^3->A`;
                 `f:real^3->real^3`; `(e1:real^3->A) y0`; `N0:real^3->A`] APX_A25_START_GEOM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 < inv(&4 * eps) /\ inv(&4 * eps) <= inv(&2 * eps) /\ &0 < inv(&2 * eps)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_INV_MUL] THEN
    SUBGOAL_THEN `&0 < inv eps` MP_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`eps:real`; `inv(&4 * eps)`] APX_A25_LEVEL_PT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`eps:real`; `inv(&2 * eps)`] APX_A25_LEVEL_PT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; STRIP_TAC] THEN
  SUBGOAL_THEN `?fU'. sphere_diffeo (f:real^3->real^3) fU'` (X_CHOOSE_TAC `fU':real^3->real^3`)
  THENL [ASM_MESON_TAC[apx_bcap]; ALL_TAC] THEN
  SUBGOAL_THEN `?f1'. sphere_diffeo (f1:real^3->real^3) f1'` (X_CHOOSE_TAC `f1':real^3->real^3`)
  THENL [ASM_MESON_TAC[apx_bcap]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `U:A->bool`; `bb:real^3->A`; `e':real^3->A`;
                 `f:real^3->real^3`; `fU':real^3->real^3`;
                 `exp(inv(&4 * eps) / sqrt(&2)) % basis 1:real^3`] APX_BCAP_SCALED_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[ASSUME
    `norm(exp(inv(&4 * eps) / sqrt(&2)) % basis 1:real^3) = exp(inv(&4 * eps) / sqrt(&2))`]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `U1:A->bool`; `bb1:real^3->A`; `e1:real^3->A`;
                 `f1:real^3->real^3`; `f1':real^3->real^3`;
                 `exp(inv(&2 * eps) / sqrt(&2)) % basis 1:real^3`] APX_BCAP_SCALED_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[ASSUME
    `norm(exp(inv(&2 * eps) / sqrt(&2)) % basis 1:real^3) = exp(inv(&2 * eps) / sqrt(&2))`]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `N0:real^3->A`]
    LSP_SIDE_HALVES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  (* switch to abbreviations *)
  FIRST_X_ASSUM(fun th -> if concl th = `r0 = exp(inv(&2 * eps) / sqrt(&2))`
    then SUBST_ALL_TAC(SYM th) THEN ASSUME_TAC(SYM th) else failwith "no") THEN
  FIRST_X_ASSUM(fun th -> if concl th = `y0:real^3 = r0 % basis 1`
    then SUBST_ALL_TAC(SYM th) THEN ASSUME_TAC(SYM th) else failwith "no") THEN
  FIRST_X_ASSUM(fun th -> if concl th = `N0 = apx_cp (e1:real^3->A) y0`
    then SUBST_ALL_TAC(SYM th) THEN ASSUME_TAC(SYM th) else failwith "no") THEN
  FIRST_X_ASSUM(fun th -> if concl th = `B1 = apx_bext (bb1:real^3->A) e1 f1`
    then SUBST_ALL_TAC(SYM th) THEN ASSUME_TAC(SYM th) else failwith "no") THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `V:A->bool`
    then ASSUME_TAC(SYM th) else failwith "no") THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
      lhs(concl th) = `lsp_side top (N0:real^3->A) (&3 / &4)`
    then RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th else failwith "no") THEN
  ABBREV_TAC `Os = lsp_side top (N0:real^3->A) (&4 / &3)` THEN
  ABBREV_TAC `rho = exp(inv(&4 * eps) / sqrt(&2))` THEN
  ABBREV_TAC `BU = apx_bext (bb:real^3->A) e' f` THEN
  ABBREV_TAC `R1 = exp(inv eps / sqrt(&2))` THEN
  (* the Schoenflies statement *)
  FIRST_X_ASSUM(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `\w. (BU:real^3->A)(rho % w)`; `N0:real^3->A`] o
    REWRITE_RULE[APX_SCHOENFLIES_REQ_STATEMENT] o check (fun th ->
      can (find_term (fun t -> is_const t &&
        fst(dest_const t) = "APX_SCHOENFLIES_REQ_STATEMENT")) (concl th))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ASSUME `IMAGE (\w. (BU:real^3->A) (rho % w)) (ball(vec 0,&1)) =
                        IMAGE (BU:real^3->A) (ball(vec 0,rho))`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^3->A` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (ASSUME_TAC o REWRITE_RULE[ASSUME
       `IMAGE (\w. (BU:real^3->A) (rho % w)) (ball(vec 0,&1)) = IMAGE (BU:real^3->A) (ball(vec 0,rho))`])
     ASSUME_TAC))) THEN
  SUBGOAL_THEN `IMAGE (c:real^3->A) (sphere(vec 0,&1)) = IMAGE (N0:real^3->A) (sphere(vec 0,&1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC APX_A25_C_SPHERE THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (c:real^3->A) (ball(vec 0,&1)) SUBSET IMAGE c (cball(vec 0,&1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[BALL_SUBSET_CBALL]; ALL_TAC] THEN
  SUBGOAL_THEN `&7 / &8 % basis 1:real^3 IN ball(vec 0,&1) /\
                &7 / &8 % basis 1:real^3 IN annulus (&3 / &4) (&2) /\
                &7 / &8 % basis 1:real^3 IN annulus (&1 / &2) (&1) /\
                &8 / &7 % basis 1:real^3 IN annulus (&1) (&2) /\
                inv(norm(&7 / &8 % basis 1:real^3) pow 2) % (&7 / &8 % basis 1:real^3) =
                &8 / &7 % basis 1`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `norm(&7 / &8 % basis 1:real^3) = &7 / &8 /\
                  norm(&8 / &7 % basis 1:real^3) = &8 / &7` STRIP_ASSUME_TAC THENL
     [SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_BALL_0; annulus; IN_ELIM_THM; VECTOR_MUL_ASSOC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th))) THENL
   [(* c agrees with N0: its ball is the inner side *)
    DISJ2_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `N0:real^3->A`;
                   `c:real^3->A`; `&3 / &4`] APX_A25_CBALL_SIDE) THEN
    REWRITE_TAC[ASSUME `lsp_side top (N0:real^3->A) (&3 / &4) = IMAGE (B1:real^3->A) (ball(vec 0,r0))`] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `(N0:real^3->A)(&7 / &8 % basis 1)` THEN CONJ_TAC THENL
       [SUBGOAL_THEN `(N0:real^3->A)(&7 / &8 % basis 1) = (c:real^3->A)(&7 / &8 % basis 1)` SUBST1_TAC THENL
         [CONV_TAC SYM_CONV THEN
          FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
            can (find_term (fun t -> t = `annulus (&3 / &4) (&2):real^3->bool`)) (concl th))) THEN
          FIRST_ASSUM ACCEPT_TAC;
          ALL_TAC] THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
        UNDISCH_TAC `IMAGE (N0:real^3->A) (annulus (&1 / &2) (&1)) SUBSET IMAGE (B1:real^3->A) (ball(vec 0,r0))` THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC];
      DISCH_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (c:real^3->A) (cball(vec 0,&1))` THEN
    CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `IMAGE (c:real^3->A) (ball(vec 0,&1)) = IMAGE (B1:real^3->A) (ball(vec 0,r0))`)) THEN
    FIRST_ASSUM ACCEPT_TAC;
    (* c agrees with N0 composed with the inversion: its ball is the outer side *)
    DISJ1_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `N0:real^3->A`;
                   `c:real^3->A`; `&4 / &3`] APX_A25_CBALL_SIDE) THEN
    REWRITE_TAC[ASSUME `lsp_side top (N0:real^3->A) (&4 / &3) = Os`] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `(N0:real^3->A)(&8 / &7 % basis 1)` THEN CONJ_TAC THENL
       [SUBGOAL_THEN `(N0:real^3->A)(&8 / &7 % basis 1) = (c:real^3->A)(&7 / &8 % basis 1)` SUBST1_TAC THENL
         [FIRST_ASSUM(MP_TAC o SPEC `&7 / &8 % basis 1:real^3` o check (fun th ->
            is_forall(concl th) &&
            can (find_term (fun t -> t = `annulus (&3 / &4) (&2):real^3->bool`)) (concl th))) THEN
          REWRITE_TAC[ASSUME `&7 / &8 % basis 1:real^3 IN annulus (&3 / &4) (&2)`;
                      ASSUME `inv(norm(&7 / &8 % basis 1:real^3) pow 2) % (&7 / &8 % basis 1:real^3) =
                              &8 / &7 % basis 1`] THEN
          DISCH_THEN(ACCEPT_TAC o SYM);
          ALL_TAC] THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
        UNDISCH_TAC `IMAGE (N0:real^3->A) (annulus (&1) (&2)) SUBSET (Os:A->bool)` THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC];
      DISCH_TAC] THEN
    SUBGOAL_THEN `mfd_param top atlas (ball(vec 0,&2)) (c:real^3->A) /\
                  mfd_param top atlas (ball(vec 0,&2)) (\w. (B1:real^3->A)(r0 % w))`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[mfd_ball_chart]; ALL_TAC] THEN
    SUBGOAL_THEN `(Os:A->bool) SUBSET V /\ (N0:real^3->A)(&8 / &7 % basis 1) IN Os`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `IMAGE (B1:real^3->A) (cball(vec 0,r0)) UNION Os = V` THEN SET_TAC[];
        UNDISCH_TAC `IMAGE (N0:real^3->A) (annulus (&1) (&2)) SUBSET (Os:A->bool)` THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC APX_A25_TWO_BALLS_INTRO THEN
    MAP_EVERY EXISTS_TAC [`\w. (B1:real^3->A)(r0 % w)`; `c:real^3->A`; `f1:real^3->real^3`;
                          `f1':real^3->real^3`; `&4 / &3`] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC(INST_TYPE [`:3`,`:N`] APX_COMPONENT_OPEN) THEN
      EXISTS_TAC `atlas:((A->bool)#(A->real^3))->bool` THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      (* b1 ball of radius 2 *)
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (B1:real^3->A) (ball(vec 0,R1))` THEN
      CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_BALL_0] THEN X_GEN_TAC `w:real^3` THEN
      DISCH_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      REWRITE_TAC[IN_BALL_0; NORM_MUL] THEN
      SUBGOAL_THEN `abs r0 * norm(w:real^3) < r0 * &2` MP_TAC THENL
       [SUBGOAL_THEN `abs r0 = r0` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      (* c ball of radius 2 *)
      MATCH_MP_TAC APX_A25_IN_COMPONENT THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
        MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `ball(vec 0:real^3,&2)`] THEN
        ASM_REWRITE_TAC[CONNECTED_BALL; SUBSET_REFL];
        REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
        EXISTS_TAC `(N0:real^3->A)(&8 / &7 % basis 1)` THEN CONJ_TAC THENL
         [SUBGOAL_THEN `IMAGE (c:real^3->A) (ball(vec 0,&1)) SUBSET IMAGE c (ball(vec 0,&2))`
          MP_TAC THENL
           [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; IN_BALL_0] THEN REAL_ARITH_TAC;
            REWRITE_TAC[ASSUME `IMAGE (c:real^3->A) (ball(vec 0,&1)) = Os`; SUBSET] THEN
            DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC];
          UNDISCH_TAC `(Os:A->bool) SUBSET V` THEN REWRITE_TAC[SUBSET] THEN
          DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC]];
      FIRST_ASSUM ACCEPT_TAC;
      REAL_ARITH_TAC;
      (* the union *)
      SUBGOAL_THEN `IMAGE (c:real^3->A) (cball(vec 0,&1)) =
                    IMAGE c (ball(vec 0,&1)) UNION IMAGE c (sphere(vec 0,&1))` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM IMAGE_UNION] THEN AP_TERM_TAC THEN
        REWRITE_TAC[EXTENSION; IN_UNION; IN_BALL_0; IN_CBALL_0; IN_SPHERE_0] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `IMAGE (B1:real^3->A) (sphere(vec 0,r0)) SUBSET IMAGE (B1:real^3->A) (cball(vec 0,r0))`
      MP_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; IN_SPHERE_0; IN_CBALL_0] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[ASSUME `IMAGE (\w. (B1:real^3->A) (r0 % w)) (cball(vec 0,&1)) =
                          IMAGE (B1:real^3->A) (cball(vec 0,r0))`;
                  ASSUME `IMAGE (c:real^3->A) (ball(vec 0,&1)) = Os`;
                  ASSUME `IMAGE (c:real^3->A) (sphere(vec 0,&1)) = IMAGE (N0:real^3->A) (sphere(vec 0,&1))`;
                  ASSUME `IMAGE (N0:real^3->A) (sphere(vec 0,&1)) = IMAGE (B1:real^3->A) (sphere(vec 0,r0))`] THEN
      UNDISCH_TAC `IMAGE (B1:real^3->A) (cball(vec 0,r0)) UNION Os = V` THEN
      MATCH_ACCEPT_TAC(SET_RULE `!K O S V. K UNION O = V ==> S SUBSET K
                                  ==> V = K UNION ((O:A->bool) UNION S)`);
      (* disjoint balls *)
      REWRITE_TAC[ASSUME `IMAGE (\w. (B1:real^3->A) (r0 % w)) (ball(vec 0,&1)) =
                          IMAGE (B1:real^3->A) (ball(vec 0,r0))`;
                  ASSUME `IMAGE (c:real^3->A) (ball(vec 0,&1)) = Os`] THEN
      SUBGOAL_THEN `IMAGE (B1:real^3->A) (ball(vec 0,r0)) SUBSET IMAGE (B1:real^3->A) (cball(vec 0,r0))`
      MP_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[BALL_SUBSET_CBALL]; ALL_TAC] THEN
      UNDISCH_TAC `DISJOINT (IMAGE (B1:real^3->A) (cball(vec 0,r0))) Os` THEN
      MATCH_ACCEPT_TAC(SET_RULE `!K O B. DISJOINT K (O:A->bool) ==> B SUBSET K ==> DISJOINT B O`);
      (* the collar *)
      X_GEN_TAC `x:real^3` THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
      ABBREV_TAC `u:real^3 = inv(norm x) % x` THEN
      SUBGOAL_THEN `(u:real^3) IN sphere(vec 0,&1)` ASSUME_TAC THENL
       [REWRITE_TAC[GSYM(ASSUME `inv(norm x) % x:real^3 = u`)] THEN
        REWRITE_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
        MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `(f1:real^3->real^3) u IN sphere(vec 0,&1) /\ (f1':real^3->real^3)(f1 u) = u`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `sphere_diffeo (f1:real^3->real^3) f1'` THEN REWRITE_TAC[sphere_diffeo] THEN
        ASM_SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `x:real^3 = norm x % u`
        (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [th]) THENL
       [REWRITE_TAC[GSYM(ASSUME `inv(norm x) % x:real^3 = u`); VECTOR_MUL_ASSOC] THEN
        SUBGOAL_THEN `norm(x:real^3) * inv(norm x) = &1` SUBST1_TAC THENL
         [MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[VECTOR_MUL_LID]];
        ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o SPECL [`norm(x:real^3)`; `(f1:real^3->real^3) u`] o check (fun th ->
        is_forall(concl th) && can (find_term (fun t -> t = `f1':real^3->real^3`)) (concl th))) THEN
      REWRITE_TAC[ASSUME `&1 < norm(x:real^3)`; ASSUME `(f1:real^3->real^3) u IN sphere(vec 0,&1)`;
                  ASSUME `(f1':real^3->real^3)((f1:real^3->real^3) u) = u`] THEN
      DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN `norm(inv(norm(x:real^3)) % (f1:real^3->real^3) u) = inv(norm(x:real^3))` ASSUME_TAC THENL
       [REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
        UNDISCH_TAC `(f1:real^3->real^3) u IN sphere(vec 0,&1)` THEN
        SIMP_TAC[IN_SPHERE_0; REAL_MUL_RID];
        ALL_TAC] THEN
      SUBGOAL_THEN `inv(norm(x:real^3)) % (f1:real^3->real^3) u IN annulus (&3 / &4) (&2)` ASSUME_TAC THENL
       [REWRITE_TAC[annulus; IN_ELIM_THM;
                    ASSUME `norm(inv(norm(x:real^3)) % (f1:real^3->real^3) u) = inv(norm(x:real^3))`] THEN
        CONJ_TAC THENL
         [SUBGOAL_THEN `inv(&4 / &3) < inv(norm(x:real^3))` MP_TAC THENL
           [MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC;
            CONV_TAC(LAND_CONV(LAND_CONV REAL_RAT_REDUCE_CONV)) THEN REWRITE_TAC[]];
          MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `&1` THEN
          CONJ_TAC THENL [MATCH_MP_TAC REAL_INV_LT_1 THEN FIRST_ASSUM ACCEPT_TAC; REAL_ARITH_TAC]];
        ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o SPEC `inv(norm(x:real^3)) % (f1:real^3->real^3) u` o check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun t -> t = `annulus (&3 / &4) (&2):real^3->bool`)) (concl th))) THEN
      REWRITE_TAC[ASSUME `inv(norm(x:real^3)) % (f1:real^3->real^3) u IN annulus (&3 / &4) (&2)`;
                  ASSUME `norm(inv(norm(x:real^3)) % (f1:real^3->real^3) u) = inv(norm(x:real^3))`] THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[ASSUME `!w. (N0:real^3->A) w = e1(r0 % w)`; VECTOR_MUL_ASSOC] THEN
      AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      SUBGOAL_THEN `~(norm(x:real^3) = &0)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]]]);;

(* ------------------------------------------------------------------------- *)
(* The growth of A25 (a copy of the region growth of                         *)
(* pc_apx_class, in the context apx_agc: one starting neck,                  *)
(* clean start instead of caps kept away, deep inner side of the start neck). *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* The growth context of A25 (the analogue of apx_rgc of pc_apx_class): the  *)
(* starting necks e k (k in J = {i}) are ep-necks that are also              *)
(* parametrizations of the (2 eps)-neck domain with the inner half of that   *)
(* domain missing the closure of P; instead of keeping all caps away from    *)
(* the e k, only the extended cores up to level 4/ep must miss the middle    *)
(* annuli of the e k (the clean start).                                      *)
(* ------------------------------------------------------------------------- *)

let apx_agc = new_definition
 `apx_agc (top:A topology,atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)
          (C:real) (eps:real) (ep:real) (J:num->bool) (e:num->real^3->A) (P:A->bool) <=>
    apx_rg (top,atlas) g C eps ep J e P /\
    apx_kc * eps = ep /\ &0 < eps /\
    apx_ch_ctx top atlas g ep /\ apx_ch_pair top atlas g ep /\
    apx_ch_more top atlas g ep /\ apx_ch_n4r top atlas g ep /\
    apx_ch_ctx top atlas g eps /\
    apx_cl_rat top atlas g ep /\
    (?i. J = {i}) /\
    (!k. k IN J
         ==> mfd_param top atlas (rfs_neck_dom (&2 * eps)) (e k) /\
             DISJOINT (top closure_of P) (IMAGE (e k) (apx_slab (--inv(&2 * eps)) (&0)))) /\
    (!U bb e' f k. apx_bcap (top,atlas) g C eps U bb e' f /\ k IN J
         ==> DISJOINT (IMAGE (e k) (annulus (&1 / &2) (&2)))
                      (IMAGE (apx_bext bb e' f) (ball(vec 0,exp((&4 * inv ep) / sqrt(&2)))))) /\
    (!U Y p. rfs_cap (top,atlas) g C eps U Y /\ rfs_twisted_chart top atlas p /\
             IMAGE p (annulus (&1 / &4) (&4)) SUBSET U
             ==> DISJOINT U (top closure_of P))`;;

let APX_AGC_SCALES = prove
 (`!top atlas (g:A->real^3^3) C eps ep J (e:num->real^3->A) P.
     apx_agc (top,atlas) g C eps ep J e P
     ==> &0 < ep /\ &0 < eps /\ eps <= ep /\ &580 * eps <= ep /\
         ep <= &1 / &1024 /\ &1024 <= inv ep /\ &1024 * &580 <= inv eps /\
         &580 * inv ep <= inv eps`,
  REPEAT GEN_TAC THEN REWRITE_TAC[apx_agc; apx_rg; apx_ch_ctx] THEN STRIP_TAC THEN
  MP_TAC APX_KC_GE THEN DISCH_TAC THEN
  SUBGOAL_THEN `&580 * eps <= ep` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `apx_kc * eps = ep`)) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1024 <= inv ep` ASSUME_TAC THENL
   [MP_TAC(SPECL [`ep:real`; `&1 / &1024`] REAL_LE_INV2) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&580 * inv ep <= inv eps` ASSUME_TAC THENL
   [SUBGOAL_THEN `inv ep <= inv(&580 * eps)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_INV_MUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let APX_AGC_SING = prove
 (`!top atlas (g:A->real^3^3) C eps ep J (e:num->real^3->A) P i j.
     apx_agc (top,atlas) g C eps ep J e P /\ i IN J /\ j IN J ==> j = i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[apx_agc] THEN STRIP_TAC THEN
  UNDISCH_TAC `(i:num) IN J` THEN UNDISCH_TAC `(j:num) IN J` THEN
  ASM_REWRITE_TAC[IN_SING] THEN MESON_TAC[]);;

let APX_AGC_INIT = prove
 (`!top atlas (g:A->real^3^3) C eps ep J (e:num->real^3->A) P i.
     apx_agc (top,atlas) g C eps ep J e P /\ i IN J
     ==> ?x N. apx_gch (top,atlas) g C eps ep J e P i (&0) x N`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_AGC_SCALES) THEN
  APX_UNFOLD_ASM_TAC "apx_agc" apx_agc THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_RG_PARTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[apx_rg] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_rg")) (concl th))) THEN
  SUBGOAL_THEN `?y. rfs_neck (top,atlas) (g:A->real^3^3) ep y ((e:num->real^3->A) i)`
  (X_CHOOSE_TAC `y:A`) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `rfs_neck (top,atlas) (g:A->real^3^3) ep y ((e:num->real^3->A) i)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1))` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) ep y ((e:num->real^3->A) i)` THEN
    SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`\m:int. (y:A)`; `\m:int. (e:num->real^3->A) i`] THEN
  REWRITE_TAC[apx_gch; INT_LE_REFL] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC APX_SINGLE_CHAIN THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `top closure_of (P:A->bool)`)) THEN
    REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN DISJ2_TAC THEN
    EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`m:int`; `U:A->bool`; `bb:real^3->A`; `e':real^3->A`;
                         `f:real^3->real^3`] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`U:A->bool`; `bb:real^3->A`; `e':real^3->A`;
        `f:real^3->real^3`; `i:num`] o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_bext")) (concl th) &&
      can (find_term (fun t -> t = `annulus (&1 / &2) (&2):real^3->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1)) SUBSET
                  IMAGE (e i) (annulus (&1 / &2) (&2))` MP_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `(y:A) IN IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1))` THEN
    MATCH_ACCEPT_TAC(SET_RULE `!y S A Y. (y:A) IN S ==> S SUBSET A ==> DISJOINT A Y
                                         ==> ~(y IN Y)`);
    MAP_EVERY X_GEN_TAC [`m:int`; `j:num`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `C:real`; `eps:real`; `ep:real`; `J:num->bool`; `e:num->real^3->A`;
                   `P:A->bool`; `i:num`; `j:num`] APX_AGC_SING) THEN
    ASM_REWRITE_TAC[]]);;
let APX_AGC_NOT_COVERED = prove
 (`!top atlas (g:A->real^3^3) C eps ep J (e:num->real^3->A) P i b x N.
     apx_agc (top,atlas) g C eps ep J e P /\ apx_a13_ctx top atlas g ep /\ i IN J /\
     apx_gch (top,atlas) g C eps ep J e P i b x N
     ==> ~(top closure_of P SUBSET apx_chain_union ep {m:int | &0 <= m /\ m <= b} N)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_AGC_SCALES) THEN
  APX_UNFOLD_ASM_TAC "apx_agc" apx_agc THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_RG_PARTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_RG_BASICS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[apx_rg] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_rg")) (concl th))) THEN
  APX_UNFOLD_ASM_TAC "apx_gch" apx_gch THEN
  MP_TAC(snd(EQ_IMP_RULE(SPEC `b:int` INT_OF_NUM_EXISTS))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_THEN `n:num` SUBST_ALL_TAC)] THEN
  (* every other cut sphere would lie in the union *)
  SUBGOAL_THEN `!j:num. j IN J /\ ~(j = i) ==> F` ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(e:num->real^3->A) j (basis 1) IN top closure_of P` MP_TAC THENL
     [FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `top closure_of (P:A->bool)`)) THEN
      REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN DISJ2_TAC THEN
      EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> MP_TAC(MATCH_MP (REWRITE_RULE[SUBSET] (ASSUME
      `top closure_of P SUBSET
       apx_chain_union ep {m:int | &0 <= m /\ m <= &n} (N:int->real^3->A)`)) th)) THEN
    REWRITE_TAC[apx_chain_union; IN_UNIONS; IN_ELIM_THM; NOT_EXISTS_THM] THEN
    X_GEN_TAC `t:A->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `m:int` STRIP_ASSUME_TAC) MP_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`m:int`; `j:num`] o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th) &&
      can (find_term (fun t -> t = `N:int->real^3->A`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `(x:A) IN s ==> DISJOINT t s ==> ~(x IN t)`) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN
    SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  (* the A13 tube *)
  FIRST_ASSUM(MP_TAC o SPECL [`n:num`; `x:int->A`; `N:int->real^3->A`] o
    REWRITE_RULE[apx_a13_ctx] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_a13_ctx")) (concl th))) THEN
  ANTS_TAC THENL
   [FIRST_ASSUM(MP_TAC o REWRITE_RULE[apx_balanced] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_balanced")) (concl th))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `E:real^3->A` (X_CHOOSE_THEN `L:real`
    (X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `f':real^3->real^3`
     STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `IMAGE (E:real^3->A) (sphere(vec 0,&1)) =
                IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1))` ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_EQ THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(N:int->real^3->A) (&0) w` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(w:real^3) IN sphere(vec 0,&1)` THEN
    REWRITE_TAC[IN_SPHERE_0; APX_SLAB_SVAL; apx_sval] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[LOG_1; REAL_MUL_RZERO] THEN CONJ_TAC THENL
     [DISCH_THEN(MP_TAC o AP_TERM `norm:real^3->real`) THEN ASM_REWRITE_TAC[NORM_0] THEN
      REAL_ARITH_TAC;
      MP_TAC(SPEC `ep:real` APX_INV_K) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the frontier of the closure lies in S_i *)
  SUBGOAL_THEN `top frontier_of (top closure_of P) SUBSET
                IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1))` ASSUME_TAC THENL
   [REWRITE_TAC[frontier_of; CLOSURE_OF_CLOSURE_OF] THEN
    SUBGOAL_THEN `(P:A->bool) SUBSET top interior_of (top closure_of P)` MP_TAC THENL
     [MATCH_MP_TAC INTERIOR_OF_MAXIMAL THEN CONJ_TAC THENL
       [MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `top closure_of (P:A->bool)`)) THEN
    REWRITE_TAC[SUBSET; IN_DIFF; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
    DISCH_TAC THEN X_GEN_TAC `q:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC MP_TAC) THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `j:num = i` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  (* N5 *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `E:real^3->A`;
                 `exp(--inv ep / sqrt(&2))`; `exp((L + inv ep) / sqrt(&2))`;
                 `IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1))`;
                 `top closure_of (P:A->bool)`]
                APX_SECTION_NOT_BOUNDING_POS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LE] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [UNDISCH_TAC `mfd_param top atlas (apx_slab (--inv ep) (L + inv ep)) (E:real^3->A)` THEN
      REWRITE_TAC[apx_slab];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `IMAGE (E:real^3->A) (sphere(vec 0,&1))`)) THEN
      MATCH_MP_TAC APX_SECTION_LEVEL THEN REWRITE_TAC[REAL_LT_01] THEN
      SUBGOAL_THEN `&0 < inv ep /\ &0 < sqrt(&2)` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
                        SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LT] THEN
        REWRITE_TAC[real_div; REAL_MUL_LNEG; REAL_NEG_LT0] THEN
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV];
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LT] THEN
        MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC[GSYM apx_slab] THEN
      FIRST_X_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_eq(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_chain_union"))
            (concl th))) THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(P:A->bool) SUBSET top interior_of (top closure_of P)` MP_TAC THENL
   [MATCH_MP_TAC INTERIOR_OF_MAXIMAL THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e:num->real^3->A) i (&4 / &3 % basis 1) IN P` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = `&4 / &3 % basis 1:real^3`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SET_TAC[]);;
let APX_AGC_FRONTIER = prove
 (`!top atlas (g:A->real^3^3) C eps ep J (e:num->real^3->A) P i b x N.
     apx_agc (top,atlas) g C eps ep J e P /\ i IN J /\
     apx_gch (top,atlas) g C eps ep J e P i b x N /\
     ~(top closure_of P SUBSET apx_chain_union ep {m:int | &0 <= m /\ m <= b} N)
     ==> ?z. z IN top closure_of P /\
             ~(z IN apx_chain_union ep {m:int | &0 <= m /\ m <= b} N) /\
             z IN top closure_of (IMAGE (N b) (apx_slab (inv(&2 * ep)) (inv ep)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_AGC_SCALES) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP APX_RG_INNER o C CONJ (ASSUME `(i:num) IN J`) o
    CONJUNCT1 o REWRITE_RULE[apx_agc]) THEN
  APX_UNFOLD_ASM_TAC "apx_agc" apx_agc THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[apx_rg] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_rg")) (concl th))) THEN
  APX_UNFOLD_ASM_TAC "apx_gch" apx_gch THEN
  SUBGOAL_THEN `mfd_param top atlas (rfs_neck_dom (&2 * eps)) ((e:num->real^3->A) i) /\
                DISJOINT (top closure_of P)
                  (IMAGE ((e:num->real^3->A) i) (apx_slab (--inv(&2 * eps)) (&0)))`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `inv ep < inv(&2 * eps) /\ &0 < inv ep` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `apx_chain (top,atlas) (g:A->real^3^3) ep {m:int | &0 <= m /\ m <= b} x N`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o REWRITE_RULE[apx_balanced] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_balanced")) (concl th))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!m. &0 <= m /\ m <= b
                    ==> rfs_neck (top,atlas) (g:A->real^3^3) ep ((x:int->A) m) (N m)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `apx_chain (top,atlas) (g:A->real^3^3) ep {m:int | &0 <= m /\ m <= b} x N` THEN
    REWRITE_TAC[apx_chain; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `U = apx_chain_union ep {m:int | &0 <= m /\ m <= b} (N:int->real^3->A)` THEN
  SUBGOAL_THEN `open_in top (U:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN REWRITE_TAC[apx_chain_union] THEN MATCH_MP_TAC OPEN_IN_UNIONS THEN
    REWRITE_TAC[FORALL_IN_GSPEC; IN_ELIM_THM] THEN X_GEN_TAC `m:int` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `rfs_neck_dom ep`; `(N:int->real^3->A) m`] GRGD_PARAM_FACTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `rfs_neck (top,atlas) (g:A->real^3^3) ep ((x:int->A) m) (N m)` MP_TAC THENL
       [ASM_SIMP_TAC[]; SIMP_TAC[rfs_neck]];
      STRIP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:int->A) (&0) IN U` ASSUME_TAC THENL
   [SUBGOAL_THEN `rfs_neck (top,atlas) (g:A->real^3^3) ep ((x:int->A) (&0))
                    ((N:int->real^3->A) (&0))`
    MP_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[INT_LE_REFL]; ALL_TAC] THEN
    REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
    MP_TAC(SPEC `ep:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    EXPAND_TAC "U" THEN REWRITE_TAC[apx_chain_union; IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `IMAGE ((N:int->real^3->A) (&0)) (rfs_neck_dom ep)` THEN
    CONJ_TAC THENL [EXISTS_TAC `&0:int` THEN ASM_REWRITE_TAC[INT_LE_REFL]; ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `top closure_of (P:A->bool)`; `U:A->bool`]
                CONNECTED_IN_INTER_FRONTIER_OF) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_IN_CLOSURE_OF THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `(x:int->A) (&0)` THEN
      ASM_SIMP_TAC[INT_LE_REFL];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `z:A` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~((z:A) IN U)` ASSUME_TAC THENL
   [UNDISCH_TAC `(z:A) IN top frontier_of U` THEN
    ASM_SIMP_TAC[frontier_of; INTERIOR_OF_OPEN_IN; IN_DIFF];
    ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `ep:real`; `&0:int`; `b:int`; `x:int->A`; `N:int->real^3->A`]
                APX_FIN_FRONTIER) THEN
  ASM_REWRITE_TAC[CLOSURE_OF_UNION] THEN
  DISCH_THEN(MP_TAC o SPEC `z:A` o REWRITE_RULE[SUBSET]) THEN ASM_REWRITE_TAC[IN_UNION] THEN
  MATCH_MP_TAC(TAUT `~p ==> p \/ q ==> q`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(e:num->real^3->A) i`; `&2 * eps`; `--inv ep`; `--inv(&2 * ep)`]
                APX_PARAM_CSLAB_CLOSURE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `ep:real` APX_INV_K) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `{y:real^3 | ~(y = vec 0) /\ --inv ep <= apx_sval y /\
                            apx_sval y <= --inv(&2 * ep)} SUBSET apx_slab (--inv(&2 * eps)) (&0)`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; APX_SLAB_SVAL] THEN X_GEN_TAC `y:real^3` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `ep:real` APX_INV_K) THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `inv(&2 * ep) = inv ep / &2`]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `DISJOINT (top closure_of P)
                 (IMAGE ((e:num->real^3->A) i) (apx_slab (--inv(&2 * eps)) (&0)))` THEN
  UNDISCH_TAC `(z:A) IN top closure_of P` THEN
  UNDISCH_TAC `(z:A) IN top closure_of
                 IMAGE ((e:num->real^3->A) i) (apx_slab (--inv ep) (--inv(&2 * ep)))` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`(e:num->real^3->A) i`;
                 `{y:real^3 | ~(y = vec 0) /\ --inv ep <= apx_sval y /\
                              apx_sval y <= --inv(&2 * ep)}`;
                 `apx_slab (--inv(&2 * eps)) (&0)`] IMAGE_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;
let APX_AGC_CASE_T = prove
 (`!top atlas (g:A->real^3^3) C eps ep J (e:num->real^3->A) P i b x N z
    U (bb:real^3->A) e' f.
     apx_agc (top,atlas) g C eps ep J e P /\ i IN J /\
     apx_gch (top,atlas) g C eps ep J e P i b x N /\
     ~(z IN apx_chain_union ep {m:int | &0 <= m /\ m <= b} N) /\
     z IN top closure_of (IMAGE (N b) (apx_slab (inv(&2 * ep)) (inv ep))) /\
     apx_bcap (top,atlas) g C eps U bb e' f /\
     z IN IMAGE (apx_bext bb e' f) (ball(vec 0,exp((&4 * inv ep) / sqrt(&2))))
     ==> ?yz. yz IN rfs_neck_dom eps /\ z = e' yz /\
              &0 < apx_sval yz /\ apx_sval yz < &4 * inv ep /\
              apx_balanced (top,atlas) g ep {m:int | &0 <= m /\ m <= b + &1}
                (\m. if m = b + &1 then e' yz else x m)
                (\m. if m = b + &1 then apx_rev (apx_cp e' yz) else N m)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_AGC_SCALES) THEN
  APX_UNFOLD_ASM_TAC "apx_agc" apx_agc THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[apx_rg] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_rg")) (concl th))) THEN
  APX_UNFOLD_ASM_TAC "apx_gch" apx_gch THEN
  SUBGOAL_THEN `apx_chain (top,atlas) (g:A->real^3^3) ep {m:int | &0 <= m /\ m <= b} x N`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o REWRITE_RULE[apx_balanced] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_balanced")) (concl th))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_neck (top,atlas) (g:A->real^3^3) ep ((x:int->A) b) (N b)` ASSUME_TAC THENL
   [UNDISCH_TAC `apx_chain (top,atlas) (g:A->real^3^3) ep {m:int | &0 <= m /\ m <= b} x N` THEN
    REWRITE_TAC[apx_chain; IN_ELIM_THM] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[INT_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(z IN IMAGE ((N:int->real^3->A) b) (rfs_neck_dom ep))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `~(z IN apx_chain_union ep {m:int | &0 <= m /\ m <= b} (N:int->real^3->A))` THEN
    REWRITE_TAC[apx_chain_union; IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `IMAGE ((N:int->real^3->A) b) (rfs_neck_dom ep)` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `b:int` THEN ASM_REWRITE_TAC[INT_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((x:int->A) b IN IMAGE (apx_bext (bb:real^3->A) e' f)
                   (ball(vec 0,exp((&4 * inv ep) / sqrt(&2)))))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_bext")) (concl th))) THEN
    EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[INT_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `ep:real`; `U:A->bool`; `bb:real^3->A`;
                 `e':real^3->A`; `f:real^3->real^3`; `(x:int->A) b`;
                 `(N:int->real^3->A) b`; `z:A`] APX_CAP_TRIGGER_GEOM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `yb:real^3` (X_CHOOSE_THEN `yz:real^3` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `yz:real^3` THEN ASM_REWRITE_TAC[] THEN
  (* the copy at z is an ep-neck *)
  SUBGOAL_THEN `rfs_neck (top,atlas) (g:A->real^3^3) ep z (apx_cp (e':real^3->A) yz)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `apx_bcap (top,atlas) (g:A->real^3^3) C eps U bb e' f` THEN
    REWRITE_TAC[apx_bcap] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC APX_CP_NECK THEN MAP_EVERY EXISTS_TAC [`eps:real`; `z':A`] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[APX_DIV34] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `ep:real`; `&0:int`; `b:int`; `x:int->A`; `N:int->real^3->A`; `z:A`;
                 `apx_cp (e':real^3->A) yz`] APX_A18_CORE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ez':real^3->A` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THENL
   [ALL_TAC;
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `z:A = e' (yz:real^3)`)) THEN
    FIRST_ASSUM ACCEPT_TAC] THEN
  (* the forward pair is impossible *)
  MATCH_MP_TAC(TAUT `F ==> p`) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `ep:real`; `b:int`; `x:int->A`; `N:int->real^3->A`; `z:A`;
                 `apx_cp (e':real^3->A) yz`] APX_EXT_LAST_PAIR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `ep:real`; `U:A->bool`; `bb:real^3->A`;
                 `e':real^3->A`; `f:real^3->real^3`; `(x:int->A) b`;
                 `(N:int->real^3->A) b`; `z:A`; `yb:real^3`; `yz:real^3`]
                APX_CAP_NO_FORWARD) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL]);;
let APX_AGC_CASE_N = prove
 (`!top atlas (g:A->real^3^3) C eps ep J (e:num->real^3->A) P i b x N z.
     apx_agc (top,atlas) g C eps ep J e P /\ i IN J /\
     apx_gch (top,atlas) g C eps ep J e P i b x N /\
     z IN top closure_of P /\
     ~(z IN apx_chain_union ep {m:int | &0 <= m /\ m <= b} N) /\
     z IN top closure_of (IMAGE (N b) (apx_slab (inv(&2 * ep)) (inv ep))) /\
     (!U bb e' f. apx_bcap (top,atlas) g C eps U bb e' f
         ==> ~(z IN IMAGE (apx_bext bb e' f) (ball(vec 0,exp((&4 * inv ep) / sqrt(&2))))))
     ==> ?x' N'. apx_gch (top,atlas) g C eps ep J e P i (b + &1) x' N'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_AGC_SCALES) THEN
  APX_UNFOLD_ASM_TAC "apx_agc" apx_agc THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[apx_rg] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_rg")) (concl th))) THEN
  APX_UNFOLD_ASM_TAC "apx_gch" apx_gch THEN
  (* z is the centre of a hypothesis neck *)
  SUBGOAL_THEN `?ez. rfs_neck (top,atlas) (g:A->real^3^3) eps z ez`
  (X_CHOOSE_TAC `ez:real^3->A`) THENL
   [FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(z:A) IN top closure_of P`) o check (fun th ->
      is_forall (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_neck_or_core")) (concl th))) THEN
    REWRITE_TAC[apx_neck_or_core] THEN
    DISCH_THEN(DISJ_CASES_THEN2 ACCEPT_TAC MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `Y:A->bool` STRIP_ASSUME_TAC)) THEN
    MATCH_MP_TAC(TAUT `F ==> p`) THEN
    FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP APX_CAP_CASES) THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `bb:real^3->A` (X_CHOOSE_THEN `e':real^3->A`
        (X_CHOOSE_THEN `f:real^3->real^3` STRIP_ASSUME_TAC))) THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`U:A->bool`; `bb:real^3->A`; `e':real^3->A`;
                                    `f:real^3->real^3`] o check (fun th ->
        is_forall (concl th) && can (find_term (fun t -> t = `z:A`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_bext")) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(z:A) IN Y` THEN ASM_REWRITE_TAC[IN_IMAGE; IN_BALL_0] THEN
      DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `w:real^3` THEN ASM_REWRITE_TAC[apx_bext] THEN
      SUBGOAL_THEN `norm(w:real^3) < &2` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LT] THEN
      MATCH_MP_TAC REAL_LT_DIV THEN SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH] THEN
      ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(X_CHOOSE_THEN `p:real^3->A` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`U:A->bool`; `Y:A->bool`; `p:real^3->A`] o check (fun th ->
        is_forall (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_twisted_chart"))
            (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`]
                    APX_CAP_CORE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      SUBGOAL_THEN `(Y:A->bool) SUBSET top closure_of Y` MP_TAC THENL
       [MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_SIMP_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
      UNDISCH_TAC `top closure_of Y SUBSET (U:A->bool)` THEN
      UNDISCH_TAC `DISJOINT (U:A->bool) (top closure_of P)` THEN
      UNDISCH_TAC `(z:A) IN Y` THEN UNDISCH_TAC `(z:A) IN top closure_of P` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_neck (top,atlas) (g:A->real^3^3) ep z ez` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_NECK_MONO_GEN THEN EXISTS_TAC `eps:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `ep:real`; `&0:int`; `b:int`; `x:int->A`; `N:int->real^3->A`; `z:A`;
                 `ez:real^3->A`] APX_A18_CORE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ez':real^3->A` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `rfs_neck (top,atlas) (g:A->real^3^3) ep z ez'` ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (fun th ->
      concl th = `ez' = (ez:real^3->A) \/ ez' = apx_rev ez`)) THEN
    ASM_SIMP_TAC[APX_REV_NECK];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`\m:int. if m = b + &1 then (z:A) else x m`;
                        `\m:int. if m = b + &1 then (ez':real^3->A) else N m`] THEN
  MATCH_MP_TAC APX_GCH_EXTEND THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `ep:real`; `J:num->bool`; `e:num->real^3->A`;
                 `P:A->bool`; `i:num`; `j:num`] APX_AGC_SING) THEN
  ASM_REWRITE_TAC[]);;
let APX_AGC_STEP = prove
 (`!top atlas (g:A->real^3^3) C eps ep J (e:num->real^3->A) P i b x N.
     apx_agc (top,atlas) g C eps ep J e P /\ i IN J /\
     apx_gch (top,atlas) g C eps ep J e P i b x N /\
     ~(top closure_of P SUBSET apx_chain_union ep {m:int | &0 <= m /\ m <= b} N)
     ==> (?U bb e' f yz. apx_bcap (top,atlas) g C eps U bb e' f /\
            yz IN rfs_neck_dom eps /\ e' yz IN top closure_of P /\
            &0 < apx_sval yz /\ apx_sval yz < &4 * inv ep /\
            apx_balanced (top,atlas) g ep {m:int | &0 <= m /\ m <= b + &1}
              (\m. if m = b + &1 then e' yz else x m)
              (\m. if m = b + &1 then apx_rev (apx_cp e' yz) else N m)) \/
         (?x' N'. apx_gch (top,atlas) g C eps ep J e P i (b + &1) x' N')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL APX_AGC_FRONTIER) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `?U bb e' f. apx_bcap (top,atlas) (g:A->real^3^3) C eps U bb e' f /\
                   (z:A) IN IMAGE (apx_bext bb e' f)
                              (ball(vec 0,exp((&4 * inv ep) / sqrt(&2))))` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `bb:real^3->A`
      (X_CHOOSE_THEN `e':real^3->A` (X_CHOOSE_THEN `f:real^3->real^3` STRIP_ASSUME_TAC)))) THEN
    DISJ1_TAC THEN
    MAP_EVERY EXISTS_TAC [`U:A->bool`; `bb:real^3->A`; `e':real^3->A`; `f:real^3->real^3`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `C:real`; `eps:real`; `ep:real`; `J:num->bool`;
                   `e:num->real^3->A`; `P:A->bool`; `i:num`; `b:int`; `x:int->A`;
                   `N:int->real^3->A`; `z:A`; `U:A->bool`; `bb:real^3->A`;
                   `e':real^3->A`; `f:real^3->real^3`] APX_AGC_CASE_T) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `yz:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `yz:real^3` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(z:A) IN top closure_of P` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!U bb e' f. apx_bcap (top,atlas) (g:A->real^3^3) C eps U bb e' f
                            ==> ~((z:A) IN IMAGE (apx_bext bb e' f)
                                    (ball(vec 0,exp((&4 * inv ep) / sqrt(&2)))))`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISJ2_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `ep:real`; `J:num->bool`;
                 `e:num->real^3->A`; `P:A->bool`; `i:num`; `b:int`; `x:int->A`;
                 `N:int->real^3->A`; `z:A`] APX_AGC_CASE_N) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]);;
let APX_AGC_GROW = prove
 (`!top atlas (g:A->real^3^3) C eps ep J (e:num->real^3->A) P i.
     apx_agc (top,atlas) g C eps ep J e P /\ apx_a13_ctx top atlas g ep /\ i IN J
     ==> ?b x N. apx_gch (top,atlas) g C eps ep J e P i b x N /\
                 ((?U bb e' f yz. apx_bcap (top,atlas) g C eps U bb e' f /\
                     yz IN rfs_neck_dom eps /\ e' yz IN top closure_of P /\
                     &0 < apx_sval yz /\
                     apx_sval yz < &4 * inv ep /\
                     apx_balanced (top,atlas) g ep {m:int | &0 <= m /\ m <= b + &1}
                       (\m. if m = b + &1 then e' yz else x m)
                       (\m. if m = b + &1 then apx_rev (apx_cp e' yz) else N m)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `apx_ch_ctx top atlas (g:A->real^3^3) ep /\
                compact_in top (top closure_of (P:A->bool))` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `apx_agc (top,atlas) (g:A->real^3^3) C eps ep J (e:num->real^3->A) P` THEN
    REWRITE_TAC[apx_agc; apx_rg] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `ep:real`; `top closure_of (P:A->bool)`] APX_CHAIN_CARD_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `NB:num` (LABEL_TAC "bd")) THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_THEN(LABEL_TAC "ns") THEN
  SUBGOAL_THEN
   `!n. ?b x (N:int->real^3->A).
          apx_gch (top,atlas) (g:A->real^3^3) C eps ep J (e:num->real^3->A) P i b x N /\
          n <= CARD {m:int | &0 <= m /\ m <= b}`
  MP_TAC THENL
   [INDUCT_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `C:real`; `eps:real`; `ep:real`;
                     `J:num->bool`; `e:num->real^3->A`; `P:A->bool`; `i:num`] APX_AGC_INIT) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `x:int->A` (X_CHOOSE_TAC `N:int->real^3->A`)) THEN
      MAP_EVERY EXISTS_TAC [`&0:int`; `x:int->A`; `N:int->real^3->A`] THEN
      ASM_REWRITE_TAC[LE_0];
      ALL_TAC] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `b:int` (X_CHOOSE_THEN `x:int->A`
      (X_CHOOSE_THEN `N:int->real^3->A` STRIP_ASSUME_TAC))) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `C:real`; `eps:real`; `ep:real`;
                   `J:num->bool`; `e:num->real^3->A`; `P:A->bool`; `i:num`; `b:int`;
                   `x:int->A`; `N:int->real^3->A`] APX_AGC_NOT_COVERED) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `C:real`; `eps:real`; `ep:real`;
                   `J:num->bool`; `e:num->real^3->A`; `P:A->bool`; `i:num`; `b:int`;
                   `x:int->A`; `N:int->real^3->A`] APX_AGC_STEP) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC MP_TAC) THENL
     [USE_THEN "ns" MP_TAC THEN MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
      MAP_EVERY EXISTS_TAC [`b:int`; `x:int->A`; `N:int->real^3->A`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x':int->A` (X_CHOOSE_TAC `N':int->real^3->A`)) THEN
    MAP_EVERY EXISTS_TAC [`b + &1:int`; `x':int->A`; `N':int->real^3->A`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0:int <= b` ASSUME_TAC THENL
     [UNDISCH_TAC `apx_gch (top,atlas) (g:A->real^3^3) C eps ep J (e:num->real^3->A) P i b x N` THEN
      SIMP_TAC[apx_gch];
      ALL_TAC] THEN
    ASM_SIMP_TAC[APX_INT_SEG_CARD_TOP] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `SUC NB`) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:int` (X_CHOOSE_THEN `x:int->A`
    (X_CHOOSE_THEN `N:int->real^3->A` STRIP_ASSUME_TAC))) THEN
  USE_THEN "bd" (MP_TAC o SPECL [`{m:int | &0 <= m /\ m <= b}`; `x:int->A`;
                                 `N:int->real^3->A`]) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `apx_gch (top,atlas) (g:A->real^3^3) C eps ep J (e:num->real^3->A) P i b x N` THEN
    REWRITE_TAC[apx_gch; apx_balanced; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The cap stop of the A25 growth (a copy of APX_RG_CAP_FINAL                *)
(* with the clean start in place of the cap condition) and two balls from a  *)
(* capped product (the construction of APX_GLUE_CAPPED).                     *)
(* ------------------------------------------------------------------------- *)

let APX_AGC_CAP_FINAL = prove
 (`!top atlas (g:A->real^3^3) C eps ep J (e:num->real^3->A) P i b x N U
    (bb:real^3->A) e' fU yz.
     apx_agc (top,atlas) g C eps ep J e P /\ apx_a13_ctx top atlas g ep /\ i IN J /\
     apx_gch (top,atlas) g C eps ep J e P i b x N /\
     apx_bcap (top,atlas) g C eps U bb e' fU /\
     yz IN rfs_neck_dom eps /\ e' yz IN top closure_of P /\
     &0 < apx_sval yz /\ apx_sval yz < &4 * inv ep /\
     apx_balanced (top,atlas) g ep {m:int | &0 <= m /\ m <= b + &1}
       (\m. if m = b + &1 then e' yz else x m)
       (\m. if m = b + &1 then apx_rev (apx_cp e' yz) else N m)
     ==> ?E L f f' b2. &1 < L /\ sphere_diffeo f f' /\
           mfd_param top atlas (annulus (&1) L) E /\
           (!x. x IN annulus (&1) (&3 / &2) ==> E x = e i x) /\
           (!x. x IN annulus (L / &2) L ==> E x = b2((L / norm x) % f(inv(norm x) % x))) /\
           mfd_ball_chart top atlas b2 /\
           P = IMAGE E (annulus (&1) L) UNION IMAGE b2 (cball(vec 0,&1)) /\
           DISJOINT (IMAGE E (annulus (&1) L)) (IMAGE b2 (cball(vec 0,&1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_AGC_SCALES) THEN
  SUBGOAL_THEN `apx_rg (top,atlas) (g:A->real^3^3) C eps ep J (e:num->real^3->A) P`
  ASSUME_TAC THENL
   [UNDISCH_TAC `apx_agc (top,atlas) (g:A->real^3^3) C eps ep J (e:num->real^3->A) P` THEN
    SIMP_TAC[apx_agc];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_RG_BASICS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_RG_PARTS) THEN
  SUBGOAL_THEN `?fU'. sphere_diffeo (fU:real^3->real^3) fU'` (X_CHOOSE_TAC `fU':real^3->real^3`)
  THENL [ASM_MESON_TAC[apx_bcap]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (e':real^3->A) (rfs_neck_dom eps) SUBSET U` ASSUME_TAC THENL
   [ASM_MESON_TAC[apx_bcap]; ALL_TAC] THEN
  APX_UNFOLD_ASM_TAC "apx_agc" apx_agc THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[apx_rg] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_rg")) (concl th))) THEN
  APX_UNFOLD_ASM_TAC "apx_gch" apx_gch THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `ep:real`; `b:int`; `x:int->A`; `N:int->real^3->A`;
                 `(e':real^3->A) yz`; `e':real^3->A`; `yz:real^3`]
                APX_STOP_TUBE_REV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `E:real^3->A` (X_CHOOSE_THEN `L0:real`
    (X_CHOOSE_THEN `f0:real^3->real^3` (X_CHOOSE_THEN `f0':real^3->real^3`
     STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`e':real^3->A`; `yz:real^3`; `eps:real`] APX_CP_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < inv ep /\ &128 <= inv(&8 * ep) /\ &0 < sqrt(&2) /\
                inv(&2 * ep) = inv ep / &2 /\ inv(&8 * ep) = inv ep / &8`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `ep:real` APX_INV_K) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * norm(yz:real^3) <= exp(inv eps / sqrt(&2))` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `exp(apx_sval(yz:real^3) / sqrt(&2)) = norm yz`)) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `exp(inv ep / sqrt(&2)) * exp(apx_sval(yz:real^3) / sqrt(&2))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      MATCH_MP_TAC APX_EXP_HALF_GE2 THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_EXP_ADD; REAL_EXP_MONO_LE] THEN
      REWRITE_TAC[real_div; GSYM REAL_ADD_RDISTRIB] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `U:A->bool`; `bb:real^3->A`; `e':real^3->A`;
                 `fU:real^3->real^3`; `fU':real^3->real^3`; `yz:real^3`]
                APX_BCAP_SCALED_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `DISJOINT (IMAGE ((e:num->real^3->A) i) (annulus (&1 / &2) (&2)))
                 (IMAGE (\w. apx_bext (bb:real^3->A) e' fU (norm(yz:real^3) % w))
                        (cball(vec 0,&1)))` ASSUME_TAC THENL
   [REWRITE_TAC[ASSUME `IMAGE (\w. apx_bext (bb:real^3->A) e' fU (norm(yz:real^3) % w))
                               (cball(vec 0,&1)) =
                        IMAGE (apx_bext bb e' fU) (cball(vec 0,norm yz))`] THEN
    MATCH_MP_TAC(SET_RULE `!A Y Z. DISJOINT (A:A->bool) Y /\ Z SUBSET Y ==> DISJOINT A Z`) THEN
    EXISTS_TAC `IMAGE (apx_bext (bb:real^3->A) e' fU)
                      (ball(vec 0,exp((&4 * inv ep) / sqrt(&2))))` THEN
    CONJ_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_bext")) (concl th) &&
        can (find_term (fun t -> t = `annulus (&1 / &2) (&2):real^3->bool`)) (concl th))) THEN
      EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN
      GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH `b < c ==> x <= b ==> x < c`) THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `exp(apx_sval(yz:real^3) / sqrt(&2)) = norm yz`)) THEN
      REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_SIMP_TAC[REAL_LT_DIV2_EQ]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1)) SUBSET
                IMAGE (e i) (annulus (&1 / &2) (&2))` ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `LL = exp(L0 / sqrt(&2))` THEN
  SUBGOAL_THEN `&1 <= LL /\ &0 < LL /\ &2 * exp((L0 - inv(&8 * ep)) / sqrt(&2)) <= LL /\
                LL < exp((L0 + inv ep) / sqrt(&2)) /\
                &2 <= exp(inv(&8 * ep) / sqrt(&2)) /\ exp(--inv ep / sqrt(&2)) < &1`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "LL" THEN REPEAT CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_EXP_POS_LT];
      SUBGOAL_THEN `exp(L0 / sqrt(&2)) =
                    exp((L0 - inv(&8 * ep)) / sqrt(&2)) * exp(inv(&8 * ep) / sqrt(&2))`
      SUBST1_TAC THENL
       [REWRITE_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN
        UNDISCH_TAC `&0 < sqrt(&2)` THEN CONV_TAC REAL_FIELD;
        ALL_TAC] THEN
      GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      MATCH_MP_TAC APX_EXP_HALF_GE2 THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_SIMP_TAC[REAL_LT_DIV2_EQ] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC APX_EXP_HALF_GE2 THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LT] THEN
      REWRITE_TAC[real_div; REAL_MUL_LNEG; REAL_NEG_LT0] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV]];
    ALL_TAC] THEN
  SUBGOAL_THEN `annulus (&1) (&3 / &2) SUBSET apx_slab (--inv ep) (inv(&8 * ep)) /\
                sphere(vec 0:real^3,&1) SUBSET apx_slab (--inv ep) (inv(&8 * ep)) /\
                annulus (LL / &2) LL SUBSET apx_slab (L0 - inv(&8 * ep)) (L0 + inv ep) /\
                sphere(vec 0:real^3,LL) SUBSET apx_slab (L0 - inv(&8 * ep)) (L0 + inv ep) /\
                annulus (&1) LL = apx_slab (&0) L0 /\
                apx_slab (&0) L0 SUBSET apx_slab (--inv ep) (L0 + inv ep) /\
                sphere(vec 0:real^3,&1) SUBSET apx_slab (--inv ep) (L0 + inv ep) /\
                sphere(vec 0:real^3,LL) SUBSET apx_slab (--inv ep) (L0 + inv ep)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `(L0 - inv(&8 * ep)) / sqrt(&2)` REAL_EXP_POS_LT) THEN DISCH_TAC THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[apx_slab; SUBSET; annulus; IN_ELIM_THM] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[apx_slab; SUBSET; annulus; IN_ELIM_THM; IN_SPHERE_0] THEN
      GEN_TAC THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[apx_slab; SUBSET; annulus; IN_ELIM_THM] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[apx_slab; SUBSET; annulus; IN_ELIM_THM; IN_SPHERE_0] THEN
      GEN_TAC THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "LL" THEN REWRITE_TAC[apx_slab; real_div; REAL_MUL_LZERO; REAL_EXP_0];
      MATCH_MP_TAC APX_SLAB_SUBSET THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[apx_slab; SUBSET; annulus; IN_ELIM_THM; IN_SPHERE_0] THEN GEN_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `a < &1 /\ &1 < b ==> (x = &1 ==> a < x /\ x < b)`) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC `&2` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(inv(&8 * ep) / sqrt(&2))` THEN
      ASM_REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[apx_slab; SUBSET; annulus; IN_ELIM_THM; IN_SPHERE_0] THEN GEN_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `a < LL /\ LL < b ==> (x = LL ==> a < x /\ x < b)`) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&1` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN apx_slab (L0 - inv(&8 * ep)) (L0 + inv ep)
                    ==> (E:real^3->A) y = apx_cp e' yz ((LL / norm y) %
                                            (f0:real^3->real^3)(inv(norm y) % y))`
  (LABEL_TAC "end") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME
      `(y:real^3) IN apx_slab (L0 - inv(&8 * ep)) (L0 + inv ep)`) o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `norm(yz:real^3)`)) (concl th) &&
      can (find_term (fun t -> t = `E:real^3->A`)) (concl th))) THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[VECTOR_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (E:real^3->A) (sphere(vec 0,&1)) =
                IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1)) /\
                IMAGE (E:real^3->A) (sphere(vec 0,LL)) = IMAGE (e':real^3->A) (sphere(vec 0,norm(yz:real^3)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_EQ THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
      MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(N:int->real^3->A) (&0) w` THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      MP_TAC(ISPECL [`E:real^3->A`; `apx_cp (e':real^3->A) yz`; `f0:real^3->real^3`;
                     `f0':real^3->real^3`; `LL:real`; `L0 - inv(&8 * ep)`; `L0 + inv ep`]
                    APX_END_SPHERE_IMAGE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[apx_cp; IMAGE_o] THEN
      SUBGOAL_THEN `&0 < norm(yz:real^3)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[GSYM(REWRITE_RULE[VECTOR_MUL_RZERO; REAL_MUL_RID]
        (ISPECL [`vec 0:real^3`; `&1`] (MATCH_MP SPHERE_SCALING
          (ASSUME `&0 < norm(yz:real^3)`))))]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 < LL` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&1 <= x /\ ~(x = &1) ==> &1 < x`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1)) SUBSET
                  IMAGE (\w. apx_bext (bb:real^3->A) e' fU (norm(yz:real^3) % w))
                        (cball(vec 0,&1))` MP_TAC THENL
     [UNDISCH_TAC `IMAGE (E:real^3->A) (sphere(vec 0,&1)) =
                   IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1))` THEN
      UNDISCH_TAC `IMAGE (E:real^3->A) (sphere(vec 0,LL)) =
                   IMAGE (e':real^3->A) (sphere(vec 0,norm(yz:real^3)))` THEN
      FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> concl th = `LL = &1`)) THEN
      DISCH_THEN SUBST1_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `IMAGE (\w. apx_bext (bb:real^3->A) e' fU (norm(yz:real^3) % w))
                               (sphere(vec 0,&1))`)) THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; IN_SPHERE_0; IN_CBALL_0] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(e:num->real^3->A) i (basis 1) IN IMAGE (e i) (sphere(vec 0,&1))` MP_TAC
    THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH];
      ALL_TAC] THEN
    UNDISCH_TAC `IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1)) SUBSET
                 IMAGE (e i) (annulus (&1 / &2) (&2))` THEN
    UNDISCH_TAC `DISJOINT (IMAGE ((e:num->real^3->A) i) (annulus (&1 / &2) (&2)))
                 (IMAGE (\w. apx_bext (bb:real^3->A) e' fU (norm(yz:real^3) % w))
                        (cball(vec 0,&1)))` THEN
    MATCH_ACCEPT_TAC(SET_RULE `!A B S x. DISJOINT (A:A->bool) B ==> S SUBSET A ==>
                                         (x:A) IN S ==> S SUBSET B ==> F`);
    ALL_TAC] THEN
  ABBREV_TAC `Q1 = IMAGE (E:real^3->A) (annulus (&1) LL)` THEN
  SUBGOAL_THEN `DISJOINT (Q1:A->bool) (IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1))) /\
                DISJOINT Q1 (IMAGE (e':real^3->A) (sphere(vec 0,norm(yz:real^3))))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Q1" THEN
    REWRITE_TAC[GSYM(ASSUME `IMAGE (E:real^3->A) (sphere(vec 0,&1)) =
                             IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1))`);
                GSYM(ASSUME `IMAGE (E:real^3->A) (sphere(vec 0,LL)) =
                             IMAGE (e':real^3->A) (sphere(vec 0,norm(yz:real^3)))`)] THEN
    CONJ_TAC THEN MATCH_MP_TAC APX_PARAM_IMAGE_DISJOINT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `apx_slab (--inv ep) (L0 + inv ep)`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; annulus; IN_SPHERE_0;
                IN_ELIM_THM] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!j. j IN J /\ ~(j = i)
                    ==> DISJOINT (Q1:A->bool) (IMAGE ((e:num->real^3->A) j) (sphere(vec 0,&1)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `C:real`; `eps:real`; `ep:real`; `J:num->bool`; `e:num->real^3->A`;
                   `P:A->bool`; `i:num`; `j:num`] APX_AGC_SING) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?r0. &1 < r0 /\ r0 < &3 / &2 /\ r0 < LL` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `(&1 + min LL (&3 / &2)) / &2` THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(E:real^3->A) (r0 % basis 1) IN Q1 /\ (E:real^3->A) (r0 % basis 1) IN P`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `r0 % basis 1:real^3 IN annulus (&1) LL /\
                  r0 % basis 1:real^3 IN annulus (&1) (&3 / &2)` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[annulus; IN_ELIM_THM; NORM_MUL] THEN
      SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "Q1" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(E:real^3->A) (r0 % basis 1) = (e:num->real^3->A) i (r0 % basis 1)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(N:int->real^3->A) (&0) (r0 % basis 1)` THEN
      CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(i:num) IN J`) o check (fun th ->
      is_forall (concl th) &&
      can (find_term (fun t -> t = `annulus (&1) (&2):real^3->bool`)) (concl th) &&
      can (find_term (fun t -> t = `P:A->bool`)) (concl th))) THEN
    MATCH_MP_TAC(SET_RULE `(x:A) IN B ==> P INTER A = B ==> x IN P`) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[annulus; IN_ELIM_THM; NORM_MUL] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(Q1:A->bool) SUBSET P /\
                IMAGE (\w. apx_bext (bb:real^3->A) e' fU (norm(yz:real^3) % w))
                      (cball(vec 0,&1)) SUBSET P` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "connected_in")) (concl th))) THEN
      REPEAT CONJ_TAC THENL
       [EXPAND_TAC "Q1" THEN MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
        MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`;
                              `apx_slab (--inv ep) (L0 + inv ep)`] THEN
        ASM_REWRITE_TAC[APX_CONNECTED_ANNULUS3];
        REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
        EXISTS_TAC `(E:real^3->A) (r0 % basis 1)` THEN ASM_REWRITE_TAC[];
        X_GEN_TAC `j:num` THEN DISCH_TAC THEN
        ASM_CASES_TAC `j:num = i` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      SUBGOAL_THEN `(e':real^3->A) yz IN
                    IMAGE (\w. apx_bext (bb:real^3->A) e' fU (norm(yz:real^3) % w))
                          (cball(vec 0,&1))` ASSUME_TAC THENL
       [SUBGOAL_THEN `IMAGE (\w. apx_bext (bb:real^3->A) e' fU (norm(yz:real^3) % w))
                            (sphere(vec 0,&1)) SUBSET
                      IMAGE (\w. apx_bext bb e' fU (norm yz % w)) (cball(vec 0,&1))` MP_TAC THENL
         [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; IN_SPHERE_0; IN_CBALL_0] THEN
          REAL_ARITH_TAC;
          ALL_TAC] THEN
        REWRITE_TAC[ASSUME `IMAGE (\w. apx_bext (bb:real^3->A) e' fU (norm(yz:real^3) % w))
                                  (sphere(vec 0,&1)) =
                            IMAGE e' (sphere(vec 0,norm yz))`; SUBSET] THEN
        DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_SPHERE_0];
        ALL_TAC] THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "connected_in")) (concl th))) THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
        MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `ball(vec 0:real^3,&2)`] THEN
        REWRITE_TAC[CONNECTED_CBALL; SUBSET; IN_CBALL_0; IN_BALL_0] THEN
        CONJ_TAC THENL [ASM_MESON_TAC[mfd_ball_chart]; REAL_ARITH_TAC];
        REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
        EXISTS_TAC `(e':real^3->A) yz` THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        UNDISCH_TAC `(e':real^3->A) yz IN top closure_of P` THEN
        FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_eq(concl th) &&
          lhs(concl th) = `top closure_of (P:A->bool)`)) THEN
        REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
        DISCH_THEN(DISJ_CASES_THEN2 ACCEPT_TAC (X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC)) THEN
        SUBGOAL_THEN `k:num = i` SUBST_ALL_TAC THENL
         [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                         `g:A->real^3^3`; `C:real`; `eps:real`; `ep:real`; `J:num->bool`;
                         `e:num->real^3->A`; `P:A->bool`; `i:num`; `k:num`] APX_AGC_SING) THEN
          ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        MATCH_MP_TAC(TAUT `F ==> p`) THEN
        UNDISCH_TAC `(e':real^3->A) yz IN IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1))` THEN
        UNDISCH_TAC `IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1)) SUBSET
                     IMAGE (e i) (annulus (&1 / &2) (&2))` THEN
        UNDISCH_TAC `(e':real^3->A) yz IN
                     IMAGE (\w. apx_bext (bb:real^3->A) e' fU (norm(yz:real^3) % w))
                           (cball(vec 0,&1))` THEN
        UNDISCH_TAC `DISJOINT (IMAGE ((e:num->real^3->A) i) (annulus (&1 / &2) (&2)))
                     (IMAGE (\w. apx_bext (bb:real^3->A) e' fU (norm(yz:real^3) % w))
                            (cball(vec 0,&1)))` THEN
        MATCH_ACCEPT_TAC(SET_RULE `!A B S x. DISJOINT (A:A->bool) B ==> (x:A) IN B ==>
                                             S SUBSET A ==> x IN S ==> F`);
        X_GEN_TAC `k:num` THEN DISCH_TAC THEN
        SUBGOAL_THEN `k:num = i` SUBST1_TAC THENL
         [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                         `g:A->real^3^3`; `C:real`; `eps:real`; `ep:real`; `J:num->bool`;
                         `e:num->real^3->A`; `P:A->bool`; `i:num`; `k:num`] APX_AGC_SING) THEN
          ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        UNDISCH_TAC `IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1)) SUBSET
                     IMAGE (e i) (annulus (&1 / &2) (&2))` THEN
        UNDISCH_TAC `DISJOINT (IMAGE ((e:num->real^3->A) i) (annulus (&1 / &2) (&2)))
                     (IMAGE (\w. apx_bext (bb:real^3->A) e' fU (norm(yz:real^3) % w))
                            (cball(vec 0,&1)))` THEN
        MATCH_ACCEPT_TAC(SET_RULE `!A B S. DISJOINT (A:A->bool) B ==> S SUBSET A ==>
                                           DISJOINT B S`)]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < L0` ASSUME_TAC THENL
   [UNDISCH_TAC `&1 < LL` THEN EXPAND_TAC "LL" THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM REAL_EXP_0] THEN
    REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_MUL_LZERO];
    ALL_TAC] THEN
  ABBREV_TAC `t0 = L0 - min L0 (inv(&8 * ep)) / &2` THEN
  SUBGOAL_THEN `&0 < t0 /\ t0 < L0 /\ L0 - inv(&8 * ep) < t0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`t0:real`; `&1`] APX_SVAL_SCALED_BASIS) THEN
  REWRITE_TAC[REAL_LT_01; VECTOR_MUL_LID; LOG_1; REAL_MUL_RZERO; REAL_ADD_RID] THEN
  ABBREV_TAC `y0 = exp(t0 / sqrt(&2)) % basis 1:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `norm(y0:real^3) = exp(t0 / sqrt(&2))` ASSUME_TAC THENL
   [EXPAND_TAC "y0" THEN SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
    REWRITE_TAC[REAL_ABS_EXP];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y0:real^3) IN annulus (&1) LL /\
                y0 IN apx_slab (L0 - inv(&8 * ep)) (L0 + inv ep)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[APX_SLAB_SVAL] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(inv(norm y0) % y0:real^3) IN sphere(vec 0,&1) /\
                (f0:real^3->real^3)(inv(norm y0) % y0) IN sphere(vec 0,&1)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
      MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[NORM_EQ_0];
      UNDISCH_TAC `sphere_diffeo (f0:real^3->real^3) f0'` THEN
      REWRITE_TAC[sphere_diffeo] THEN MESON_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `w0 = norm(yz:real^3) % (LL / norm(y0:real^3)) %
                   (f0:real^3->real^3)(inv(norm y0) % y0)` THEN
  SUBGOAL_THEN `~(w0:real^3 = vec 0) /\
                apx_sval w0 = apx_sval(yz:real^3) + L0 - t0` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < norm(yz:real^3) /\ &0 < norm(y0:real^3) /\
                  norm(w0:real^3) = norm(yz:real^3) * (LL / norm(y0:real^3))`
    STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_EXP_POS_LT] THEN
      EXPAND_TAC "w0" THEN REWRITE_TAC[NORM_MUL; REAL_ABS_NORM] THEN
      UNDISCH_TAC `(f0:real^3->real^3)(inv(norm y0) % y0) IN sphere(vec 0,&1)` THEN
      REWRITE_TAC[IN_SPHERE_0] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[REAL_MUL_RID; REAL_ABS_DIV; REAL_ABS_NORM] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < norm(w0:real^3)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT];
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[GSYM NORM_POS_LT]; ALL_TAC] THEN
    REWRITE_TAC[apx_sval] THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[LOG_MUL; LOG_DIV; REAL_LT_DIV; REAL_EXP_POS_LT; LOG_EXP] THEN
    SUBGOAL_THEN `log LL = L0 / sqrt(&2)` SUBST1_TAC THENL
     [EXPAND_TAC "LL" THEN REWRITE_TAC[LOG_EXP]; ALL_TAC] THEN
    UNDISCH_TAC `&0 < sqrt(&2)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `(E:real^3->A) y0 IN Q1` ASSUME_TAC THENL
   [EXPAND_TAC "Q1" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(E:real^3->A) y0 = e' (w0:real^3) /\ (w0:real^3) IN rfs_neck_dom eps`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "end" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
        `(y0:real^3) IN apx_slab (L0 - inv(&8 * ep)) (L0 + inv ep)`)]) THEN
      EXPAND_TAC "w0" THEN REWRITE_TAC[apx_cp; o_THM];
      ASM_REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((E:real^3->A) y0 IN
                  IMAGE (apx_bext (bb:real^3->A) e' fU) (cball(vec 0,norm(yz:real^3))))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `C:real`; `eps:real`; `U:A->bool`; `bb:real^3->A`; `e':real^3->A`;
                   `fU:real^3->real^3`; `(apx_sval(yz:real^3) + apx_sval(w0:real^3)) / &2`;
                   `w0:real^3`] APX_BEXT_LEVELS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(apx_sval(w0:real^3) < (apx_sval(yz:real^3) + apx_sval w0) / &2)`
    (fun th -> REWRITE_TAC[th]) THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `(s:A->bool) SUBSET t ==> ~(x IN t) ==> ~(x IN s)`) THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN
    GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH `b < c ==> x <= b ==> x < c`) THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `exp(apx_sval(yz:real^3) / sqrt(&2)) = norm yz`)) THEN
    REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_SIMP_TAC[REAL_LT_DIV2_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `\w. apx_bext (bb:real^3->A) e' fU (norm(yz:real^3) % w)`; `&2`; `&1`]
                APX_PARAM_BALL_FRONTIER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `mfd_ball_chart top atlas
                  (\w. apx_bext (bb:real^3->A) e' fU (norm(yz:real^3) % w))` THEN
    SIMP_TAC[mfd_ball_chart] THEN REAL_ARITH_TAC;
    STRIP_TAC] THEN
  SUBGOAL_THEN `IMAGE (\w. apx_bext (bb:real^3->A) e' fU (norm(yz:real^3) % w))
                      (cball(vec 0,&1)) =
                IMAGE (\w. apx_bext bb e' fU (norm yz % w)) (ball(vec 0,&1)) UNION
                IMAGE (e':real^3->A) (sphere(vec 0,norm yz))` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM BALL_UNION_SPHERE; IMAGE_UNION] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (Q1:A->bool)
                  (IMAGE (\w. apx_bext (bb:real^3->A) e' fU (norm(yz:real^3) % w))
                         (cball(vec 0,&1)))` ASSUME_TAC THENL
   [SUBGOAL_THEN `(Q1:A->bool) INTER
                  IMAGE (\w. apx_bext (bb:real^3->A) e' fU (norm(yz:real^3) % w))
                        (ball(vec 0,&1)) = {}` MP_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `Q1:A->bool`;
                     `(Q1:A->bool) INTER
                      IMAGE (\w. apx_bext (bb:real^3->A) e' fU (norm(yz:real^3) % w))
                            (ball(vec 0,&1))`] APX_CONNECTED_CLOPEN_EQ) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [EXPAND_TAC "Q1" THEN MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
          MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`;
                                `apx_slab (--inv ep) (L0 + inv ep)`] THEN
          ASM_REWRITE_TAC[APX_CONNECTED_ANNULUS3];
          SET_TAC[];
          MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
          EXPAND_TAC "Q1" THEN MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
          MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`;
                                `apx_slab (--inv ep) (L0 + inv ep)`] THEN
          ASM_REWRITE_TAC[OPEN_ANNULUS];
          FIRST_ASSUM ACCEPT_TAC;
          MATCH_MP_TAC(SET_RULE `!c B1 S Q1:A->bool. c SUBSET B1 UNION S /\ DISJOINT Q1 S
                                     ==> Q1 INTER c SUBSET Q1 INTER B1`) THEN
          EXISTS_TAC `IMAGE (e':real^3->A) (sphere(vec 0,norm(yz:real^3)))` THEN
          CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
          MATCH_MP_TAC SUBSET_TRANS THEN
          EXISTS_TAC `top closure_of (IMAGE (\w. apx_bext (bb:real^3->A) e' fU
                                         (norm(yz:real^3) % w)) (ball(vec 0,&1)))` THEN
          CONJ_TAC THENL [MATCH_MP_TAC CLOSURE_OF_MONO THEN SET_TAC[]; ALL_TAC] THEN
          MATCH_MP_TAC SUBSET_TRANS THEN
          EXISTS_TAC `IMAGE (\w. apx_bext (bb:real^3->A) e' fU (norm(yz:real^3) % w))
                            (cball(vec 0,&1))` THEN
          CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
          FIRST_ASSUM(fun th -> REWRITE_TAC[th; SUBSET_REFL] THEN NO_TAC)];
        DISCH_TAC THEN
        UNDISCH_TAC `~((E:real^3->A) y0 IN
                       IMAGE (apx_bext (bb:real^3->A) e' fU) (cball(vec 0,norm(yz:real^3))))` THEN
        REWRITE_TAC[] THEN
        UNDISCH_TAC `(E:real^3->A) y0 IN Q1` THEN
        SUBGOAL_THEN `IMAGE (\w. apx_bext (bb:real^3->A) e' fU (norm(yz:real^3) % w))
                            (ball(vec 0,&1)) SUBSET
                      IMAGE (apx_bext bb e' fU) (cball(vec 0,norm yz))` MP_TAC THENL
         [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
          REWRITE_TAC[SUBSET; IN_BALL_0; IN_CBALL_0] THEN REAL_ARITH_TAC;
          ALL_TAC] THEN
        FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
          lhs(concl th) = `(Q1:A->bool) INTER
                           IMAGE (\w. apx_bext (bb:real^3->A) e' fU (norm(yz:real^3) % w))
                                 (ball(vec 0,&1))`)) THEN
        SET_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `DISJOINT (Q1:A->bool) (IMAGE (e':real^3->A) (sphere(vec 0,norm(yz:real^3))))` THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `IMAGE (\w. apx_bext (bb:real^3->A) e' fU (norm(yz:real^3) % w))
                             (cball(vec 0,&1))` &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "UNION")) (concl th))) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN apx_slab (L0 - inv(&8 * ep)) (L0 + inv ep)
                    ==> ?w. (E:real^3->A) y = e' w /\ w IN rfs_neck_dom eps /\
                            apx_sval w = apx_sval(yz:real^3) + L0 - apx_sval y`
  (LABEL_TAC "lev") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    EXISTS_TAC `norm(yz:real^3) % (LL / norm(y:real^3)) %
                (f0:real^3->real^3)(inv(norm y) % y)` THEN
    SUBGOAL_THEN `~(y:real^3 = vec 0) /\ L0 - inv(&8 * ep) < apx_sval y /\
                  apx_sval y < L0 + inv ep` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[APX_SLAB_SVAL]; ALL_TAC] THEN
    SUBGOAL_THEN `inv(norm y) % (y:real^3) IN sphere(vec 0,&1)` ASSUME_TAC THENL
     [REWRITE_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
      MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[NORM_EQ_0];
      ALL_TAC] THEN
    SUBGOAL_THEN `(f0:real^3->real^3)(inv(norm y) % y) IN sphere(vec 0,&1)` ASSUME_TAC THENL
     [UNDISCH_TAC `sphere_diffeo (f0:real^3->real^3) f0'` THEN
      REWRITE_TAC[sphere_diffeo] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
    SUBGOAL_THEN `norm(norm(yz:real^3) % (LL / norm(y:real^3)) %
                       (f0:real^3->real^3)(inv(norm y) % y)) =
                  norm yz * (LL / norm y)` ASSUME_TAC THENL
     [REWRITE_TAC[NORM_MUL; REAL_ABS_NORM] THEN
      UNDISCH_TAC `(f0:real^3->real^3)(inv(norm y) % y) IN sphere(vec 0,&1)` THEN
      REWRITE_TAC[IN_SPHERE_0] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[REAL_MUL_RID; REAL_ABS_DIV; REAL_ABS_NORM] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < norm(yz:real^3) * (LL / norm(y:real^3))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `apx_sval(norm(yz:real^3) % (LL / norm(y:real^3)) %
                           (f0:real^3->real^3)(inv(norm y) % y)) =
                  apx_sval yz + L0 - apx_sval y` ASSUME_TAC THENL
     [REWRITE_TAC[apx_sval] THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[LOG_MUL; LOG_DIV; REAL_LT_DIV; REAL_EXP_POS_LT; LOG_EXP] THEN
      SUBGOAL_THEN `log LL = L0 / sqrt(&2)` SUBST1_TAC THENL
       [EXPAND_TAC "LL" THEN REWRITE_TAC[LOG_EXP]; ALL_TAC] THEN
      UNDISCH_TAC `&0 < sqrt(&2)` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "end" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
        `(y:real^3) IN apx_slab (L0 - inv(&8 * ep)) (L0 + inv ep)`)]) THEN
      REWRITE_TAC[apx_cp; o_THM];
      ALL_TAC] THEN
    REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM NORM_POS_LT] THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `dd = min (min (apx_sval(yz:real^3)) (inv(&8 * ep))) L0 / &2` THEN
  SUBGOAL_THEN `&0 < dd /\ dd < L0 /\ dd < apx_sval(yz:real^3) /\ dd < inv(&8 * ep)`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "dd" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (E:real^3->A) (apx_slab (L0 - dd) (L0 + dd)) SUBSET
                Q1 UNION IMAGE (\w. apx_bext (bb:real^3->A) e' fU (norm(yz:real^3) % w))
                               (cball(vec 0,&1))` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(y:real^3 = vec 0) /\ L0 - dd < apx_sval y /\ apx_sval y < L0 + dd`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[APX_SLAB_SVAL]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNION] THEN
    ASM_CASES_TAC `apx_sval(y:real^3) < L0` THENL
     [DISJ1_TAC THEN EXPAND_TAC "Q1" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISJ2_TAC THEN
    ASM_CASES_TAC `apx_sval(y:real^3) = L0` THENL
     [SUBGOAL_THEN `(E:real^3->A) y IN IMAGE E (sphere(vec 0,LL))` MP_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[APX_SPHERE_LEVEL; IN_ELIM_THM] THEN
        ASM_REWRITE_TAC[] THEN
        FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `exp(L0 / sqrt(&2)) = LL`)) THEN
        REWRITE_TAC[APX_SPHERE_LEVEL; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `IMAGE (\w. apx_bext (bb:real^3->A) e' fU (norm(yz:real^3) % w))
                               (cball(vec 0,&1))` &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "UNION")) (concl th))) THEN
      FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `IMAGE (E:real^3->A) (sphere(vec 0,LL))`)) THEN
      REWRITE_TAC[IN_UNION] THEN MESON_TAC[];
      ALL_TAC] THEN
    USE_THEN "lev" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `!x f s t. (x:A) IN IMAGE (f:real^3->A) s /\ s SUBSET t
                                     ==> x IN IMAGE f t`) THEN
    EXISTS_TAC `ball(vec 0:real^3,norm(yz:real^3))` THEN
    REWRITE_TAC[BALL_SUBSET_CBALL] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `exp(apx_sval(yz:real^3) / sqrt(&2)) = norm yz`)) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `C:real`; `eps:real`; `U:A->bool`; `bb:real^3->A`; `e':real^3->A`;
                   `fU:real^3->real^3`; `apx_sval(yz:real^3)`; `w:real^3`] APX_BEXT_LEVELS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `top closure_of (IMAGE (\w. apx_bext (bb:real^3->A) e' fU (norm(yz:real^3) % w))
                                      (cball(vec 0,&1))) =
                IMAGE (\w. apx_bext (bb:real^3->A) e' fU (norm(yz:real^3) % w))
                      (cball(vec 0,&1))` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_OF_CLOSED_IN THEN MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology euclidean (ball(vec 0:real^3,&2))` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `ball(vec 0:real^3,&2)`;
                   `\w. apx_bext (bb:real^3->A) e' fU (norm(yz:real^3) % w)`] GRGD_PARAM_FACTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `mfd_ball_chart top atlas
                     (\w. apx_bext (bb:real^3->A) e' fU (norm(yz:real^3) % w))` THEN
      SIMP_TAC[mfd_ball_chart];
      STRIP_TAC] THEN
    CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN; COMPACT_CBALL] THEN
    REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `top closure_of (Q1:A->bool) SUBSET
                Q1 UNION IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1)) UNION
                IMAGE (e':real^3->A) (sphere(vec 0,norm(yz:real^3)))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `E:real^3->A`;
                   `--inv ep`; `L0 + inv ep`; `&0`; `L0:real`] APX_PARAM_SLAB_CLOSURE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`&0`; `L0:real`] APX_CSLAB_SPLIT) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `&0 / sqrt(&2) = &0` SUBST1_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_LZERO]; ALL_TAC] THEN
    REWRITE_TAC[REAL_EXP_0; IMAGE_UNION] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM(ASSUME `annulus (&1) LL = apx_slab (&0) L0`)] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sphere(vec 0:real^3,LL) SUBSET apx_slab (L0 - dd) (L0 + dd) /\
                apx_slab (L0 - dd) (L0 + dd) SUBSET apx_slab (--inv ep) (L0 + inv ep)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `exp(L0 / sqrt(&2)) = LL`)) THEN
      REWRITE_TAC[APX_SPHERE_LEVEL; SUBSET; IN_ELIM_THM; APX_SLAB_SVAL] THEN
      GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC APX_SLAB_SUBSET THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Q1:A->bool) UNION
                IMAGE (\w. apx_bext (bb:real^3->A) e' fU (norm(yz:real^3) % w))
                      (cball(vec 0,&1)) = P` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_CONNECTED_CLOPEN_EQ THEN EXISTS_TAC `top:A topology` THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      ASM_REWRITE_TAC[UNION_SUBSET];
      SUBGOAL_THEN
       `(Q1:A->bool) UNION
        IMAGE (\w. apx_bext (bb:real^3->A) e' fU (norm(yz:real^3) % w)) (cball(vec 0,&1)) =
        Q1 UNION IMAGE (\w. apx_bext bb e' fU (norm yz % w)) (ball(vec 0,&1)) UNION
        IMAGE (E:real^3->A) (apx_slab (L0 - dd) (L0 + dd))` SUBST1_TAC THENL
       [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
         [FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_eq(concl th) &&
            lhs(concl th) = `IMAGE (\w. apx_bext (bb:real^3->A) e' fU (norm(yz:real^3) % w))
                                   (cball(vec 0,&1))` &&
            can (find_term (fun t -> is_const t && fst(dest_const t) = "UNION")) (concl th))) THEN
          SUBGOAL_THEN `IMAGE (e':real^3->A) (sphere(vec 0,norm(yz:real^3))) SUBSET
                        IMAGE (E:real^3->A) (apx_slab (L0 - dd) (L0 + dd))` MP_TAC THENL
           [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
              lhs(concl th) = `IMAGE (E:real^3->A) (sphere(vec 0,LL))`)) THEN
            MATCH_MP_TAC IMAGE_SUBSET THEN FIRST_ASSUM ACCEPT_TAC;
            SET_TAC[]];
          MATCH_MP_TAC(SET_RULE `!Q1 B Q2 G9:A->bool. B SUBSET Q2 /\ G9 SUBSET Q1 UNION Q2
                                 ==> Q1 UNION B UNION G9 SUBSET Q1 UNION Q2`) THEN
          CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
          MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[BALL_SUBSET_CBALL]];
        ALL_TAC] THEN
      REPEAT(MATCH_MP_TAC OPEN_IN_UNION THEN CONJ_TAC) THENL
       [EXPAND_TAC "Q1" THEN MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
        MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`;
                              `apx_slab (--inv ep) (L0 + inv ep)`] THEN
        ASM_REWRITE_TAC[OPEN_ANNULUS];
        FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
        MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`;
                              `apx_slab (--inv ep) (L0 + inv ep)`] THEN
        ASM_REWRITE_TAC[apx_slab; OPEN_ANNULUS] THEN
        UNDISCH_TAC `apx_slab (L0 - dd) (L0 + dd) SUBSET apx_slab (--inv ep) (L0 + inv ep)` THEN
        REWRITE_TAC[apx_slab]];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_UNION] THEN
      EXISTS_TAC `(E:real^3->A) (r0 % basis 1)` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[CLOSURE_OF_UNION] THEN
      FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `top closure_of
                           (IMAGE (\w. apx_bext (bb:real^3->A) e' fU (norm(yz:real^3) % w))
                                  (cball(vec 0,&1)))`)) THEN
      MATCH_MP_TAC(SET_RULE `!P Q1 Q2 C S Z9:A->bool.
                               C SUBSET Q1 UNION S UNION Z9 /\ DISJOINT P S /\ Z9 SUBSET Q2
                               ==> P INTER (C UNION Q2) SUBSET Q1 UNION Q2`) THEN
      MAP_EVERY EXISTS_TAC [`IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1))`;
                            `IMAGE (e':real^3->A) (sphere(vec 0,norm(yz:real^3)))`] THEN
      REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(i:num) IN J`) o check (fun th ->
          is_forall (concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_neck_chart"))
              (concl th))) THEN SIMP_TAC[];
        FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_eq(concl th) &&
          lhs(concl th) = `IMAGE (\w. apx_bext (bb:real^3->A) e' fU (norm(yz:real^3) % w))
                                 (cball(vec 0,&1))` &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "UNION")) (concl th))) THEN
        SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `sphere_diffeo (\v. (fU':real^3->real^3)((f0:real^3->real^3) v))
                              (\v. (f0':real^3->real^3)((fU:real^3->real^3) v))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMT_SPHERE_DIFFEO_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `sphere_diffeo (fU:real^3->real^3) fU'` THEN
    REWRITE_TAC[sphere_diffeo] THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`E:real^3->A`; `LL:real`;
                        `\v. (fU':real^3->real^3)((f0:real^3->real^3) v)`;
                        `\v. (f0':real^3->real^3)((fU:real^3->real^3) v)`;
                        `\w. apx_bext (bb:real^3->A) e' fU (norm(yz:real^3) % w)`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `apx_slab (--inv ep) (L0 + inv ep)` THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN REWRITE_TAC[OPEN_ANNULUS] THEN
  ASM_REWRITE_TAC[];
    X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(N:int->real^3->A) (&0) w` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(w:real^3) IN apx_slab (L0 - inv(&8 * ep)) (L0 + inv ep)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  USE_THEN "end" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
    `(w:real^3) IN apx_slab (L0 - inv(&8 * ep)) (L0 + inv ep)`)]) THEN
  REWRITE_TAC[apx_cp; o_THM] THEN
  SUBGOAL_THEN `&1 < LL / norm(w:real^3) /\ inv(norm w) % w IN sphere(vec 0,&1) /\
                (f0:real^3->real^3)(inv(norm w) % w) IN sphere(vec 0,&1)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(w:real^3) IN annulus (LL / &2) LL` THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < norm(w:real^3)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `p /\ q /\ (q ==> r) ==> p /\ q /\ r`) THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ];
      UNDISCH_TAC `sphere_diffeo (f0:real^3->real^3) f0'` THEN
      REWRITE_TAC[sphere_diffeo] THEN MESON_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC];
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `P:A->bool` &&
    can (find_term (fun t -> t = `Q1:A->bool`)) (lhs(concl th)))) THEN
  EXPAND_TAC "Q1" THEN REFL_TAC;
    FIRST_ASSUM(SUBST1_TAC o check (fun th ->
    concl th = `IMAGE (E:real^3->A) (annulus (&1) LL) = Q1`)) THEN
  FIRST_ASSUM ACCEPT_TAC]);;

(* Capping a product by two balls inside V gives two balls for V (the     *)
(* construction of APX_GLUE_CAPPED, without the final appeal to M2).        *)

let APX_A25_CAPPED_BALLS = prove
 (`!top atlas c E L b2 f f' (V:A->bool).
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
        mfd_ball_chart top atlas c /\ mfd_ball_chart top atlas b2 /\
        &1 < L /\ sphere_diffeo f f' /\
        mfd_param top atlas (annulus (&1) L) E /\
        (!x. x IN annulus (&1) (&3 / &2) ==> E x = c x) /\
        (!x. x IN annulus (L / &2) L ==> E x = b2((L / norm x) % f(inv(norm x) % x))) /\
        V = IMAGE c (cball(vec 0,&1)) UNION IMAGE E (annulus (&1) L) UNION
            IMAGE b2 (cball(vec 0,&1)) /\
        DISJOINT (IMAGE c (cball(vec 0,&1))) (IMAGE E (annulus (&1) L)) /\
        DISJOINT (IMAGE c (cball(vec 0,&1))) (IMAGE b2 (cball(vec 0,&1))) /\
        DISJOINT (IMAGE E (annulus (&1) L)) (IMAGE b2 (cball(vec 0,&1)))
        ==> ?b1. mfd_ball_chart top atlas b1 /\
                 V = IMAGE b1 (cball(vec 0,&1)) UNION IMAGE b2 (cball(vec 0,&1)) /\
                 DISJOINT (IMAGE b1 (ball(vec 0,&1))) (IMAGE b2 (ball(vec 0,&1))) /\
                 (?r. &1 < r /\
                      !x. x IN annulus (&1) r
                          ==> b1 x = b2(inv(norm x) % f(inv(norm x) % x)))`,
  MAP_EVERY X_GEN_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `c:real^3->A`;
    `E:real^3->A`; `L:real`; `b2:real^3->A`; `f:real^3->real^3`;
    `f':real^3->real^3`; `V:A->bool`] THEN
  STRIP_TAC THEN
  ABBREV_TAC `a = min (&3 / &2) L` THEN
  ABBREV_TAC `b = (&3 * L + &1) / &4` THEN
  SUBGOAL_THEN
   `&1 < a /\ a <= &3 / &2 /\ a <= L /\ &1 <= b /\ L / &2 <= b /\
    b < L /\ &0 < L /\ &0 < b /\ b <= &2 * L /\ L * inv b <= &2`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL
     [EXPAND_TAC "b" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    MAP_EVERY EXPAND_TAC ["a"; "b"] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^3. x IN annulus (&1) (&3 / &2) ==> (E:real^3->A) x = c x`
  (LABEL_TAC "Ec") THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^3. x IN annulus (L / &2) L
               ==> (E:real^3->A) x =
                   (b2:real^3->A)((L / norm x) % (f:real^3->real^3)(inv(norm x) % x))`
  (LABEL_TAC "Eb") THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `hh = radial_ext (f:real^3->real^3) o (\x. L % x) o
                   (\x. inv(norm x pow 2) % x)` THEN
  SUBGOAL_THEN
   `!x:real^3. ~(x = vec 0)
               ==> (hh:real^3->real^3) x = (L / norm x) % f(inv(norm x) % x) /\
                   norm(hh x) = L / norm x`
  (LABEL_TAC "hh") THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`f:real^3->real^3`; `L:real`; `x:real^3`] APX_FLIP_EQ) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "hh" THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC APX_FLIP_NORM THEN EXISTS_TAC `f':real^3->real^3` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `C = \x:real^3. if norm x < a then (c:real^3->A) x
                             else if norm x < L then (E:real^3->A) x
                             else (b2:real^3->A) ((hh:real^3->real^3) x)` THEN
  SUBGOAL_THEN
   `!x:real^3. norm x < L
               ==> (norm x <= &1 ==> (C:real^3->A) x = c x) /\
                   (&1 < norm x ==> C x = E x)`
  (LABEL_TAC "C1") THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN EXPAND_TAC "C" THEN
    REWRITE_TAC[] THEN
    ASM_CASES_TAC `norm(x:real^3) < a` THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THENL
     [CONV_TAC SYM_CONV THEN USE_THEN "Ec" MATCH_MP_TAC THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^3. b < norm x /\ norm x < &2 * L
               ==> (C:real^3->A) x = b2((hh:real^3->real^3) x)`
  (LABEL_TAC "C2") THENL
   [X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM NORM_POS_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "hh" (MP_TAC o SPEC `x:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    EXPAND_TAC "C" THEN REWRITE_TAC[] THEN
    ASM_CASES_TAC `norm(x:real^3) < a` THEN ASM_REWRITE_TAC[] THENL
     [TRANS_TAC EQ_TRANS `(E:real^3->A) x` THEN CONJ_TAC THENL
       [CONV_TAC SYM_CONV THEN USE_THEN "Ec" MATCH_MP_TAC;
        USE_THEN "Eb" MATCH_MP_TAC] THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      USE_THEN "Eb" MATCH_MP_TAC THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x z. norm(x:real^3) <= &1 /\ &1 < norm(z:real^3) /\ norm z < L
          ==> ~((c:real^3->A) x = E z)`
  (LABEL_TAC "D1") THENL
   [UNDISCH_TAC `DISJOINT (IMAGE (c:real^3->A) (cball(vec 0,&1)))
                          (IMAGE (E:real^3->A) (annulus (&1) L))` THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY;
                IN_CBALL_0; annulus; IN_ELIM_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x z. norm(x:real^3) <= &1 /\ norm(z:real^3) <= &1
          ==> ~((c:real^3->A) x = b2 z)`
  (LABEL_TAC "D2") THENL
   [UNDISCH_TAC `DISJOINT (IMAGE (c:real^3->A) (cball(vec 0,&1)))
                          (IMAGE (b2:real^3->A) (cball(vec 0,&1)))` THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY;
                IN_CBALL_0] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x z. &1 < norm(x:real^3) /\ norm x < L /\ norm(z:real^3) <= &1
          ==> ~((E:real^3->A) x = b2 z)`
  (LABEL_TAC "D3") THENL
   [UNDISCH_TAC `DISJOINT (IMAGE (E:real^3->A) (annulus (&1) L))
                          (IMAGE (b2:real^3->A) (cball(vec 0,&1)))` THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY;
                IN_CBALL_0; annulus; IN_ELIM_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x z. norm(x:real^3) < L /\ norm(z:real^3) <= &1
          ==> ~((C:real^3->A) x = b2 z)`
  (LABEL_TAC "G2") THENL
   [MAP_EVERY X_GEN_TAC [`x:real^3`; `z:real^3`] THEN STRIP_TAC THEN
    USE_THEN "C1" (MP_TAC o SPEC `x:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `norm(x:real^3) <= &1` THENL
     [DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST1_TAC THEN
      USE_THEN "D2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      USE_THEN "D3" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param top atlas (ball(vec 0:real^3,&2 * L)) (C:real^3->A)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `mfd_param top atlas (ball(vec 0:real^3,a)) (c:real^3->A)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `ball(vec 0:real^3,&2)` THEN
      REWRITE_TAC[GSYM mfd_ball_chart; OPEN_BALL] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `mfd_param top atlas (annulus b (&2 * L)) ((b2:real^3->A) o (hh:real^3->real^3))`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `ball(vec 0:real^3,&2)`; `b2:real^3->A`;
                     `annulus b (&2 * L):real^3->bool`;
                     `annulus (L * inv(&2 * L)) (L * inv b):real^3->bool`;
                     `hh:real^3->real^3`;
                     `((\x:real^3. inv(norm x pow 2) % x) o (\x. inv L % x)) o
                      radial_ext (f':real^3->real^3)`]
                    MFD_PARAM_PRECOMPOSE) THEN
      DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[GSYM mfd_ball_chart] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [EXPAND_TAC "hh" THEN MATCH_MP_TAC APX_FLIP_DIFFEO THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM; IN_BALL_0] THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `mfd_param top atlas (ball(vec 0:real^3,a) UNION annulus (&1) L)
                (C:real^3->A)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_UNION THEN
      MAP_EVERY EXISTS_TAC [`c:real^3->A`; `E:real^3->A`] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[IN_BALL_0] THEN EXPAND_TAC "C" THEN SIMP_TAC[];
        REWRITE_TAC[annulus; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN
        STRIP_TAC THEN USE_THEN "C1" (MP_TAC o SPEC `x:real^3`) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[]; DISCH_THEN(MATCH_MP_TAC o CONJUNCT2)] THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
         [REWRITE_TAC[SUBSET; IN_INTER; IMP_CONJ; FORALL_IN_IMAGE] THEN
          X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_BALL_0] THEN DISCH_TAC THEN
          REWRITE_TAC[IN_IMAGE; IN_INTER; IN_BALL_0; annulus; IN_ELIM_THM] THEN
          DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
          SUBGOAL_THEN `&1 < norm(x:real^3)` ASSUME_TAC THENL
           [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
            USE_THEN "D1" (MP_TAC o SPECL [`x:real^3`; `z:real^3`]) THEN
            ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
            ALL_TAC] THEN
          EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[] THEN
          CONJ_TAC THENL
           [EXPAND_TAC "C" THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
          REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
          REWRITE_TAC[IN_INTER; IN_IMAGE; IN_BALL_0; annulus; IN_ELIM_THM] THEN
          X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN CONJ_TAC THEN
          EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[] THENL
           [EXPAND_TAC "C" THEN ASM_REWRITE_TAC[];
            USE_THEN "C1" (MP_TAC o SPEC `x:real^3`) THEN
            ANTS_TAC THENL
             [ASM_REWRITE_TAC[]; DISCH_THEN(MATCH_MP_TAC o CONJUNCT2)] THEN
            ASM_REWRITE_TAC[]]]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `mfd_param top atlas
        ((ball(vec 0:real^3,a) UNION annulus (&1) L) UNION annulus b (&2 * L))
        (C:real^3->A)`
    MP_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_UNION THEN
      MAP_EVERY EXISTS_TAC [`C:real^3->A`; `(b2:real^3->A) o (hh:real^3->real^3)`] THEN
      ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL
       [REWRITE_TAC[annulus; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
        USE_THEN "C2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_INTER; IMP_CONJ; FORALL_IN_IMAGE] THEN
        X_GEN_TAC `x:real^3` THEN
        REWRITE_TAC[IN_UNION; IN_BALL_0; annulus; IN_ELIM_THM] THEN
        DISCH_TAC THEN
        SUBGOAL_THEN `norm(x:real^3) < L` ASSUME_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[IN_IMAGE; o_THM; IN_INTER; IN_UNION; IN_BALL_0; annulus;
                    IN_ELIM_THM] THEN
        DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
        ASM_CASES_TAC `norm(z:real^3) < L` THENL
         [EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
           [CONV_TAC SYM_CONV THEN USE_THEN "C2" MATCH_MP_TAC THEN
            ASM_REWRITE_TAC[];
            ASM_REAL_ARITH_TAC];
          USE_THEN "G2" (MP_TAC o SPECL [`x:real^3`; `(hh:real^3->real^3) z`]) THEN
          ANTS_TAC THENL
           [ASM_REWRITE_TAC[] THEN
            SUBGOAL_THEN `~(z:real^3 = vec 0)` ASSUME_TAC THENL
             [REWRITE_TAC[GSYM NORM_POS_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
            USE_THEN "hh" (MP_TAC o SPEC `z:real^3`) THEN
            ANTS_TAC THENL
             [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o CONJUNCT2)] THEN
            ASM_SIMP_TAC[REAL_LE_LDIV_EQ; NORM_POS_LT] THEN ASM_REAL_ARITH_TAC;
            ASM_REWRITE_TAC[]]];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN
        X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN CONJ_TAC THENL
         [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[IN_IMAGE; o_THM] THEN EXISTS_TAC `x:real^3` THEN
          ASM_REWRITE_TAC[] THEN USE_THEN "C2" MATCH_MP_TAC THEN
          UNDISCH_TAC `(x:real^3) IN annulus b (&2 * L)` THEN
          REWRITE_TAC[annulus; IN_ELIM_THM]]];
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[EXTENSION; IN_UNION; IN_BALL_0; annulus; IN_ELIM_THM] THEN
      GEN_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `(C:real^3->A) o (\x. L % x)` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!x:real^3. L % inv L % x = x /\ norm(inv L % x) = norm x / L /\
               norm(L % x) = L * norm x`
  (LABEL_TAC "sc") THENL
   [GEN_TAC THEN REWRITE_TAC[VECTOR_MUL_ASSOC; NORM_MUL; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID;
                 REAL_ARITH `&0 < L ==> abs L = L`] THEN
    REWRITE_TAC[real_div; REAL_MUL_SYM];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[mfd_ball_chart] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `ball(vec 0:real^3,&2 * L)`; `C:real^3->A`;
                   `ball(vec 0:real^3,&2)`; `ball(vec 0:real^3,L * &2)`;
                   `\x:real^3. L % x`; `\x:real^3. inv L % x`]
                  MFD_PARAM_PRECOMPOSE) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[SMT_DIFFEO_SCALING_BALL] THEN
    MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC;
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[UNION_SUBSET; SUBSET_UNION] THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_CBALL_0] THEN
        X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
        REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN
        REWRITE_TAC[IN_IMAGE; o_THM; IN_CBALL_0] THEN
        EXISTS_TAC `inv L % x:real^3` THEN
        USE_THEN "sc" (fun th -> REWRITE_TAC[th]) THEN CONJ_TAC THENL
         [CONV_TAC SYM_CONV THEN USE_THEN "C1" (MP_TAC o SPEC `x:real^3`) THEN
          ANTS_TAC THENL
           [ASM_REAL_ARITH_TAC; DISCH_THEN(MATCH_MP_TAC o CONJUNCT1)] THEN
          ASM_REWRITE_TAC[];
          ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; annulus; IN_ELIM_THM] THEN
        X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
        REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN
        REWRITE_TAC[IN_IMAGE; o_THM; IN_CBALL_0] THEN
        EXISTS_TAC `inv L % x:real^3` THEN
        USE_THEN "sc" (fun th -> REWRITE_TAC[th]) THEN CONJ_TAC THENL
         [CONV_TAC SYM_CONV THEN USE_THEN "C1" (MP_TAC o SPEC `x:real^3`) THEN
          ANTS_TAC THENL
           [ASM_REAL_ARITH_TAC; DISCH_THEN(MATCH_MP_TAC o CONJUNCT2)] THEN
          ASM_REWRITE_TAC[];
          ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_CBALL_0; o_THM] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    ASM_CASES_TAC `norm(L % x:real^3) < L` THENL
     [USE_THEN "C1" (MP_TAC o SPEC `L % x:real^3`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_CASES_TAC `norm(L % x:real^3) <= &1` THENL
       [DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_CBALL_0];
        DISCH_THEN(MP_TAC o CONJUNCT2) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
        REWRITE_TAC[IN_UNION] THEN DISJ2_TAC THEN DISJ1_TAC THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN
        ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `~(L % x:real^3 = vec 0)` ASSUME_TAC THENL
       [REWRITE_TAC[GSYM NORM_POS_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "C2" (MP_TAC o SPEC `L % x:real^3`) THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `~(norm(L % x:real^3) < L)` THEN
        USE_THEN "sc" (fun th -> REWRITE_TAC[th]) THEN
        DISCH_TAC THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `L * &1` THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
            ASM_REAL_ARITH_TAC]];
        DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[IN_UNION] THEN DISJ2_TAC THEN DISJ2_TAC THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_CBALL_0] THEN
      USE_THEN "hh" (MP_TAC o SPEC `L % x:real^3`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o CONJUNCT2)] THEN
      UNDISCH_TAC `~(norm(L % x:real^3) < L)` THEN
      USE_THEN "sc" (fun th -> REWRITE_TAC[th]) THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 < L * norm(x:real^3)` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[SET_RULE
     `DISJOINT (IMAGE (f:real^3->A) s) (IMAGE (g:real^3->A) t) <=>
      !x y. x IN s /\ y IN t ==> ~(f x = g y)`] THEN
    REWRITE_TAC[IN_BALL_0; o_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^3`; `z:real^3`] THEN STRIP_TAC THEN
    USE_THEN "G2" MATCH_MP_TAC THEN
    USE_THEN "sc" (fun th -> REWRITE_TAC[th]) THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `L * &1` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    EXISTS_TAC `&2` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[annulus; IN_ELIM_THM; o_THM] THEN
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < norm(x:real^3) /\ ~(L % x:real^3 = vec 0)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM NORM_POS_LT] THEN
      USE_THEN "sc" (fun th -> REWRITE_TAC[th]) THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "C2" (MP_TAC o SPEC `L % x:real^3`) THEN
    ANTS_TAC THENL
     [USE_THEN "sc" (fun th -> REWRITE_TAC[th]) THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `L * &1` THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `L * &2` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
      DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN
    USE_THEN "hh" (MP_TAC o SPEC `L % x:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o CONJUNCT1)] THEN
    USE_THEN "sc" (fun th -> REWRITE_TAC[th]) THEN
    BINOP_TAC THENL [ALL_TAC; AP_TERM_TAC THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
                     AP_THM_TAC THEN AP_TERM_TAC] THEN
    UNDISCH_TAC `&0 < norm(x:real^3)` THEN UNDISCH_TAC `&0 < L` THEN
    CONV_TAC REAL_FIELD]);;

(* ------------------------------------------------------------------------- *)
(* The clean case.  The base configuration satisfies the growth              *)
(* context; the growth stops at a ball cap and V is two balls.               *)
(* ------------------------------------------------------------------------- *)

(* The central sphere of a neck chart lies in the closure of its outer collar. *)

let APX_A25_SPHERE_CLOSURE = prove
 (`!top atlas (e:real^3->A).
     mfd_neck_chart top atlas e
     ==> IMAGE e (sphere(vec 0,&1)) SUBSET top closure_of (IMAGE e (annulus (&1) (&2)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_neck_chart] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MFD_PARAM_MAPS) THEN STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `IMAGE (e:real^3->A)
                ((subtopology euclidean (annulus (&1 / &2) (&2))) closure_of
                 (annulus (&1) (&2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[CLOSURE_OF_SUBTOPOLOGY; EUCLIDEAN_CLOSURE_OF] THEN
    SUBGOAL_THEN `annulus (&1 / &2) (&2) INTER annulus (&1) (&2) =
                  annulus (&1) (&2):real^3->bool` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; annulus; IN_ELIM_THM] THEN GEN_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET_INTER; APX_SPHERE_CLOSURE_ANNULUS] THEN
    REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN GEN_TAC THEN REAL_ARITH_TAC;
    MATCH_MP_TAC CONTINUOUS_MAP_IMAGE_CLOSURE_SUBSET THEN ASM_REWRITE_TAC[]]);;

(* The clean start configuration satisfies the growth context. *)

let APX_A25_AGC_HOLDS = prove
 (`!top atlas (g:A->real^3^3) C eps ep V U1 (bb1:real^3->A) e1 f1 r0 y0 N0 B1.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     apx_sphere_sep top atlas /\ V IN connected_components_of top /\ compact_in top V /\
     (!x. x IN V ==> apx_neck_or_core (top,atlas) g C eps x) /\
     &0 < eps /\ apx_kc * eps = ep /\ ep <= &1 / &1024 /\
     apx_ch_ctx top atlas g ep /\ apx_ch_pair top atlas g ep /\ apx_ch_more top atlas g ep /\
     apx_ch_n4r top atlas g ep /\ apx_ch_ctx top atlas g eps /\ apx_cl_rat top atlas g ep /\
     apx_bcap (top,atlas) g C eps U1 bb1 e1 f1 /\ ~DISJOINT V (IMAGE bb1 (ball(vec 0,&1))) /\
     r0 = exp(inv(&2 * eps) / sqrt(&2)) /\ y0 = r0 % basis 1 /\ N0 = apx_cp e1 y0 /\
     B1 = apx_bext bb1 e1 f1 /\
     (!U bb e' f. apx_bcap (top,atlas) g C eps U bb e' f
          ==> DISJOINT (IMAGE N0 (annulus (&1 / &2) (&2)))
                       (IMAGE (apx_bext bb e' f) (ball(vec 0,exp((&4 * inv ep) / sqrt(&2)))))) /\
     (!U Y p. rfs_cap (top,atlas) g C eps U Y /\ rfs_twisted_chart top atlas p /\
              IMAGE p (annulus (&1 / &4) (&4)) SUBSET U ==> DISJOINT U V)
     ==> apx_agc (top,atlas) g C eps ep {0} (\k:num. N0) (lsp_side top N0 (&4 / &3))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `ep:real`; `V:A->bool`; `U1:A->bool`; `bb1:real^3->A`;
                 `e1:real^3->A`; `f1:real^3->real^3`; `r0:real`; `y0:real^3`;
                 `N0:real^3->A`; `B1:real^3->A`] APX_A25_BASE_SETUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `N0:real^3->A`]
    LSP_SIDES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (fun th ->
    MP_TAC(SPEC `&3 / &4` th) THEN MP_TAC(SPEC `&4 / &3` th))) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `N0:real^3->A`]
    LSP_SIDE_HALVES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `N0:real^3->A`]
    APX_A25_SPHERE_CLOSURE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FIRST_X_ASSUM(fun th -> if concl th = `r0 = exp(inv(&2 * eps) / sqrt(&2))`
    then SUBST_ALL_TAC(SYM th) THEN ASSUME_TAC(SYM th) else failwith "no") THEN
  FIRST_X_ASSUM(fun th -> if concl th = `y0:real^3 = r0 % basis 1`
    then SUBST_ALL_TAC(SYM th) THEN ASSUME_TAC(SYM th) else failwith "no") THEN
  FIRST_X_ASSUM(fun th -> if concl th = `N0 = apx_cp (e1:real^3->A) y0`
    then SUBST_ALL_TAC(SYM th) THEN ASSUME_TAC(SYM th) else failwith "no") THEN
  FIRST_X_ASSUM(fun th -> if concl th = `B1 = apx_bext (bb1:real^3->A) e1 f1`
    then SUBST_ALL_TAC(SYM th) THEN ASSUME_TAC(SYM th) else failwith "no") THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `V:A->bool`
    then ASSUME_TAC(SYM th) else failwith "no") THEN
  ABBREV_TAC `Os = lsp_side top (N0:real^3->A) (&4 / &3)` THEN
  ABBREV_TAC `S0 = IMAGE (N0:real^3->A) (sphere(vec 0,&1))` THEN
  FIRST_X_ASSUM(fun th -> if concl th = `S0 = IMAGE (B1:real^3->A) (sphere(vec 0,r0))`
    then ASSUME_TAC(SYM th) else failwith "no") THEN
  SUBGOAL_THEN `(Os:A->bool) SUBSET V /\ top closure_of Os SUBSET V` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (B1:real^3->A) (cball(vec 0,r0)) UNION Os = V` THEN SET_TAC[];
      DISCH_TAC THEN MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CLOSED_IN_CONNECTED_COMPONENTS_OF THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < ep /\ eps <= &1 / &8` STRIP_ASSUME_TAC THENL
   [MP_TAC APX_KC_GE THEN DISCH_TAC THEN
    SUBGOAL_THEN `&580 * eps <= apx_kc * eps` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[apx_agc; apx_rg; IN_SING; FINITE_SING; NOT_INSERT_EMPTY] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC `(e1:real^3->A) y0` THEN FIRST_ASSUM ACCEPT_TAC;
    MESON_TAC[];
    MATCH_MP_TAC CLOSED_COMPACT_IN THEN EXISTS_TAC `V:A->bool` THEN
    ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
    SUBGOAL_THEN `UNIONS {S0 | i:num | i = 0} = S0:A->bool` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSURE_OF_SUBSET THEN
      UNDISCH_TAC `(Os:A->bool) SUBSET topspace top DIFF S0` THEN SET_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `top closure_of (IMAGE (N0:real^3->A) (annulus (&1) (&2)))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_OF_MONO THEN ASM_REWRITE_TAC[]];
    GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `IMAGE (N0:real^3->A) (annulus (&1 / &2) (&2)) =
                  IMAGE (N0:real^3->A) (annulus (&1 / &2) (&1)) UNION S0 UNION
                  IMAGE (N0:real^3->A) (annulus (&1) (&2))` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM(ASSUME `IMAGE (N0:real^3->A) (sphere(vec 0,&1)) = S0`);
                   GSYM IMAGE_UNION] THEN AP_TERM_TAC THEN
      REWRITE_TAC[EXTENSION; IN_UNION; annulus; IN_ELIM_THM; IN_SPHERE_0] THEN
      GEN_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`DISJOINT (IMAGE (N0:real^3->A) (annulus (&1 / &2) (&1))) Os`;
      `(Os:A->bool) SUBSET topspace top DIFF S0`;
      `IMAGE (N0:real^3->A) (annulus (&1) (&2)) SUBSET Os`] THEN
    MATCH_ACCEPT_TAC(SET_RULE `!A B Os S T. B SUBSET Os ==> Os SUBSET T DIFF S ==>
       DISJOINT A Os ==> Os INTER (A UNION S UNION B) = (B:A->bool)`);
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    MESON_TAC[];
    GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `mfd_param top atlas (rfs_neck_dom eps) (e1:real^3->A) /\
                  mfd_param top atlas (ball(vec 0,&2)) (bb1:real^3->A) /\
                  IMAGE (e1:real^3->A) (sphere(vec 0,&1)) = IMAGE bb1 (sphere(vec 0,&1)) /\
                  (?f1'. sphere_diffeo (f1:real^3->real^3) f1') /\
                  (!y. y IN annulus (&1) (&2) ==> bb1 y = e1(radial_ext f1 y))`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `apx_bcap (top,atlas) (g:A->real^3^3) C eps U1 bb1 e1 f1` THEN
      REWRITE_TAC[apx_bcap; mfd_ball_chart] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[rfs_neck]; ASM_MESON_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `norm(y0:real^3) = r0 /\ &0 < r0` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[GSYM(ASSUME `r0 % basis 1:real^3 = y0`)] THEN
        SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `r0 * exp(--inv(&2 * eps) / sqrt(&2)) = &1 /\
                  r0 * exp(inv(&2 * eps) / sqrt(&2)) = exp(inv eps / sqrt(&2)) /\
                  exp(--inv eps / sqrt(&2)) < &1` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM(ASSUME `exp(inv(&2 * eps) / sqrt(&2)) = r0`); GSYM REAL_EXP_ADD] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[real_div; REAL_MUL_LNEG; REAL_ADD_RINV; REAL_EXP_0];
        AP_TERM_TAC THEN REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC;
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LT] THEN
        REWRITE_TAC[real_div; REAL_MUL_LNEG; REAL_NEG_LT0] THEN
        MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THENL
         [ASM_REAL_ARITH_TAC; SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]]];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM(ASSUME `apx_cp (e1:real^3->A) y0 = N0`); apx_cp] THEN
      REWRITE_TAC[ASSUME `norm(y0:real^3) = r0`] THEN
      MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
      MAP_EVERY EXISTS_TAC
       [`rfs_neck_dom eps`;
        `annulus (r0 * exp(--inv(&2 * eps) / sqrt(&2))) (r0 * exp(inv(&2 * eps) / sqrt(&2))):
         real^3->bool`;
        `\x:real^3. inv r0 % x`] THEN
      REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC;
        REWRITE_TAC[APX_NECK_DOM_ANNULUS] THEN MATCH_MP_TAC SMT_DIFFEO_SCALING_ANNULUS THEN
        FIRST_ASSUM ACCEPT_TAC;
        REWRITE_TAC[APX_NECK_DOM_ANNULUS;
                    ASSUME `r0 * exp(--inv(&2 * eps) / sqrt(&2)) = &1`;
                    ASSUME `r0 * exp(inv(&2 * eps) / sqrt(&2)) = exp(inv eps / sqrt(&2))`] THEN
        REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(SPECL [`eps:real`; `inv(&2 * eps)`] APX_A25_LEVEL_PT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL] THEN MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[ASSUME `exp(inv(&2 * eps) / sqrt(&2)) = r0`;
                ASSUME `r0 % basis 1:real^3 = y0`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`e1:real^3->A`; `y0:real^3`; `eps:real`] APX_CP_FACTS) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `apx_cp (e1:real^3->A) y0 = N0`;
                ASSUME `apx_sval(y0:real^3) = inv(&2 * eps)`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `apx_slab (--inv(&2 * eps) + inv(&2 * eps)) (&0 + inv(&2 * eps)) =
                  annulus (&1) r0` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_ADD_LINV; REAL_ADD_LID; apx_slab;
                  ASSUME `exp(inv(&2 * eps) / sqrt(&2)) = r0`] THEN
      REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_EXP_0];
      ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (e1:real^3->A) (annulus (&1) r0) SUBSET IMAGE (B1:real^3->A) (ball(vec 0,r0))`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `bb1:real^3->A`;
                     `e1:real^3->A`; `f1:real^3->real^3`; `f1':real^3->real^3`; `eps:real`]
                    APX_BEXT_FACTS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; annulus; IN_ELIM_THM] THEN
      X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`bb1:real^3->A`; `e1:real^3->A`; `f1:real^3->real^3`;
                     `f1':real^3->real^3`; `v:real^3`] APX_A25_BEXT_E) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_BALL_0];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`top closure_of Os SUBSET Os UNION (S0:A->bool)`;
      `DISJOINT (lsp_side top (N0:real^3->A) (&3 / &4)) Os`;
      `lsp_side top (N0:real^3->A) (&3 / &4) SUBSET topspace top DIFF S0`;
      `lsp_side top (N0:real^3->A) (&3 / &4) = IMAGE (B1:real^3->A) (ball(vec 0,r0))`;
      `IMAGE (e1:real^3->A) (annulus (&1) r0) SUBSET IMAGE (B1:real^3->A) (ball(vec 0,r0))`] THEN
    MATCH_ACCEPT_TAC(SET_RULE `!Cl Os S I T B E. E SUBSET B ==> I = B ==> I SUBSET T DIFF S ==>
                       DISJOINT I Os ==> Cl SUBSET Os UNION S ==> DISJOINT Cl (E:A->bool)`);
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `U:A->bool` THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `DISJOINT (U:A->bool) V` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `Y:A->bool` THEN
      EXISTS_TAC `p:real^3->A` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `top closure_of Os SUBSET (V:A->bool)` THEN SET_TAC[]]]);;

(* A ball chart whose closed unit ball lies in a component lies in it.     *)

let APX_A25_BALL2_IN = prove
 (`!top atlas V (b:real^3->A).
     V IN connected_components_of top /\ mfd_ball_chart top atlas b /\
     IMAGE b (cball(vec 0,&1)) SUBSET V
     ==> IMAGE b (ball(vec 0,&2)) SUBSET V`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC APX_A25_IN_COMPONENT THEN
  EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `ball(vec 0:real^3,&2)`] THEN
    REWRITE_TAC[CONNECTED_BALL; SUBSET_REFL] THEN ASM_MESON_TAC[mfd_ball_chart];
    REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `(b:real^3->A)(vec 0)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[CENTRE_IN_BALL] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `IMAGE (b:real^3->A) (cball(vec 0,&1)) SUBSET V` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      REWRITE_TAC[CENTRE_IN_CBALL] THEN REAL_ARITH_TAC]]);;

(* The clean case: the growth from the base neck ends at a ball cap, and V  *)
(* is the closed core ball of U1, a product and the rescaled core of the    *)
(* stop cap, hence two balls.                                               *)

let APX_A25_CLEAN_CASE = prove
 (`!top atlas (g:A->real^3^3) C eps ep V U1 (bb1:real^3->A) e1 f1 r0 y0 N0 B1.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     apx_sphere_sep top atlas /\ V IN connected_components_of top /\ compact_in top V /\
     (!x. x IN V ==> apx_neck_or_core (top,atlas) g C eps x) /\
     &0 < eps /\ apx_kc * eps = ep /\ ep <= &1 / &1024 /\
     apx_ch_ctx top atlas g ep /\ apx_ch_pair top atlas g ep /\ apx_ch_more top atlas g ep /\
     apx_ch_n4r top atlas g ep /\ apx_ch_ctx top atlas g eps /\ apx_cl_rat top atlas g ep /\
     apx_a13_ctx top atlas g ep /\
     apx_bcap (top,atlas) g C eps U1 bb1 e1 f1 /\ ~DISJOINT V (IMAGE bb1 (ball(vec 0,&1))) /\
     r0 = exp(inv(&2 * eps) / sqrt(&2)) /\ y0 = r0 % basis 1 /\ N0 = apx_cp e1 y0 /\
     B1 = apx_bext bb1 e1 f1 /\
     (!U bb e' f. apx_bcap (top,atlas) g C eps U bb e' f
          ==> DISJOINT (IMAGE N0 (annulus (&1 / &2) (&2)))
                       (IMAGE (apx_bext bb e' f) (ball(vec 0,exp((&4 * inv ep) / sqrt(&2)))))) /\
     (!U Y p. rfs_cap (top,atlas) g C eps U Y /\ rfs_twisted_chart top atlas p /\
              IMAGE p (annulus (&1 / &4) (&4)) SUBSET U ==> DISJOINT U V)
     ==> apx_two_balls (subtopology top V) (restrict_atlas atlas V)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `ep:real`; `V:A->bool`; `U1:A->bool`; `bb1:real^3->A`;
                 `e1:real^3->A`; `f1:real^3->real^3`; `r0:real`; `y0:real^3`;
                 `N0:real^3->A`; `B1:real^3->A`] APX_A25_AGC_HOLDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `ep:real`; `V:A->bool`; `U1:A->bool`; `bb1:real^3->A`;
                 `e1:real^3->A`; `f1:real^3->real^3`; `r0:real`; `y0:real^3`;
                 `N0:real^3->A`; `B1:real^3->A`] APX_A25_BASE_SETUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; STRIP_TAC] THEN
  (* the growth and its cap stop *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `ep:real`; `{0}`; `\k:num. (N0:real^3->A)`;
                 `lsp_side top (N0:real^3->A) (&4 / &3)`; `0`] APX_AGC_GROW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_SING]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:int` (X_CHOOSE_THEN `x:int->A` (X_CHOOSE_THEN
    `N:int->real^3->A` (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `U:A->bool`
    (X_CHOOSE_THEN `bb:real^3->A` (X_CHOOSE_THEN `e':real^3->A` (X_CHOOSE_THEN
    `fU:real^3->real^3` (X_CHOOSE_THEN `yz:real^3` STRIP_ASSUME_TAC))))))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `ep:real`; `{0}`; `\k:num. (N0:real^3->A)`;
                 `lsp_side top (N0:real^3->A) (&4 / &3)`; `0`; `b:int`; `x:int->A`;
                 `N:int->real^3->A`; `U:A->bool`; `bb:real^3->A`; `e':real^3->A`;
                 `fU:real^3->real^3`; `yz:real^3`] APX_AGC_CAP_FINAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_SING]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `E:real^3->A` (X_CHOOSE_THEN `L:real` (X_CHOOSE_THEN
    `f:real^3->real^3` (X_CHOOSE_THEN `f':real^3->real^3` (X_CHOOSE_THEN `b2:real^3->A`
    (STRIP_ASSUME_TAC o BETA_RULE)))))) THEN
  (* the base cap data *)
  SUBGOAL_THEN `?f1'. sphere_diffeo (f1:real^3->real^3) f1'` (X_CHOOSE_TAC `f1':real^3->real^3`)
  THENL [ASM_MESON_TAC[apx_bcap]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(&2 * eps) /\ eps <= &1 / &8` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC APX_KC_GE THEN DISCH_TAC THEN
    SUBGOAL_THEN `&580 * eps <= apx_kc * eps` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`eps:real`; `inv(&2 * eps)`] APX_A25_LEVEL_PT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `U1:A->bool`; `bb1:real^3->A`; `e1:real^3->A`;
                 `f1:real^3->real^3`; `f1':real^3->real^3`;
                 `exp(inv(&2 * eps) / sqrt(&2)) % basis 1:real^3`] APX_BCAP_SCALED_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[ASSUME
    `norm(exp(inv(&2 * eps) / sqrt(&2)) % basis 1:real^3) = exp(inv(&2 * eps) / sqrt(&2))`]) THEN
  SUBGOAL_THEN `mfd_param top atlas (rfs_neck_dom eps) (e1:real^3->A) /\
                mfd_param top atlas (ball(vec 0,&2)) (bb1:real^3->A) /\
                IMAGE (e1:real^3->A) (sphere(vec 0,&1)) = IMAGE bb1 (sphere(vec 0,&1)) /\
                (!y. y IN annulus (&1) (&2) ==> bb1 y = e1(radial_ext f1 y))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `apx_bcap (top,atlas) (g:A->real^3^3) C eps U1 bb1 e1 f1` THEN
    REWRITE_TAC[apx_bcap; mfd_ball_chart] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[rfs_neck];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `bb1:real^3->A`;
                 `e1:real^3->A`; `f1:real^3->real^3`; `f1':real^3->real^3`; `eps:real`]
                APX_BEXT_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  (* switch to abbreviations *)
  FIRST_X_ASSUM(fun th -> if concl th = `r0 = exp(inv(&2 * eps) / sqrt(&2))`
    then SUBST_ALL_TAC(SYM th) THEN ASSUME_TAC(SYM th) else failwith "no") THEN
  FIRST_X_ASSUM(fun th -> if concl th = `y0:real^3 = r0 % basis 1`
    then SUBST_ALL_TAC(SYM th) THEN ASSUME_TAC(SYM th) else failwith "no") THEN
  FIRST_X_ASSUM(fun th -> if concl th = `N0 = apx_cp (e1:real^3->A) y0`
    then SUBST_ALL_TAC(SYM th) THEN ASSUME_TAC(SYM th) else failwith "no") THEN
  FIRST_X_ASSUM(fun th -> if concl th = `B1 = apx_bext (bb1:real^3->A) e1 f1`
    then SUBST_ALL_TAC(SYM th) THEN ASSUME_TAC(SYM th) else failwith "no") THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `V:A->bool`
    then ASSUME_TAC(SYM th) else failwith "no") THEN
  ABBREV_TAC `Os = lsp_side top (N0:real^3->A) (&4 / &3)` THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `Os:A->bool`
    then ASSUME_TAC(SYM th) else failwith "no") THEN
  (* the product reparametrized so that it starts as the ball chart of U1 *)
  SUBGOAL_THEN `diffeomorphism_on (annulus (&1) L) (annulus (&1) L)
                  (radial_ext (f1:real^3->real^3)) (radial_ext f1')` ASSUME_TAC THENL
   [MATCH_MP_TAC SMT_DIFFEO_RADIAL_EXT_ANNULUS THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE ((E:real^3->A) o radial_ext f1) (annulus (&1) L) =
                IMAGE E (annulus (&1) L)` ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_o] THEN AP_TERM_TAC THEN
    UNDISCH_TAC `diffeomorphism_on (annulus (&1) L) (annulus (&1) L)
                   (radial_ext (f1:real^3->real^3)) (radial_ext f1')` THEN
    SIMP_TAC[diffeomorphism_on];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. norm(radial_ext (f1:real^3->real^3) x) = norm x` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMT_RADIAL_EXT_NORM THEN ASM_MESON_TAC[sphere_diffeo];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `\w. (B1:real^3->A)(r0 % w)`; `(E:real^3->A) o radial_ext f1`; `L:real`;
                 `b2:real^3->A`; `\v. (f:real^3->real^3)((f1:real^3->real^3) v)`;
                 `\v. (f1':real^3->real^3)((f':real^3->real^3) v)`; `V:A->bool`]
                APX_A25_CAPPED_BALLS) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC SMT_SPHERE_DIFFEO_COMPOSE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
      MAP_EVERY EXISTS_TAC [`annulus (&1) L:real^3->bool`; `annulus (&1) L:real^3->bool`;
                            `radial_ext (f1':real^3->real^3)`] THEN
      ASM_REWRITE_TAC[SUBSET_REFL];
      X_GEN_TAC `x:real^3` THEN REWRITE_TAC[annulus; IN_ELIM_THM; o_THM] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(E:real^3->A)(radial_ext f1 x) = N0(radial_ext f1 x)` SUBST1_TAC THENL
       [MATCH_MP_TAC(ASSUME `!x. x IN annulus (&1) (&3 / &2) ==> (E:real^3->A) x = N0 x`) THEN
        REWRITE_TAC[annulus; IN_ELIM_THM;
                    ASSUME `!x:real^3. norm(radial_ext (f1:real^3->real^3) x) = norm x`] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[ASSUME `!w. (N0:real^3->A) w = e1(r0 % w)`] THEN
      SUBGOAL_THEN `(B1:real^3->A)(r0 % x) = e1(radial_ext f1 (r0 % x))` SUBST1_TAC THENL
       [MATCH_MP_TAC(ASSUME `!x. &1 < norm x ==> (B1:real^3->A) x = e1 (radial_ext f1 x)`) THEN
        REWRITE_TAC[NORM_MUL] THEN
        SUBGOAL_THEN `abs r0 = r0` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `&1 * &1 < r0 * norm(x:real^3)` MP_TAC THENL
         [MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
        ALL_TAC] THEN
      AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC SMT_RADIAL_EXT_HOMOG THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
      SUBGOAL_THEN `&0 < norm(x:real^3)` ASSUME_TAC THENL
       [UNDISCH_TAC `(x:real^3) IN annulus (L / &2) L` THEN
        REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `radial_ext (f1:real^3->real^3) x IN annulus (L / &2) L` ASSUME_TAC THENL
       [UNDISCH_TAC `(x:real^3) IN annulus (L / &2) L` THEN
        REWRITE_TAC[annulus; IN_ELIM_THM;
                    ASSUME `!x:real^3. norm(radial_ext (f1:real^3->real^3) x) = norm x`];
        ALL_TAC] THEN
      REWRITE_TAC[MATCH_MP (ASSUME `!x. x IN annulus (L / &2) L
                                    ==> (E:real^3->A) x = (b2:real^3->A) (L / norm x % (f:real^3->real^3) (inv (norm x) % x))`)
                           (ASSUME `radial_ext (f1:real^3->real^3) x IN annulus (L / &2) L`)] THEN
      REWRITE_TAC[ASSUME `!x:real^3. norm(radial_ext (f1:real^3->real^3) x) = norm x`] THEN
      SUBGOAL_THEN `inv(norm x) % radial_ext (f1:real^3->real^3) x = f1(inv(norm x) % x)`
      SUBST1_TAC THENL
       [REWRITE_TAC[radial_ext; VECTOR_MUL_ASSOC] THEN
        SUBGOAL_THEN `inv(norm(x:real^3)) * norm x = &1` SUBST1_TAC THENL
         [MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[VECTOR_MUL_LID]];
        REFL_TAC];
      REWRITE_TAC[ASSUME `IMAGE (\w. (B1:real^3->A) (r0 % w)) (cball(vec 0,&1)) =
                          IMAGE (B1:real^3->A) (cball(vec 0,r0))`;
                  ASSUME `IMAGE ((E:real^3->A) o radial_ext f1) (annulus (&1) L) =
                          IMAGE E (annulus (&1) L)`;
                  ASSUME `IMAGE (E:real^3->A) (annulus (&1) L) UNION
                          IMAGE (b2:real^3->A) (cball(vec 0,&1)) = Os`] THEN
      CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[ASSUME `IMAGE (\w. (B1:real^3->A) (r0 % w)) (cball(vec 0,&1)) =
                          IMAGE (B1:real^3->A) (cball(vec 0,r0))`;
                  ASSUME `IMAGE ((E:real^3->A) o radial_ext f1) (annulus (&1) L) =
                          IMAGE E (annulus (&1) L)`] THEN
      UNDISCH_TAC `IMAGE (E:real^3->A) (annulus (&1) L) UNION
                   IMAGE (b2:real^3->A) (cball(vec 0,&1)) = Os` THEN
      UNDISCH_TAC `DISJOINT (IMAGE (B1:real^3->A) (cball(vec 0,r0))) Os` THEN
      MATCH_ACCEPT_TAC(SET_RULE `!K E B O. DISJOINT K O ==> E UNION B = O ==>
                                           DISJOINT K (E:A->bool)`);
      REWRITE_TAC[ASSUME `IMAGE (\w. (B1:real^3->A) (r0 % w)) (cball(vec 0,&1)) =
                          IMAGE (B1:real^3->A) (cball(vec 0,r0))`] THEN
      UNDISCH_TAC `IMAGE (E:real^3->A) (annulus (&1) L) UNION
                   IMAGE (b2:real^3->A) (cball(vec 0,&1)) = Os` THEN
      UNDISCH_TAC `DISJOINT (IMAGE (B1:real^3->A) (cball(vec 0,r0))) Os` THEN
      MATCH_ACCEPT_TAC(SET_RULE `!K E B O. DISJOINT K O ==> E UNION B = O ==>
                                           DISJOINT K (B:A->bool)`);
      REWRITE_TAC[ASSUME `IMAGE ((E:real^3->A) o radial_ext f1) (annulus (&1) L) =
                          IMAGE E (annulus (&1) L)`] THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b1':real^3->A` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC))))) THEN
  MATCH_MP_TAC APX_A25_TWO_BALLS_INTRO THEN
  MAP_EVERY EXISTS_TAC [`b1':real^3->A`; `b2:real^3->A`;
                        `\v. (f:real^3->real^3)((f1:real^3->real^3) v)`;
                        `\v. (f1':real^3->real^3)((f':real^3->real^3) v)`; `r:real`] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC(INST_TYPE [`:3`,`:N`] APX_COMPONENT_OPEN) THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^3))->bool` THEN ASM_REWRITE_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC APX_A25_BALL2_IN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    UNDISCH_TAC `V = IMAGE (b1':real^3->A) (cball(vec 0,&1)) UNION IMAGE (b2:real^3->A) (cball(vec 0,&1))` THEN
    SET_TAC[];
    MATCH_MP_TAC APX_A25_BALL2_IN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    UNDISCH_TAC `V = IMAGE (b1':real^3->A) (cball(vec 0,&1)) UNION IMAGE (b2:real^3->A) (cball(vec 0,&1))` THEN
    SET_TAC[];
    MATCH_MP_TAC SMT_SPHERE_DIFFEO_COMPOSE THEN ASM_REWRITE_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The ball-cap case.  A packing bound for disjoint necks; the switching     *)
(* step (clean start, or the Schoenflies statement: two balls, or a new base *)
(* cap whose core swallows the old one and holds one more disjoint neck);    *)
(* switching stops, so V is two balls.                                       *)
(* ------------------------------------------------------------------------- *)

(* A packing bound: centres in a compact set of ep-necks with pairwise    *)
(* disjoint neck domains are boundedly many (adapted from               *)
(* APX_CHAIN_CARD_BOUND).                                                 *)

let APX_A25_PACK = prove
 (`!top atlas (g:A->real^3^3) eps K.
     apx_ch_ctx top atlas g eps /\ compact_in top K
     ==> ?N. !Ix x (e:num->real^3->A).
               (!i. i IN Ix ==> rfs_neck (top,atlas) g eps (x i) (e i) /\ x i IN K) /\
               (!i j. i IN Ix /\ j IN Ix /\ ~(i = j)
                      ==> DISJOINT (IMAGE (e i) (rfs_neck_dom eps))
                                   (IMAGE (e j) (rfs_neck_dom eps)))
               ==> FINITE Ix /\ CARD Ix <= N`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[apx_ch_ctx] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_ch_ctx")) (concl th))) THEN
  SUBGOAL_THEN `?Rm. &1 <= Rm /\ !p. p IN K ==> mfd_scalar atlas (g:A->real^3^3) p <= Rm`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `euclideanreal`; `mfd_scalar atlas (g:A->real^3^3)`;
                   `K:A->bool`] IMAGE_COMPACT_IN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_SCALAR_CONTINUOUS THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[COMPACT_IN_EUCLIDEANREAL; MBOUNDED_REAL_EUCLIDEAN_METRIC; real_bounded;
                FORALL_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_TAC `B:real` o CONJUNCT1) THEN
    EXISTS_TAC `max (&1) B` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `p:A` THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `p:A`) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(sqrt Rm) /\ &0 < inv(&8 * eps)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `r = &99 / &100 * inv(sqrt Rm) * inv(&8 * eps)` THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* a finite cover of K by balls of radius r / 2 *)
  UNDISCH_TAC `compact_in top (K:A->bool)` THEN REWRITE_TAC[compact_in] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o SPEC `{mfd_ball (top,atlas) (g:A->real^3^3) p (r / &2) | p IN K}`)) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM] THEN X_GEN_TAC `p:A` THEN DISCH_TAC THEN
      EXISTS_TAC `p:A` THEN ASM_SIMP_TAC[MFD_CENTRE_IN_BALL] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `CARD(V:(A->bool)->bool)` THEN
  MAP_EVERY X_GEN_TAC [`Ix:num->bool`; `x:num->A`; `e:num->real^3->A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!i. i IN Ix ==> rfs_neck (top,atlas) g eps ((x:num->A) i) ((e:num->real^3->A) i)`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!i. i IN Ix ==> (x:num->A) i IN K` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  (* separation of the centres *)
  SUBGOAL_THEN
   `!i j. i IN Ix /\ j IN Ix /\ mfd_joinable (top,atlas) ((x:num->A) i) (x j) /\
          mfd_dist (top,atlas) (g:A->real^3^3) (x i) (x j) < r ==> i = j`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `r <= &99 / &100 * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) ((x:num->A) i))) *
                       inv(&8 * eps)` ASSUME_TAC THENL
     [EXPAND_TAC "r" THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN
      SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) ((x:num->A) i)` ASSUME_TAC THENL
       [FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(i:num) IN Ix`) o check (fun th ->
          is_forall (concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck")) (concl th) &&
          not (can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_dist"))
                              (concl th)))) THEN
        SIMP_TAC[rfs_neck];
        ALL_TAC] THEN
      ASM_SIMP_TAC[SQRT_POS_LT; SQRT_MONO_LE; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `(x:num->A) i`; `(e:num->real^3->A) i`; `(x:num->A) j`]
                  APX_CENTRE_DEEP_BALL) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`] o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(x:num->A) j IN IMAGE ((e:num->real^3->A) j) (rfs_neck_dom eps)` MP_TAC THENL
     [SUBGOAL_THEN `rfs_neck (top,atlas) g eps ((x:num->A) j) ((e:num->real^3->A) j)` MP_TAC
      THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
      MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(x:num->A) j IN IMAGE ((e:num->real^3->A) j) (sphere(vec 0,&1))` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:num->A) j IN IMAGE ((e:num->real^3->A) i) (rfs_neck_dom eps)` MP_TAC THENL
     [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i IN Ix ==> ?B. B IN V /\ (x:num->A) i IN B` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(x:num->A) i IN UNIONS V` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS] THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `f = \i. @B. B IN V /\ (x:num->A) i IN B` THEN
  SUBGOAL_THEN `!i j. i IN Ix /\ j IN Ix /\ (f:num->A->bool) i = f j ==> i = j`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN EXPAND_TAC "f" THEN BETA_TAC THEN
    STRIP_TAC THEN
    ABBREV_TAC `B0 = @B. B IN V /\ (x:num->A) i IN B` THEN
    SUBGOAL_THEN `B0 IN V /\ (x:num->A) i IN B0 /\ x j IN B0` STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o SELECT_RULE o C MATCH_MP (ASSUME `(i:num) IN Ix`) o check (fun th ->
        is_forall (concl th) && can (find_term (fun t -> t = `V:(A->bool)->bool`)) (concl th))) THEN
      FIRST_ASSUM(MP_TAC o SELECT_RULE o C MATCH_MP (ASSUME `(j:num) IN Ix`) o check (fun th ->
        is_forall (concl th) && can (find_term (fun t -> t = `V:(A->bool)->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `?p. p IN K /\ B0 = mfd_ball (top,atlas) (g:A->real^3^3) p (r / &2)`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `B0 IN (V:(A->bool)->bool)` THEN
      UNDISCH_TAC `V SUBSET {mfd_ball (top,atlas) (g:A->real^3^3) p (r / &2) | p IN K}` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(x:num->A) i IN B0` THEN UNDISCH_TAC `(x:num->A) j IN B0` THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_ball")) (concl th))) THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `mfd_joinable (top,(atlas:((A->bool)#(A->real^3))->bool)) ((x:num->A) i) p`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `(x:num->A) i`;
                     `p:A`] MFD_JOINABLE_SYM) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `r:real`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_dist")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `p:A` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `mfd_dist (top,atlas) (g:A->real^3^3) ((x:num->A) i) p +
                  mfd_dist (top,atlas) g p (x j)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_REWRITE_TAC[];
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `(x:num->A) i`; `p:A`] MFD_DIST_SYM) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:num->A->bool) Ix SUBSET V` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    EXPAND_TAC "f" THEN BETA_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SELECT_RULE o C MATCH_MP (ASSUME `(i:num) IN Ix`) o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `V:(A->bool)->bool`)) (concl th))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (Ix:num->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:num->A->bool`; `Ix:num->bool`] FINITE_IMAGE_INJ_EQ) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `V:(A->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD(IMAGE (f:num->A->bool) Ix)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN
    ASM_MESON_TAC[];
    MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[]]);;

(* Neck slabs of a ball cap at positive levels are slabs of its extended   *)
(* core.                                                                   *)

let APX_A25_CORE_SLAB = prove
 (`!top atlas (g:A->real^3^3) C eps U (bb:real^3->A) e' f a b.
     hausdorff_space top /\ &0 < eps /\ eps <= &1 / &8 /\
     apx_bcap (top,atlas) g C eps U bb e' f /\ &0 <= a /\ b <= inv eps
     ==> IMAGE e' (apx_slab a b) SUBSET IMAGE (apx_bext bb e' f) (apx_slab a b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[apx_bcap] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_bcap")) (concl th))) THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
                mfd_param top atlas (rfs_neck_dom eps) (e':real^3->A)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `bb:real^3->A`;
                 `e':real^3->A`; `f:real^3->real^3`; `f':real^3->real^3`; `eps:real`]
                APX_BEXT_FACTS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[mfd_ball_chart]; STRIP_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&1 < norm(v:real^3)` ASSUME_TAC THENL
   [UNDISCH_TAC `(v:real^3) IN apx_slab a b` THEN REWRITE_TAC[apx_slab; annulus; IN_ELIM_THM] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> x < y /\ y < z ==> &1 < y`) THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[SQRT_POS_LE; REAL_POS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`bb:real^3->A`; `e':real^3->A`; `f:real^3->real^3`; `f':real^3->real^3`;
                 `v:real^3`] APX_A25_BEXT_E) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
  UNDISCH_TAC `(v:real^3) IN apx_slab a b` THEN
  REWRITE_TAC[apx_slab; annulus; IN_ELIM_THM] THEN ASM_REWRITE_TAC[]);;

(* A ball cap meeting a component lies in it. *)

let APX_A25_CAP_IN_V = prove
 (`!top atlas (g:A->real^3^3) C eps U (bb:real^3->A) e' f V.
     apx_bcap (top,atlas) g C eps U bb e' f /\ V IN connected_components_of top /\
     ~DISJOINT U V
     ==> U SUBSET V`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC APX_A25_IN_COMPONENT THEN EXISTS_TAC `top:A topology` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(INST_TYPE [`:3`,`:N`] APX_JOINABLE_IN_CONNECTED) THEN
  EXISTS_TAC `atlas:((A->bool)#(A->real^3))->bool` THEN
  MATCH_MP_TAC APX_CAP_JOINABLE THEN
  MAP_EVERY EXISTS_TAC [`g:A->real^3^3`; `C:real`; `eps:real`;
                        `IMAGE (bb:real^3->A) (ball(vec 0,&1))`] THEN
  UNDISCH_TAC `apx_bcap (top,atlas) (g:A->real^3^3) C eps U bb e' f` THEN SIMP_TAC[apx_bcap]);;

(* The switching step: from a base ball cap U whose core up to level      *)
(* 1/(2 eps) holds n pairwise disjoint ep-necks centred in V, either V is  *)
(* two balls or another ball cap does the same with n + 1 necks (the new   *)
(* neck at level 3/(8 eps) of the new cap, outside its core up to level    *)
(* 1/(4 eps), which contains the old core).                                *)

let APX_A25_SWITCH_STEP = prove
 (`!u top atlas (g:A->real^3^3) C eps ep V n.
     APX_SCHOENFLIES_REQ_STATEMENT (u:A->bool) /\
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     apx_sphere_sep top atlas /\ V IN connected_components_of top /\ compact_in top V /\
     (!x. x IN V ==> apx_neck_or_core (top,atlas) g C eps x) /\
     &0 < eps /\ apx_kc * eps = ep /\ ep <= &1 / &1024 /\
     apx_ch_ctx top atlas g ep /\ apx_ch_pair top atlas g ep /\ apx_ch_more top atlas g ep /\
     apx_ch_n4r top atlas g ep /\ apx_ch_ctx top atlas g eps /\ apx_cl_rat top atlas g ep /\
     apx_a13_ctx top atlas g ep /\
     (!U Y p. rfs_cap (top,atlas) g C eps U Y /\ rfs_twisted_chart top atlas p /\
              IMAGE p (annulus (&1 / &4) (&4)) SUBSET U ==> DISJOINT U V) /\
     (?U bb e' f xs Ns.
        apx_bcap (top,atlas) g C eps U bb e' f /\ ~DISJOINT V (IMAGE bb (ball(vec 0,&1))) /\
        (!k. k < n ==> rfs_neck (top,atlas) g ep (xs k) (Ns k) /\ xs k IN V /\
                       IMAGE (Ns k) (rfs_neck_dom ep) SUBSET
                       IMAGE (apx_bext bb e' f) (ball(vec 0,exp(inv(&2 * eps) / sqrt(&2))))) /\
        (!j k. j < n /\ k < n /\ ~(j = k)
               ==> DISJOINT (IMAGE (Ns j) (rfs_neck_dom ep)) (IMAGE (Ns k) (rfs_neck_dom ep))))
     ==> apx_two_balls (subtopology top V) (restrict_atlas atlas V) \/
         (?U bb e' f xs Ns.
            apx_bcap (top,atlas) g C eps U bb e' f /\ ~DISJOINT V (IMAGE bb (ball(vec 0,&1))) /\
            (!k. k < SUC n ==> rfs_neck (top,atlas) g ep (xs k) (Ns k) /\ xs k IN V /\
                           IMAGE (Ns k) (rfs_neck_dom ep) SUBSET
                           IMAGE (apx_bext bb e' f)
                                 (ball(vec 0,exp(inv(&2 * eps) / sqrt(&2))))) /\
            (!j k. j < SUC n /\ k < SUC n /\ ~(j = k)
                   ==> DISJOINT (IMAGE (Ns j) (rfs_neck_dom ep))
                                (IMAGE (Ns k) (rfs_neck_dom ep))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC
   `!U' bb' e'' f''. apx_bcap (top,atlas) (g:A->real^3^3) C eps U' bb' e'' f''
      ==> DISJOINT (IMAGE (apx_cp (e':real^3->A) (exp(inv(&2 * eps) / sqrt(&2)) % basis 1))
                          (annulus (&1 / &2) (&2)))
                   (IMAGE (apx_bext bb' e'' f'') (ball(vec 0,exp((&4 * inv ep) / sqrt(&2)))))`
  THENL
   [DISJ1_TAC THEN MATCH_MP_TAC APX_A25_CLEAN_CASE THEN
    MAP_EVERY EXISTS_TAC
     [`g:A->real^3^3`; `C:real`; `eps:real`; `ep:real`; `U:A->bool`; `bb:real^3->A`;
      `e':real^3->A`; `f:real^3->real^3`; `exp(inv(&2 * eps) / sqrt(&2))`;
      `exp(inv(&2 * eps) / sqrt(&2)) % basis 1:real^3`;
      `apx_cp (e':real^3->A) (exp(inv(&2 * eps) / sqrt(&2)) % basis 1)`;
      `apx_bext (bb:real^3->A) e' f`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
  DISCH_THEN(X_CHOOSE_THEN `U':A->bool` (X_CHOOSE_THEN `bb':real^3->A`
    (X_CHOOSE_THEN `e'':real^3->A` (X_CHOOSE_THEN `f'':real^3->real^3` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`u:A->bool`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `C:real`; `eps:real`; `ep:real`; `V:A->bool`; `U:A->bool`;
                 `bb:real^3->A`; `e':real^3->A`; `f:real^3->real^3`;
                 `exp(inv(&2 * eps) / sqrt(&2))`;
                 `exp(inv(&2 * eps) / sqrt(&2)) % basis 1:real^3`;
                 `apx_cp (e':real^3->A) (exp(inv(&2 * eps) / sqrt(&2)) % basis 1)`;
                 `apx_bext (bb:real^3->A) e' f`; `U':A->bool`; `bb':real^3->A`;
                 `e'':real^3->A`; `f'':real^3->real^3`] APX_A25_SCHREQ_CASE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN2 (fun th -> DISJ1_TAC THEN ACCEPT_TAC th) ASSUME_TAC) THEN
  DISJ2_TAC THEN
  (* scales *)
  SUBGOAL_THEN `&580 * eps <= ep /\ eps <= &1 / &8 /\ &0 < ep /\ &580 * inv ep <= inv eps /\
                &0 < inv ep /\ &0 < inv eps` STRIP_ASSUME_TAC THENL
   [MP_TAC APX_KC_GE THEN DISCH_TAC THEN
    SUBGOAL_THEN `&580 * eps <= ep` ASSUME_TAC THENL
     [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `apx_kc * eps = ep`)) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `inv ep <= inv(&580 * eps)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_INV_MUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    SUBGOAL_THEN `&0 < inv ep /\ &0 < inv eps` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
  ABBREV_TAC `t = &3 * inv(&8 * eps)` THEN
  SUBGOAL_THEN `&0 <= --inv ep + t /\ inv(&4 * eps) <= --inv ep + t /\
                inv ep + t <= inv(&2 * eps) /\ &0 < t /\ t <= inv(&2 * eps) /\
                inv(&4 * eps) <= inv(&2 * eps) /\ inv(&2 * eps) <= inv eps /\
                abs t <= &3 / (&4 * eps) /\ &0 < inv(&4 * eps)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN REWRITE_TAC[real_div; REAL_INV_MUL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`eps:real`; `t:real`] APX_A25_LEVEL_PT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `yn:real^3 = exp(t / sqrt(&2)) % basis 1` THEN
  SUBGOAL_THEN `?h''. sphere_diffeo (f'':real^3->real^3) h''` (X_CHOOSE_TAC `h'':real^3->real^3`)
  THENL [ASM_MESON_TAC[apx_bcap]; ALL_TAC] THEN
  SUBGOAL_THEN `?z''. rfs_neck (top,atlas) (g:A->real^3^3) eps z'' e''` (X_CHOOSE_TAC `z'':A`)
  THENL [ASM_MESON_TAC[apx_bcap]; ALL_TAC] THEN
  SUBGOAL_THEN `?h. sphere_diffeo (f:real^3->real^3) h` (X_CHOOSE_TAC `h:real^3->real^3`)
  THENL [ASM_MESON_TAC[apx_bcap]; ALL_TAC] THEN
  (* the extended cores *)
  SUBGOAL_THEN `mfd_param top atlas (ball(vec 0,exp(inv eps / sqrt(&2))))
                  (apx_bext (bb':real^3->A) e'' f'') /\
                IMAGE (apx_bext (bb':real^3->A) e'' f'') (ball(vec 0,exp(inv(&4 * eps) / sqrt(&2))))
                SUBSET U' /\
                IMAGE (apx_bext (bb:real^3->A) e' f) (ball(vec 0,exp(inv(&2 * eps) / sqrt(&2))))
                SUBSET U` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `apx_bcap (top,atlas) (g:A->real^3^3) C eps U' bb' e'' f''` THEN
      REWRITE_TAC[apx_bcap; mfd_ball_chart] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `bb':real^3->A`;
                     `e'':real^3->A`; `f'':real^3->real^3`; `h'':real^3->real^3`; `eps:real`]
                    APX_BEXT_FACTS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[rfs_neck]; SIMP_TAC[]];
      MATCH_MP_TAC APX_BEXT_IN_U THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `g:A->real^3^3`; `C:real`; `eps:real`] THEN
      ASM_REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC APX_BEXT_IN_U THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `g:A->real^3^3`; `C:real`; `eps:real`] THEN
      ASM_REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `B = apx_bext (bb:real^3->A) e' f` THEN
  ABBREV_TAC `B' = apx_bext (bb':real^3->A) e'' f''` THEN
  ABBREV_TAC `r0 = exp(inv(&2 * eps) / sqrt(&2))` THEN
  ABBREV_TAC `rho = exp(inv(&4 * eps) / sqrt(&2))` THEN
  (* both caps lie in V *)
  SUBGOAL_THEN `(U:A->bool) SUBSET V` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_A25_CAP_IN_V THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:A->real^3^3`; `C:real`; `eps:real`; `bb:real^3->A`;
                          `e':real^3->A`; `f:real^3->real^3`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~DISJOINT V (IMAGE (bb:real^3->A) (ball(vec 0,&1)))` THEN
    SUBGOAL_THEN `IMAGE (bb:real^3->A) (ball(vec 0,&1)) SUBSET U` MP_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (bb:real^3->A) (ball(vec 0,&2))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; IN_BALL_0] THEN REAL_ARITH_TAC;
        ASM_MESON_TAC[apx_bcap]];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(B:real^3->A) (vec 0) IN IMAGE (B:real^3->A) (ball(vec 0,r0))` ASSUME_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[CENTRE_IN_BALL] THEN
    EXPAND_TAC "r0" THEN REWRITE_TAC[REAL_EXP_POS_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(U':A->bool) SUBSET V` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_A25_CAP_IN_V THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:A->real^3^3`; `C:real`; `eps:real`; `bb':real^3->A`;
                          `e'':real^3->A`; `f'':real^3->real^3`] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`(U:A->bool) SUBSET V`;
      `IMAGE (B:real^3->A) (ball(vec 0,r0)) SUBSET U`;
      `IMAGE (B':real^3->A) (ball(vec 0,rho)) SUBSET U'`;
      `IMAGE (B:real^3->A) (ball(vec 0,r0)) SUBSET IMAGE (B':real^3->A) (ball(vec 0,rho))`;
      `(B:real^3->A) (vec 0) IN IMAGE (B:real^3->A) (ball(vec 0,r0))`] THEN
    MATCH_ACCEPT_TAC(SET_RULE `!x:A Q Q' U' U V. x IN Q ==> Q SUBSET Q' ==> Q' SUBSET U' ==>
                                 Q SUBSET U ==> U SUBSET V ==> ~DISJOINT U' V`);
    ALL_TAC] THEN
  (* the new neck *)
  SUBGOAL_THEN `rfs_neck (top,atlas) (g:A->real^3^3) ep ((e'':real^3->A) yn) (apx_cp e'' yn)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC APX_CP_NECK THEN MAP_EVERY EXISTS_TAC [`eps:real`; `z'':A`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(e'':real^3->A) yn IN V` ASSUME_TAC THENL
   [SUBGOAL_THEN `IMAGE (e'':real^3->A) (rfs_neck_dom eps) SUBSET U'` MP_TAC THENL
     [ASM_MESON_TAC[apx_bcap]; ALL_TAC] THEN
    UNDISCH_TAC `(yn:real^3) IN rfs_neck_dom eps` THEN UNDISCH_TAC `(U':A->bool) SUBSET V` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (apx_cp (e'':real^3->A) yn) (rfs_neck_dom ep) =
                IMAGE e'' (apx_slab (--inv ep + t) (inv ep + t))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`e'':real^3->A`; `yn:real^3`; `eps:real`] APX_CP_FACTS) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `apx_sval(yn:real^3) = t`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[APX_SLAB_NECK_DOM];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (e'':real^3->A) (apx_slab (--inv ep + t) (inv ep + t)) SUBSET
                IMAGE (B':real^3->A) (apx_slab (--inv ep + t) (inv ep + t))` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM(ASSUME `apx_bext (bb':real^3->A) e'' f'' = B'`)] THEN
    MATCH_MP_TAC APX_A25_CORE_SLAB THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:A->real^3^3`; `C:real`; `eps:real`; `U':A->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (B':real^3->A) (apx_slab (--inv ep + t) (inv ep + t)) SUBSET
                IMAGE (B':real^3->A) (ball(vec 0,r0)) /\
                DISJOINT (IMAGE (B':real^3->A) (apx_slab (--inv ep + t) (inv ep + t)))
                         (IMAGE (B':real^3->A) (ball(vec 0,rho))) /\
                IMAGE (B':real^3->A) (ball(vec 0,rho)) SUBSET IMAGE (B':real^3->A) (ball(vec 0,r0))`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["r0"; "rho"] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; apx_slab; annulus; IN_ELIM_THM; IN_BALL_0] THEN
      GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH `b <= c ==> a < x /\ x < b ==> x < c`) THEN
      REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_SIMP_TAC[REAL_LE_DIV2_EQ];
      MATCH_MP_TAC APX_PARAM_IMAGE_DISJOINT THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `ball(vec 0:real^3,exp(inv eps / sqrt(&2)))`] THEN
      REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        REWRITE_TAC[SUBSET; apx_slab; annulus; IN_ELIM_THM; IN_BALL_0] THEN GEN_TAC THEN
        MATCH_MP_TAC(REAL_ARITH `b <= c ==> a < x /\ x < b ==> x < c`) THEN
        REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC SUBSET_BALL THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
        ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; apx_slab; annulus;
                    IN_ELIM_THM; IN_BALL_0] THEN
        GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH `c <= a ==> ~((a < x /\ x < b) /\ x < c)`) THEN
        REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_SIMP_TAC[REAL_LE_DIV2_EQ]];
      MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC SUBSET_BALL THEN
      REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_SIMP_TAC[REAL_LE_DIV2_EQ]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`U':A->bool`; `bb':real^3->A`; `e'':real^3->A`; `f'':real^3->real^3`;
    `\k:num. if k = n then (e'':real^3->A) yn else xs k`;
    `\k:num. if k = n then apx_cp (e'':real^3->A) yn else Ns k`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `IMAGE (bb':real^3->A) (ball(vec 0,&2)) SUBSET U'` MP_TAC THENL
     [ASM_MESON_TAC[apx_bcap]; ALL_TAC] THEN
    SUBGOAL_THEN `(bb':real^3->A) (vec 0) IN IMAGE bb' (ball(vec 0,&1)) /\
                  (bb':real^3->A) (vec 0) IN IMAGE bb' (ball(vec 0,&2))` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[CENTRE_IN_BALL] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `(U':A->bool) SUBSET V` THEN SET_TAC[];
    X_GEN_TAC `k:num` THEN REWRITE_TAC[LT] THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC) THENL
     [REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (B':real^3->A) (apx_slab (--inv ep + t) (inv ep + t))` THEN
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN `~(k:num = n)` (fun th -> REWRITE_TAC[th]) THENL
       [UNDISCH_TAC `k:num < n` THEN ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `xs:num->A`)) (concl th) &&
        not(can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (B:real^3->A) (ball(vec 0,r0))` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (B':real^3->A) (ball(vec 0,rho))` THEN
      ASM_REWRITE_TAC[]];
    MAP_EVERY X_GEN_TAC [`j:num`; `k:num`] THEN REWRITE_TAC[LT] THEN
    ASM_CASES_TAC `j:num = n` THEN ASM_CASES_TAC `k:num = n` THEN ASM_REWRITE_TAC[] THENL
     [STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `xs:num->A`)) (concl th) &&
        not(can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MAP_EVERY UNDISCH_TAC
       [`IMAGE (B:real^3->A) (ball(vec 0,r0)) SUBSET IMAGE (B':real^3->A) (ball(vec 0,rho))`;
        `IMAGE ((Ns:num->real^3->A) k) (rfs_neck_dom ep) SUBSET IMAGE (B:real^3->A) (ball(vec 0,r0))`;
        `DISJOINT (IMAGE (B':real^3->A) (apx_slab (--inv ep + t) (inv ep + t)))
                  (IMAGE (B':real^3->A) (ball(vec 0,rho)))`;
        `IMAGE (e'':real^3->A) (apx_slab (--inv ep + t) (inv ep + t)) SUBSET
         IMAGE (B':real^3->A) (apx_slab (--inv ep + t) (inv ep + t))`] THEN
      MATCH_ACCEPT_TAC(SET_RULE `!A A' D O O1. A SUBSET A' ==> DISJOINT A' D ==>
                                  O SUBSET O1 ==> O1 SUBSET D ==> DISJOINT (A:A->bool) O`);
      STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `xs:num->A`)) (concl th) &&
        not(can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MAP_EVERY UNDISCH_TAC
       [`IMAGE (B:real^3->A) (ball(vec 0,r0)) SUBSET IMAGE (B':real^3->A) (ball(vec 0,rho))`;
        `IMAGE ((Ns:num->real^3->A) j) (rfs_neck_dom ep) SUBSET IMAGE (B:real^3->A) (ball(vec 0,r0))`;
        `DISJOINT (IMAGE (B':real^3->A) (apx_slab (--inv ep + t) (inv ep + t)))
                  (IMAGE (B':real^3->A) (ball(vec 0,rho)))`;
        `IMAGE (e'':real^3->A) (apx_slab (--inv ep + t) (inv ep + t)) SUBSET
         IMAGE (B':real^3->A) (apx_slab (--inv ep + t) (inv ep + t))`] THEN
      MATCH_ACCEPT_TAC(SET_RULE `!A A' D O O1. A SUBSET A' ==> DISJOINT A' D ==>
                                  O SUBSET O1 ==> O1 SUBSET D ==> DISJOINT O (A:A->bool)`)]]);;

(* The ball-cap case: switching cannot go on forever (packing), so V is    *)
(* two balls.                                                              *)

let APX_A25_BALL_CASE = prove
 (`!u top atlas (g:A->real^3^3) C eps ep V U (bb:real^3->A) e' f.
     APX_SCHOENFLIES_REQ_STATEMENT (u:A->bool) /\
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     apx_sphere_sep top atlas /\ V IN connected_components_of top /\ compact_in top V /\
     (!x. x IN V ==> apx_neck_or_core (top,atlas) g C eps x) /\
     &0 < eps /\ apx_kc * eps = ep /\ ep <= &1 / &1024 /\
     apx_ch_ctx top atlas g ep /\ apx_ch_pair top atlas g ep /\ apx_ch_more top atlas g ep /\
     apx_ch_n4r top atlas g ep /\ apx_ch_ctx top atlas g eps /\ apx_cl_rat top atlas g ep /\
     apx_a13_ctx top atlas g ep /\
     (!U Y p. rfs_cap (top,atlas) g C eps U Y /\ rfs_twisted_chart top atlas p /\
              IMAGE p (annulus (&1 / &4) (&4)) SUBSET U ==> DISJOINT U V) /\
     apx_bcap (top,atlas) g C eps U bb e' f /\ ~DISJOINT V (IMAGE bb (ball(vec 0,&1)))
     ==> apx_two_balls (subtopology top V) (restrict_atlas atlas V)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `ep:real`; `V:A->bool`] APX_A25_PACK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `M:num` (LABEL_TAC "pack")) THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!n:num. ?U (bb:real^3->A) e' f xs Ns.
        apx_bcap (top,atlas) (g:A->real^3^3) C eps U bb e' f /\
        ~DISJOINT V (IMAGE bb (ball(vec 0,&1))) /\
        (!k:num. k < n ==> rfs_neck (top,atlas) g ep (xs k) (Ns k) /\ xs k IN V /\
                       IMAGE (Ns k) (rfs_neck_dom ep) SUBSET
                       IMAGE (apx_bext bb e' f) (ball(vec 0,exp(inv(&2 * eps) / sqrt(&2))))) /\
        (!j k:num. j < n /\ k < n /\ ~(j = k)
               ==> DISJOINT (IMAGE (Ns j) (rfs_neck_dom ep)) (IMAGE (Ns k) (rfs_neck_dom ep)))`
  MP_TAC THENL
   [INDUCT_TAC THENL
     [MAP_EVERY EXISTS_TAC [`U:A->bool`; `bb:real^3->A`; `e':real^3->A`; `f:real^3->real^3`;
                            `\k:num. (e':real^3->A) (vec 0)`; `\k:num. (e':real^3->A)`] THEN
      ASM_REWRITE_TAC[LT];
      MP_TAC(ISPECL [`u:A->bool`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `C:real`; `eps:real`; `ep:real`; `V:A->bool`; `n:num`]
                    APX_A25_SWITCH_STEP) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `SUC M`) THEN
  DISCH_THEN(X_CHOOSE_THEN `U':A->bool` (X_CHOOSE_THEN `bb':real^3->A`
    (X_CHOOSE_THEN `e'':real^3->A` (X_CHOOSE_THEN `f'':real^3->real^3`
    (X_CHOOSE_THEN `xs:num->A` (X_CHOOSE_THEN `Ns:num->real^3->A` STRIP_ASSUME_TAC)))))) THEN
  USE_THEN "pack" (MP_TAC o SPECL [`{k:num | k < SUC M}`; `xs:num->A`; `Ns:num->real^3->A`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    REWRITE_TAC[CARD_NUMSEG_LT] THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The other cases and MT Prop A.25 (separating case) from                   *)
(* the Schoenflies statement: a twisted cap meeting V gives a twisted        *)
(* chart; a ball cap core meeting V gives two balls; otherwise V would be a   *)
(* tube (A.19), which is not compact.                                         *)
(* ------------------------------------------------------------------------- *)

(* The image of an open annulus under a parametrization is not compact.   *)

let APX_A25_ANNULUS_NOT_COMPACT = prove
 (`!top atlas (E:real^3->A) r1 r2.
     &0 < r1 /\ r1 < r2 /\ mfd_param top atlas (annulus r1 r2) E
     ==> ~compact_in top (IMAGE E (annulus r1 r2))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `E':A->real^3` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  SUBGOAL_THEN `compact(annulus r1 r2:real^3->bool)` MP_TAC THENL
   [REWRITE_TAC[GSYM COMPACT_IN_EUCLIDEAN] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `IMAGE (E':A->real^3) (IMAGE (E:real^3->A) (annulus r1 r2)) = annulus r1 r2`)) THEN
    MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology top (IMAGE (E:real^3->A) (annulus r1 r2))` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; SUBSET_REFL];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `r1 % basis 1:real^3` o MATCH_MP CLOSED_APPROACHABLE o
             MATCH_MP COMPACT_IMP_CLOSED) THEN
  SUBGOAL_THEN `norm(r1 % basis 1:real^3) = r1` ASSUME_TAC THENL
   [SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[annulus; IN_ELIM_THM; REAL_LT_REFL] THEN
  X_GEN_TAC `d:real` THEN DISCH_TAC THEN
  EXISTS_TAC `(r1 + min d (r2 - r1) / &2) % basis 1:real^3` THEN
  SUBGOAL_THEN `norm((r1 + min d (r2 - r1) / &2) % basis 1:real^3) = r1 + min d (r2 - r1) / &2 /\
                dist((r1 + min d (r2 - r1) / &2) % basis 1:real^3,r1 % basis 1) =
                min d (r2 - r1) / &2`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[dist; GSYM VECTOR_SUB_RDISTRIB; REAL_ARITH `(a + b) - a = b:real`] THEN
    SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

(* A twisted cap meeting a component gives a twisted chart of it. *)

let APX_A25_TWISTED_CASE = prove
 (`!top atlas (g:A->real^3^3) C eps V U Y (p:real^3->A).
     smooth_manifold_atlas top atlas /\ V IN connected_components_of top /\
     rfs_cap (top,atlas) g C eps U Y /\ rfs_twisted_chart top atlas p /\
     IMAGE p (annulus (&1 / &4) (&4)) SUBSET U /\ ~DISJOINT U V
     ==> rfs_has_twisted (subtopology top V) (restrict_atlas atlas V)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC APX_TWISTED_IN_OPEN THEN
  EXISTS_TAC `p:real^3->A` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(INST_TYPE [`:3`,`:N`] APX_COMPONENT_OPEN) THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^3))->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC APX_A25_IN_COMPONENT THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(INST_TYPE [`:3`,`:N`] APX_JOINABLE_IN_CONNECTED) THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^3))->bool` THEN
    MATCH_MP_TAC APX_CAP_JOINABLE THEN
    MAP_EVERY EXISTS_TAC [`g:A->real^3^3`; `C:real`; `eps:real`; `Y:A->bool`] THEN
    ASM_REWRITE_TAC[]]);;

(* MT Prop A.25 (separating case) from the Schoenflies statement.          *)

let APX_A25_FROM_SCHREQ = prove
 (`!u:A->bool. APX_SCHOENFLIES_REQ_STATEMENT u ==> APX_A25_STATEMENT u`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[APX_A25_STATEMENT] THEN
  X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ctx"))
    (INST_TYPE [`:A`,`:A`] APX_CH_CTX_HOLDS) THEN
  X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "more"))
    (INST_TYPE [`:A`,`:A`] APX_CH_MORE_HOLDS) THEN
  X_CHOOSE_THEN `e3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "n4r"))
    (INST_TYPE [`:A`,`:A`] APX_CH_N4R_HOLDS) THEN
  X_CHOOSE_THEN `e4:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rat"))
    (INST_TYPE [`:A`,`:A`] APX_CL_RAT_HOLDS) THEN
  X_CHOOSE_THEN `e5:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "a13"))
    (INST_TYPE [`:A`,`:A`] APX_A13_CTX_HOLDS) THEN
  MP_TAC(ISPEC `u:A->bool` APX_A19) THEN REWRITE_TAC[APX_A19_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `e6:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "a19"))) THEN
  MP_TAC APX_KC_GE THEN DISCH_TAC THEN
  ABBREV_TAC `m0 = min (min (min e1 e2) (min e3 e4)) (min e5 (&1 / &1024))` THEN
  SUBGOAL_THEN `&0 < m0 /\ m0 <= e1 /\ m0 <= e2 /\ m0 <= e3 /\ m0 <= e4 /\ m0 <= e5 /\
                m0 <= &1 / &1024` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < m0 / apx_kc` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `min (min (m0 / apx_kc) e6) m0` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `top:A topology`;
                       `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `V:A->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `eps <= m0 / apx_kc /\ eps <= e6 /\ eps <= m0` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(V:A->bool = {}) /\ connected_in top V` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[NONEMPTY_CONNECTED_COMPONENTS_OF; CONNECTED_IN_CONNECTED_COMPONENTS_OF];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool)` ASSUME_TAC
  THENL
   [FIRST_X_ASSUM(X_CHOOSE_TAC `x0:A` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY] o check (fun th ->
      concl th = `~(V:A->bool = {})`)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x0:A` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_neck_or_core")) (concl th))) THEN
    ASM_REWRITE_TAC[apx_neck_or_core] THEN STRIP_TAC THENL
     [ASM_MESON_TAC[rfs_neck]; ASM_MESON_TAC[rfs_cap]];
    ALL_TAC] THEN
  ABBREV_TAC `ep = apx_kc * eps` THEN
  SUBGOAL_THEN `&0 < ep /\ ep <= m0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ep" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `eps <= m0 / apx_kc` THEN
      SUBGOAL_THEN `&0 < apx_kc` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SIMP_TAC[REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `apx_ch_ctx top atlas (g:A->real^3^3) ep /\ apx_ch_pair top atlas g ep /\
                apx_ch_more top atlas g ep /\ apx_ch_n4r top atlas g ep /\
                apx_ch_ctx top atlas g eps /\ apx_cl_rat top atlas g ep /\
                apx_a13_ctx top atlas g ep` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "ctx" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
        `g:A->real^3^3`; `ep:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      USE_THEN "ctx" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
        `g:A->real^3^3`; `ep:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      USE_THEN "more" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      USE_THEN "n4r" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      USE_THEN "ctx" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
        `g:A->real^3^3`; `eps:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      USE_THEN "rat" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      USE_THEN "a13" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* (I) a twisted cap meets V *)
  ASM_CASES_TAC `?U Y p. rfs_cap (top,atlas) (g:A->real^3^3) C eps U Y /\
                         rfs_twisted_chart top atlas (p:real^3->A) /\
                         IMAGE p (annulus (&1 / &4) (&4)) SUBSET U /\ ~DISJOINT U V` THENL
   [DISJ2_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `Y:A->bool`
      (X_CHOOSE_THEN `p:real^3->A` STRIP_ASSUME_TAC))) THEN
    MATCH_MP_TAC APX_A25_TWISTED_CASE THEN
    MAP_EVERY EXISTS_TAC [`g:A->real^3^3`; `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`;
                          `p:real^3->A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!U Y p. rfs_cap (top,atlas) (g:A->real^3^3) C eps U Y /\
                        rfs_twisted_chart top atlas (p:real^3->A) /\
                        IMAGE p (annulus (&1 / &4) (&4)) SUBSET U ==> DISJOINT U V`
  (LABEL_TAC "notw") THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  (* (III) a ball cap core meets V *)
  ASM_CASES_TAC `?U (bb:real^3->A) e' f. apx_bcap (top,atlas) (g:A->real^3^3) C eps U bb e' f /\
                                         ~DISJOINT V (IMAGE bb (ball(vec 0,&1)))` THENL
   [DISJ1_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `bb:real^3->A`
      (X_CHOOSE_THEN `e':real^3->A` (X_CHOOSE_THEN `f:real^3->real^3` STRIP_ASSUME_TAC)))) THEN
    MATCH_MP_TAC APX_A25_BALL_CASE THEN
    MAP_EVERY EXISTS_TAC [`u:A->bool`; `g:A->real^3^3`; `C:real`; `eps:real`; `ep:real`;
                          `U:A->bool`; `bb:real^3->A`; `e':real^3->A`; `f:real^3->real^3`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* (II) no cap core meets V: V is a tube, not compact *)
  MATCH_MP_TAC(TAUT `F ==> p`) THEN
  SUBGOAL_THEN `!x. x IN V ==> ?e. rfs_neck (top,atlas) (g:A->real^3^3) eps x e` ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_neck_or_core")) (concl th))) THEN
    ASM_REWRITE_TAC[apx_neck_or_core] THEN
    DISCH_THEN(DISJ_CASES_THEN2 ACCEPT_TAC MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `Y:A->bool` STRIP_ASSUME_TAC)) THEN
    MATCH_MP_TAC(TAUT `F ==> p`) THEN
    FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP APX_CAP_CASES) THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `bb:real^3->A` (X_CHOOSE_THEN `e':real^3->A`
        (X_CHOOSE_THEN `f:real^3->real^3` STRIP_ASSUME_TAC))) THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_bcap")) (concl th))) THEN
      REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`U:A->bool`; `bb:real^3->A`; `e':real^3->A`; `f:real^3->real^3`] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(x:A) IN Y` THEN UNDISCH_TAC `(x:A) IN V` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      FIRST_X_ASSUM(X_CHOOSE_THEN `p:real^3->A` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`]
                    APX_CAP_CORE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      SUBGOAL_THEN `(Y:A->bool) SUBSET top closure_of Y` MP_TAC THENL
       [MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_SIMP_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
      SUBGOAL_THEN `DISJOINT (U:A->bool) V` MP_TAC THENL
       [USE_THEN "notw" MATCH_MP_TAC THEN
        MAP_EVERY EXISTS_TAC [`Y:A->bool`; `p:real^3->A`] THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `top closure_of Y SUBSET (U:A->bool)` THEN
      UNDISCH_TAC `(x:A) IN Y` THEN UNDISCH_TAC `(x:A) IN V` THEN SET_TAC[]];
    ALL_TAC] THEN
  USE_THEN "a19" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `eps:real`;
    `\(x:A) (e:real^3->A). rfs_neck (top,atlas) (g:A->real^3^3) eps x e`; `V:A->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(V:A->bool) SUBSET IMAGE (E:real^3->A) (annulus r1 r2)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (E:real^3->A) (annulus r1 r2) SUBSET V` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_A25_IN_COMPONENT THEN EXISTS_TAC `top:A topology` THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`;
                            `annulus r1 r2:real^3->bool`] THEN
      REWRITE_TAC[APX_CONNECTED_ANNULUS3; SUBSET_REFL] THEN ASM_MESON_TAC[apx_tube];
      UNDISCH_TAC `(V:A->bool) SUBSET IMAGE (E:real^3->A) (annulus r1 r2)` THEN
      UNDISCH_TAC `~(V:A->bool = {})` THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `E:real^3->A`;
                 `r1:real`; `r2:real`] APX_A25_ANNULUS_NOT_COMPACT) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[apx_tube]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (E:real^3->A) (annulus r1 r2) = V` SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]);;


(* ========================================================================= *)
(* Unit pc_p2b_kncl1 (Part 2B piece (d) of COR_9_94_L; MT Cor                *)
(* 9.88 in L form): neck tools for the noncompact canonical neighbourhoods. *)
(*  - re-centring along a neck: two exactly adjacent eps-necks from one     *)
(*    eps/K1-neck (P2BF_END_NECK_SRC);                                      *)
(*  - orienting a neck so that a given point outside its middle lies on the *)
(*    inner side of its far spheres (geodesic first exit, P2FL_NECK_OPP_SEP);*)
(*  - the one-to-one cylinder model (piece (h)).                            *)
(* ========================================================================= *)

needs "src/pc_p2b_c994req.ml";;
needs "src/pc_p2b_capfix.ml";;
needs "src/pc_cmp_soul.ml";;
needs "src/pc_cmp_bg.ml";;
needs "src/pc_p2a_l965.ml";;
needs "src/pc_rfa_htrace.ml";;
needs "src/pc_apx_chain.ml";;
needs "src/pc_p2c_c1116b.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Re-centring.  From an (eps/K1)-neck e, the maps                           *)
(* e o (exp(c) .) and e o (exp(2c) .), c = 1/(sqrt 2 eps), are eps-necks     *)
(* (P2BF_END_NECK_SRC); the second starts exactly at the central sphere of  *)
(* the first.                                                                *)
(* ------------------------------------------------------------------------- *)

let KNCL_SQRT2_POS = prove
 (`&0 < sqrt(&2)`,
  MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC);;

let KNCL_DILATE_NECK_DOM = prove
 (`!a eps. &0 < eps
     ==> IMAGE (\w:real^3. exp a % w) (rfs_neck_dom eps) =
         annulus (exp(a - inv(sqrt(&2) * eps))) (exp(a + inv(sqrt(&2) * eps)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_neck_dom] THEN
  SIMP_TAC[P2BF_DILATE_ANNULUS; REAL_EXP_POS_LT] THEN
  REWRITE_TAC[GSYM REAL_EXP_ADD; real_sub]);;

let KNCL_NECK_PAIR = prove
 (`?K1. &4 <= K1 /\
     !top atlas (g:A->real^3^3) eps z (e:real^3->A).
       &0 < eps /\ eps <= &1 / &2 /\ riemannian_metric atlas g /\
       rfs_neck (top,atlas) g (eps / K1) z e
       ==> rfs_neck (top,atlas) g eps (e(exp(inv(sqrt(&2) * eps)) % basis 1))
                    (e o (\w. exp(inv(sqrt(&2) * eps)) % w)) /\
           rfs_neck (top,atlas) g eps (e(exp(&2 * inv(sqrt(&2) * eps)) % basis 1))
                    (e o (\w. exp(&2 * inv(sqrt(&2) * eps)) % w)) /\
           IMAGE (e o (\w. exp(inv(sqrt(&2) * eps)) % w)) (rfs_neck_dom eps) =
             IMAGE e (annulus (&1) (exp(&2 * inv(sqrt(&2) * eps)))) /\
           IMAGE (e o (\w. exp(&2 * inv(sqrt(&2) * eps)) % w)) (rfs_neck_dom eps) =
             IMAGE e (annulus (exp(inv(sqrt(&2) * eps)))
                              (exp(&3 * inv(sqrt(&2) * eps))))`,
  X_CHOOSE_THEN `K0:real` (LABEL_TAC "K0") APX_CYL0_RM_BOUND THEN
  MP_TAC(SPEC `K0:real` P2BF_END_NECK_SRC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "src") THEN
  EXISTS_TAC `&4 + &576 * (&1 + abs K0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &4 <= &4 + &576 * x`) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `K1 = &4 + &576 * (&1 + abs K0)` THEN
  SUBGOAL_THEN `&4 <= K1` ASSUME_TAC THENL [EXPAND_TAC "K1" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `c = inv(sqrt(&2) * eps)` THEN
  SUBGOAL_THEN `&0 < c /\ &0 < eps / K1 /\ K1 * eps / K1 = eps /\
                inv(sqrt(&2) * eps / &2) = &2 * c /\ eps / K1 <= eps / &4`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_REWRITE_TAC[KNCL_SQRT2_POS];
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&4 <= K1` THEN CONV_TAC REAL_FIELD;
      MP_TAC KNCL_SQRT2_POS THEN UNDISCH_TAC `&0 < eps` THEN CONV_TAC REAL_FIELD;
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* the first neck *)
  USE_THEN "src" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `eps / K1`; `eps:real`; `z:A`; `e:real^3->A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM REAL_EXP_ADD; REAL_ARITH `c + c = &2 * c`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  (* the second neck *)
  USE_THEN "src" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `eps / K1`; `eps / &2`; `z:A`; `e:real^3->A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)) THEN
  ASM_REWRITE_TAC[IMAGE_o] THEN
  MP_TAC(SPECL [`&2 * c`; `eps:real`] KNCL_DILATE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN BINOP_TAC THEN AP_TERM_TAC THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Sides.  A point p far from the centre of an eps-neck e is                 *)
(* joined to a neck point e(w), 35 <= abs(sval w) <= 46, by a connected set *)
(* missing the central sphere (a minimal geodesic tail, P2FL_GEO_TAIL).     *)
(* If sval w < 0, p is separated from the outer point of every re-centred   *)
(* neck e o (exp a .) beyond the centre (P2FL_NECK_OPP_SEP twice).           *)
(* ------------------------------------------------------------------------- *)

(* Along a minimal unit-speed geodesic z = gamma(0), gamma(L), the distances *)
(* from both ends are the parameter distances.                                *)

let KNCL_GEO_DIST = prove
 (`!top atlas (g:A->real^N^N) z u L t.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
     z IN topspace top /\ mfd_tnorm g z u = &1 /\
     mfd_dist (top,atlas) g z (mfd_geo (top,atlas) g z u L) = L /\
     &0 <= t /\ t <= L
     ==> mfd_dist (top,atlas) g z (mfd_geo (top,atlas) g z u t) = t /\
         mfd_dist (top,atlas) g (mfd_geo (top,atlas) g z u t)
                  (mfd_geo (top,atlas) g z u L) = L - t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `z:A`; `u:real^N`] CMPB_GEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "gd")))) THEN
  USE_THEN "gd" (MP_TAC o SPECL [`&0`; `t:real`]) THEN
  USE_THEN "gd" (MP_TAC o SPECL [`t:real`; `L:real`]) THEN
  REMOVE_THEN "gd" (K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN DISCH_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `z:A`; `mfd_geo (top,atlas) (g:A->real^N^N) z u t`;
                 `mfd_geo (top,atlas) (g:A->real^N^N) z u L`] MFD_DIST_TRIANGLE) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let KNCL_NECK_SIDE = prove
 (`!top atlas (g:A->real^3^3) eps z (e:real^3->A) p.
     hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
     &0 < eps /\ eps <= &1 / &100 /\ rfs_neck (top,atlas) g eps z e /\
     p IN topspace top /\
     &45 * inv(sqrt(mfd_scalar atlas g z)) <= mfd_dist (top,atlas) g z p
     ==> ?K w. connected_in top K /\ p IN K /\
               K INTER IMAGE e (sphere(vec 0,&1)) = {} /\
               w IN rfs_neck_dom eps /\ e w IN K /\
               &35 <= abs(apx_sval w) /\ abs(apx_sval w) <= &46 /\
               mfd_dist (top,atlas) g z (e w) = &45 * inv(sqrt(mfd_scalar atlas g z)) /\
               mfd_dist (top,atlas) g z (e w) + mfd_dist (top,atlas) g (e w) p =
               mfd_dist (top,atlas) g z p /\
               (!y. y IN K
                    ==> &45 * inv(sqrt(mfd_scalar atlas g z)) <= mfd_dist (top,atlas) g z y)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck]) THEN
  ABBREV_TAC `R = mfd_scalar atlas (g:A->real^3^3) z` THEN
  SUBGOAL_THEN `&0 < inv(sqrt R)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:A) IN topspace top` ASSUME_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
    SUBGOAL_THEN `IMAGE (e:real^3->A) (rfs_neck_dom eps) SUBSET topspace top` MP_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
    MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(z:A) IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mfd_dist (top,atlas) (g:A->real^3^3) z p` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `z:A`; `p:A`] P2FL_MIN_GEO_EXISTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC)] THEN
  ABBREV_TAC `L = mfd_dist (top,atlas) (g:A->real^3^3) z p` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `z:A`; `u:real^3`] CMPB_GEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^3^3) z (mfd_geo (top,atlas) g z u L) = L`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. &0 <= t /\ t <= L
        ==> mfd_dist (top,atlas) (g:A->real^3^3) z (mfd_geo (top,atlas) g z u t) = t /\
            mfd_dist (top,atlas) g (mfd_geo (top,atlas) g z u t) p = L - t`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `z:A`; `u:real^3`; `L:real`; `t:real`] KNCL_GEO_DIST) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `z:A`; `e:real^3->A`; `z:A`; `u:real^3`; `L:real`; `&0`;
                 `&45 * inv(sqrt R)`] P2FL_NECK_GEO_POINT) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; REAL_ADD_LID] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `z:A`; `e:real^3->A`; `z:A`; `u:real^3`; `L:real`; `&0`;
                 `&45 * inv(sqrt R)`] P2FL_GEO_TAIL) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; REAL_ADD_LID] THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `&45 * inv(sqrt R)` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `L - t:real`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(e:real^3->A) w IN
    IMAGE (mfd_geo (top,atlas) (g:A->real^3^3) z u) (real_interval[&45 * inv(sqrt R),L])`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN IMAGE (mfd_geo (top,atlas) (g:A->real^3^3) z u)
                   (real_interval[&45 * inv(sqrt R),L])
        ==> &45 * inv(sqrt R) <= mfd_dist (top,atlas) g z y`
  ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `L - t:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`IMAGE (mfd_geo (top,atlas) (g:A->real^3^3) z u) (real_interval[&45 * inv(sqrt R),L])`;
    `w:real^3`] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* The reversed neck turns an outer point into an inner one.                 *)

let KNCL_REV_POINT = prove
 (`!(e:real^3->A) eps w.
     &0 < eps /\ w IN rfs_neck_dom eps
     ==> inv(norm w pow 2) % w IN rfs_neck_dom eps /\
         apx_rev e (inv(norm w pow 2) % w) = e w /\
         apx_sval(inv(norm w pow 2) % w) = --(apx_sval w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(w:real^3)` ASSUME_TAC THENL
   [UNDISCH_TAC `(w:real^3) IN rfs_neck_dom eps` THEN
    REWRITE_TAC[rfs_neck_dom; annulus; IN_ELIM_THM] THEN
    MP_TAC(SPEC `--(inv(sqrt(&2) * eps))` REAL_EXP_POS_LT) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(inv(norm w pow 2) % (w:real^3)) = inv(norm w)` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_POW; REAL_ABS_NORM] THEN
    UNDISCH_TAC `&0 < norm(w:real^3)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `(w:real^3) IN rfs_neck_dom eps` THEN
    REWRITE_TAC[rfs_neck_dom; annulus; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_EXP_NEG] THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REWRITE_TAC[];
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_INV THEN REWRITE_TAC[REAL_EXP_POS_LT]];
    REWRITE_TAC[apx_rev] THEN AP_TERM_TAC THEN ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM VECTOR_MUL_LID] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `&0 < norm(w:real^3)` THEN CONV_TAC REAL_FIELD;
    ASM_SIMP_TAC[apx_sval; LOG_INV] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Basic facts of kappa-solutions at time 0 and the one-to-one               *)
(* cylinder model: there every point is the centre of an evolving neck of  *)
(* every length (piece (h)).                                                 *)
(* ------------------------------------------------------------------------- *)

let KNCL_KSOL_RIEM = prove
 (`!kappa top atlas (g:real->B->real^3^3).
     p2b_kappa_solution kappa (top,atlas) g
     ==> smooth_manifold_atlas top atlas /\ hausdorff_space top /\ connected_space top /\
         ~(topspace top = {}) /\
         (!t. t <= &0 ==> riemannian_metric atlas (g t) /\ mfd_complete (top,atlas) (g t))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2b_kappa_solution; p2c_kappa_sol] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t - &1` o check (fun th ->
    can (find_term (fun u -> is_const u && fst(dest_const u) = "rfs_flow_upto")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[rfs_flow_upto; ricci_flow_on] THEN STRIP_TAC THEN
  ASM_CASES_TAC `t = &0` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

let KNCL_M1_CANON = prove
 (`!(w:B->bool) top atlas (g:real->B->real^3^3) p lam C eps L x.
     P2B_CYL_MODEL_NECKS_STATEMENT w /\
     smooth_manifold_atlas top atlas /\ &0 < lam /\
     (!t. t <= &0 ==> riemannian_metric atlas (g t)) /\
     IMAGE p {y:real^3 | ~(y = vec 0)} = topspace top /\
     (!y. ~(y = vec 0) ==> ?r. &0 < r /\ r < norm y /\ mfd_param top atlas (ball(y,r)) p) /\
     (!y z. ~(y = vec 0) /\ ~(z = vec 0) ==> (p y = p z <=> z = y)) /\
     (!t y. t <= &0 /\ ~(y = vec 0)
            ==> rfs_pullback atlas p (g t) y = lam %% cylinder_flow (t / lam) y) /\
     &0 < eps /\ &1 <= L /\ x IN topspace top
     ==> p2b_canon_L (p2b_kview (top,atlas) g) C eps L x (&0)`,
  REWRITE_TAC[P2B_CYL_MODEL_NECKS_STATEMENT] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[p2b_canon_L] THEN DISJ1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `g:real->B->real^3^3`; `p:real^3->B`; `lam:real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Separation for re-centred necks.  If p is joined to an                    *)
(* inner point e(w) of an eps-neck e by a connected set missing the central *)
(* sphere, then the sphere e(sphere(exp a)) of the re-centred neck          *)
(* e o (exp a .) separates p from its outer point, and p lies in the       *)
(* component of its inner point.                                            *)
(* ------------------------------------------------------------------------- *)

let KNCL_SPHERE_DILATE = prove
 (`!c. &0 < c ==> IMAGE (\y:real^3. c % y) (sphere(vec 0,&1)) = sphere(vec 0,c)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_SPHERE_0] THEN
  X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[NORM_MUL] THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC THEN EXISTS_TAC `inv c % (x:real^3)` THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
    ASM_REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < c ==> abs c = c`; REAL_MUL_LINV; REAL_LT_IMP_NZ]]);;

let KNCL_NECK_INJ = prove
 (`!top atlas (g:A->real^3^3) eps z (e:real^3->A) y1 y2.
     rfs_neck (top,atlas) g eps z e /\ y1 IN rfs_neck_dom eps /\ y2 IN rfs_neck_dom eps /\
     e y1 = e y2
     ==> y1 = y2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  ASM_MESON_TAC[]);;

let KNCL_NECK_IMAGE_DISJ = prove
 (`!top atlas (g:A->real^3^3) eps z (e:real^3->A) s t.
     rfs_neck (top,atlas) g eps z e /\ s SUBSET rfs_neck_dom eps /\
     t SUBSET rfs_neck_dom eps /\ DISJOINT s t
     ==> DISJOINT (IMAGE e s) (IMAGE e t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
  X_GEN_TAC `q:A` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y1:real^3` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `y2:real^3` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `y1:real^3 = y2` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC KNCL_NECK_INJ THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:A->real^3^3`; `eps:real`; `z:A`; `e:real^3->A`] THEN
    ASM_MESON_TAC[SUBSET];
    ASM SET_TAC[]]);;

let KNCL_NECK_CONNECTED = prove
 (`!top atlas (g:A->real^3^3) eps z (e:real^3->A) s.
     rfs_neck (top,atlas) g eps z e /\ s SUBSET rfs_neck_dom eps /\ connected s
     ==> connected_in top (IMAGE e s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
  MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
  MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
  ASM_REWRITE_TAC[]);;

let KNCL_NECK_IN_TOPSPACE = prove
 (`!top atlas (g:A->real^3^3) eps z (e:real^3->A) y.
     rfs_neck (top,atlas) g eps z e /\ y IN rfs_neck_dom eps ==> e y IN topspace top`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN ASM SET_TAC[]);;

(* The annuli and spheres used for the re-centred necks lie in neck_dom.     *)

(* sval of a multiple of basis 1.                                             *)

let KNCL_SVAL_BASIS = prove
 (`!r. &0 < r ==> apx_sval(r % basis 1:real^3) = sqrt(&2) * log r /\
                  norm(r % basis 1:real^3) = r`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `norm(r % basis 1:real^3) = r` ASSUME_TAC THENL
   [SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[apx_sval]]);;

let KNCL_SHIFT_SEP = prove
 (`!top atlas (g:A->real^3^3) eps z (e:real^3->A) K w p a eps' z'.
     hausdorff_space top /\ connected_space top /\ apx_sphere_sep top atlas /\
     riemannian_metric atlas g /\
     &0 < eps /\ eps <= &1 / &100 /\ rfs_neck (top,atlas) g eps z e /\
     connected_in top K /\ p IN K /\ K INTER IMAGE e (sphere(vec 0,&1)) = {} /\
     w IN rfs_neck_dom eps /\ e w IN K /\ apx_sval w < &0 /\
     &0 < a /\ &4 / &3 * exp a < exp(inv(sqrt(&2) * eps)) /\
     &0 < eps' /\ eps' <= &1 / &100 /\
     rfs_neck (top,atlas) g eps' z' (e o (\y. exp a % y))
     ==> apx_separates top (IMAGE (e o (\y. exp a % y)) (sphere(vec 0,&1))) p
                           ((e o (\y. exp a % y)) (&4 / &3 % basis 1)) /\
         connected_component_of
           (subtopology top
              (topspace top DIFF IMAGE (e o (\y. exp a % y)) (sphere(vec 0,&1))))
           p ((e o (\y. exp a % y)) (&3 / &4 % basis 1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `ce = inv(sqrt(&2) * eps)` THEN
  SUBGOAL_THEN `&1 <= ce` ASSUME_TAC THENL
   [EXPAND_TAC "ce" THEN MATCH_MP_TAC REAL_INV_1_LE THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[KNCL_SQRT2_POS];
      SUBGOAL_THEN `sqrt(&2) <= &2` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_LSQRT THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * eps` THEN
      CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 < exp a /\ exp(--ce) < &3 / &4 /\ &0 < exp a` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LT] THEN CONJ_TAC THENL
     [MP_TAC(SPEC `a:real` REAL_EXP_LE_X) THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_EXP_NEG] THEN MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&2)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN MP_TAC(SPEC `ce:real` REAL_EXP_LE_X) THEN
        ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_neck_dom eps = annulus (exp(--ce)) (exp ce):real^3->bool` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[rfs_neck_dom]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(w:real^3) /\ norm(w:real^3) < &1 /\ exp(--ce) < norm(w:real^3)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(w:real^3) IN rfs_neck_dom eps` THEN
    ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < norm(w:real^3)` ASSUME_TAC THENL
     [MP_TAC(SPEC `--ce` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `log(norm(w:real^3)) < &0` MP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `~(&0 <= l) ==> l < &0`) THEN DISCH_TAC THEN
      UNDISCH_TAC `apx_sval w < &0` THEN REWRITE_TAC[apx_sval; REAL_NOT_LT] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; KNCL_SQRT2_POS];
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM LOG_1] THEN
      ASM_SIMP_TAC[LOG_MONO_LT; REAL_LT_01]];
    ALL_TAC] THEN
  SUBGOAL_THEN `sphere(vec 0:real^3,exp a) SUBSET rfs_neck_dom eps /\
                annulus (exp(--ce)) (exp a) SUBSET rfs_neck_dom eps:real^3->bool /\
                (exp a % basis 1:real^3) IN sphere(vec 0,exp a) /\
                ((&3 / &4 * exp a) % basis 1:real^3) IN annulus (exp(--ce)) (exp a) /\
                (w:real^3) IN annulus (exp(--ce)) (exp a)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &3 / &4 * exp a /\ exp a < exp ce` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM; KNCL_SVAL_BASIS] THEN
    REPEAT CONJ_TAC THEN TRY(GEN_TAC THEN DISCH_TAC) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (e o (\y. exp a % y)) (sphere(vec 0,&1)) =
                IMAGE (e:real^3->A) (sphere(vec 0,exp a))` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_SIMP_TAC[IMAGE_o; KNCL_SPHERE_DILATE]; ALL_TAC] THEN
  ABBREV_TAC `S = IMAGE (e:real^3->A) (sphere(vec 0,exp a))` THEN
  (* K misses S *)
  SUBGOAL_THEN `K INTER (S:A->bool) = {}` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `z:A`; `e:real^3->A`] P2FL_NECK_SEP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `z:A`; `e:real^3->A`; `(e:real^3->A)(&3 / &4 % basis 1)`;
                   `(e:real^3->A)(&4 / &3 % basis 1)`; `w:real^3`; `exp a % basis 1:real^3`;
                   `K:A->bool`; `S:A->bool`; `x:A`; `x:A`] P2FL_NECK_OPP_SEP) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[KNCL_SVAL_BASIS; LOG_EXP] THEN REPEAT CONJ_TAC THENL
       [ASM SET_TAC[];
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[KNCL_SQRT2_POS];
        EXPAND_TAC "S" THEN MATCH_MP_TAC KNCL_NECK_CONNECTED THEN
        MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                              `eps:real`; `z:A`] THEN
        ASM_SIMP_TAC[CONNECTED_SPHERE; DIMINDEX_3; ARITH];
        EXPAND_TAC "S" THEN REWRITE_TAC[GSYM DISJOINT] THEN
        MATCH_MP_TAC KNCL_NECK_IMAGE_DISJ THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                              `g:A->real^3^3`; `eps:real`; `z:A`] THEN
        ASM_SIMP_TAC[APX_UNIT_SPHERE_NECK_DOM] THEN
        REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_SPHERE_0; NOT_IN_EMPTY] THEN
        ASM_REAL_ARITH_TAC;
        EXPAND_TAC "S" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[apx_separates; CONNECTED_COMPONENT_OF_REFL; TOPSPACE_SUBTOPOLOGY] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  (* the connected set K' through the inner annulus *)
  ABBREV_TAC `K' = K UNION IMAGE (e:real^3->A) (annulus (exp(--ce)) (exp a))` THEN
  SUBGOAL_THEN `connected_in top (K':A->bool) /\ K' INTER S = {} /\ p IN K' /\
                (e:real^3->A)((&3 / &4 * exp a) % basis 1) IN K'` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K'" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_IN_UNION THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC KNCL_NECK_CONNECTED THEN
        MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                              `eps:real`; `z:A`] THEN
        ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`vec 0:real^3`; `exp(--ce)`; `exp a`] (CONJUNCT1 CONNECTED_ANNULUS)) THEN
        REWRITE_TAC[DIMINDEX_3; ARITH; VECTOR_SUB_RZERO; annulus];
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `(e:real^3->A) w` THEN
        ASM_SIMP_TAC[FUN_IN_IMAGE]];
      REWRITE_TAC[SET_RULE `((s:A->bool) UNION t) INTER u = {} <=> s INTER u = {} /\ t INTER u = {}`] THEN
      ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "S" THEN REWRITE_TAC[GSYM DISJOINT] THEN
      MATCH_MP_TAC KNCL_NECK_IMAGE_DISJ THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `g:A->real^3^3`; `eps:real`; `z:A`] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_SPHERE_0; annulus; IN_ELIM_THM;
                  NOT_IN_EMPTY] THEN REAL_ARITH_TAC;
      ASM SET_TAC[];
      MATCH_MP_TAC(SET_RULE `(x:A) IN t ==> x IN s UNION t`) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the re-centred neck *)
  ABBREV_TAC `e' = (e:real^3->A) o (\y. exp a % y)` THEN
  SUBGOAL_THEN `IMAGE (e':real^3->A) (sphere(vec 0,&1)) = S /\
                e'(&3 / &4 % basis 1) = (e:real^3->A)((&3 / &4 * exp a) % basis 1)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["e'"; "S"] THEN
    SIMP_TAC[IMAGE_o; KNCL_SPHERE_DILATE; REAL_EXP_POS_LT] THEN
    REWRITE_TAC[o_THM; VECTOR_MUL_ASSOC] THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&3 / &4 % basis 1:real^3) IN rfs_neck_dom eps' /\
                (&4 / &3 % basis 1:real^3) IN rfs_neck_dom eps' /\
                apx_sval(&3 / &4 % basis 1:real^3) < &0 /\
                &0 < apx_sval(&4 / &3 % basis 1:real^3)` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `eps':real` P2FL_MID_NECK_DOM) THEN ASM_REWRITE_TAC[SUBSET] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `&0 < &3 / &4 /\ &0 < &4 / &3` STRIP_ASSUME_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[KNCL_SVAL_BASIS] THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[annulus; IN_ELIM_THM; KNCL_SVAL_BASIS] THEN
      REAL_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[annulus; IN_ELIM_THM; KNCL_SVAL_BASIS] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `s * l < s * &0 ==> s * l < &0`) THEN
      MATCH_MP_TAC REAL_LT_LMUL THEN REWRITE_TAC[KNCL_SQRT2_POS] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM LOG_1] THEN MATCH_MP_TAC LOG_MONO_LT_IMP THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[KNCL_SQRT2_POS] THEN
      MATCH_MP_TAC LOG_POS_LT THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps':real`; `z':A`; `e':real^3->A`] P2FL_NECK_SEP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(e':real^3->A)(&4 / &3 % basis 1) IN topspace top /\
                ~((e':real^3->A)(&4 / &3 % basis 1) IN S)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC KNCL_NECK_IN_TOPSPACE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                            `eps':real`; `z':A`] THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
        `IMAGE (e':real^3->A) (sphere(vec 0,&1)) = S`)) THEN
      REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `eps':real`; `z':A`; `e':real^3->A`; `&4 / &3 % basis 1:real^3`;
                     `y:real^3`] KNCL_NECK_INJ) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `eps':real` APX_UNIT_SPHERE_NECK_DOM) THEN
        ASM_REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN ASM_MESON_TAC[];
        DISCH_THEN(MP_TAC o AP_TERM `norm:real^3->real`) THEN
        ASM_SIMP_TAC[KNCL_SVAL_BASIS; REAL_ARITH `&0 < &4 / &3`] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps':real`; `z':A`; `e':real^3->A`; `(e':real^3->A)(&3 / &4 % basis 1)`;
                   `(e':real^3->A)(&4 / &3 % basis 1)`; `&3 / &4 % basis 1:real^3`;
                   `&4 / &3 % basis 1:real^3`; `K':A->bool`;
                   `{(e':real^3->A)(&4 / &3 % basis 1)}`; `p:A`;
                   `(e':real^3->A)(&4 / &3 % basis 1)`] P2FL_NECK_OPP_SEP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[CONNECTED_IN_SING; IN_SING;
                      SET_RULE `{x:A} INTER s = {} <=> ~(x IN s)`];
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[connected_component_of] THEN EXISTS_TAC `K':A->bool` THEN
    ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP CONNECTED_IN_SUBSET_TOPSPACE) THEN ASM SET_TAC[]]);;


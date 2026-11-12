(* ========================================================================= *)
(* pc_apx_class: the classification results of MT Appendix A, section 5,   *)
(* and the region theorem: APX_REGION (the corrected core of MT Prop 15.3),  *)
(* MT Prop A.25 and A.21 (1)-(2) as implications from the Schoenflies-type   *)
(* statement APX_SCHOENFLIES_REQ_STATEMENT, MT Claim A.22 and the other      *)
(* alternatives of A.21.  Chains run at the scale ep = apx_kc eps, so that   *)
(* recentred copies of the surgery necks (scale dl) and of the caps'         *)
(* boundary necks (scale eps) are chain necks.                               *)
(* ========================================================================= *)

needs "src/pc_apx_chain.ml";;
needs "src/pc_apx_schreq.ml";;
needs "src/pc_smt_pole.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The recentring constant apx_kc and copies of necks.  A copy               *)
(* of a d-neck e at y1 (with |s y1| <= 3/(4d)) is e o (scaling by |y1|): an  *)
(* (apx_kc d)-neck centred at e y1 (APX_NECK_RECENTRE_GEN), whose levels are *)
(* those of e shifted by s y1.                                               *)
(* ------------------------------------------------------------------------- *)

(* Tactic helper: strip the assumption mentioning the constant NAME after   *)
(* unfolding it with the theorem DEF (FIRST_ASSUM alone would succeed on any *)
(* assumption, leaving the definition folded).                               *)

let APX_UNFOLD_ASM_TAC name (def:thm) =
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[def] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = name)) (concl th)));;

let apx_kc = new_definition
 `apx_kc = &4 + &576 * (&1 + abs(@K0. !y:real^3. ~(y = vec 0)
                                ==> lrm_deriv_norm2 0 (cylinder_flow (&0)) y <= K0 pow 2))`;;

let apx_cp = new_definition
 `apx_cp (e:real^3->A) (y:real^3) = e o (\w. norm y % w)`;;

let APX_KC_GE = prove
 (`&580 <= apx_kc`,
  REWRITE_TAC[apx_kc] THEN REAL_ARITH_TAC);;

let APX_KC_RC = prove
 (`!top atlas (g:A->real^3^3) d x (e:real^3->A) y1.
     &0 < d /\ apx_kc * d <= &1 / &2 /\
     riemannian_metric atlas g /\ rfs_neck (top,atlas) g d x e /\
     y1 IN rfs_neck_dom d /\ abs(apx_sval y1) <= &3 / (&4 * d)
     ==> rfs_neck (top,atlas) g (apx_kc * d) (e y1) (apx_cp e y1)`,
  REWRITE_TAC[apx_cp; apx_kc] THEN
  MP_TAC(SPEC `@K0. !y:real^3. ~(y = vec 0)
                    ==> lrm_deriv_norm2 0 (cylinder_flow (&0)) y <= K0 pow 2`
              (INST_TYPE [`:A`,`:A`] APX_NECK_RECENTRE_GEN)) THEN
  ANTS_TAC THENL
   [CONV_TAC SELECT_CONV THEN ACCEPT_TAC APX_CYL0_RM_BOUND; ALL_TAC] THEN
  DISCH_THEN ACCEPT_TAC);;

let APX_CP_NECK = prove
 (`!top atlas (g:A->real^3^3) d ep x (e:real^3->A) y1.
     &0 < d /\ apx_kc * d <= ep /\ ep <= &1 / &2 /\
     riemannian_metric atlas g /\ rfs_neck (top,atlas) g d x e /\
     y1 IN rfs_neck_dom d /\ abs(apx_sval y1) <= &3 / (&4 * d)
     ==> rfs_neck (top,atlas) g ep (e y1) (apx_cp e y1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC APX_NECK_MONO_GEN THEN
  EXISTS_TAC `apx_kc * d` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MP_TAC APX_KC_GE THEN REAL_ARITH_TAC;
    MATCH_MP_TAC APX_KC_RC THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

(* Levels under scaling. *)

let APX_SLAB_DILATE = prove
 (`!r a b. &0 < r
           ==> IMAGE (\w:real^3. r % w) (apx_slab a b) =
               apx_slab (a + sqrt(&2) * log r) (b + sqrt(&2) * log r)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; APX_SLAB_SVAL] THEN
  X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `w:real^3` (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
    ASM_SIMP_TAC[APX_SVAL_SCALE; VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ] THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC THEN EXISTS_TAC `inv r % y:real^3` THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
    SUBGOAL_THEN `~(inv r % y:real^3 = vec 0)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_INV_EQ_0; REAL_LT_IMP_NZ]; ALL_TAC] THEN
    MP_TAC(SPECL [`r:real`; `inv r % y:real^3`] APX_SVAL_SCALE) THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
    ASM_REAL_ARITH_TAC]);;

let APX_CP_FACTS = prove
 (`!(e:real^3->A) y1 d.
     y1 IN rfs_neck_dom d
     ==> &0 < norm y1 /\ exp(apx_sval y1 / sqrt(&2)) = norm y1 /\
         (!w. apx_cp e y1 w = e(norm y1 % w)) /\
         (!w. ~(w = vec 0) ==> apx_sval(norm y1 % w) = apx_sval w + apx_sval y1) /\
         (!a b. IMAGE (apx_cp e y1) (apx_slab a b) =
                IMAGE e (apx_slab (a + apx_sval y1) (b + apx_sval y1))) /\
         (!a b. IMAGE (apx_rev (apx_cp e y1)) (apx_slab a b) =
                IMAGE e (apx_slab (apx_sval y1 - b) (apx_sval y1 - a)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < norm(y1:real^3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[APX_SVAL_NECK_DOM; NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `exp(apx_sval y1 / sqrt(&2)) = norm(y1:real^3)` ASSUME_TAC THENL
   [REWRITE_TAC[apx_sval] THEN
    SUBGOAL_THEN `~(sqrt(&2) = &0)` ASSUME_TAC THENL
     [SIMP_TAC[SQRT_EQ_0; REAL_OF_NUM_EQ; ARITH]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_FIELD `~(s = &0) ==> (s * l) / s = l`; EXP_LOG];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&2) * log(norm(y1:real^3)) = apx_sval y1` ASSUME_TAC THENL
   [REWRITE_TAC[apx_sval]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!w:real^3. apx_cp (e:real^3->A) y1 w = e(norm y1 % w)` ASSUME_TAC THENL
   [REWRITE_TAC[apx_cp; o_THM]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!a b. IMAGE (apx_cp (e:real^3->A) y1) (apx_slab a b) =
                      IMAGE e (apx_slab (a + apx_sval y1) (b + apx_sval y1))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[apx_cp; IMAGE_o] THEN
    ASM_SIMP_TAC[APX_SLAB_DILATE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[APX_REV_IMAGE_SLAB] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[APX_SVAL_SCALE] THEN REAL_ARITH_TAC;
    REWRITE_TAC[REAL_ARITH `--x + y:real = y - x`]]);;

(* ------------------------------------------------------------------------- *)
(* Distances and levels in a neck.  (1) Near-level: a point q                *)
(* at distance less than 0.99 h (1/d - |s y|) from e y lies in the neck, at  *)
(* a level within dist / (0.99 h) of s y (N2 lower bound; the wrap-around    *)
(* term is excluded by the distance bound).  (2) The scalar curvature along  *)
(* a neck is within a factor 1 +- 1/1000 of its value at the centre for      *)
(* small scales (N1).                                                        *)
(* ------------------------------------------------------------------------- *)

let APX_NEAR_LEVEL = prove
 (`!top atlas (g:A->real^3^3) d x (e:real^3->A) y q.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ &0 < d /\
     apx_eng_n2 top atlas g d (&1 / &100) /\ rfs_neck (top,atlas) g d x e /\
     y IN rfs_neck_dom d /\ mfd_joinable (top,atlas) (e y) q /\
     mfd_dist (top,atlas) g (e y) q <
     &99 / &100 * inv(sqrt(mfd_scalar atlas g x)) * (inv d - abs(apx_sval y))
     ==> ?y'. y' IN rfs_neck_dom d /\ q = e y' /\
              &99 / &100 * inv(sqrt(mfd_scalar atlas g x)) * abs(apx_sval y' - apx_sval y)
              <= mfd_dist (top,atlas) g (e y) q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `d:real`; `x:A`; `e:real^3->A`; `y:real^3`; `q:A`] APX_NECK_EXIT_BALL) THEN
  ASM_REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `y':real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  EXISTS_TAC `y':real^3` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`x:A`; `e:real^3->A`; `y:real^3`; `y':real^3`] o
              REWRITE_RULE[apx_eng_n2]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
  SUBGOAL_THEN `&0 < inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN
    ASM_MESON_TAC[rfs_neck];
    ALL_TAC] THEN
  MP_TAC(SPECL [`d:real`; `y:real^3`] APX_SVAL_NECK_DOM) THEN
  MP_TAC(SPECL [`d:real`; `y':real^3`] APX_SVAL_NECK_DOM) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC `h = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x))` THEN
  ABBREV_TAC `D = mfd_dist (top,atlas) (g:A->real^3^3) ((e:real^3->A) y) (e y')` THEN
  ABBREV_TAC `a = abs(apx_sval(y:real^3) - apx_sval(y':real^3))` THEN
  ABBREV_TAC `w = &2 * inv d - abs(apx_sval(y:real^3)) - abs(apx_sval(y':real^3))` THEN
  SUBGOAL_THEN `abs(apx_sval(y':real^3) - apx_sval y) = a` SUBST1_TAC THENL
   [EXPAND_TAC "a" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `inv d - abs(apx_sval(y:real^3)) < w` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `a <= w` THENL
   [UNDISCH_TAC `(&1 - &1 / &100) * h * min a w <= D` THEN
    ASM_REWRITE_TAC[REAL_ARITH `min a w = if a <= w then a else w`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `(&1 - &1 / &100) * h * min a w <= D` THEN
  ASM_REWRITE_TAC[REAL_ARITH `min a w = if a <= w then a else w`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&99 / &100 * h * (inv d - abs(apx_sval(y:real^3))) < &99 / &100 * h * w`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The scalar curvature along a neck, for scales up to eps (N1 at 1/1000). *)

let apx_cl_rat = new_definition
 `apx_cl_rat (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)
             (eps:real) <=>
    !d x (e:real^3->A) y.
       &0 < d /\ d <= eps /\ rfs_neck (top,atlas) g d x e /\ y IN rfs_neck_dom d
       ==> abs(mfd_scalar atlas g (e y) / mfd_scalar atlas g x - &1) <= &1 / &1000`;;

let APX_CL_RAT_HOLDS = prove
 (`?eps0. &0 < eps0 /\
     !top atlas (g:A->real^3^3) eps.
        &0 < eps /\ eps <= eps0 /\ riemannian_metric atlas g
        ==> apx_cl_rat top atlas g eps`,
  MP_TAC(ISPEC `UNIV:A->bool` APX_NECK_CURV) THEN REWRITE_TAC[APX_NECK_CURV_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `&1 / &1000`) THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps1:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `eps1:real` THEN ASM_REWRITE_TAC[apx_cl_rat] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `d:real`; `x:A`; `e:real^3->A`; `y:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                `g:A->real^3^3`; `d:real`; `x:A`; `e:real^3->A`] APX_NECK_FIELDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ASSUME `rfs_neck (top,atlas) (g:A->real^3^3) d x (e:real^3->A)`) THEN
  REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rfs_neck_dom d`; `rfs_pullback atlas (e:real^3->A) (g:A->real^3^3)`;
                 `mfd_scalar atlas (g:A->real^3^3) x`; `y:real^3`] LSCALAR_SCALE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `rfs_neck_dom d`; `e:real^3->A`; `y:real^3`]
                APX_PULLBACK_SCALAR_GEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The extended core chart of a ball cap.  A ball cap has a                  *)
(* core chart b (ball(0,2)) and a boundary neck e' with b = e' o radial_ext f *)
(* on annulus(1,2).  The outer half of e' misses the closed core, so b and   *)
(* e' o radial_ext f glue to a ball chart apx_bext b e' f of radius          *)
(* exp(1/(sqrt 2 eps)); its balls of radius > 1 are the closed core plus    *)
(* collars bounded by level spheres of e'.                                   *)
(* ------------------------------------------------------------------------- *)

let apx_bext = new_definition
 `apx_bext (b:real^3->A) (e':real^3->A) (f:real^3->real^3) =
    \x. if norm x < &2 then b x else e'(radial_ext f x)`;;

let APX_NECK_DOM_ANNULUS = prove
 (`!eps. rfs_neck_dom eps =
         annulus (exp(--inv eps / sqrt(&2))) (exp(inv eps / sqrt(&2)))`,
  REWRITE_TAC[APX_SLAB_NECK_DOM; apx_slab]);;

let APX_BEXT_RADIUS = prove
 (`!eps. &0 < eps /\ eps <= &1 / &8
         ==> &2 < exp(inv eps / sqrt(&2)) /\
             annulus (&1) (exp(inv eps / sqrt(&2))) SUBSET rfs_neck_dom eps /\
             sphere(vec 0:real^3,&1) SUBSET rfs_neck_dom eps`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&8 <= inv eps` ASSUME_TAC THENL
   [MP_TAC(SPECL [`eps:real`; `&1 / &8`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&2) /\ sqrt(&2) <= &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LSQRT THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 <= inv eps / sqrt(&2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `inv eps / sqrt(&2)` REAL_EXP_LE_X) THEN DISCH_TAC THEN
  SUBGOAL_THEN `exp(--inv eps / sqrt(&2)) < &1` ASSUME_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_LNEG; GSYM REAL_EXP_0] THEN
    REWRITE_TAC[REAL_EXP_MONO_LT] THEN REWRITE_TAC[REAL_ARITH `--x < &0 <=> &0 < x`] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_ARITH `&8 <= x ==> &0 < x`];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REWRITE_TAC[APX_NECK_DOM_ANNULUS; SUBSET; annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[APX_NECK_DOM_ANNULUS; SUBSET; annulus; IN_ELIM_THM; IN_SPHERE_0] THEN
    ASM_REAL_ARITH_TAC]);;

let APX_BEXT_FACTS = prove
 (`!top atlas (b:real^3->A) e' f f' eps.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ &0 < eps /\ eps <= &1 / &8 /\
     mfd_param top atlas (ball(vec 0,&2)) b /\ mfd_param top atlas (rfs_neck_dom eps) e' /\
     IMAGE e' (sphere(vec 0,&1)) = IMAGE b (sphere(vec 0,&1)) /\
     sphere_diffeo f f' /\
     (!y. y IN annulus (&1) (&2) ==> b y = e'(radial_ext f y))
     ==> DISJOINT (IMAGE e' (annulus (&1) (exp(inv eps / sqrt(&2)))))
                  (IMAGE b (cball(vec 0,&1))) /\
         mfd_param top atlas (ball(vec 0,exp(inv eps / sqrt(&2)))) (apx_bext b e' f) /\
         (!x. norm x < &2 ==> apx_bext b e' f x = b x) /\
         (!x. &1 < norm x ==> apx_bext b e' f x = e'(radial_ext f x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `eps:real` APX_BEXT_RADIUS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `R = exp(inv eps / sqrt(&2))` THEN
  SUBGOAL_THEN `(!x. norm x < &2 ==> apx_bext (b:real^3->A) e' f x = b x) /\
                (!x. &1 < norm x ==> apx_bext b e' f x = e'(radial_ext f x))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[apx_bext] THEN CONJ_TAC THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THENL
     [ASM_REWRITE_TAC[];
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* the outer half of e' as a parametrization *)
  SUBGOAL_THEN `diffeomorphism_on (annulus (&1) R) (annulus (&1) R)
                  (radial_ext (f:real^3->real^3)) (radial_ext f')` ASSUME_TAC THENL
   [MATCH_MP_TAC SMT_DIFFEO_RADIAL_EXT_ANNULUS THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param top atlas (annulus (&1) R) ((e':real^3->A) o radial_ext f)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
    MAP_EVERY EXISTS_TAC [`rfs_neck_dom eps`; `annulus (&1) R:real^3->bool`;
                          `radial_ext (f':real^3->real^3)`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (radial_ext (f:real^3->real^3)) (annulus (&1) R) = annulus (&1) R`
  ASSUME_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on (annulus (&1) R) (annulus (&1) R)
                   (radial_ext (f:real^3->real^3)) (radial_ext f')` THEN
    SIMP_TAC[diffeomorphism_on];
    ALL_TAC] THEN
  (* the outer half misses the closed core *)
  SUBGOAL_THEN `DISJOINT (IMAGE (e':real^3->A) (annulus (&1) R)) (IMAGE (b:real^3->A) (cball(vec 0,&1)))`
  ASSUME_TAC THENL
   [ABBREV_TAC `Aa = IMAGE (e':real^3->A) (annulus (&1) R)` THEN
    ABBREV_TAC `Yc = IMAGE (b:real^3->A) (ball(vec 0,&1))` THEN
    SUBGOAL_THEN `connected_in top (Aa:A->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "Aa" THEN MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
      ASM_REWRITE_TAC[APX_CONNECTED_ANNULUS3];
      ALL_TAC] THEN
    SUBGOAL_THEN `DISJOINT (Aa:A->bool) (IMAGE (b:real^3->A) (sphere(vec 0,&1)))` ASSUME_TAC THENL
     [EXPAND_TAC "Aa" THEN
      FIRST_ASSUM((fun th -> REWRITE_TAC[SYM th]) o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `IMAGE (e':real^3->A) (sphere(vec 0,&1))`)) THEN
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
      X_GEN_TAC `p:A` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC)
                                 (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `u:real^3 = v` SUBST_ALL_TAC THENL
       [MATCH_MP_TAC MFD_PARAM_INJ THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                              `rfs_neck_dom eps`; `e':real^3->A`] THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `(v:real^3) IN annulus (&1) R` THEN
      UNDISCH_TAC `(v:real^3) IN sphere(vec 0,&1)` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM; IN_SPHERE_0] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `open_in top (Yc:A->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "Yc" THEN MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `ball(vec 0:real^3,&2)`] THEN
      ASM_REWRITE_TAC[OPEN_BALL; SUBSET; IN_BALL_0] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `ball(vec 0:real^3,&2)`; `b:real^3->A`] GRGD_PARAM_FACTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `bi:A->real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `compact_in top (IMAGE (b:real^3->A) (cball(vec 0,&1)))` ASSUME_TAC THENL
     [MATCH_MP_TAC IMAGE_COMPACT_IN THEN
      EXISTS_TAC `subtopology euclidean (ball(vec 0:real^3,&2))` THEN
      ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN; COMPACT_CBALL] THEN
      REWRITE_TAC[SUBSET; IN_BALL_0; IN_CBALL_0] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `top frontier_of (Yc:A->bool) SUBSET IMAGE (b:real^3->A) (sphere(vec 0,&1))`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[frontier_of; INTERIOR_OF_OPEN_IN] THEN
      SUBGOAL_THEN `top closure_of (Yc:A->bool) SUBSET IMAGE (b:real^3->A) (cball(vec 0,&1))`
      MP_TAC THENL
       [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN CONJ_TAC THENL
         [EXPAND_TAC "Yc" THEN MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[BALL_SUBSET_CBALL];
          MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `ball(vec 0:real^3,&2)`; `cball(vec 0:real^3,&1)`;
                     `ball(vec 0:real^3,&1)`; `b:real^3->A`] APX_PARAM_IMAGE_DIFF) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[SUBSET; IN_BALL_0; IN_CBALL_0] THEN CONJ_TAC THEN GEN_TAC THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[CBALL_DIFF_BALL] THEN EXPAND_TAC "Yc" THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((Aa:A->bool) DIFF Yc = {})` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_DIFF] THEN
      EXISTS_TAC `(b:real^3->A)(&3 / &2 % basis 1)` THEN
      SUBGOAL_THEN `norm(&3 / &2 % basis 1:real^3) = &3 / &2` ASSUME_TAC THENL
       [SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL
       [EXPAND_TAC "Aa" THEN
        SUBGOAL_THEN `(b:real^3->A)(&3 / &2 % basis 1) =
                      (e':real^3->A)(radial_ext f (&3 / &2 % basis 1))` SUBST1_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN
          REAL_ARITH_TAC;
          ALL_TAC] THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN
        UNDISCH_TAC `IMAGE (radial_ext (f:real^3->real^3)) (annulus (&1) R) = annulus (&1) R` THEN
        REWRITE_TAC[EXTENSION] THEN
        DISCH_THEN(MP_TAC o SPEC `radial_ext (f:real^3->real^3) (&3 / &2 % basis 1)`) THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
        EXPAND_TAC "Yc" THEN REWRITE_TAC[IN_IMAGE; NOT_EXISTS_THM; IN_BALL_0] THEN
        X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
        SUBGOAL_THEN `&3 / &2 % basis 1:real^3 = w` MP_TAC THENL
         [MATCH_MP_TAC MFD_PARAM_INJ THEN
          MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                `ball(vec 0:real^3,&2)`; `b:real^3->A`] THEN
          ASM_REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
          DISCH_THEN(SUBST_ALL_TAC o SYM) THEN ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    SUBGOAL_THEN `DISJOINT (Aa:A->bool) Yc` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `Aa:A->bool`; `Yc:A->bool`]
                    CONNECTED_IN_INTER_FRONTIER_OF) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `top frontier_of (Yc:A->bool) SUBSET IMAGE (b:real^3->A) (sphere(vec 0,&1))` THEN
      UNDISCH_TAC `DISJOINT (Aa:A->bool) (IMAGE (b:real^3->A) (sphere(vec 0,&1)))` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (b:real^3->A) (cball(vec 0,&1)) = Yc UNION IMAGE (b:real^3->A) (sphere(vec 0,&1))`
    SUBST1_TAC THENL
     [EXPAND_TAC "Yc" THEN REWRITE_TAC[GSYM IMAGE_UNION] THEN AP_TERM_TAC THEN
      REWRITE_TAC[EXTENSION; IN_UNION; IN_CBALL_0; IN_BALL_0; IN_SPHERE_0] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `DISJOINT (Aa:A->bool) Yc` THEN
    UNDISCH_TAC `DISJOINT (Aa:A->bool) (IMAGE (b:real^3->A) (sphere(vec 0,&1)))` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* the glued parametrization *)
  SUBGOAL_THEN `ball(vec 0:real^3,R) = ball(vec 0,&2) UNION annulus (&1) R` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_BALL_0; annulus; IN_ELIM_THM] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MFD_PARAM_UNION THEN
  MAP_EVERY EXISTS_TAC [`b:real^3->A`; `(e':real^3->A) o radial_ext f`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_BALL_0] THEN ASM_MESON_TAC[];
    REWRITE_TAC[annulus; IN_ELIM_THM; o_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `x:real^3` THEN
    REWRITE_TAC[IN_BALL_0; annulus; IN_ELIM_THM] THEN STRIP_TAC THEN CONJ_TAC THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:real^3` THEN
    ASM_SIMP_TAC[o_THM; annulus; IN_ELIM_THM; IN_BALL_0]] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_IMAGE; o_THM] THEN X_GEN_TAC `p:A` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `p:A = (b:real^3->A) x`)) THEN
  SUBGOAL_THEN `radial_ext (f:real^3->real^3) y IN annulus (&1) R` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (radial_ext (f:real^3->real^3)) (annulus (&1) R) = annulus (&1) R` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `norm(x:real^3) <= &1` THENL
   [MATCH_MP_TAC(TAUT `F ==> p`) THEN
    UNDISCH_TAC `DISJOINT (IMAGE (e':real^3->A) (annulus (&1) R))
                          (IMAGE (b:real^3->A) (cball(vec 0,&1)))` THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `(b:real^3->A) x`) THEN REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_CBALL_0]];
    ALL_TAC] THEN
  EXISTS_TAC `x:real^3` THEN
  SUBGOAL_THEN `(x:real^3) IN annulus (&1) (&2)` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN ball(vec 0,&2)` THEN
    REWRITE_TAC[IN_BALL_0; annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `(x:real^3) IN annulus (&1) (&2)` THEN
  REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The point-set topology of the region P of APX_REGION.                     *)
(* apx_rg collects its hypotheses (thresholds aside).  The cut spheres S_k   *)
(* miss P; a connected set meeting P and missing all S_k lies in P; the      *)
(* closure of P misses the inner side W_k of every surgery neck (P lies on   *)
(* the outer side of S_k, and the sphere separates); caps meeting the        *)
(* closure lie in P when they miss the middle halves of the surgery necks    *)
(* (N6); a twisted cap meeting the closure gives a twisted chart of P.       *)
(* ------------------------------------------------------------------------- *)

let apx_rg = new_definition
 `apx_rg (top:A topology,atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)
         (C:real) (eps:real) (dl:real) (J:num->bool) (e:num->real^3->A) (P:A->bool) <=>
    hausdorff_space top /\ smooth_manifold_atlas top atlas /\
    riemannian_metric atlas g /\ apx_sphere_sep top atlas /\
    &0 < dl /\ dl <= &1 / &8 /\ FINITE J /\ ~(J = {}) /\
    (!i. i IN J ==> ?y. rfs_neck (top,atlas) g dl y (e i)) /\
    (!i j. i IN J /\ j IN J /\ ~(i = j)
           ==> DISJOINT (IMAGE (e i) (annulus (&1 / &2) (&2)))
                        (IMAGE (e j) (annulus (&1 / &2) (&2)))) /\
    open_in top P /\ connected_in top P /\
    compact_in top (top closure_of P) /\
    top closure_of P = P UNION UNIONS {IMAGE (e i) (sphere(vec 0,&1)) | i IN J} /\
    (!i. i IN J
         ==> P INTER IMAGE (e i) (annulus (&1 / &2) (&2)) =
             IMAGE (e i) (annulus (&1) (&2))) /\
    (!x. x IN top closure_of P ==> apx_neck_or_core (top,atlas) g C eps x)`;;

let APX_JOINABLE_IN_CONNECTED = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (U:A->bool).
     (!y1 y2. y1 IN U /\ y2 IN U ==> mfd_joinable_in (top,atlas) U y1 y2)
     ==> connected_in top U`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PATH_CONNECTED_IN_IMP_CONNECTED_IN THEN
  REWRITE_TAC[path_connected_in; path_connected_space] THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y:A`; `y:A`]) THEN
    ASM_REWRITE_TAC[mfd_joinable_in] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `gamma:real->A`; `&0`; `&1`; `&0`] MFD_C1_CURVE_IN_TOPSPACE) THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL; REAL_LE_REFL; REAL_POS];
    ALL_TAC] THEN
  ASM_SIMP_TAC[TOPSPACE_SUBTOPOLOGY; SET_RULE `(s:A->bool) SUBSET t ==> t INTER s = s`] THEN
  MAP_EVERY X_GEN_TAC [`y1:A`; `y2:A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`y1:A`; `y2:A`]) THEN
  ASM_REWRITE_TAC[mfd_joinable_in] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[PATH_IN_SUBTOPOLOGY] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[path_in] THEN
    UNDISCH_TAC `mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool) gamma (&0) (&1)` THEN
    SIMP_TAC[mfd_c1_curve];
    REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_SIMP_TAC[]]);;

(* The topological part of apx_rg (no canonical neighbourhood clause): the  *)
(* point-set lemmas below need only this; the tight-shell statement (below)  *)
(* has no canonical neighbourhood hypothesis.                               *)

let apx_rg0 = new_definition
 `apx_rg0 (top:A topology,atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)
          (dl:real) (J:num->bool) (e:num->real^3->A) (P:A->bool) <=>
    hausdorff_space top /\ smooth_manifold_atlas top atlas /\
    riemannian_metric atlas g /\ apx_sphere_sep top atlas /\
    &0 < dl /\ dl <= &1 / &8 /\ FINITE J /\ ~(J = {}) /\
    (!i. i IN J ==> ?y. rfs_neck (top,atlas) g dl y (e i)) /\
    (!i j. i IN J /\ j IN J /\ ~(i = j)
           ==> DISJOINT (IMAGE (e i) (annulus (&1 / &2) (&2)))
                        (IMAGE (e j) (annulus (&1 / &2) (&2)))) /\
    open_in top P /\ connected_in top P /\
    compact_in top (top closure_of P) /\
    top closure_of P = P UNION UNIONS {IMAGE (e i) (sphere(vec 0,&1)) | i IN J} /\
    (!i. i IN J
         ==> P INTER IMAGE (e i) (annulus (&1 / &2) (&2)) =
             IMAGE (e i) (annulus (&1) (&2)))`;;

let APX_RG_RG0 = prove
 (`!top atlas (g:A->real^3^3) C eps dl J (e:num->real^3->A) P.
     apx_rg (top,atlas) g C eps dl J e P <=>
     apx_rg0 (top,atlas) g dl J e P /\
     (!x. x IN top closure_of P ==> apx_neck_or_core (top,atlas) g C eps x)`,
  REWRITE_TAC[apx_rg; apx_rg0; GSYM CONJ_ASSOC]);;

let APX_RG0_BASICS = prove
 (`!top atlas (g:A->real^3^3) dl J (e:num->real^3->A) P.
     apx_rg0 (top,atlas) g dl J e P
     ==> (!k. k IN J
              ==> mfd_param top atlas (rfs_neck_dom dl) (e k) /\
                  mfd_neck_chart top atlas (e k) /\
                  annulus (&1 / &2) (&2) SUBSET rfs_neck_dom dl /\
                  DISJOINT P (IMAGE (e k) (sphere(vec 0,&1)))) /\
         top closure_of P SUBSET topspace top /\ P SUBSET topspace top /\
         (!Cc. connected_in top Cc /\ ~(DISJOINT Cc P) /\
               (!k. k IN J ==> DISJOINT Cc (IMAGE (e k) (sphere(vec 0,&1))))
               ==> Cc SUBSET P)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[apx_rg0] THEN STRIP_TAC THEN
  SUBGOAL_THEN `annulus (&1 / &2) (&2) SUBSET rfs_neck_dom dl /\
                sphere(vec 0:real^3,&1) SUBSET annulus (&1 / &2) (&2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPEC `dl:real` APX_BEXT_RADIUS) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN
      REWRITE_TAC[APX_NECK_DOM_ANNULUS; SUBSET; annulus; IN_ELIM_THM] THEN
      REWRITE_TAC[real_div; REAL_MUL_LNEG; REAL_EXP_NEG] THEN
      REWRITE_TAC[GSYM real_div] THEN
      ABBREV_TAC `R = exp(inv dl / sqrt(&2))` THEN DISCH_TAC THEN
      SUBGOAL_THEN `inv R < &1 / &2` ASSUME_TAC THENL
       [MP_TAC(SPECL [`&2`; `R:real`] REAL_LT_INV2) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `y:real^3` THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. k IN J ==> mfd_param top atlas (rfs_neck_dom dl) ((e:num->real^3->A) k)`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(k:num) IN J`) o check (fun th ->
      is_forall (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck")) (concl th))) THEN
    DISCH_THEN(X_CHOOSE_THEN `y:A` (MP_TAC o REWRITE_RULE[rfs_neck])) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `P SUBSET topspace (top:A topology) /\ top closure_of P SUBSET topspace top`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_IN_SUBSET; CLOSURE_OF_SUBSET_TOPSPACE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `mfd_param top atlas (rfs_neck_dom dl) ((e:num->real^3->A) k)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[mfd_neck_chart] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `rfs_neck_dom dl` THEN
      ASM_REWRITE_TAC[OPEN_ANNULUS];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(k:num) IN J`) o check (fun th ->
      is_forall (concl th) &&
      can (find_term (fun t -> t = `annulus (&1) (&2):real^3->bool`)) (concl th))) THEN
    REWRITE_TAC[EXTENSION; IN_INTER] THEN DISCH_TAC THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    X_GEN_TAC `p:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `w:real^3`
      (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC))) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(e:num->real^3->A) k w`) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(w:real^3) IN annulus (&1 / &2) (&2)` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(e:num->real^3->A) k w IN IMAGE (e k) (annulus (&1 / &2) (&2))`
    (fun th -> REWRITE_TAC[th]) THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; NOT_EXISTS_THM] THEN X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `w:real^3 = v` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_INJ THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `rfs_neck_dom dl`; `(e:num->real^3->A) k`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM SET_TAC[];
        UNDISCH_TAC `(v:real^3) IN annulus (&1) (&2)` THEN
        UNDISCH_TAC `annulus (&1 / &2) (&2) SUBSET rfs_neck_dom dl` THEN
        REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN
        DISCH_THEN(MP_TAC o SPEC `v:real^3`) THEN
        DISCH_THEN(fun h -> DISCH_TAC THEN MATCH_MP_TAC h) THEN ASM_REAL_ARITH_TAC];
      UNDISCH_TAC `(v:real^3) IN annulus (&1) (&2)` THEN
      UNDISCH_TAC `(v:real^3) IN sphere(vec 0,&1)` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM; IN_SPHERE_0] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `Cc:A->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `Cc SUBSET topspace (top:A topology)` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONNECTED_IN_SUBSET_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `Cc:A->bool`; `P:A->bool`]
                CONNECTED_IN_INTER_FRONTIER_OF) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `Cc DIFF P:A->bool = {}` THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(Cc INTER P:A->bool = {})` (fun th -> REWRITE_TAC[th]) THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SIMP_TAC[frontier_of; INTERIOR_OF_OPEN_IN; ASSUME `open_in top (P:A->bool)`] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_DIFF] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:A` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(p:A) IN top closure_of P` THEN
  FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `top closure_of (P:A->bool)`)) THEN
  REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `!k. k IN J ==> DISJOINT Cc (IMAGE ((e:num->real^3->A) k) (sphere(vec 0,&1)))` THEN
  DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* Components of apx_rg. *)

let APX_RG0_PARTS = prove
 (`!top atlas (g:A->real^3^3) dl J (e:num->real^3->A) P.
     apx_rg0 (top,atlas) g dl J e P
     ==> (!i j. i IN J /\ j IN J /\ ~(i = j)
                ==> DISJOINT (IMAGE (e i) (annulus (&1 / &2) (&2)))
                             (IMAGE (e j) (annulus (&1 / &2) (&2)))) /\
         (!i. i IN J ==> ?y. rfs_neck (top,atlas) g dl y (e i)) /\
         (!i. i IN J
              ==> P INTER IMAGE (e i) (annulus (&1 / &2) (&2)) =
                  IMAGE (e i) (annulus (&1) (&2))) /\
         (!i. i IN J ==> e i (&4 / &3 % basis 1) IN P)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[apx_rg0] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall (concl th) &&
    can (find_term (fun t -> t = `annulus (&1) (&2):real^3->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(SET_RULE
   `(x:A) IN B ==> P INTER A = B ==> x IN P`) THEN
  MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN
  SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC);;

(* The closure of P misses the inner side of every surgery neck. *)

let APX_RG0_KP = prove
 (`!top atlas (g:A->real^3^3) dl J (e:num->real^3->A) P k.
     apx_rg0 (top,atlas) g dl J e P /\ k IN J
     ==> top closure_of P DIFF IMAGE (e k) (sphere(vec 0,&1)) SUBSET
         connected_component_of
           (subtopology top (topspace top DIFF IMAGE (e k) (sphere(vec 0,&1))))
           (e k (&4 / &3 % basis 1)) /\
         DISJOINT (IMAGE (e k) (apx_slab (--inv dl) (&0)))
                  (connected_component_of
                    (subtopology top (topspace top DIFF IMAGE (e k) (sphere(vec 0,&1))))
                    (e k (&4 / &3 % basis 1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_RG0_BASICS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_RG0_PARTS) THEN
  APX_UNFOLD_ASM_TAC "apx_rg0" apx_rg0 THEN
  SUBGOAL_THEN `mfd_param top atlas (rfs_neck_dom dl) ((e:num->real^3->A) k) /\
                mfd_neck_chart top atlas (e k) /\
                annulus (&1 / &2) (&2) SUBSET rfs_neck_dom dl /\
                DISJOINT P (IMAGE (e k) (sphere(vec 0,&1)))` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&8 <= inv dl` ASSUME_TAC THENL
   [MP_TAC(SPECL [`dl:real`; `&1 / &8`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `S = IMAGE ((e:num->real^3->A) k) (sphere(vec 0,&1))` THEN
  ABBREV_TAC `Kp = connected_component_of (subtopology top (topspace top DIFF S))
                     ((e:num->real^3->A) k (&4 / &3 % basis 1))` THEN
  STRIP_ASSUME_TAC APX_LOG_43 THEN
  SUBGOAL_THEN `norm(&4 / &3 % basis 1:real^3) = &4 / &3 /\
                norm(&3 / &4 % basis 1:real^3) = &3 / &4` STRIP_ASSUME_TAC THENL
   [SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(P:A->bool) SUBSET topspace top DIFF S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(e:num->real^3->A) k (&4 / &3 % basis 1) IN P` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(e:num->real^3->A) k (&4 / &3 % basis 1) IN Kp` ASSUME_TAC THENL
   [EXPAND_TAC "Kp" THEN GEN_REWRITE_TAC I [IN] THEN
    REWRITE_TAC[CONNECTED_COMPONENT_OF_REFL; TOPSPACE_SUBTOPOLOGY] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(P:A->bool) SUBSET Kp` ASSUME_TAC THENL
   [EXPAND_TAC "Kp" THEN MATCH_MP_TAC APX_CC_ABSORB THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `(e:num->real^3->A) k (&4 / &3 % basis 1)` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(e:num->real^3->A) k (&4 / &3 % basis 1) IN Kp` THEN EXPAND_TAC "Kp" THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  (* the other surgery spheres lie in Kp *)
  SUBGOAL_THEN `!m. m IN J /\ ~(m = k)
                    ==> IMAGE ((e:num->real^3->A) m) (annulus (&1 / &2) (&2)) SUBSET Kp`
  ASSUME_TAC THENL
   [X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `mfd_param top atlas (rfs_neck_dom dl) ((e:num->real^3->A) m)`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE ((e:num->real^3->A) m) (annulus (&1 / &2) (&2)) SUBSET topspace top`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `rfs_neck_dom dl`; `(e:num->real^3->A) m`] GRGD_PARAM_FACTS) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `DISJOINT (IMAGE ((e:num->real^3->A) m) (annulus (&1 / &2) (&2)))
                           (IMAGE (e k) (annulus (&1 / &2) (&2)))` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(S:A->bool) SUBSET IMAGE ((e:num->real^3->A) k) (annulus (&1 / &2) (&2))`
    ASSUME_TAC THENL
     [EXPAND_TAC "S" THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(e:num->real^3->A) m (&4 / &3 % basis 1) IN P` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(e:num->real^3->A) m (&4 / &3 % basis 1) IN
                  IMAGE (e m) (annulus (&1 / &2) (&2))` ASSUME_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "Kp" THEN MATCH_MP_TAC APX_CC_ABSORB THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom dl`] THEN
      ASM_REWRITE_TAC[APX_CONNECTED_ANNULUS3];
      ASM SET_TAC[];
      UNDISCH_TAC `(P:A->bool) SUBSET Kp` THEN EXPAND_TAC "Kp" THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  (* the inner side misses Kp *)
  ABBREV_TAC `W = IMAGE ((e:num->real^3->A) k) (apx_slab (--inv dl) (&0))` THEN
  SUBGOAL_THEN `apx_slab (--inv dl) (&0) SUBSET rfs_neck_dom dl /\
                &3 / &4 % basis 1:real^3 IN apx_slab (--inv dl) (&0)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[APX_SLAB_NECK_DOM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC APX_SLAB_SUBSET THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[APX_SLAB_SVAL; apx_sval] THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC[VECTOR_MUL_EQ_0; BASIS_NONZERO; DIMINDEX_3; ARITH] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(W:A->bool) SUBSET topspace top DIFF S` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `rfs_neck_dom dl`; `(e:num->real^3->A) k`] GRGD_PARAM_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXPAND_TAC ["W"; "S"] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF] THEN X_GEN_TAC `y:real^3` THEN
    DISCH_TAC THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; NOT_EXISTS_THM] THEN X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `y:real^3 = w` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_INJ THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `rfs_neck_dom dl`; `(e:num->real^3->A) k`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MP_TAC(SPEC `dl:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM SET_TAC[];
      UNDISCH_TAC `(w:real^3) IN apx_slab (--inv dl) (&0)` THEN
      UNDISCH_TAC `(w:real^3) IN sphere(vec 0,&1)` THEN
      REWRITE_TAC[APX_SLAB_SVAL; IN_SPHERE_0; apx_sval] THEN
      SIMP_TAC[LOG_1] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (W:A->bool) Kp` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(W:A->bool) SUBSET Kp` MP_TAC THENL
     [EXPAND_TAC "Kp" THEN MATCH_MP_TAC APX_CC_ABSORB THEN REPEAT CONJ_TAC THENL
       [EXPAND_TAC "W" THEN MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
        MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom dl`] THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[apx_slab; APX_CONNECTED_ANNULUS3];
        FIRST_ASSUM ACCEPT_TAC;
        UNDISCH_TAC `~DISJOINT (W:A->bool) Kp` THEN EXPAND_TAC "Kp" THEN REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `(e:num->real^3->A) k (&3 / &4 % basis 1)` o
               REWRITE_RULE[SUBSET]) THEN
    ANTS_TAC THENL [EXPAND_TAC "W" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
                    ALL_TAC] THEN
    EXPAND_TAC "Kp" THEN GEN_REWRITE_TAC LAND_CONV [IN] THEN DISCH_TAC THEN
    UNDISCH_TAC `apx_sphere_sep top (atlas:((A->bool)#(A->real^3))->bool)` THEN
    REWRITE_TAC[apx_sphere_sep; apx_separates] THEN
    DISCH_THEN(MP_TAC o SPEC `(e:num->real^3->A) k`) THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CONNECTED_COMPONENT_OF_SYM];
    ALL_TAC] THEN
  (* the closure *)
  CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
  FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `top closure_of (P:A->bool)`)) THEN
  REWRITE_TAC[SUBSET; IN_DIFF; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
  X_GEN_TAC `q:A` THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC MP_TAC) THENL
   [UNDISCH_TAC `(P:A->bool) SUBSET Kp` THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `m:num = k` THENL
   [UNDISCH_TAC `~((q:A) IN S)` THEN EXPAND_TAC "S" THEN
    UNDISCH_TAC `(q:A) IN IMAGE ((e:num->real^3->A) m) (sphere(vec 0,&1))` THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE ((e:num->real^3->A) m) (annulus (&1 / &2) (&2)) SUBSET Kp`
  MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `sphere(vec 0:real^3,&1) SUBSET annulus (&1 / &2) (&2)` MP_TAC THENL
   [REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `(q:A) IN IMAGE ((e:num->real^3->A) m) (sphere(vec 0,&1))` THEN
  SET_TAC[]);;

let APX_RG0_INNER = prove
 (`!top atlas (g:A->real^3^3) dl J (e:num->real^3->A) P k.
     apx_rg0 (top,atlas) g dl J e P /\ k IN J
     ==> DISJOINT (top closure_of P) (IMAGE (e k) (apx_slab (--inv dl) (&0)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL APX_RG0_KP) THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_RG0_BASICS) THEN
  APX_UNFOLD_ASM_TAC "apx_rg0" apx_rg0 THEN
  SUBGOAL_THEN `mfd_param top atlas (rfs_neck_dom dl) ((e:num->real^3->A) k)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&8 <= inv dl` ASSUME_TAC THENL
   [MP_TAC(SPECL [`dl:real`; `&1 / &8`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(e:num->real^3->A) k`; `dl:real`; `&0`; `--inv dl`; `&0`]
                APX_LEVEL_SPHERE_DISJOINT) THEN
  REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_EXP_0; REAL_LE_REFL] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(SPEC `dl:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[APX_SLAB_NECK_DOM] THEN MATCH_MP_TAC APX_SLAB_SUBSET THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SET_TAC[]);;

(* A connected set meeting the closure of P and missing S_k misses the inner *)
(* side of S_k.                                                              *)

let APX_RG0_SIDE = prove
 (`!top atlas (g:A->real^3^3) dl J (e:num->real^3->A) P k Cc.
     apx_rg0 (top,atlas) g dl J e P /\ k IN J /\ connected_in top Cc /\
     DISJOINT Cc (IMAGE (e k) (sphere(vec 0,&1))) /\ ~(DISJOINT Cc (top closure_of P))
     ==> DISJOINT Cc (IMAGE (e k) (apx_slab (--inv dl) (&0)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL APX_RG0_KP) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `S = IMAGE ((e:num->real^3->A) k) (sphere(vec 0,&1))` THEN
  ABBREV_TAC `Kp = connected_component_of (subtopology top (topspace top DIFF S))
                     ((e:num->real^3->A) k (&4 / &3 % basis 1))` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(Cc:A->bool) SUBSET Kp` MP_TAC THENL
   [EXPAND_TAC "Kp" THEN MATCH_MP_TAC APX_CC_ABSORB THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP CONNECTED_IN_SUBSET_TOPSPACE) THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM SET_TAC[]);;

(* The same facts for apx_rg (corollaries; the statements are unchanged). *)
let APX_RG_BASICS = prove
 (`!top atlas (g:A->real^3^3) C eps dl J (e:num->real^3->A) P.
     apx_rg (top,atlas) g C eps dl J e P
     ==> (!k. k IN J
              ==> mfd_param top atlas (rfs_neck_dom dl) (e k) /\
                  mfd_neck_chart top atlas (e k) /\
                  annulus (&1 / &2) (&2) SUBSET rfs_neck_dom dl /\
                  DISJOINT P (IMAGE (e k) (sphere(vec 0,&1)))) /\
         top closure_of P SUBSET topspace top /\ P SUBSET topspace top /\
         (!Cc. connected_in top Cc /\ ~(DISJOINT Cc P) /\
               (!k. k IN J ==> DISJOINT Cc (IMAGE (e k) (sphere(vec 0,&1))))
               ==> Cc SUBSET P)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[APX_RG_RG0] THEN
  DISCH_THEN(ACCEPT_TAC o MATCH_MP APX_RG0_BASICS o CONJUNCT1));;

let APX_RG_PARTS = prove
 (`!top atlas (g:A->real^3^3) C eps dl J (e:num->real^3->A) P.
     apx_rg (top,atlas) g C eps dl J e P
     ==> (!i j. i IN J /\ j IN J /\ ~(i = j)
                ==> DISJOINT (IMAGE (e i) (annulus (&1 / &2) (&2)))
                             (IMAGE (e j) (annulus (&1 / &2) (&2)))) /\
         (!i. i IN J ==> ?y. rfs_neck (top,atlas) g dl y (e i)) /\
         (!i. i IN J
              ==> P INTER IMAGE (e i) (annulus (&1 / &2) (&2)) =
                  IMAGE (e i) (annulus (&1) (&2))) /\
         (!i. i IN J ==> e i (&4 / &3 % basis 1) IN P)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[APX_RG_RG0] THEN
  DISCH_THEN(ACCEPT_TAC o MATCH_MP APX_RG0_PARTS o CONJUNCT1));;

let APX_RG_KP = prove
 (`!top atlas (g:A->real^3^3) C eps dl J (e:num->real^3->A) P k.
     apx_rg (top,atlas) g C eps dl J e P /\ k IN J
     ==> top closure_of P DIFF IMAGE (e k) (sphere(vec 0,&1)) SUBSET
         connected_component_of
           (subtopology top (topspace top DIFF IMAGE (e k) (sphere(vec 0,&1))))
           (e k (&4 / &3 % basis 1)) /\
         DISJOINT (IMAGE (e k) (apx_slab (--inv dl) (&0)))
                  (connected_component_of
                    (subtopology top (topspace top DIFF IMAGE (e k) (sphere(vec 0,&1))))
                    (e k (&4 / &3 % basis 1)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[APX_RG_RG0] THEN STRIP_TAC THEN
  MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `dl:real`; `J:num->bool`; `e:num->real^3->A`; `P:A->bool`; `k:num`]
    APX_RG0_KP) THEN ASM_REWRITE_TAC[]);;

let APX_RG_INNER = prove
 (`!top atlas (g:A->real^3^3) C eps dl J (e:num->real^3->A) P k.
     apx_rg (top,atlas) g C eps dl J e P /\ k IN J
     ==> DISJOINT (top closure_of P) (IMAGE (e k) (apx_slab (--inv dl) (&0)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[APX_RG_RG0] THEN STRIP_TAC THEN
  MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `dl:real`; `J:num->bool`; `e:num->real^3->A`; `P:A->bool`; `k:num`]
    APX_RG0_INNER) THEN ASM_REWRITE_TAC[]);;

let APX_RG_SIDE = prove
 (`!top atlas (g:A->real^3^3) C eps dl J (e:num->real^3->A) P k Cc.
     apx_rg (top,atlas) g C eps dl J e P /\ k IN J /\ connected_in top Cc /\
     DISJOINT Cc (IMAGE (e k) (sphere(vec 0,&1))) /\ ~(DISJOINT Cc (top closure_of P))
     ==> DISJOINT Cc (IMAGE (e k) (apx_slab (--inv dl) (&0)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[APX_RG_RG0] THEN STRIP_TAC THEN
  MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `dl:real`; `J:num->bool`; `e:num->real^3->A`; `P:A->bool`; `k:num`; `Cc:A->bool`]
    APX_RG0_SIDE) THEN ASM_REWRITE_TAC[]);;


(* Caps meeting the closure of P lie in P; twisted ones give a twisted chart. *)

let APX_RG_CAP_IN_P = prove
 (`!top atlas (g:A->real^3^3) C eps dl J (e:num->real^3->A) P U Y.
     apx_rg (top,atlas) g C eps dl J e P /\ rfs_cap (top,atlas) g C eps U Y /\
     (!k. k IN J ==> DISJOINT U (IMAGE (e k) (apx_slab (--inv(&2 * dl)) (inv(&2 * dl))))) /\
     ~(DISJOINT U (top closure_of P))
     ==> U SUBSET P`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_RG_BASICS) THEN
  FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "connected_in")) (concl th))) THEN
  SUBGOAL_THEN `!k. k IN J ==> DISJOINT U (IMAGE ((e:num->real^3->A) k) (sphere(vec 0,&1)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = `inv(&2 * dl)`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(SET_RULE
     `t SUBSET u ==> DISJOINT (a:A->bool) u ==> DISJOINT a t`) THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[SUBSET; IN_SPHERE_0; APX_SLAB_SVAL; apx_sval] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN ASM_REWRITE_TAC[LOG_1; REAL_MUL_RZERO] THEN
    CONJ_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `norm(vec 0:real^3) = &1` THEN
      REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < inv(&2 * dl)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN UNDISCH_TAC `apx_rg (top,atlas) (g:A->real^3^3) C eps dl J e P` THEN
      REWRITE_TAC[apx_rg] THEN REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(INST_TYPE [`:3`,`:N`] APX_JOINABLE_IN_CONNECTED) THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^3))->bool` THEN
    MATCH_MP_TAC APX_CAP_JOINABLE THEN
    MAP_EVERY EXISTS_TAC [`g:A->real^3^3`; `C:real`; `eps:real`; `Y:A->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `~(DISJOINT U (top closure_of (P:A->bool)))` THEN
  APX_UNFOLD_ASM_TAC "apx_rg" apx_rg THEN
  FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `top closure_of (P:A->bool)`)) THEN
  REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_UNION; UNIONS_GSPEC;
              IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:A` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `q:A` THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = `sphere(vec 0:real^3,&1)`)) (concl th) &&
      can (find_term (fun t -> t = `U:A->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

let APX_TWISTED_IN_OPEN = prove
 (`!top atlas (p:real^3->A) W.
     smooth_manifold_atlas top atlas /\ open_in top W /\
     rfs_twisted_chart top atlas p /\ IMAGE p (annulus (&1 / &4) (&4)) SUBSET W
     ==> rfs_has_twisted (subtopology top W) (restrict_atlas atlas W)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_has_twisted] THEN EXISTS_TAC `p:real^3->A` THEN
  UNDISCH_TAC `rfs_twisted_chart top atlas (p:real^3->A)` THEN
  REWRITE_TAC[rfs_twisted_chart] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `W:A->bool` APX_PARAM_RESTRICT) THEN
  REWRITE_TAC[APX_PARAM_RESTRICT_STATEMENT] THEN DISCH_THEN(fun th ->
    W(fun (asl,w) -> MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `W:A->bool`; `ball(y:real^3,r)`; `p:real^3->A`] th))) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]]);;

let APX_RG_TWISTED = prove
 (`!top atlas (g:A->real^3^3) C eps dl J (e:num->real^3->A) P U Y p.
     apx_rg (top,atlas) g C eps dl J e P /\ rfs_cap (top,atlas) g C eps U Y /\
     (!k. k IN J ==> DISJOINT U (IMAGE (e k) (apx_slab (--inv(&2 * dl)) (inv(&2 * dl))))) /\
     ~(DISJOINT U (top closure_of P)) /\
     rfs_twisted_chart top atlas p /\ IMAGE p (annulus (&1 / &4) (&4)) SUBSET U
     ==> rfs_has_twisted (subtopology top P) (restrict_atlas atlas P)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC APX_TWISTED_IN_OPEN THEN
  EXISTS_TAC `p:real^3->A` THEN
  APX_UNFOLD_ASM_TAC "apx_rg" apx_rg THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC_ALL APX_RG_CAP_IN_P) THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Ball caps and their extended cores; reach of a neck; the                  *)
(* sphere zones of the region growth.                                        *)
(* ------------------------------------------------------------------------- *)

let apx_bcap = new_definition
 `apx_bcap (top:A topology,atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)
           (C:real) (eps:real) (U:A->bool) (b:real^3->A) (e':real^3->A)
           (f:real^3->real^3) <=>
    rfs_cap (top,atlas) g C eps U (IMAGE b (ball(vec 0,&1))) /\
    mfd_ball_chart top atlas b /\ IMAGE b (ball(vec 0,&2)) SUBSET U /\
    (?z'. rfs_neck (top,atlas) g eps z' e') /\ IMAGE e' (rfs_neck_dom eps) SUBSET U /\
    IMAGE e' (sphere(vec 0,&1)) = IMAGE b (sphere(vec 0,&1)) /\
    (?f'. sphere_diffeo f f') /\
    (!y. y IN annulus (&1) (&2) ==> b y = e'(radial_ext f y))`;;

let APX_CAP_CASES = prove
 (`!top atlas (g:A->real^3^3) C eps U Y.
     rfs_cap (top,atlas) g C eps U Y
     ==> (?b e' f. apx_bcap (top,atlas) g C eps U b e' f /\ Y = IMAGE b (ball(vec 0,&1))) \/
         (?p. rfs_twisted_chart top atlas p /\ IMAGE p (annulus (&1 / &4) (&4)) SUBSET U)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[rfs_cap]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 MP_TAC (K ALL_TAC)))) THEN
  STRIP_TAC THENL
   [DISJ1_TAC THEN MAP_EVERY EXISTS_TAC [`b:real^3->A`; `e':real^3->A`; `f:real^3->real^3`] THEN
    ASM_REWRITE_TAC[apx_bcap] THEN
    UNDISCH_TAC `rfs_cap (top,atlas) (g:A->real^3^3) C eps U Y` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [EXISTS_TAC `z':A` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `f':real^3->real^3` THEN ASM_REWRITE_TAC[];
    DISJ2_TAC THEN EXISTS_TAC `p:real^3->A` THEN ASM_REWRITE_TAC[]]);;

(* Distances from the centre of a neck. *)

let APX_CENTRE_DIST = prove
 (`!top atlas (g:A->real^3^3) d z (N:real^3->A) v.
     apx_eng_n2 top atlas g d (&1 / &100) /\ rfs_neck (top,atlas) g d z N /\
     v IN rfs_neck_dom d
     ==> mfd_joinable (top,atlas) z (N v) /\
         mfd_dist (top,atlas) g z (N v)
         <= &101 / &100 * inv(sqrt(mfd_scalar atlas g z)) *
            (abs(apx_sval v) + sqrt(&2) * pi)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?u. u IN sphere(vec 0:real^3,&1) /\ z = (N:real^3->A) u`
  (X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC) THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) d z N` THEN
    REWRITE_TAC[rfs_neck; IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^3) IN rfs_neck_dom d /\ apx_sval u = &0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPEC `d:real` APX_UNIT_SPHERE_NECK_DOM) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[rfs_neck]; ASM SET_TAC[]];
      UNDISCH_TAC `(u:real^3) IN sphere(vec 0,&1)` THEN
      SIMP_TAC[IN_SPHERE_0; apx_sval; LOG_1; REAL_MUL_RZERO]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`z:A`; `N:real^3->A`; `u:real^3`; `v:real^3`] o
                REWRITE_RULE[apx_eng_n2]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o CONJUNCT1)) THEN
  ASM_REWRITE_TAC[REAL_SUB_LZERO; REAL_ABS_NEG] THEN
  REWRITE_TAC[REAL_ARITH `&1 + &1 / &100 = &101 / &100`]);;

(* The context of the region growth (thresholds discharged in the assembly). *)

let apx_rgc = new_definition
 `apx_rgc (top:A topology,atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)
             (C:real) (eps:real) (dl:real) (ep:real) (J:num->bool)
             (e:num->real^3->A) (P:A->bool) <=>
    apx_rg (top,atlas) g C eps dl J e P /\
    apx_kc * eps = ep /\ &0 < eps /\ dl <= eps /\
    apx_ch_ctx top atlas g ep /\ apx_ch_pair top atlas g ep /\
    apx_ch_more top atlas g ep /\ apx_ch_n4r top atlas g ep /\
    apx_ch_ctx top atlas g eps /\ apx_ch_ctx top atlas g dl /\
    apx_cl_rat top atlas g ep /\
    (!U Y k. rfs_cap (top,atlas) g C eps U Y /\ k IN J
             ==> DISJOINT U (IMAGE (e k) (apx_slab (--inv(&2 * dl)) (inv(&2 * dl))))) /\
    (!j k. j IN J /\ k IN J /\ ~(j = k)
           ==> DISJOINT (IMAGE (e k) (sphere(vec 0,&1)))
                        (IMAGE (e j) (apx_slab (--(&8 / ep)) (&8 / ep)))) /\
    (!U Y p. rfs_cap (top,atlas) g C eps U Y /\ rfs_twisted_chart top atlas p /\
             IMAGE p (annulus (&1 / &4) (&4)) SUBSET U
             ==> DISJOINT U (top closure_of P))`;;

(* Scale facts of the context. *)

let APX_RG_CTX_SCALES = prove
 (`!top atlas (g:A->real^3^3) C eps dl ep J (e:num->real^3->A) P.
     apx_rgc (top,atlas) g C eps dl ep J e P
     ==> &0 < dl /\ dl <= eps /\ &0 < eps /\ eps <= ep /\ &580 * eps <= ep /\
         ep <= &1 / &1024 /\ &1024 <= inv ep /\ &1024 * &580 <= inv eps /\
         &580 * inv ep <= inv eps /\ inv eps <= inv dl`,
  REPEAT GEN_TAC THEN REWRITE_TAC[apx_rgc; apx_rg; apx_ch_ctx] THEN STRIP_TAC THEN
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
  SUBGOAL_THEN `inv eps <= inv dl` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let APX_RATIO_SQRT = prove
 (`!a b c. &0 < a /\ &0 < b /\ &0 < c /\
           abs(c / a - &1) <= &1 / &1000 /\ abs(c / b - &1) <= &1 / &1000
           ==> inv(sqrt a) <= &1002 / &1000 * inv(sqrt b)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC APX_INV_SQRT_RATIO_GEN THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&999 / &1000 * a <= c /\ c <= &1001 / &1000 * a /\
                &999 / &1000 * b <= c /\ c <= &1001 / &1000 * b` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `abs(c / a - &1) <= &1 / &1000` THEN
    UNDISCH_TAC `abs(c / b - &1) <= &1 / &1000` THEN
    ASM_SIMP_TAC[REAL_FIELD `&0 < a ==> c / a - &1 = (c - a) / a`; REAL_ABS_DIV;
                 REAL_ARITH `&0 < a ==> abs a = a`; REAL_LE_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_REAL_ARITH_TAC);;

(* A neck centred in the closure of P that meets S_k is centred in the     *)
(* collar of S_k on the side of P, within level 2/ep of S_k.                *)

let APX_RG_SPHERE_REACH = prove
 (`!top atlas (g:A->real^3^3) C eps dl ep J (e:num->real^3->A) P k z N.
     apx_rgc (top,atlas) g C eps dl ep J e P /\ k IN J /\
     rfs_neck (top,atlas) g ep z N /\ z IN top closure_of P /\
     ~DISJOINT (IMAGE N (rfs_neck_dom ep)) (IMAGE (e k) (sphere(vec 0,&1)))
     ==> ?y. y IN rfs_neck_dom dl /\ z = e k y /\
             &0 <= apx_sval y /\ apx_sval y < &2 * inv ep`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_RG_CTX_SCALES) THEN
  APX_UNFOLD_ASM_TAC "apx_rgc" apx_rgc THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_RG_PARTS) THEN
  APX_UNFOLD_ASM_TAC "apx_rg" apx_rg THEN
  SUBGOAL_THEN `?yk. rfs_neck (top,atlas) (g:A->real^3^3) dl yk ((e:num->real^3->A) k)`
  (X_CHOOSE_TAC `yk:A`) THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `~DISJOINT (IMAGE (N:real^3->A) (rfs_neck_dom ep))
                         (IMAGE ((e:num->real^3->A) k) (sphere(vec 0,&1)))` THEN
  REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) (X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `(u:real^3) IN rfs_neck_dom dl /\ apx_sval u = &0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPEC `dl:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM SET_TAC[];
      UNDISCH_TAC `(u:real^3) IN sphere(vec 0,&1)` THEN
      SIMP_TAC[IN_SPHERE_0; apx_sval; LOG_1; REAL_MUL_RZERO]];
    ALL_TAC] THEN
  (* scales *)
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) z /\ &0 < mfd_scalar atlas g yk`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(mfd_scalar atlas (g:A->real^3^3) w / mfd_scalar atlas g z - &1)
                <= &1 / &1000 /\
                abs(mfd_scalar atlas g w / mfd_scalar atlas g yk - &1) <= &1 / &1000`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(REWRITE_RULE[apx_cl_rat] (ASSUME `apx_cl_rat top atlas (g:A->real^3^3) ep`)) THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPECL [`ep:real`; `z:A`; `N:real^3->A`; `v:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `(w:A) = (N:real^3->A) v` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[];
      FIRST_ASSUM(MP_TAC o SPECL [`dl:real`; `yk:A`; `(e:num->real^3->A) k`; `u:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `(w:A) = (e:num->real^3->A) k u` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) w` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) w / mfd_scalar atlas g z` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_MUL_LZERO]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`mfd_scalar atlas (g:A->real^3^3) z`; `mfd_scalar atlas (g:A->real^3^3) yk`;
                `mfd_scalar atlas (g:A->real^3^3) w`] APX_RATIO_SQRT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `hz = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) z))` THEN
  ABBREV_TAC `hk = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) yk))` THEN
  SUBGOAL_THEN `&0 < hz /\ &0 < hk` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["hz"; "hk"] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN
    MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the distance from z to w *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `ep:real`; `z:A`; `N:real^3->A`; `v:real^3`] APX_CENTRE_DIST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `apx_ch_ctx top atlas (g:A->real^3^3) ep` THEN SIMP_TAC[apx_ch_ctx];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`ep:real`; `v:real^3`] APX_SVAL_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN MP_TAC APX_SQRT2_PI THEN DISCH_TAC THEN
  ABBREV_TAC `D = mfd_dist (top,atlas) (g:A->real^3^3) z ((N:real^3->A) v)` THEN
  SUBGOAL_THEN `D <= &101 / &100 * (&1002 / &1000 * hk) * (inv ep + &24 / &5)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&101 / &100 * hz * (abs(apx_sval(v:real^3)) + sqrt(&2) * pi)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `&2` SQRT_POS_LE) THEN MP_TAC PI_POS THEN
    REWRITE_TAC[REAL_POS] THEN REPEAT STRIP_TAC THEN
    TRY(MATCH_MP_TAC REAL_LE_ADD) THEN
    ASM_SIMP_TAC[REAL_ABS_POS; REAL_LE_MUL; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the near level in e k *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `dl:real`; `yk:A`; `(e:num->real^3->A) k`; `u:real^3`; `z:A`]
                APX_NEAR_LEVEL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `apx_ch_ctx top atlas (g:A->real^3^3) dl` THEN SIMP_TAC[apx_ch_ctx];
      UNDISCH_TAC `(w:A) = (e:num->real^3->A) k u` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `(w:A) = (N:real^3->A) v` THEN DISCH_THEN SUBST1_TAC THEN
      ASM_MESON_TAC[MFD_JOINABLE_SYM];
      UNDISCH_TAC `(w:A) = (e:num->real^3->A) k u` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `w:A`; `z:A`] MFD_DIST_SYM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `(w:A) = (N:real^3->A) v` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      ASM_REWRITE_TAC[REAL_ABS_0; REAL_SUB_RZERO] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `&101 / &100 * (&1002 / &1000 * hk) * (inv ep + &24 / &5)` THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&101 / &100 * (&1002 / &1000 * hk) * (inv ep + &24 / &5) =
                    hk * (&101 / &100 * &1002 / &1000 * (inv ep + &24 / &5)) /\
                    &99 / &100 * hk * inv dl = hk * (&99 / &100 * inv dl)`
      (fun th -> REWRITE_TAC[th]) THENL [CONJ_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_LMUL_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `inv(sqrt(mfd_scalar atlas (g:A->real^3^3) yk)) = hk`]) THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^3^3) ((e:num->real^3->A) k u) z = D`
  ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN
    SUBGOAL_THEN `(e:num->real^3->A) k u = (N:real^3->A) v` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MFD_DIST_SYM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `abs(apx_sval(y:real^3)) < &2 * inv ep` ASSUME_TAC THENL
   [UNDISCH_TAC `&99 / &100 * hk * abs(apx_sval(y:real^3) - apx_sval(u:real^3)) <=
                 mfd_dist (top,atlas) (g:A->real^3^3) ((e:num->real^3->A) k u) z` THEN
    ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `hk * (&99 / &100 * abs(apx_sval(y:real^3))) <
                  hk * (&99 / &100 * &2 * inv ep)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `D:real` THEN CONJ_TAC THENL
       [UNDISCH_TAC `&99 / &100 * hk * abs(apx_sval(y:real^3)) <= D` THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LET_TRANS THEN
        EXISTS_TAC `&101 / &100 * (&1002 / &1000 * hk) * (inv ep + &24 / &5)` THEN
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `&101 / &100 * (&1002 / &1000 * hk) * (inv ep + &24 / &5) =
                      hk * (&101 / &100 * &1002 / &1000 * (inv ep + &24 / &5))`
        SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[REAL_LT_LMUL_EQ] THEN ASM_REAL_ARITH_TAC];
      ASM_SIMP_TAC[REAL_LT_LMUL_EQ] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `~(x < &0) ==> &0 <= x`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:A) IN IMAGE ((e:num->real^3->A) k) (apx_slab (--inv dl) (&0))`
  MP_TAC THENL
   [UNDISCH_TAC `(z:A) = (e:num->real^3->A) k y` THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[APX_SLAB_SVAL] THEN
    MP_TAC(SPECL [`dl:real`; `y:real^3`] APX_SVAL_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(MATCH_MP APX_RG_INNER (CONJ
    (ASSUME `apx_rg (top,atlas) (g:A->real^3^3) C eps dl J (e:num->real^3->A) P`)
    (ASSUME `(k:num) IN J`))) THEN
  UNDISCH_TAC `(z:A) IN top closure_of P` THEN SET_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* The extended cores Yhat(tau) = apx_bext(ball(exp(tau/sqrt2)))             *)
(* of a ball cap: open, frontier in the level-tau sphere of the boundary     *)
(* neck e', and membership of points of the outer half of e' by level.       *)
(* ------------------------------------------------------------------------- *)

let APX_PARAM_BALL_FRONTIER = prove
 (`!top atlas (B:real^3->A) R r.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     mfd_param top atlas (ball(vec 0,R)) B /\ &0 < r /\ r < R
     ==> open_in top (IMAGE B (ball(vec 0,r))) /\
         top closure_of (IMAGE B (ball(vec 0,r))) SUBSET IMAGE B (cball(vec 0,r)) /\
         top frontier_of (IMAGE B (ball(vec 0,r))) SUBSET IMAGE B (sphere(vec 0,r))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `ball(vec 0:real^3,R)`; `B:real^3->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Bi:A->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `cball(vec 0:real^3,r) SUBSET ball(vec 0,R) /\
                ball(vec 0:real^3,r) SUBSET ball(vec 0,R)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL_0; IN_CBALL_0] THEN CONJ_TAC THEN GEN_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (IMAGE (B:real^3->A) (ball(vec 0,r)))` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `ball(vec 0:real^3,R)`] THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in top (IMAGE (B:real^3->A) (cball(vec 0,r)))` ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology euclidean (ball(vec 0:real^3,R))` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN; COMPACT_CBALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `top closure_of (IMAGE (B:real^3->A) (ball(vec 0,r))) SUBSET
                IMAGE B (cball(vec 0,r))` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[BALL_SUBSET_CBALL];
      MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[frontier_of; INTERIOR_OF_OPEN_IN] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `ball(vec 0:real^3,R)`; `cball(vec 0:real^3,r)`;
                 `ball(vec 0:real^3,r)`; `B:real^3->A`] APX_PARAM_IMAGE_DIFF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[CBALL_DIFF_BALL] THEN ASM SET_TAC[]);;

let APX_BEXT_LEVELS = prove
 (`!top atlas (g:A->real^3^3) C eps U (b:real^3->A) e' f tau y.
     hausdorff_space top /\ &0 < eps /\ eps <= &1 / &8 /\
     apx_bcap (top,atlas) g C eps U b e' f /\
     &0 < tau /\ tau < inv eps /\
     y IN rfs_neck_dom eps /\ &0 <= apx_sval y
     ==> (e' y IN IMAGE (apx_bext b e' f) (ball(vec 0,exp(tau / sqrt(&2)))) <=>
          apx_sval y < tau)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[apx_bcap] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_bcap")) (concl th))) THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
                mfd_param top atlas (rfs_neck_dom eps) (e':real^3->A)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `b:real^3->A`;
                 `e':real^3->A`; `f:real^3->real^3`; `f':real^3->real^3`; `eps:real`]
                APX_BEXT_FACTS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[mfd_ball_chart]; ALL_TAC] THEN STRIP_TAC THEN
  MP_TAC(SPEC `eps:real` APX_BEXT_RADIUS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `R = exp(inv eps / sqrt(&2))` THEN
  ABBREV_TAC `r = exp(tau / sqrt(&2))` THEN
  SUBGOAL_THEN `&1 < r /\ r < R` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["r"; "R"] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_EXP_0; REAL_EXP_MONO_LT] THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH];
      REWRITE_TAC[REAL_EXP_MONO_LT] THEN
      ASM_SIMP_TAC[REAL_LT_DIV2_EQ; SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `f':real^3->real^3`] APX_RADIAL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0) /\ exp(apx_sval y / sqrt(&2)) = norm y /\
                &1 <= norm y /\ norm y < R` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`eps:real`; `y:real^3`] APX_SVAL_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `exp(apx_sval y / sqrt(&2)) = norm(y:real^3)` ASSUME_TAC THENL
     [REWRITE_TAC[apx_sval] THEN
      SUBGOAL_THEN `~(sqrt(&2) = &0)` ASSUME_TAC THENL
       [SIMP_TAC[SQRT_EQ_0; REAL_OF_NUM_EQ; ARITH]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_FIELD `~(s = &0) ==> (s * l) / s = l`; EXP_LOG; NORM_POS_LT];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[GSYM REAL_EXP_0; REAL_EXP_MONO_LE] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_POS];
      UNDISCH_TAC `(y:real^3) IN rfs_neck_dom eps` THEN
      REWRITE_TAC[APX_NECK_DOM_ANNULUS; annulus; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(apx_sval y < tau <=> norm(y:real^3) < r)` SUBST1_TAC THENL
   [EXPAND_TAC "r" THEN
    REWRITE_TAC[SYM(ASSUME `exp(apx_sval y / sqrt(&2)) = norm(y:real^3)`)] THEN
    REWRITE_TAC[REAL_EXP_MONO_LT] THEN
    ASM_SIMP_TAC[REAL_LT_DIV2_EQ; SQRT_POS_LT; REAL_OF_NUM_LT; ARITH];
    ALL_TAC] THEN
  EQ_TAC THENL
   [REWRITE_TAC[IN_IMAGE; IN_BALL_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC(REAL_ARITH `~(r <= y) ==> y < r`) THEN DISCH_TAC THEN
    ASM_CASES_TAC `norm(x:real^3) <= &1` THENL
     [UNDISCH_TAC `DISJOINT (IMAGE (e':real^3->A) (annulus (&1) R))
                            (IMAGE (b:real^3->A) (cball(vec 0,&1)))` THEN
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
      DISCH_THEN(MP_TAC o SPEC `(e':real^3->A) y`) THEN REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN
        ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:real^3` THEN
        ASM_SIMP_TAC[IN_CBALL_0; REAL_ARITH `x <= &1 ==> x < &2`]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(e':real^3->A) y = e'(radial_ext f x)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `y:real^3 = radial_ext f x` MP_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_INJ THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `rfs_neck_dom eps`; `e':real^3->A`] THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      UNDISCH_TAC `annulus (&1) R SUBSET rfs_neck_dom eps` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN(MP_TAC o AP_TERM `norm:real^3->real`) THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    DISCH_TAC THEN ASM_CASES_TAC `norm(y:real^3) = &1` THENL
     [SUBGOAL_THEN `(e':real^3->A) y IN IMAGE (b:real^3->A) (sphere(vec 0,&1))` MP_TAC THENL
       [FIRST_ASSUM((fun th -> REWRITE_TAC[SYM th]) o check (fun th -> is_eq(concl th) &&
          lhs(concl th) = `IMAGE (e':real^3->A) (sphere(vec 0,&1))`)) THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_SPHERE_0];
        ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `x:real^3` THEN ASM_SIMP_TAC[IN_BALL_0; REAL_ARITH `x = &1 ==> x < &2`] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_BALL_0] THEN EXISTS_TAC `radial_ext (f':real^3->real^3) y` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&1 < norm(radial_ext (f':real^3->real^3) y)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[]]);;

let APX_BEXT_SPHERE = prove
 (`!(b:real^3->A) e' f f' r.
     sphere_diffeo f f' /\ &1 < r /\
     (!x. &1 < norm x ==> apx_bext b e' f x = e'(radial_ext f x))
     ==> IMAGE (apx_bext b e' f) (sphere(vec 0,r)) = IMAGE e' (sphere(vec 0,r))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `f':real^3->real^3`] APX_RADIAL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_SPHERE_0] THEN X_GEN_TAC `p:A` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `radial_ext (f:real^3->real^3) x` THEN
    ASM_SIMP_TAC[REAL_ARITH `&1 < r /\ x = r ==> &1 < x`];
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `radial_ext (f':real^3->real^3) y` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&1 < norm(radial_ext (f':real^3->real^3) y)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[]]);;

(* The cap trigger: the last centre x_b lies outside Yhat(4/ep) and the new  *)
(* centre z inside; then both lie in the outer half of the boundary neck,    *)
(* x_b at level >= 4/ep and z at a positive level < 4/ep.                    *)

let APX_CAP_TRIGGER_GEOM = prove
 (`!top atlas (g:A->real^3^3) C eps ep U (bb:real^3->A) e' f xb (Nb:real^3->A) z.
     hausdorff_space top /\ riemannian_metric atlas g /\ &0 < eps /\
     &580 * eps <= ep /\ ep <= &1 / &1024 /\
     apx_ch_ctx top atlas g ep /\ apx_ch_ctx top atlas g eps /\ apx_cl_rat top atlas g ep /\
     apx_bcap (top,atlas) g C eps U bb e' f /\
     rfs_neck (top,atlas) g ep xb Nb /\
     z IN top closure_of (IMAGE Nb (apx_slab (inv(&2 * ep)) (inv ep))) /\
     ~(z IN IMAGE Nb (rfs_neck_dom ep)) /\
     ~(xb IN IMAGE (apx_bext bb e' f) (ball(vec 0,exp((&4 * inv ep) / sqrt(&2))))) /\
     z IN IMAGE (apx_bext bb e' f) (ball(vec 0,exp((&4 * inv ep) / sqrt(&2))))
     ==> ?yb yz. yb IN rfs_neck_dom eps /\ xb = e' yb /\
                 &4 * inv ep <= apx_sval yb /\ apx_sval yb <= &6 * inv ep /\
                 yz IN rfs_neck_dom eps /\ z = e' yz /\
                 &0 < apx_sval yz /\ apx_sval yz < &4 * inv ep`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  APX_UNFOLD_ASM_TAC "apx_bcap" apx_bcap THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
                mfd_param top atlas (rfs_neck_dom eps) (e':real^3->A) /\
                mfd_param top atlas (rfs_neck_dom ep) (Nb:real^3->A)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  SUBGOAL_THEN `eps <= &1 / &8 /\ &1024 <= inv ep /\ &580 * inv ep <= inv eps /\ &0 < ep`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < ep` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MP_TAC(SPECL [`ep:real`; `&1 / &1024`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `inv ep <= inv(&580 * eps)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_INV_MUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `bb:real^3->A`;
                 `e':real^3->A`; `f:real^3->real^3`; `f':real^3->real^3`; `eps:real`]
                APX_BEXT_FACTS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[mfd_ball_chart]; STRIP_TAC] THEN
  MP_TAC(SPEC `eps:real` APX_BEXT_RADIUS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `R = exp(inv eps / sqrt(&2))` THEN ABBREV_TAC `r = exp((&4 * inv ep) / sqrt(&2))` THEN
  SUBGOAL_THEN `&1 < r /\ r < R /\ &4 * inv ep < inv eps` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&4 * inv ep < inv eps` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["r"; "R"] THEN
    REWRITE_TAC[GSYM REAL_EXP_0; REAL_EXP_MONO_LT] THEN
    SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
     [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV2_EQ] THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `apx_bext (bb:real^3->A) e' f`; `R:real`; `r:real`] APX_PARAM_BALL_FRONTIER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`bb:real^3->A`; `e':real^3->A`; `f:real^3->real^3`; `f':real^3->real^3`;
                 `r:real`] APX_BEXT_SPHERE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~DISJOINT (IMAGE (Nb:real^3->A) (rfs_neck_dom ep))
                          (IMAGE (apx_bext (bb:real^3->A) e' f) (ball(vec 0,r)))` ASSUME_TAC THENL
   [UNDISCH_TAC `z IN top closure_of (IMAGE (Nb:real^3->A) (apx_slab (inv(&2 * ep)) (inv ep)))` THEN
    REWRITE_TAC[IN_CLOSURE_OF] THEN
    DISCH_THEN(MP_TAC o SPEC `IMAGE (apx_bext (bb:real^3->A) e' f) (ball(vec 0,r))` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `q:A` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `q:A` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `ep:real` APX_QUARTERS_SUB_DOM) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(xb:A) IN IMAGE (Nb:real^3->A) (rfs_neck_dom ep)` ASSUME_TAC THENL
   [MP_TAC(SPEC `ep:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) ep xb Nb` THEN
    REWRITE_TAC[rfs_neck] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?w. w IN IMAGE (Nb:real^3->A) (rfs_neck_dom ep) /\
                    w IN IMAGE (e':real^3->A) (sphere(vec 0,r))` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `IMAGE (Nb:real^3->A) (rfs_neck_dom ep)`;
                   `IMAGE (apx_bext (bb:real^3->A) e' f) (ball(vec 0,r))`]
                  CONNECTED_IN_INTER_FRONTIER_OF) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
        MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom ep`] THEN
        ASM_REWRITE_TAC[SUBSET_REFL; APX_NECK_DOM_ANNULUS; APX_CONNECTED_ANNULUS3];
        ASM_REWRITE_TAC[GSYM DISJOINT];
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_DIFF] THEN EXISTS_TAC `xb:A` THEN
        ASM_REWRITE_TAC[]];
      UNDISCH_TAC `top frontier_of IMAGE (apx_bext (bb:real^3->A) e' f) (ball(vec 0,r)) SUBSET
                   IMAGE (apx_bext bb e' f) (sphere(vec 0,r))` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `vw:real^3` STRIP_ASSUME_TAC o REWRITE_RULE[IN_IMAGE] o
    check (fun th -> concl th = `(w:A) IN IMAGE (Nb:real^3->A) (rfs_neck_dom ep)`)) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `yw:real^3` STRIP_ASSUME_TAC o REWRITE_RULE[IN_IMAGE] o
    check (fun th -> concl th = `(w:A) IN IMAGE (e':real^3->A) (sphere(vec 0,r))`)) THEN
  SUBGOAL_THEN `(yw:real^3) IN rfs_neck_dom eps /\ apx_sval yw = &4 * inv ep` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `norm(yw:real^3) = r` ASSUME_TAC THENL
     [UNDISCH_TAC `(yw:real^3) IN sphere(vec 0,r)` THEN REWRITE_TAC[IN_SPHERE_0]; ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `annulus (&1) R SUBSET rfs_neck_dom eps` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[annulus; IN_ELIM_THM];
      ASM_REWRITE_TAC[apx_sval] THEN
      REWRITE_TAC[SYM(ASSUME `exp((&4 * inv ep) / sqrt(&2)) = r`); LOG_EXP] THEN
      SUBGOAL_THEN `~(sqrt(&2) = &0)` MP_TAC THENL
       [SIMP_TAC[SQRT_EQ_0; REAL_OF_NUM_EQ; ARITH]; CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) xb /\ &0 < mfd_scalar atlas g z'`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(mfd_scalar atlas (g:A->real^3^3) w / mfd_scalar atlas g xb - &1)
                <= &1 / &1000 /\
                abs(mfd_scalar atlas g w / mfd_scalar atlas g z' - &1) <= &1 / &1000`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(REWRITE_RULE[apx_cl_rat] (ASSUME `apx_cl_rat top atlas (g:A->real^3^3) ep`)) THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPECL [`ep:real`; `xb:A`; `Nb:real^3->A`; `vw:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
      UNDISCH_TAC `(w:A) = (Nb:real^3->A) vw` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[];
      FIRST_ASSUM(MP_TAC o SPECL [`eps:real`; `z':A`; `e':real^3->A`; `yw:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `(w:A) = (e':real^3->A) yw` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) w` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) w / mfd_scalar atlas g xb` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_MUL_LZERO]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`mfd_scalar atlas (g:A->real^3^3) xb`; `mfd_scalar atlas (g:A->real^3^3) z'`;
                `mfd_scalar atlas (g:A->real^3^3) w`] APX_RATIO_SQRT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `hb = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) xb))` THEN
  ABBREV_TAC `hp = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) z'))` THEN
  SUBGOAL_THEN `&0 < hb /\ &0 < hp` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["hb"; "hp"] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN
    MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `ep:real`; `xb:A`; `Nb:real^3->A`; `vw:real^3`] APX_CENTRE_DIST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `apx_ch_ctx top atlas (g:A->real^3^3) ep` THEN
    SIMP_TAC[apx_ch_ctx];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`ep:real`; `vw:real^3`] APX_SVAL_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN MP_TAC APX_SQRT2_PI THEN DISCH_TAC THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^3^3) xb ((Nb:real^3->A) vw) <=
                hp * (&101 / &100 * &1002 / &1000 * (inv ep + &24 / &5))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&101 / &100 * hb * (abs(apx_sval(vw:real^3)) + sqrt(&2) * pi)` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `hb * (abs(apx_sval(vw:real^3)) + sqrt(&2) * pi) <=
                  (&1002 / &1000 * hp) * (inv ep + &24 / &5)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MP_TAC(SPEC `&2` SQRT_POS_LE) THEN MP_TAC PI_POS THEN REWRITE_TAC[REAL_POS] THEN
      REPEAT STRIP_TAC THEN TRY(MATCH_MP_TAC REAL_LE_ADD) THEN
      ASM_SIMP_TAC[REAL_ABS_POS; REAL_LE_MUL; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas) ((e':real^3->A) yw) xb /\
                mfd_dist (top,atlas) (g:A->real^3^3) (e' yw) xb =
                mfd_dist (top,atlas) g xb ((Nb:real^3->A) vw)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(e':real^3->A) yw = (Nb:real^3->A) vw` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_SYM]; ASM_MESON_TAC[MFD_DIST_SYM]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `z':A`; `e':real^3->A`; `yw:real^3`; `xb:A`] APX_NEAR_LEVEL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `apx_ch_ctx top atlas (g:A->real^3^3) eps` THEN SIMP_TAC[apx_ch_ctx];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `hp * (&101 / &100 * &1002 / &1000 * (inv ep + &24 / &5))` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&99 / &100 * hp * (inv eps - abs(&4 * inv ep)) =
                  hp * (&99 / &100 * (inv eps - abs(&4 * inv ep)))` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LMUL_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `yb:real^3` (STRIP_ASSUME_TAC o
    REWRITE_RULE[ASSUME `inv(sqrt(mfd_scalar atlas (g:A->real^3^3) z')) = hp`])) THEN
  SUBGOAL_THEN `abs(apx_sval(yb:real^3) - &4 * inv ep) <= &2 * inv ep` ASSUME_TAC THENL
   [SUBGOAL_THEN `hp * (&99 / &100 * abs(apx_sval(yb:real^3) - &4 * inv ep)) <=
                  hp * (&101 / &100 * &1002 / &1000 * (inv ep + &24 / &5))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `mfd_dist (top,atlas) (g:A->real^3^3) xb ((Nb:real^3->A) vw)` THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t ->
          t = `apx_sval(yb:real^3) - apx_sval(yw:real^3)`)) (concl th))) THEN
        REWRITE_TAC[ASSUME `apx_sval(yw:real^3) = &4 * inv ep`;
                    ASSUME `mfd_dist (top,atlas) (g:A->real^3^3) ((e':real^3->A) yw) xb =
                            mfd_dist (top,atlas) g xb ((Nb:real^3->A) vw)`] THEN
        REAL_ARITH_TAC;
        FIRST_ASSUM ACCEPT_TAC];
      ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 * inv ep <= apx_sval(yb:real^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `~(s < t) ==> t <= s`) THEN DISCH_TAC THEN
    UNDISCH_TAC `~((xb:A) IN IMAGE (apx_bext (bb:real^3->A) e' f) (ball(vec 0,r)))` THEN
    REWRITE_TAC[] THEN
    UNDISCH_TAC `(xb:A) = (e':real^3->A) yb` THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `C:real`; `eps:real`; `U:A->bool`; `bb:real^3->A`; `e':real^3->A`;
                   `f:real^3->real^3`; `&4 * inv ep`; `yb:real^3`] APX_BEXT_LEVELS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `exp((&4 * inv ep) / sqrt(&2)) = r`] THEN
    DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `ep:real`; `xb:A`; `Nb:real^3->A`; `z:A`] APX_FRONTIER_DIST) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `z':A`; `e':real^3->A`; `yb:real^3`; `z:A`] APX_NEAR_LEVEL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `apx_ch_ctx top atlas (g:A->real^3^3) eps` THEN SIMP_TAC[apx_ch_ctx];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&101 / &100 * hb * inv ep` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&101 / &100 * hb * inv ep <= hp * (&101 / &100 * &1002 / &1000 * inv ep)`
    MP_TAC THENL
     [SUBGOAL_THEN `hb * inv ep <= (&1002 / &1000 * hp) * inv ep` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `hp * (&101 / &100 * &1002 / &1000 * inv ep) <
                  &99 / &100 * hp * (inv eps - abs(apx_sval(yb:real^3)))` MP_TAC THENL
     [SUBGOAL_THEN `&99 / &100 * hp * (inv eps - abs(apx_sval(yb:real^3))) =
                    hp * (&99 / &100 * (inv eps - abs(apx_sval yb)))` SUBST1_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_LMUL_EQ] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `yz:real^3` (STRIP_ASSUME_TAC o
    REWRITE_RULE[ASSUME `inv(sqrt(mfd_scalar atlas (g:A->real^3^3) z')) = hp`])) THEN
  SUBGOAL_THEN `abs(apx_sval(yz:real^3) - apx_sval(yb:real^3)) <= &2 * inv ep` ASSUME_TAC THENL
   [SUBGOAL_THEN `hp * (&99 / &100 * abs(apx_sval(yz:real^3) - apx_sval(yb:real^3))) <=
                  hp * (&101 / &100 * &1002 / &1000 * inv ep)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `mfd_dist (top,atlas) (g:A->real^3^3) ((e':real^3->A) yb) z` THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t ->
          t = `apx_sval(yz:real^3) - apx_sval(yb:real^3)`)) (concl th))) THEN
        REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&101 / &100 * hb * inv ep` THEN
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `hb * inv ep <= (&1002 / &1000 * hp) * inv ep` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
          REAL_ARITH_TAC]];
      ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`yb:real^3`; `yz:real^3`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `~(t <= s) ==> s < t`) THEN DISCH_TAC THEN
  UNDISCH_TAC `(z:A) IN IMAGE (apx_bext (bb:real^3->A) e' f) (ball(vec 0,r))` THEN
  UNDISCH_TAC `(z:A) = (e':real^3->A) yz` THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `U:A->bool`; `bb:real^3->A`; `e':real^3->A`;
                 `f:real^3->real^3`; `&4 * inv ep`; `yz:real^3`] APX_BEXT_LEVELS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `exp((&4 * inv ep) / sqrt(&2)) = r`] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The cap trigger, part 2.  Two arithmetic helpers, and the                 *)
(* impossibility of a forward pair from a chain neck centred at cap levels   *)
(* [4/ep, 6/ep] to the copy of the cap neck centred at a level in (0, 4/ep): *)
(* the pair offset Delta (at least 1/(2 ep)) would push the copy centre      *)
(* above level 4/ep.                                                         *)
(* ------------------------------------------------------------------------- *)

let APX_DIV34 = prove
 (`!x. &3 / (&4 * x) = &3 / &4 * inv x`,
  REWRITE_TAC[real_div; REAL_INV_MUL] THEN REAL_ARITH_TAC);;

let APX_INV_K = prove
 (`!x. inv(&2 * x) = inv x / &2 /\ inv(&4 * x) = inv x / &4 /\
       inv(&8 * x) = inv x / &8 /\ inv(&32 * x) = inv x / &32`,
  REWRITE_TAC[REAL_INV_MUL; real_div] THEN REAL_ARITH_TAC);;

let APX_CAP_NO_FORWARD = prove
 (`!top atlas (g:A->real^3^3) C eps ep U (bb:real^3->A) e' f xb (Nb:real^3->A) z yb yz.
     hausdorff_space top /\ riemannian_metric atlas g /\ &0 < eps /\
     &580 * eps <= ep /\ apx_kc * eps <= ep /\ ep <= &1 / &1024 /\
     apx_ch_ctx top atlas g ep /\ apx_ch_pair top atlas g ep /\
     apx_bcap (top,atlas) g C eps U bb e' f /\
     rfs_neck (top,atlas) g ep xb Nb /\
     yb IN rfs_neck_dom eps /\ xb = e' yb /\
     &4 * inv ep <= apx_sval yb /\ apx_sval yb <= &6 * inv ep /\
     yz IN rfs_neck_dom eps /\ z = e' yz /\ &0 < apx_sval yz /\ apx_sval yz < &4 * inv ep /\
     IMAGE Nb (apx_slab (inv(&2 * ep)) (inv ep)) UNION
     IMAGE (apx_cp e' yz) (apx_slab (--inv ep) (--inv(&2 * ep)))
     SUBSET IMAGE Nb (rfs_neck_dom ep) INTER IMAGE (apx_cp e' yz) (rfs_neck_dom ep) /\
     IMAGE Nb (rfs_neck_dom ep) INTER IMAGE (apx_cp e' yz) (rfs_neck_dom ep)
     SUBSET IMAGE Nb (apx_slab (--inv(&2 * ep)) (inv ep)) INTER
            IMAGE (apx_cp e' yz) (apx_slab (--inv ep) (inv(&2 * ep)))
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  APX_UNFOLD_ASM_TAC "apx_bcap" apx_bcap THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
                mfd_param top atlas (rfs_neck_dom eps) (e':real^3->A) /\
                mfd_param top atlas (rfs_neck_dom ep) (Nb:real^3->A)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  SUBGOAL_THEN `&1024 <= inv ep /\ &580 * inv ep <= inv eps /\ &0 < ep /\ eps <= &1 / &8`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < ep` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(SPECL [`ep:real`; `&1 / &1024`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `inv ep <= inv(&580 * eps)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_INV_MUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_neck (top,atlas) (g:A->real^3^3) ep z (apx_cp e' yz) /\
                rfs_neck (top,atlas) g ep xb (apx_cp e' yb)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC APX_CP_NECK THEN
    MAP_EVERY EXISTS_TAC [`eps:real`; `z':A`] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[APX_DIV34] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `xb:A = (e':real^3->A) yb`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `z:A = (e':real^3->A) yz`)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom ep`; `Nb:real^3->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ei:A->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`(e':real^3->A) yb`; `Nb:real^3->A`; `(e':real^3->A) yz`;
                `apx_cp (e':real^3->A) yz`; `ei:A->real^3`]
         (REWRITE_RULE[apx_ch_pair] (ASSUME `apx_ch_pair top atlas (g:A->real^3^3) ep`))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Delta:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) ((e':real^3->A) yb)` ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  ABBREV_TAC `hb = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) ((e':real^3->A) yb)))` THEN
  SUBGOAL_THEN `&0 < hb` ASSUME_TAC THENL
   [EXPAND_TAC "hb" THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!sig. --inv ep < sig /\ sig < inv ep - Delta - inv(&32 * ep) /\
          abs(sig + Delta) <= &3 / &5 * inv ep
          ==> apx_sval(yb:real^3) -
              &10203 / &10000 * (abs(sig + Delta) + inv(&32 * ep) + &24 / &5) <=
              apx_sval(yz:real^3) + sig`
  ASSUME_TAC THENL
   [X_GEN_TAC `sig:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(exp(sig / sqrt(&2)) % basis 1:real^3 = vec 0) /\
                apx_sval(exp(sig / sqrt(&2)) % basis 1:real^3) = sig /\
                exp(sig / sqrt(&2)) % basis 1:real^3 IN rfs_neck_dom ep` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`sig:real`; `&1`] APX_SVAL_SCALED_BASIS) THEN
    REWRITE_TAC[REAL_LT_01; VECTOR_MUL_LID; LOG_1; REAL_MUL_RZERO; REAL_ADD_RID] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `v = exp(sig / sqrt(&2)) % basis 1:real^3` THEN
  SUBGOAL_THEN `apx_cp (e':real^3->A) yz v IN IMAGE (Nb:real^3->A) (rfs_neck_dom ep)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `inv ep - Delta - inv(&32 * ep)`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(apx_sval((ei:A->real^3) (apx_cp (e':real^3->A) yz v)) - sig - Delta)
                <= inv(&32 * ep)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `v:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `Delta:real`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "real_abs")) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `p = apx_cp (e':real^3->A) yz v` THEN
  SUBGOAL_THEN `(ei:A->real^3) p IN rfs_neck_dom ep /\ (Nb:real^3->A)(ei p) = p`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(p:A) IN IMAGE (Nb:real^3->A) (rfs_neck_dom ep)` THEN
    REWRITE_TAC[IN_IMAGE] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `ep:real`; `(e':real^3->A) yb`; `Nb:real^3->A`; `(ei:A->real^3) p`]
                APX_CENTRE_DIST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `apx_ch_ctx top atlas (g:A->real^3^3) ep` THEN
    SIMP_TAC[apx_ch_ctx];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`e':real^3->A`; `yb:real^3`; `eps:real`] APX_CP_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`e':real^3->A`; `yz:real^3`; `eps:real`] APX_CP_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `inv(norm yb) % yb:real^3 IN rfs_neck_dom ep /\
                apx_sval(inv(norm yb) % yb:real^3) = &0 /\
                apx_cp (e':real^3->A) yb (inv(norm yb) % yb) = e' yb` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `norm(inv(norm yb) % yb:real^3) = &1` ASSUME_TAC THENL
     [REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(SPEC `ep:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[apx_sval; LOG_1; REAL_MUL_RZERO];
      ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `ep:real`; `(e':real^3->A) yb`; `apx_cp (e':real^3->A) yb`;
                 `inv(norm yb) % yb:real^3`; `p:A`] APX_NEAR_LEVEL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_ABS_0; REAL_SUB_RZERO] THEN CONJ_TAC THENL
     [UNDISCH_TAC `apx_ch_ctx top atlas (g:A->real^3^3) ep` THEN SIMP_TAC[apx_ch_ctx];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `&101 / &100 * hb * (abs(apx_sval((ei:A->real^3) p)) + sqrt(&2) * pi)` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `abs(apx_sval((ei:A->real^3) p)) + sqrt(&2) * pi < &98 / &100 * inv ep`
    ASSUME_TAC THENL
     [MP_TAC APX_SQRT2_PI THEN MP_TAC(SPEC `ep:real` APX_INV_K) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&101 / &100 * hb * (abs(apx_sval((ei:A->real^3) p)) + sqrt(&2) * pi) =
                  hb * (&101 / &100 * (abs(apx_sval(ei p)) + sqrt(&2) * pi)) /\
                  &99 / &100 * hb * inv ep = hb * (&99 / &100 * inv ep)` (fun th -> REWRITE_TAC[th])
    THENL [CONJ_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LMUL_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3` (STRIP_ASSUME_TAC o
    REWRITE_RULE[ASSUME `inv(sqrt(mfd_scalar atlas (g:A->real^3^3) ((e':real^3->A) yb))) = hb`;
                 ASSUME `apx_sval(inv(norm yb) % yb:real^3) = &0`; REAL_SUB_RZERO])) THEN
  SUBGOAL_THEN `&99 / &100 * abs(apx_sval(u:real^3)) <=
                &101 / &100 * (abs(apx_sval((ei:A->real^3) p)) + sqrt(&2) * pi)` ASSUME_TAC THENL
   [SUBGOAL_THEN `hb * (&99 / &100 * abs(apx_sval(u:real^3))) <=
                  hb * (&101 / &100 * (abs(apx_sval((ei:A->real^3) p)) + sqrt(&2) * pi))`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `mfd_dist (top,atlas) (g:A->real^3^3) ((e':real^3->A) yb) p` THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t ->
          t = `abs(apx_sval(u:real^3))`)) (concl th))) THEN
        REWRITE_TAC[ASSUME `apx_cp (e':real^3->A) yb (inv(norm yb) % yb) = e' yb`] THEN
        REAL_ARITH_TAC;
        FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t ->
          t = `mfd_dist (top,atlas) (g:A->real^3^3) ((e':real^3->A) yb) p`)) (concl th) &&
          can (find_term (fun t -> t = `sqrt(&2) * pi`)) (concl th))) THEN
        REAL_ARITH_TAC];
      ASM_SIMP_TAC[REAL_LE_LMUL_EQ]];
    ALL_TAC] THEN
  SUBGOAL_THEN `apx_sval(norm(yz:real^3) % v) = apx_sval(norm(yb:real^3) % u)` MP_TAC THENL
   [AP_TERM_TAC THEN MATCH_MP_TAC MFD_PARAM_INJ THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `rfs_neck_dom eps`; `e':real^3->A`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`ep:real`; `u:real^3`] APX_SVAL_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN MP_TAC APX_SQRT2_PI THEN MP_TAC(SPEC `ep:real` APX_INV_K) THEN
    REPEAT STRIP_TAC THENL
     [ASM_SIMP_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL; VECTOR_MUL_EQ_0; NORM_EQ_0] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ASM_REAL_ARITH_TAC];
      ASM_SIMP_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL; VECTOR_MUL_EQ_0; NORM_EQ_0] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ASM_REAL_ARITH_TAC];
      UNDISCH_TAC `apx_cp (e':real^3->A) yz v = p` THEN
      UNDISCH_TAC `(p:A) = apx_cp (e':real^3->A) yb u` THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`ep:real`; `u:real^3`] APX_SVAL_NECK_DOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM((fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `~(u:real^3 = vec 0)`)]) o check (fun th ->
    is_forall (concl th) && can (find_term (fun t -> t = `norm(yb:real^3)`)) (concl th) &&
    can (find_term (fun t -> is_neg t)) (concl th))) THEN
  FIRST_ASSUM((fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `~(v:real^3 = vec 0)`)]) o check (fun th ->
    is_forall (concl th) && can (find_term (fun t -> t = `norm(yz:real^3)`)) (concl th) &&
    can (find_term (fun t -> is_neg t)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC APX_SQRT2_PI THEN
  UNDISCH_TAC `abs (apx_sval ((ei:A->real^3) p) - sig - Delta) <= inv (&32 * ep)` THEN
  UNDISCH_TAC `&99 / &100 * abs(apx_sval(u:real^3)) <=
               &101 / &100 * (abs(apx_sval((ei:A->real^3) p)) + sqrt(&2) * pi)` THEN
  SUBGOAL_THEN `&0 < inv(&32 * ep)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `ep:real` APX_INV_K) THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `inv(&2 * ep) = inv ep / &2`;
                              ASSUME `inv(&32 * ep) = inv ep / &32`]) THEN
  ASM_CASES_TAC `Delta <= &31 / &32 * inv ep` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `--Delta` o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `&10203 / &10000`)) (concl th))) THEN
  REWRITE_TAC[REAL_ARITH `--Delta + Delta = &0`; REAL_ABS_0] THEN
  ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `--(&31 / &32 * inv ep)` o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `&10203 / &10000`)) (concl th))) THEN
  SUBGOAL_THEN `abs(--(&31 / &32 * inv ep) + Delta) = Delta - &31 / &32 * inv ep`
    SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The region growth, part 1.  Closures of slab images, the                  *)
(* extended core inside its cap, the A13 context, growth chains (a balanced  *)
(* chain starting at e_i, centred in the closure of P, centres outside every *)
(* Yhat_U(4/ep), necks missing the other cut spheres), the start, and the    *)
(* impossibility of covering the closure of P without a stop (N5).          *)
(* ------------------------------------------------------------------------- *)

let APX_PARAM_CSLAB_CLOSURE = prove
 (`!top atlas (e:real^3->A) d a b.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     mfd_param top atlas (rfs_neck_dom d) e /\ --inv d < a /\ b < inv d
     ==> top closure_of (IMAGE e (apx_slab a b)) SUBSET
         IMAGE e {y | ~(y = vec 0) /\ a <= apx_sval y /\ apx_sval y <= b}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom d`; `e:real^3->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ei:A->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`a:real`; `b:real`] APX_CSLAB) THEN STRIP_TAC THEN
  SUBGOAL_THEN `{y:real^3 | ~(y = vec 0) /\ a <= apx_sval y /\ apx_sval y <= b} =
                cball(vec 0,exp(b / sqrt(&2))) DIFF ball(vec 0,exp(a / sqrt(&2)))`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `cball(vec 0:real^3,exp(b / sqrt(&2))) DIFF ball(vec 0,exp(a / sqrt(&2)))
                SUBSET rfs_neck_dom d` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN X_GEN_TAC `y:real^3` THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN CONJ_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; APX_SLAB_SVAL] THEN
    ASM_REWRITE_TAC[] THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC IMAGE_COMPACT_IN THEN
  EXISTS_TAC `subtopology euclidean (rfs_neck_dom d)` THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN]);;

let APX_BEXT_IN_U = prove
 (`!top atlas (g:A->real^3^3) C eps U (bb:real^3->A) e' f r.
     &0 < eps /\ eps <= &1 / &8 /\ apx_bcap (top,atlas) g C eps U bb e' f /\
     r <= exp(inv eps / sqrt(&2))
     ==> IMAGE (apx_bext bb e' f) (ball(vec 0,r)) SUBSET U`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  APX_UNFOLD_ASM_TAC "apx_bcap" apx_bcap THEN
  MP_TAC(SPEC `eps:real` APX_BEXT_RADIUS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_BALL_0] THEN X_GEN_TAC `x:real^3` THEN
  DISCH_TAC THEN REWRITE_TAC[apx_bext] THEN COND_CASES_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (find_term (fun t -> t = `ball(vec 0:real^3,&2)`)) (concl th) &&
      is_comb (concl th) && not (is_forall (concl th)))) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_BALL_0];
    ALL_TAC] THEN
  FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
    can (find_term (fun t -> t = `rfs_neck_dom eps`)) (concl th) &&
    can (find_term (fun t -> t = `U:A->bool`)) (concl th))) THEN
  MATCH_MP_TAC FUN_IN_IMAGE THEN
  FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
    can (find_term (fun t -> t = `annulus (&1) (exp(inv eps / sqrt(&2))):real^3->bool`))
        (concl th))) THEN
  REWRITE_TAC[annulus; IN_ELIM_THM] THEN
  SUBGOAL_THEN `norm(radial_ext (f:real^3->real^3) x) = norm x` SUBST1_TAC THENL
   [MATCH_MP_TAC SMT_RADIAL_EXT_NORM THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[sphere_diffeo] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "sphere_diffeo")) (concl th))) THEN
    MESON_TAC[];
    ASM_REAL_ARITH_TAC]);;

let apx_a13_ctx = new_definition
 `apx_a13_ctx (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)
              (ep:real) <=>
    !n x (N:int->real^3->A).
       apx_chain (top,atlas) g ep {m:int | &0 <= m /\ m <= &n} x N
       ==> ?E L f f'. &0 <= L /\ sphere_diffeo f f' /\
             mfd_param top atlas (apx_slab (--inv ep) (L + inv ep)) E /\
             (!y. y IN apx_slab (--inv ep) (inv(&8 * ep)) ==> E y = N (&0) y) /\
             (!y. y IN apx_slab (L - inv(&8 * ep)) (L + inv ep)
                  ==> E y = N (&n) (radial_ext f (exp(--L / sqrt(&2)) % y))) /\
             IMAGE E (apx_slab (--inv ep) (L + inv ep)) =
             apx_chain_union ep {m:int | &0 <= m /\ m <= &n} N`;;

let APX_A13_CTX_HOLDS = prove
 (`?eps0. &0 < eps0 /\
     !top atlas (g:A->real^3^3) ep.
        &0 < ep /\ ep <= eps0 /\ hausdorff_space top /\ riemannian_metric atlas g
        ==> apx_a13_ctx top atlas g ep`,
  MP_TAC(ISPEC `UNIV:A->bool` APX_A13_CORE_UNCOND) THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[apx_a13_ctx] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
     `g:A->real^3^3`; `ep:real`; `n:num`; `x:int->A`; `N:int->real^3->A`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `E:real^3->A` (X_CHOOSE_THEN `L:real`
    (X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `f':real^3->real^3`
     STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`E:real^3->A`; `L:real`; `f:real^3->real^3`; `f':real^3->real^3`] THEN
  ASM_REWRITE_TAC[]);;

let apx_gch = new_definition
 `apx_gch (top:A topology,atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)
          (C:real) (eps:real) (ep:real) (J:num->bool) (e:num->real^3->A) (P:A->bool)
          (i:num) (b:int) (x:int->A) (N:int->real^3->A) <=>
    &0 <= b /\
    apx_balanced (top,atlas) g ep {m:int | &0 <= m /\ m <= b} x N /\
    N (&0) = e i /\
    (!m. &0 <= m /\ m <= b ==> x m IN top closure_of P) /\
    (!m U bb e' f. &0 <= m /\ m <= b /\ apx_bcap (top,atlas) g C eps U bb e' f
         ==> ~(x m IN IMAGE (apx_bext bb e' f) (ball(vec 0,exp((&4 * inv ep) / sqrt(&2)))))) /\
    (!m j. &0 <= m /\ m <= b /\ j IN J /\ ~(j = i)
         ==> DISJOINT (IMAGE (N m) (rfs_neck_dom ep)) (IMAGE (e j) (sphere(vec 0,&1))))`;;

let APX_RG_INIT = prove
 (`!top atlas (g:A->real^3^3) C eps dl ep J (e:num->real^3->A) P i.
     apx_rgc (top,atlas) g C eps dl ep J e P /\ i IN J
     ==> ?x N. apx_gch (top,atlas) g C eps ep J e P i (&0) x N`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_RG_CTX_SCALES) THEN
  APX_UNFOLD_ASM_TAC "apx_rgc" apx_rgc THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_RG_PARTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[apx_rg] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_rg")) (concl th))) THEN
  SUBGOAL_THEN `?y. rfs_neck (top,atlas) (g:A->real^3^3) dl y ((e:num->real^3->A) i)`
  (X_CHOOSE_TAC `y:A`) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `rfs_neck (top,atlas) (g:A->real^3^3) ep y ((e:num->real^3->A) i)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC APX_NECK_MONO_GEN THEN EXISTS_TAC `dl:real` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1))` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) dl y ((e:num->real^3->A) i)` THEN
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
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `C:real`; `eps:real`; `U:A->bool`; `bb:real^3->A`;
                   `e':real^3->A`; `f:real^3->real^3`;
                   `exp((&4 * inv ep) / sqrt(&2))`] APX_BEXT_IN_U) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      MP_TAC(SPECL [`&4 * inv ep`; `inv eps`; `sqrt(&2)`] REAL_LE_DIV2_EQ) THEN
      ANTS_TAC THENL [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `DISJOINT (U:A->bool)
                    (IMAGE ((e:num->real^3->A) i) (apx_slab (--inv(&2 * dl)) (inv(&2 * dl))))`
    MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> t = `inv(&2 * dl)`)) (concl th))) THEN
      EXISTS_TAC `IMAGE (bb:real^3->A) (ball(vec 0,&1))` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `apx_bcap (top,atlas) (g:A->real^3^3) C eps U bb e' f` THEN
      SIMP_TAC[apx_bcap];
      ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1)) SUBSET
                  IMAGE (e i) (apx_slab (--inv(&2 * dl)) (inv(&2 * dl)))` MP_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; IN_SPHERE_0; APX_SLAB_SVAL; apx_sval] THEN
      X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN ASM_REWRITE_TAC[LOG_1; REAL_MUL_RZERO] THEN
      CONJ_TAC THENL
       [DISCH_THEN(MP_TAC o AP_TERM `norm:real^3->real`) THEN ASM_REWRITE_TAC[NORM_0] THEN
        REAL_ARITH_TAC;
        SUBGOAL_THEN `&0 < inv(&2 * dl)` MP_TAC THENL
         [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
      ALL_TAC] THEN
    UNDISCH_TAC `(y:A) IN IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1))` THEN
    SET_TAC[];
    MAP_EVERY X_GEN_TAC [`m:int`; `j:num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`] o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = `&8 / ep`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `(s:A->bool) SUBSET t ==> DISJOINT u t ==> DISJOINT s u`) THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[APX_SLAB_NECK_DOM] THEN
    MATCH_MP_TAC APX_SLAB_SUBSET THEN REWRITE_TAC[real_div; REAL_MUL_LID] THEN
    SUBGOAL_THEN `&0 < inv ep` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]]);;

let APX_RG_NOT_COVERED = prove
 (`!top atlas (g:A->real^3^3) C eps dl ep J (e:num->real^3->A) P i b x N.
     apx_rgc (top,atlas) g C eps dl ep J e P /\ apx_a13_ctx top atlas g ep /\ i IN J /\
     apx_gch (top,atlas) g C eps ep J e P i b x N
     ==> ~(top closure_of P SUBSET apx_chain_union ep {m:int | &0 <= m /\ m <= b} N)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_RG_CTX_SCALES) THEN
  APX_UNFOLD_ASM_TAC "apx_rgc" apx_rgc THEN
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

(* ------------------------------------------------------------------------- *)
(* The region growth, part 2.  The frontier point of a growth                *)
(* chain that does not cover the closure of P lies at its positive end; the  *)
(* step: a cap trigger (the reversed copy of the cap neck, a stop), a sphere *)
(* zone (the copy of e_k: a reversed stop if it meets S_k, else growth), or *)
(* a hypothesis neck (growth).                                               *)
(* ------------------------------------------------------------------------- *)

let APX_RG_FRONTIER = prove
 (`!top atlas (g:A->real^3^3) C eps dl ep J (e:num->real^3->A) P i b x N.
     apx_rgc (top,atlas) g C eps dl ep J e P /\ i IN J /\
     apx_gch (top,atlas) g C eps ep J e P i b x N /\
     ~(top closure_of P SUBSET apx_chain_union ep {m:int | &0 <= m /\ m <= b} N)
     ==> ?z. z IN top closure_of P /\
             ~(z IN apx_chain_union ep {m:int | &0 <= m /\ m <= b} N) /\
             z IN top closure_of (IMAGE (N b) (apx_slab (inv(&2 * ep)) (inv ep)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_RG_CTX_SCALES) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP APX_RG_INNER o C CONJ (ASSUME `(i:num) IN J`) o
    CONJUNCT1 o REWRITE_RULE[apx_rgc]) THEN
  APX_UNFOLD_ASM_TAC "apx_rgc" apx_rgc THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[apx_rg] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_rg")) (concl th))) THEN
  APX_UNFOLD_ASM_TAC "apx_gch" apx_gch THEN
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
                 `(e:num->real^3->A) i`; `dl:real`; `--inv ep`; `--inv(&2 * ep)`]
                APX_PARAM_CSLAB_CLOSURE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
    MP_TAC(SPEC `ep:real` APX_INV_K) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < inv ep` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `{y:real^3 | ~(y = vec 0) /\ --inv ep <= apx_sval y /\
                            apx_sval y <= --inv(&2 * ep)} SUBSET apx_slab (--inv dl) (&0)`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; APX_SLAB_SVAL] THEN X_GEN_TAC `y:real^3` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `ep:real` APX_INV_K) THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `inv(&2 * ep) = inv ep / &2`]) THEN
    SUBGOAL_THEN `&0 < inv ep` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `DISJOINT (top closure_of P)
                 (IMAGE ((e:num->real^3->A) i) (apx_slab (--inv dl) (&0)))` THEN
  UNDISCH_TAC `(z:A) IN top closure_of P` THEN
  UNDISCH_TAC `(z:A) IN top closure_of
                 IMAGE ((e:num->real^3->A) i) (apx_slab (--inv ep) (--inv(&2 * ep)))` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`(e:num->real^3->A) i`;
                 `{y:real^3 | ~(y = vec 0) /\ --inv ep <= apx_sval y /\
                              apx_sval y <= --inv(&2 * ep)}`;
                 `apx_slab (--inv dl) (&0)`] IMAGE_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let APX_GCH_EXTEND = prove
 (`!top atlas (g:A->real^3^3) C eps ep J (e:num->real^3->A) P i b x N z ez.
     apx_gch (top,atlas) g C eps ep J e P i b x N /\
     apx_balanced (top,atlas) g ep {m:int | &0 <= m /\ m <= b + &1}
       (\m. if m = b + &1 then z else x m) (\m. if m = b + &1 then ez else N m) /\
     z IN top closure_of P /\
     (!U bb e' f. apx_bcap (top,atlas) g C eps U bb e' f
         ==> ~(z IN IMAGE (apx_bext bb e' f) (ball(vec 0,exp((&4 * inv ep) / sqrt(&2)))))) /\
     (!j. j IN J /\ ~(j = i)
         ==> DISJOINT (IMAGE ez (rfs_neck_dom ep)) (IMAGE (e j) (sphere(vec 0,&1))))
     ==> apx_gch (top,atlas) g C eps ep J e P i (b + &1)
           (\m. if m = b + &1 then z else x m) (\m. if m = b + &1 then ez else N m)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[apx_gch] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(&0:int = b + &1)` ASSUME_TAC THENL
   [UNDISCH_TAC `&0:int <= b` THEN INT_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `&0:int <= b` THEN INT_ARITH_TAC;
    X_GEN_TAC `m:int` THEN STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = `top closure_of (P:A->bool)`)) (concl th))) THEN
    UNDISCH_TAC `m:int <= b + &1` THEN UNDISCH_TAC `~(m:int = b + &1)` THEN
    UNDISCH_TAC `&0:int <= m` THEN INT_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`m:int`; `U:A->bool`; `bb:real^3->A`; `e':real^3->A`;
                         `f:real^3->real^3`] THEN
    STRIP_TAC THEN COND_CASES_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> t = `z:A`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_bext")) (concl th))) THEN
      EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> t = `x:int->A`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_bext")) (concl th))) THEN
      EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `m:int <= b + &1` THEN UNDISCH_TAC `~(m:int = b + &1)` THEN INT_ARITH_TAC];
    MAP_EVERY X_GEN_TAC [`m:int`; `j:num`] THEN STRIP_TAC THEN COND_CASES_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> t = `ez:real^3->A`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th))) THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> t = `N:int->real^3->A`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `m:int <= b + &1` THEN UNDISCH_TAC `~(m:int = b + &1)` THEN INT_ARITH_TAC]]);;

let APX_EXT_LAST_PAIR = prove
 (`!top atlas (g:A->real^3^3) ep b x (N:int->real^3->A) z ez.
     &0 <= b /\
     apx_balanced (top,atlas) g ep {m:int | &0 <= m /\ m <= b + &1}
       (\m. if m = b + &1 then z else x m) (\m. if m = b + &1 then ez else N m)
     ==> IMAGE (N b) (apx_slab (inv(&2 * ep)) (inv ep)) UNION
         IMAGE ez (apx_slab (--inv ep) (--inv(&2 * ep)))
         SUBSET IMAGE (N b) (rfs_neck_dom ep) INTER IMAGE ez (rfs_neck_dom ep) /\
         IMAGE (N b) (rfs_neck_dom ep) INTER IMAGE ez (rfs_neck_dom ep)
         SUBSET IMAGE (N b) (apx_slab (--inv(&2 * ep)) (inv ep)) INTER
                IMAGE ez (apx_slab (--inv ep) (inv(&2 * ep)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[apx_balanced; apx_chain; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT1)) THEN
  DISCH_THEN(MP_TAC o SPEC `b:int`) THEN
  REWRITE_TAC[INT_ARITH `~(b:int = b + &1)`] THEN
  ANTS_TAC THENL [UNDISCH_TAC `&0:int <= b` THEN INT_ARITH_TAC; SIMP_TAC[]]);;

let APX_RG_CASE_T = prove
 (`!top atlas (g:A->real^3^3) C eps dl ep J (e:num->real^3->A) P i b x N z
    U (bb:real^3->A) e' f.
     apx_rgc (top,atlas) g C eps dl ep J e P /\ i IN J /\
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
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_RG_CTX_SCALES) THEN
  APX_UNFOLD_ASM_TAC "apx_rgc" apx_rgc THEN
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

let APX_RG_CASE_S = prove
 (`!top atlas (g:A->real^3^3) C eps dl ep J (e:num->real^3->A) P i b x N z k yk.
     apx_rgc (top,atlas) g C eps dl ep J e P /\ i IN J /\
     apx_gch (top,atlas) g C eps ep J e P i b x N /\
     z IN top closure_of P /\
     ~(z IN apx_chain_union ep {m:int | &0 <= m /\ m <= b} N) /\
     z IN top closure_of (IMAGE (N b) (apx_slab (inv(&2 * ep)) (inv ep))) /\
     (!U bb e' f. apx_bcap (top,atlas) g C eps U bb e' f
         ==> ~(z IN IMAGE (apx_bext bb e' f) (ball(vec 0,exp((&4 * inv ep) / sqrt(&2)))))) /\
     k IN J /\ ~(k = i) /\ yk IN rfs_neck_dom dl /\ z = e k yk /\
     &0 <= apx_sval yk /\ apx_sval yk < &2 * inv ep
     ==> (apx_sval yk < inv ep /\
          apx_balanced (top,atlas) g ep {m:int | &0 <= m /\ m <= b + &1}
            (\m. if m = b + &1 then e k yk else x m)
            (\m. if m = b + &1 then apx_rev (apx_cp (e k) yk) else N m)) \/
         (?x' N'. apx_gch (top,atlas) g C eps ep J e P i (b + &1) x' N')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_RG_CTX_SCALES) THEN
  APX_UNFOLD_ASM_TAC "apx_rgc" apx_rgc THEN
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
  SUBGOAL_THEN `?yk0. rfs_neck (top,atlas) (g:A->real^3^3) dl yk0 ((e:num->real^3->A) k)`
  (X_CHOOSE_TAC `yk0:A`) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param top atlas (rfs_neck_dom dl) ((e:num->real^3->A) k)` ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  (* the copy of e_k at z is an ep-neck *)
  SUBGOAL_THEN `rfs_neck (top,atlas) (g:A->real^3^3) ep z (apx_cp ((e:num->real^3->A) k) yk)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APX_CP_NECK THEN
    MAP_EVERY EXISTS_TAC [`dl:real`; `yk0:A`] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC APX_KC_GE THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
     [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `apx_kc * eps = ep`)) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[APX_DIV34] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `ep:real`; `&0:int`; `b:int`; `x:int->A`; `N:int->real^3->A`; `z:A`;
                 `apx_cp ((e:num->real^3->A) k) yk`] APX_A18_CORE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ez':real^3->A` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`(e:num->real^3->A) k`; `yk:real^3`; `dl:real`] APX_CP_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `apx_sval(yk:real^3) < inv ep` THENL
   [DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ez' = apx_cp ((e:num->real^3->A) k) yk \/ ez' = apx_rev (apx_cp (e k) yk)` THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THENL
     [ALL_TAC;
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `z:A = e (k:num) (yk:real^3)`)) THEN
      FIRST_ASSUM ACCEPT_TAC] THEN
    MATCH_MP_TAC(TAUT `F ==> p`) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `ep:real`; `b:int`; `x:int->A`; `N:int->real^3->A`; `z:A`;
                   `apx_cp ((e:num->real^3->A) k) yk`] APX_EXT_LAST_PAIR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    (* a point of the inner side in N_b *)
    ABBREV_TAC `t = &3 / &4 * (apx_sval(yk:real^3) - inv ep)` THEN
    MP_TAC(SPECL [`t:real`; `&1`] APX_SVAL_SCALED_BASIS) THEN
    REWRITE_TAC[REAL_LT_01; VECTOR_MUL_LID; LOG_1; REAL_MUL_RZERO; REAL_ADD_RID] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(e:num->real^3->A) k (exp(t / sqrt(&2)) % basis 1) IN
                  IMAGE ((N:int->real^3->A) b) (rfs_neck_dom ep)` ASSUME_TAC THENL
     [SUBGOAL_THEN `(e:num->real^3->A) k (exp(t / sqrt(&2)) % basis 1) IN
                    IMAGE (apx_cp (e k) yk) (apx_slab (--inv ep) (--inv(&2 * ep)))` MP_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN
        MP_TAC(SPEC `ep:real` APX_INV_K) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        EXPAND_TAC "t" THEN ASM_REAL_ARITH_TAC;
        ASM SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(e:num->real^3->A) k (exp(t / sqrt(&2)) % basis 1) IN
                  IMAGE (e k) (apx_slab (--inv dl) (&0))` ASSUME_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN
      EXPAND_TAC "t" THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `C:real`; `eps:real`; `dl:real`; `J:num->bool`;
                   `e:num->real^3->A`; `P:A->bool`; `k:num`;
                   `IMAGE ((N:int->real^3->A) b) (rfs_neck_dom ep)`] APX_RG_SIDE) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
       [MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
        EXISTS_TAC `atlas:((A->bool)#(A->real^3))->bool` THEN
        EXISTS_TAC `rfs_neck_dom ep` THEN REWRITE_TAC[SUBSET_REFL] THEN
        CONJ_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
        REWRITE_TAC[APX_SLAB_NECK_DOM; apx_slab; APX_CONNECTED_ANNULUS3];
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th) &&
          can (find_term (fun t -> t = `N:int->real^3->A`)) (concl th))) THEN
        ASM_REWRITE_TAC[INT_LE_REFL];
        REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
        EXISTS_TAC `(x:int->A) b` THEN CONJ_TAC THENL
         [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) ep ((x:int->A) b) (N b)` THEN
          REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
          MP_TAC(SPEC `ep:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
          ASM SET_TAC[];
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[INT_LE_REFL]]];
      UNDISCH_TAC `(e:num->real^3->A) k (exp(t / sqrt(&2)) % basis 1) IN
                   IMAGE ((N:int->real^3->A) b) (rfs_neck_dom ep)` THEN
      UNDISCH_TAC `(e:num->real^3->A) k (exp(t / sqrt(&2)) % basis 1) IN
                   IMAGE (e k) (apx_slab (--inv dl) (&0))` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  (* the copy misses every other cut sphere: the chain grows *)
  DISJ2_TAC THEN
  MAP_EVERY EXISTS_TAC [`\m:int. if m = b + &1 then (z:A) else x m`;
                        `\m:int. if m = b + &1 then (ez':real^3->A) else N m`] THEN
  MATCH_MP_TAC APX_GCH_EXTEND THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `IMAGE (ez':real^3->A) (rfs_neck_dom ep) =
                IMAGE ((e:num->real^3->A) k)
                      (apx_slab (apx_sval(yk:real^3) - inv ep) (apx_sval yk + inv ep))`
  SUBST1_TAC THENL
   [UNDISCH_TAC `ez' = apx_cp ((e:num->real^3->A) k) yk \/ ez' = apx_rev (apx_cp (e k) yk)` THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN REWRITE_TAC[APX_REV_IMAGE_DOM] THEN
    ASM_REWRITE_TAC[APX_SLAB_NECK_DOM] THEN AP_TERM_TAC THEN BINOP_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  ASM_CASES_TAC `j:num = k` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ONCE_REWRITE_TAC[DISJOINT_SYM] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(e:num->real^3->A) k`; `dl:real`; `&0`;
                   `apx_sval(yk:real^3) - inv ep`; `apx_sval(yk:real^3) + inv ep`]
                  APX_LEVEL_SPHERE_DISJOINT) THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_EXP_0] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(SPEC `dl:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[APX_SLAB_NECK_DOM] THEN MATCH_MP_TAC APX_SLAB_SUBSET THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `j:num`] o check (fun th -> is_forall (concl th) &&
    can (find_term (fun t -> t = `&8 / ep`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(SET_RULE `(s:A->bool) SUBSET t ==> DISJOINT u t ==> DISJOINT s u`) THEN
  MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC APX_SLAB_SUBSET THEN
  REWRITE_TAC[real_div; REAL_MUL_LID] THEN ASM_REAL_ARITH_TAC);;

let APX_RG_CASE_N = prove
 (`!top atlas (g:A->real^3^3) C eps dl ep J (e:num->real^3->A) P i b x N z.
     apx_rgc (top,atlas) g C eps dl ep J e P /\ i IN J /\
     apx_gch (top,atlas) g C eps ep J e P i b x N /\
     z IN top closure_of P /\
     ~(z IN apx_chain_union ep {m:int | &0 <= m /\ m <= b} N) /\
     z IN top closure_of (IMAGE (N b) (apx_slab (inv(&2 * ep)) (inv ep))) /\
     (!U bb e' f. apx_bcap (top,atlas) g C eps U bb e' f
         ==> ~(z IN IMAGE (apx_bext bb e' f) (ball(vec 0,exp((&4 * inv ep) / sqrt(&2)))))) /\
     ~(?k yk. k IN J /\ ~(k = i) /\ yk IN rfs_neck_dom dl /\ z = e k yk /\
              &0 <= apx_sval yk /\ apx_sval yk < &2 * inv ep)
     ==> ?x' N'. apx_gch (top,atlas) g C eps ep J e P i (b + &1) x' N'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_RG_CTX_SCALES) THEN
  APX_UNFOLD_ASM_TAC "apx_rgc" apx_rgc THEN
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
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `dl:real`; `ep:real`; `J:num->bool`;
                 `e:num->real^3->A`; `P:A->bool`; `j:num`; `z:A`; `ez':real^3->A`]
                APX_RG_SPHERE_REACH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `~(?k yk. k IN J /\ ~(k = i) /\ yk IN rfs_neck_dom dl /\
                        z = (e:num->real^3->A) k yk /\
                        &0 <= apx_sval yk /\ apx_sval yk < &2 * inv ep)` THEN
  REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC [`j:num`; `y:real^3`] THEN ASM_REWRITE_TAC[]);;

let APX_RG_STEP = prove
 (`!top atlas (g:A->real^3^3) C eps dl ep J (e:num->real^3->A) P i b x N.
     apx_rgc (top,atlas) g C eps dl ep J e P /\ i IN J /\
     apx_gch (top,atlas) g C eps ep J e P i b x N /\
     ~(top closure_of P SUBSET apx_chain_union ep {m:int | &0 <= m /\ m <= b} N)
     ==> (?U bb e' f yz. apx_bcap (top,atlas) g C eps U bb e' f /\
            yz IN rfs_neck_dom eps /\ e' yz IN top closure_of P /\
            &0 < apx_sval yz /\ apx_sval yz < &4 * inv ep /\
            apx_balanced (top,atlas) g ep {m:int | &0 <= m /\ m <= b + &1}
              (\m. if m = b + &1 then e' yz else x m)
              (\m. if m = b + &1 then apx_rev (apx_cp e' yz) else N m)) \/
         (?k yk. k IN J /\ ~(k = i) /\ yk IN rfs_neck_dom dl /\
            &0 <= apx_sval yk /\ apx_sval yk < inv ep /\
            apx_balanced (top,atlas) g ep {m:int | &0 <= m /\ m <= b + &1}
              (\m. if m = b + &1 then e k yk else x m)
              (\m. if m = b + &1 then apx_rev (apx_cp (e k) yk) else N m)) \/
         (?x' N'. apx_gch (top,atlas) g C eps ep J e P i (b + &1) x' N')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL APX_RG_FRONTIER) THEN ASM_REWRITE_TAC[] THEN
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
                   `C:real`; `eps:real`; `dl:real`; `ep:real`; `J:num->bool`;
                   `e:num->real^3->A`; `P:A->bool`; `i:num`; `b:int`; `x:int->A`;
                   `N:int->real^3->A`; `z:A`; `U:A->bool`; `bb:real^3->A`;
                   `e':real^3->A`; `f:real^3->real^3`] APX_RG_CASE_T) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `yz:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `yz:real^3` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(z:A) IN top closure_of P` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!U bb e' f. apx_bcap (top,atlas) (g:A->real^3^3) C eps U bb e' f
                            ==> ~((z:A) IN IMAGE (apx_bext bb e' f)
                                    (ball(vec 0,exp((&4 * inv ep) / sqrt(&2)))))`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `?k yk. k IN J /\ ~(k = i) /\ yk IN rfs_neck_dom dl /\
                        (z:A) = (e:num->real^3->A) k yk /\
                        &0 <= apx_sval yk /\ apx_sval yk < &2 * inv ep` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `yk:real^3` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `C:real`; `eps:real`; `dl:real`; `ep:real`; `J:num->bool`;
                   `e:num->real^3->A`; `P:A->bool`; `i:num`; `b:int`; `x:int->A`;
                   `N:int->real^3->A`; `z:A`; `k:num`; `yk:real^3`] APX_RG_CASE_S) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN2 STRIP_ASSUME_TAC ASSUME_TAC) THENL
     [DISJ2_TAC THEN DISJ1_TAC THEN
      MAP_EVERY EXISTS_TAC [`k:num`; `yk:real^3`] THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN DISJ2_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  DISJ2_TAC THEN DISJ2_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `dl:real`; `ep:real`; `J:num->bool`;
                 `e:num->real^3->A`; `P:A->bool`; `i:num`; `b:int`; `x:int->A`;
                 `N:int->real^3->A`; `z:A`] APX_RG_CASE_N) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The region growth, part 3.  The growth induction with the                 *)
(* card bound (a stopped chain exists), and helpers for the final charts:    *)
(* closures of slab images of a tube, the clopen argument, the A13 tube of a *)
(* stopped chain, and the end formula of a reversed copy.                    *)
(* ------------------------------------------------------------------------- *)

let APX_RG_GROW = prove
 (`!top atlas (g:A->real^3^3) C eps dl ep J (e:num->real^3->A) P i.
     apx_rgc (top,atlas) g C eps dl ep J e P /\ apx_a13_ctx top atlas g ep /\ i IN J
     ==> ?b x N. apx_gch (top,atlas) g C eps ep J e P i b x N /\
                 ((?U bb e' f yz. apx_bcap (top,atlas) g C eps U bb e' f /\
                     yz IN rfs_neck_dom eps /\ e' yz IN top closure_of P /\
                     &0 < apx_sval yz /\
                     apx_sval yz < &4 * inv ep /\
                     apx_balanced (top,atlas) g ep {m:int | &0 <= m /\ m <= b + &1}
                       (\m. if m = b + &1 then e' yz else x m)
                       (\m. if m = b + &1 then apx_rev (apx_cp e' yz) else N m)) \/
                  (?k yk. k IN J /\ ~(k = i) /\ yk IN rfs_neck_dom dl /\
                     &0 <= apx_sval yk /\ apx_sval yk < inv ep /\
                     apx_balanced (top,atlas) g ep {m:int | &0 <= m /\ m <= b + &1}
                       (\m. if m = b + &1 then e k yk else x m)
                       (\m. if m = b + &1 then apx_rev (apx_cp (e k) yk) else N m)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `apx_ch_ctx top atlas (g:A->real^3^3) ep /\
                compact_in top (top closure_of (P:A->bool))` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `apx_rgc (top,atlas) (g:A->real^3^3) C eps dl ep J (e:num->real^3->A) P` THEN
    REWRITE_TAC[apx_rgc; apx_rg] THEN SIMP_TAC[];
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
                     `g:A->real^3^3`; `C:real`; `eps:real`; `dl:real`; `ep:real`;
                     `J:num->bool`; `e:num->real^3->A`; `P:A->bool`; `i:num`] APX_RG_INIT) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `x:int->A` (X_CHOOSE_TAC `N:int->real^3->A`)) THEN
      MAP_EVERY EXISTS_TAC [`&0:int`; `x:int->A`; `N:int->real^3->A`] THEN
      ASM_REWRITE_TAC[LE_0];
      ALL_TAC] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `b:int` (X_CHOOSE_THEN `x:int->A`
      (X_CHOOSE_THEN `N:int->real^3->A` STRIP_ASSUME_TAC))) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `C:real`; `eps:real`; `dl:real`; `ep:real`;
                   `J:num->bool`; `e:num->real^3->A`; `P:A->bool`; `i:num`; `b:int`;
                   `x:int->A`; `N:int->real^3->A`] APX_RG_NOT_COVERED) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `C:real`; `eps:real`; `dl:real`; `ep:real`;
                   `J:num->bool`; `e:num->real^3->A`; `P:A->bool`; `i:num`; `b:int`;
                   `x:int->A`; `N:int->real^3->A`] APX_RG_STEP) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN2 ASSUME_TAC MP_TAC)) THENL
     [USE_THEN "ns" MP_TAC THEN MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
      MAP_EVERY EXISTS_TAC [`b:int`; `x:int->A`; `N:int->real^3->A`] THEN
      ASM_REWRITE_TAC[];
      USE_THEN "ns" MP_TAC THEN MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
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

let APX_PARAM_SLAB_CLOSURE = prove
 (`!top atlas (E:real^3->A) a0 b0 a b.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     mfd_param top atlas (apx_slab a0 b0) E /\ a0 < a /\ b < b0
     ==> top closure_of (IMAGE E (apx_slab a b)) SUBSET
         IMAGE E {y | ~(y = vec 0) /\ a <= apx_sval y /\ apx_sval y <= b}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `apx_slab a0 b0`; `E:real^3->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ei:A->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`a:real`; `b:real`] APX_CSLAB) THEN STRIP_TAC THEN
  SUBGOAL_THEN `{y:real^3 | ~(y = vec 0) /\ a <= apx_sval y /\ apx_sval y <= b} =
                cball(vec 0,exp(b / sqrt(&2))) DIFF ball(vec 0,exp(a / sqrt(&2)))`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `cball(vec 0:real^3,exp(b / sqrt(&2))) DIFF ball(vec 0,exp(a / sqrt(&2)))
                SUBSET apx_slab a0 b0` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; APX_SLAB_SVAL] THEN X_GEN_TAC `y:real^3` THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN CONJ_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; APX_SLAB_SVAL] THEN
    ASM_REWRITE_TAC[] THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC IMAGE_COMPACT_IN THEN
  EXISTS_TAC `subtopology euclidean (apx_slab a0 b0)` THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN]);;

let APX_CONNECTED_CLOPEN_EQ = prove
 (`!top (P:A->bool) Q.
     connected_in top P /\ Q SUBSET P /\ open_in top Q /\ ~(Q = {}) /\
     P INTER top closure_of Q SUBSET Q
     ==> Q = P`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[CONNECTED_IN] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "connected_in")) (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`Q:A->bool`; `topspace top DIFF top closure_of (Q:A->bool)`]) THEN
  SUBGOAL_THEN `(Q:A->bool) SUBSET top closure_of Q /\ Q SUBSET topspace top`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_SIMP_TAC[OPEN_IN_SUBSET];
      ASM_SIMP_TAC[OPEN_IN_SUBSET]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_TOPSPACE; CLOSED_IN_CLOSURE_OF] THEN
  ASM SET_TAC[]);;

let APX_STOP_TUBE = prove
 (`!top atlas (g:A->real^3^3) ep b x (N:int->real^3->A).
     apx_a13_ctx top atlas g ep /\ &0 <= b /\
     apx_balanced (top,atlas) g ep {m:int | &0 <= m /\ m <= b + &1} x N
     ==> ?E L f f'. &0 <= L /\ sphere_diffeo f f' /\
           mfd_param top atlas (apx_slab (--inv ep) (L + inv ep)) E /\
           (!y. y IN apx_slab (--inv ep) (inv(&8 * ep)) ==> E y = N (&0) y) /\
           (!y. y IN apx_slab (L - inv(&8 * ep)) (L + inv ep)
                ==> E y = N (b + &1) (radial_ext f (exp(--L / sqrt(&2)) % y))) /\
           IMAGE E (apx_slab (--inv ep) (L + inv ep)) =
           apx_chain_union ep {m:int | &0 <= m /\ m <= b + &1} N`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(snd(EQ_IMP_RULE(SPEC `b + &1:int` INT_OF_NUM_EXISTS))) THEN
  ANTS_TAC THENL [UNDISCH_TAC `&0:int <= b` THEN INT_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (fun th -> REWRITE_TAC[th] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[th]))) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `x:int->A`; `N:int->real^3->A`] o
    REWRITE_RULE[apx_a13_ctx] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_a13_ctx")) (concl th))) THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[apx_balanced] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_balanced")) (concl th))) THEN
    SIMP_TAC[];
    SIMP_TAC[]]);;

let APX_REV_CP_RADIAL = prove
 (`!(e1:real^3->A) y1 (f:real^3->real^3) L y.
     (!w. w IN sphere(vec 0,&1) ==> f w IN sphere(vec 0,&1)) /\ ~(y = vec 0)
     ==> apx_rev (apx_cp e1 y1) (radial_ext f (exp(--L / sqrt(&2)) % y)) =
         e1 ((norm y1 * exp(L / sqrt(&2)) / norm y) % f(inv(norm y) % y))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < exp(--L / sqrt(&2)) /\ &0 < norm(y:real^3)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_EXP_POS_LT; NORM_POS_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[SMT_RADIAL_EXT_HOMOG] THEN
  SUBGOAL_THEN `norm((f:real^3->real^3)(inv(norm y) % y)) = &1` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IN_SPHERE_0] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  REWRITE_TAC[apx_rev; apx_cp; radial_ext; o_THM] THEN
  ABBREV_TAC `w = (f:real^3->real^3)(inv(norm y) % y)` THEN
  SUBGOAL_THEN `exp(L / sqrt(&2)) = inv(exp(--L / sqrt(&2)))` SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_LNEG; REAL_EXP_NEG; REAL_INV_INV]; ALL_TAC] THEN
  ABBREV_TAC `c = exp(--L / sqrt(&2))` THEN
  AP_TERM_TAC THEN
  ASM_REWRITE_TAC[NORM_MUL; REAL_ABS_NORM; VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < c ==> abs c = c`] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `~(c = &0) /\ ~(norm(y:real^3) = &0)` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]);;

(* ------------------------------------------------------------------------- *)
(* The region growth, part 4.  The tube of a stopped chain                   *)
(* whose last neck is a reversed copy, with the end formula; images of      *)
(* disjoint sets under a parametrization; closed slabs as slab plus two     *)
(* spheres; the end sphere of the tube is the copied neck's sphere.         *)
(* ------------------------------------------------------------------------- *)

let APX_STOP_TUBE_REV = prove
 (`!top atlas (g:A->real^3^3) ep b x (N:int->real^3->A) z (e1:real^3->A) y1.
     apx_a13_ctx top atlas g ep /\ &0 <= b /\
     apx_balanced (top,atlas) g ep {m:int | &0 <= m /\ m <= b + &1}
       (\m. if m = b + &1 then z else x m)
       (\m. if m = b + &1 then apx_rev (apx_cp e1 y1) else N m)
     ==> ?E L f f'. &0 <= L /\ sphere_diffeo f f' /\
           mfd_param top atlas (apx_slab (--inv ep) (L + inv ep)) E /\
           (!y. y IN apx_slab (--inv ep) (inv(&8 * ep)) ==> E y = N (&0) y) /\
           (!y. y IN apx_slab (L - inv(&8 * ep)) (L + inv ep)
                ==> E y = e1 ((norm y1 * exp(L / sqrt(&2)) / norm y) %
                              f(inv(norm y) % y))) /\
           IMAGE E (apx_slab (--inv ep) (L + inv ep)) =
           apx_chain_union ep {m:int | &0 <= m /\ m <= b + &1}
             (\m. if m = b + &1 then apx_rev (apx_cp e1 y1) else N m)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `ep:real`; `b:int`; `\m:int. if m = b + &1 then (z:A) else x m`;
                 `\m:int. if m = b + &1 then apx_rev (apx_cp (e1:real^3->A) y1) else N m`]
                APX_STOP_TUBE) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(&0:int = b + &1)` (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `&0:int <= b` THEN INT_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `E:real^3->A` (X_CHOOSE_THEN `L:real`
    (X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `f':real^3->real^3`
     STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`E:real^3->A`; `L:real`; `f:real^3->real^3`; `f':real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  FIRST_X_ASSUM((fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
    `(y:real^3) IN apx_slab (L - inv(&8 * ep)) (L + inv ep)`)]) o check (fun th ->
    is_forall (concl th) && can (find_term (fun t -> t = `radial_ext (f:real^3->real^3)`))
      (concl th))) THEN
  MATCH_MP_TAC APX_REV_CP_RADIAL THEN CONJ_TAC THENL
   [UNDISCH_TAC `sphere_diffeo (f:real^3->real^3) f'` THEN SIMP_TAC[sphere_diffeo];
    UNDISCH_TAC `(y:real^3) IN apx_slab (L - inv(&8 * ep)) (L + inv ep)` THEN
    SIMP_TAC[APX_SLAB_SVAL]]);;

let APX_PARAM_IMAGE_DISJOINT = prove
 (`!top atlas s (e:real^3->A) a b.
     mfd_param top atlas s e /\ a SUBSET s /\ b SUBSET s /\ DISJOINT a b
     ==> DISJOINT (IMAGE e a) (IMAGE e b)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
  X_GEN_TAC `q:A` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `u:real^3 = v` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_INJ THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `s:real^3->bool`; `e:real^3->A`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ASM SET_TAC[]]);;

let APX_CSLAB_SPLIT = prove
 (`!a b. a <= b
         ==> {y:real^3 | ~(y = vec 0) /\ a <= apx_sval y /\ apx_sval y <= b} =
             apx_slab a b UNION sphere(vec 0,exp(a / sqrt(&2))) UNION
             sphere(vec 0,exp(b / sqrt(&2)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[APX_SPHERE_LEVEL; EXTENSION; IN_UNION; IN_ELIM_THM; APX_SLAB_SVAL] THEN
  X_GEN_TAC `y:real^3` THEN ASM_CASES_TAC `y:real^3 = vec 0` THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

let APX_EXP_HALF_GE2 = prove
 (`!t. &2 <= t ==> &2 <= exp(t / sqrt(&2))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&1 + t / sqrt(&2)` THEN REWRITE_TAC[REAL_EXP_LE_X] THEN
  SUBGOAL_THEN `&1 <= t / sqrt(&2)` (fun th -> MP_TAC th THEN REAL_ARITH_TAC) THEN
  SUBGOAL_THEN `&0 < sqrt(&2) /\ sqrt(&2) <= &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LSQRT THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC]);;

let APX_END_SPHERE_IMAGE = prove
 (`!(E:real^3->A) (e1:real^3->A) f f' c a b.
     sphere_diffeo f f' /\ &0 < c /\ sphere(vec 0,c) SUBSET apx_slab a b /\
     (!y. y IN apx_slab a b ==> E y = e1((c / norm y) % f(inv(norm y) % y)))
     ==> IMAGE E (sphere(vec 0,c)) = IMAGE e1 (sphere(vec 0,&1))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[sphere_diffeo] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "sphere_diffeo")) (concl th))) THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN X_GEN_TAC `q:A` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(y:real^3) IN apx_slab a b` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `norm(y:real^3) = c` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN sphere(vec 0,c)` THEN SIMP_TAC[IN_SPHERE_0]; ALL_TAC] THEN
    SUBGOAL_THEN `inv(norm y) % (y:real^3) IN sphere(vec 0,&1)` ASSUME_TAC THENL
     [REWRITE_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ];
      ALL_TAC] THEN
    EXISTS_TAC `(f:real^3->real^3)(inv(norm y) % y)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
    ASM_SIMP_TAC[] THEN ASM_SIMP_TAC[REAL_DIV_REFL; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `c % (f':real^3->real^3) w` THEN
  SUBGOAL_THEN `norm((f':real^3->real^3) w) = &1` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IN_SPHERE_0] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `c % (f':real^3->real^3) w IN sphere(vec 0,c)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_SPHERE_0; NORM_MUL; REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `c % (f':real^3->real^3) w IN apx_slab a b` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(c % (f':real^3->real^3) w) = c` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_MUL; REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[] THEN
  ASM_SIMP_TAC[REAL_DIV_REFL; REAL_LT_IMP_NZ; VECTOR_MUL_LID; VECTOR_MUL_ASSOC;
               REAL_MUL_LINV]);;

(* ------------------------------------------------------------------------- *)
(* The sphere stop.  A stopped chain whose last neck is the                  *)
(* reversed copy of the surgery neck e_k (k <> i, copy level in [0, 1/ep))  *)
(* gives the REGION product chart: E = e_i on annulus(1,3/2), E =           *)
(* e_k((L/|x|) f(x/|x|)) on annulus(L/2,L), J = {i,k} and P = E(annulus).   *)
(* The tube image misses every cut sphere (injectivity at the two ends, the *)
(* growth invariant and no close pairs elsewhere), so it lies in P; its      *)
(* closure adds only S_i and S_k, so it is all of P (clopen).               *)
(* ------------------------------------------------------------------------- *)

let APX_RG_SPHERE_FINAL = prove
 (`!top atlas (g:A->real^3^3) C eps dl ep J (e:num->real^3->A) P i b x N k yk.
     apx_rgc (top,atlas) g C eps dl ep J e P /\ apx_a13_ctx top atlas g ep /\ i IN J /\
     apx_gch (top,atlas) g C eps ep J e P i b x N /\
     k IN J /\ ~(k = i) /\ yk IN rfs_neck_dom dl /\
     &0 <= apx_sval yk /\ apx_sval yk < inv ep /\
     apx_balanced (top,atlas) g ep {m:int | &0 <= m /\ m <= b + &1}
       (\m. if m = b + &1 then e k yk else x m)
       (\m. if m = b + &1 then apx_rev (apx_cp (e k) yk) else N m)
     ==> ?E L f f'. &1 < L /\ sphere_diffeo f f' /\
           mfd_param top atlas (annulus (&1) L) E /\
           (!x. x IN annulus (&1) (&3 / &2) ==> E x = e i x) /\
           (!x. x IN annulus (L / &2) L
                ==> E x = e k ((L / norm x) % f(inv(norm x) % x))) /\
           J = {i,k} /\ P = IMAGE E (annulus (&1) L)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_RG_CTX_SCALES) THEN
  SUBGOAL_THEN `apx_rg (top,atlas) (g:A->real^3^3) C eps dl J (e:num->real^3->A) P`
  ASSUME_TAC THENL
   [UNDISCH_TAC `apx_rgc (top,atlas) (g:A->real^3^3) C eps dl ep J (e:num->real^3->A) P` THEN
    SIMP_TAC[apx_rgc];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_RG_BASICS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_RG_PARTS) THEN
  APX_UNFOLD_ASM_TAC "apx_rgc" apx_rgc THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[apx_rg] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_rg")) (concl th))) THEN
  APX_UNFOLD_ASM_TAC "apx_gch" apx_gch THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `ep:real`; `b:int`; `x:int->A`; `N:int->real^3->A`;
                 `(e:num->real^3->A) k yk`; `(e:num->real^3->A) k`; `yk:real^3`]
                APX_STOP_TUBE_REV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `E:real^3->A` (X_CHOOSE_THEN `L0:real`
    (X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `f':real^3->real^3`
     STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`(e:num->real^3->A) k`; `yk:real^3`; `dl:real`] APX_CP_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `LR = norm(yk:real^3) * exp(L0 / sqrt(&2))` THEN
  SUBGOAL_THEN `LR = exp((L0 + apx_sval(yk:real^3)) / sqrt(&2))` ASSUME_TAC THENL
   [SUBGOAL_THEN `exp((L0 + apx_sval(yk:real^3)) / sqrt(&2)) =
                  exp(L0 / sqrt(&2)) * exp(apx_sval yk / sqrt(&2))` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_EXP_ADD; real_div; REAL_ADD_RDISTRIB]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "LR" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv ep /\ &128 <= inv(&8 * ep) /\ &1 <= norm(yk:real^3) /\
                &1 <= exp(L0 / sqrt(&2)) /\ &0 < sqrt(&2)` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `ep:real` APX_INV_K) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
     [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check
        (let tq1 = `exp(apx_sval(yk:real^3) / sqrt(&2)) = norm yk` in fun th ->
        concl th = tq1)) THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 <= exp(inv(&8 * ep) / sqrt(&2)) /\ exp(--inv ep / sqrt(&2)) < &1`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC APX_EXP_HALF_GE2 THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LT] THEN
      REWRITE_TAC[real_div; REAL_MUL_LNEG; REAL_NEG_LT0] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV]];
    ALL_TAC] THEN
  SUBGOAL_THEN `annulus (&1) (&3 / &2) SUBSET apx_slab (--inv ep) (inv(&8 * ep)) /\
                sphere(vec 0:real^3,&1) SUBSET apx_slab (--inv ep) (inv(&8 * ep))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[apx_slab; SUBSET; annulus; IN_ELIM_THM; IN_SPHERE_0] THEN
    CONJ_TAC THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * exp((L0 - inv(&8 * ep)) / sqrt(&2)) <= LR /\
                LR < exp((L0 + inv ep) / sqrt(&2))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `exp(L0 / sqrt(&2)) =
                    exp((L0 - inv(&8 * ep)) / sqrt(&2)) * exp(inv(&8 * ep) / sqrt(&2))`
      ASSUME_TAC THENL
       [REWRITE_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN
        UNDISCH_TAC `&0 < sqrt(&2)` THEN CONV_TAC REAL_FIELD;
        ALL_TAC] THEN
      EXPAND_TAC "LR" THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(L0 / sqrt(&2))` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM SUBST1_TAC THEN GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE];
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE]];
      FIRST_ASSUM(SUBST1_TAC o check (let tq1 = `LR = exp((L0 + apx_sval(yk:real^3)) / sqrt(&2))` in
          fun th ->
        concl th = tq1)) THEN
      REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_SIMP_TAC[REAL_LT_DIV2_EQ] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < LR` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o check (let tq1 = `LR = exp((L0 + apx_sval(yk:real^3)) / sqrt(&2))` in
       fun th ->
      concl th = tq1)) THEN
    REWRITE_TAC[REAL_EXP_POS_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `annulus (LR / &2) LR SUBSET apx_slab (L0 - inv(&8 * ep)) (L0 + inv ep) /\
                sphere(vec 0:real^3,LR) SUBSET apx_slab (L0 - inv(&8 * ep)) (L0 + inv ep)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `(L0 - inv(&8 * ep)) / sqrt(&2)` REAL_EXP_POS_LT) THEN DISCH_TAC THEN
    REWRITE_TAC[apx_slab; SUBSET; annulus; IN_ELIM_THM; IN_SPHERE_0] THEN
    CONJ_TAC THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN apx_slab (L0 - inv(&8 * ep)) (L0 + inv ep)
                    ==> (E:real^3->A) y = (e:num->real^3->A) k
                                            ((LR / norm y) % (f:real^3->real^3)(inv(norm y) % y))`
  (LABEL_TAC "end") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN EXPAND_TAC "LR" THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME
      `(y:real^3) IN apx_slab (L0 - inv(&8 * ep)) (L0 + inv ep)`) o check
        (let tq1 = `norm(yk:real^3)` and tq2 = `E:real^3->A` in fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = tq1)) (concl th) &&
      can (find_term (fun t -> t = tq2)) (concl th))) THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `annulus (&1) LR = apx_slab (&0) (L0 + apx_sval(yk:real^3)) /\
                apx_slab (&0) (L0 + apx_sval yk) SUBSET apx_slab (--inv ep) (L0 + inv ep)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_REWRITE_TAC[apx_slab; real_div; REAL_MUL_LZERO; REAL_EXP_0];
      MATCH_MP_TAC APX_SLAB_SUBSET THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (E:real^3->A) (sphere(vec 0,&1)) =
                IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1)) /\
                IMAGE (E:real^3->A) (sphere(vec 0,LR)) = IMAGE (e k) (sphere(vec 0,&1))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_EQ THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
      MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(N:int->real^3->A) (&0) w` THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN UNDISCH_TAC `(w:real^3) IN sphere(vec 0,&1)` THEN
      UNDISCH_TAC `sphere(vec 0:real^3,&1) SUBSET apx_slab (--inv ep) (inv(&8 * ep))` THEN
      SET_TAC[];
      MATCH_MP_TAC APX_END_SPHERE_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`f:real^3->real^3`; `f':real^3->real^3`;
                            `L0 - inv(&8 * ep)`; `L0 + inv ep`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `annulus (&1) LR SUBSET apx_slab (--inv ep) (L0 + inv ep) /\
                sphere(vec 0:real^3,&1) SUBSET apx_slab (--inv ep) (L0 + inv ep) /\
                sphere(vec 0:real^3,LR) SUBSET apx_slab (--inv ep) (L0 + inv ep)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `ep:real` APX_INV_K) THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `apx_slab (--inv ep) (inv(&8 * ep))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APX_SLAB_SUBSET THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `apx_slab (L0 - inv(&8 * ep)) (L0 + inv ep)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APX_SLAB_SUBSET THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 < LR` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&1 <= x /\ ~(x = &1) ==> &1 < x`) THEN CONJ_TAC THENL
     [EXPAND_TAC "LR" THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
      DISCH_TAC THEN
      SUBGOAL_THEN `IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1)) =
                    IMAGE (e k) (sphere(vec 0,&1))` MP_TAC THENL
       [UNDISCH_TAC `IMAGE (E:real^3->A) (sphere(vec 0,&1)) =
                     IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1))` THEN
        UNDISCH_TAC `IMAGE (E:real^3->A) (sphere(vec 0,LR)) =
                     IMAGE ((e:num->real^3->A) k) (sphere(vec 0,&1))` THEN
        FIRST_X_ASSUM(SUBST1_TAC o check (let tq1 = `LR = &1` in fun th -> concl th = tq1)) THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC;
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `k:num`] o check
        (let tq1 = `annulus (&1 / &2) (&2):real^3->bool` in fun th ->
        is_forall (concl th) &&
        can (find_term (fun t -> t = tq1)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `sphere(vec 0:real^3,&1) SUBSET annulus (&1 / &2) (&2)` MP_TAC THENL
       [REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `basis 1:real^3 IN sphere(vec 0,&1)` MP_TAC THENL
       [SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH]; ALL_TAC] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `Q = IMAGE (E:real^3->A) (annulus (&1) LR)` THEN
  SUBGOAL_THEN `DISJOINT (Q:A->bool) (IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1))) /\
                DISJOINT Q (IMAGE (e k) (sphere(vec 0,&1)))` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN
    REWRITE_TAC[GSYM(ASSUME `IMAGE (E:real^3->A) (sphere(vec 0,&1)) =
                             IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1))`);
                GSYM(ASSUME `IMAGE (E:real^3->A) (sphere(vec 0,LR)) =
                             IMAGE ((e:num->real^3->A) k) (sphere(vec 0,&1))`)] THEN
    CONJ_TAC THEN MATCH_MP_TAC APX_PARAM_IMAGE_DISJOINT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `apx_slab (--inv ep) (L0 + inv ep)`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; annulus; IN_SPHERE_0;
                IN_ELIM_THM] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!j. j IN J /\ ~(j = i) /\ ~(j = k)
                    ==> DISJOINT (Q:A->bool) (IMAGE ((e:num->real^3->A) j) (sphere(vec 0,&1)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(Q:A->bool) SUBSET IMAGE (E:real^3->A) (apx_slab (--inv ep) (L0 + inv ep))`
    MP_TAC THENL
     [EXPAND_TAC "Q" THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_eq(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_chain_union"))
          (concl th))) THEN
    REWRITE_TAC[apx_chain_union; SUBSET; IN_UNIONS; IN_ELIM_THM] THEN DISCH_TAC THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    X_GEN_TAC `q:A` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `q:A`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:A->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `m:int` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    UNDISCH_TAC `(q:A) IN t` THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THENL
     [ASM_REWRITE_TAC[APX_SLAB_NECK_DOM] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `j:num`] o check (let tq1 = `&8 / ep` in fun th ->
        is_forall (concl th) && can (find_term (fun t -> t = tq1)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `apx_slab (apx_sval(yk:real^3) - inv ep) (apx_sval yk - --inv ep) SUBSET
                    apx_slab (--(&8 / ep)) (&8 / ep)` MP_TAC THENL
       [MATCH_MP_TAC APX_SLAB_SUBSET THEN REWRITE_TAC[real_div; REAL_MUL_LID] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      UNDISCH_TAC `(q:A) IN IMAGE ((e:num->real^3->A) k)
                     (apx_slab (apx_sval(yk:real^3) - inv ep) (apx_sval yk - --inv ep))` THEN
      UNDISCH_TAC `(q:A) IN IMAGE ((e:num->real^3->A) j) (sphere(vec 0,&1))` THEN
      SET_TAC[];
      DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`m:int`; `j:num`] o check (let tq1 = `N:int->real^3->A` in
          fun th ->
        is_forall (concl th) && can (find_term (fun t -> t = tq1)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th))) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `m:int <= b + &1` THEN UNDISCH_TAC `~(m:int = b + &1)` THEN INT_ARITH_TAC;
        ALL_TAC] THEN
      UNDISCH_TAC `(q:A) IN IMAGE ((N:int->real^3->A) m) (rfs_neck_dom ep)` THEN
      UNDISCH_TAC `(q:A) IN IMAGE ((e:num->real^3->A) j) (sphere(vec 0,&1))` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?r0. &1 < r0 /\ r0 < &3 / &2 /\ r0 < LR` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `(&1 + min LR (&3 / &2)) / &2` THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(E:real^3->A) (r0 % basis 1) IN Q /\ (E:real^3->A) (r0 % basis 1) IN P`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `r0 % basis 1:real^3 IN annulus (&1) LR /\
                  r0 % basis 1:real^3 IN annulus (&1) (&3 / &2)` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[annulus; IN_ELIM_THM; NORM_MUL] THEN
      SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "Q" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(E:real^3->A) (r0 % basis 1) = (e:num->real^3->A) i (r0 % basis 1)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(N:int->real^3->A) (&0) (r0 % basis 1)` THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN
        UNDISCH_TAC `r0 % basis 1:real^3 IN annulus (&1) (&3 / &2)` THEN
        UNDISCH_TAC `annulus (&1) (&3 / &2) SUBSET apx_slab (--inv ep) (inv(&8 * ep))` THEN
        SET_TAC[];
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(i:num) IN J`) o check
      (let tq1 = `annulus (&1) (&2):real^3->bool` and tq2 = `P:A->bool` in fun th ->
      is_forall (concl th) &&
      can (find_term (fun t -> t = tq1)) (concl th) &&
      can (find_term (fun t -> t = tq2)) (concl th))) THEN
    MATCH_MP_TAC(SET_RULE `(x:A) IN B ==> P INTER A = B ==> x IN P`) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[annulus; IN_ELIM_THM; NORM_MUL] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(Q:A->bool) SUBSET P` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "connected_in")) (concl th))) THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "Q" THEN MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`;
                            `apx_slab (--inv ep) (L0 + inv ep)`] THEN
      ASM_REWRITE_TAC[APX_CONNECTED_ANNULUS3];
      REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `(E:real^3->A) (r0 % basis 1)` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      ASM_CASES_TAC `j:num = i` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_CASES_TAC `j:num = k` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `top closure_of (Q:A->bool) SUBSET
                Q UNION IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1)) UNION
                IMAGE (e k) (sphere(vec 0,&1))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `E:real^3->A`;
                   `--inv ep`; `L0 + inv ep`; `&0`; `L0 + apx_sval(yk:real^3)`]
                  APX_PARAM_SLAB_CLOSURE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`&0`; `L0 + apx_sval(yk:real^3)`] APX_CSLAB_SPLIT) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `&0 / sqrt(&2) = &0` SUBST1_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_LZERO]; ALL_TAC] THEN
    REWRITE_TAC[REAL_EXP_0; IMAGE_UNION] THEN
    REWRITE_TAC[GSYM(ASSUME `LR = exp((L0 + apx_sval(yk:real^3)) / sqrt(&2))`);
                GSYM(ASSUME `annulus (&1) LR = apx_slab (&0) (L0 + apx_sval(yk:real^3))`)] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `Q:A->bool = P` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_CONNECTED_CLOPEN_EQ THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "Q" THEN MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`;
                            `apx_slab (--inv ep) (L0 + inv ep)`] THEN
      ASM_REWRITE_TAC[OPEN_ANNULUS];
      UNDISCH_TAC `(E:real^3->A) (r0 % basis 1) IN Q` THEN SET_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `P INTER (Q UNION IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1)) UNION
                           IMAGE (e k) (sphere(vec 0,&1)))` THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `top closure_of (Q:A->bool) SUBSET
                     Q UNION IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1)) UNION
                     IMAGE (e k) (sphere(vec 0,&1))` THEN
        SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `DISJOINT (P:A->bool) (IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1))) /\
                    DISJOINT P (IMAGE (e k) (sphere(vec 0,&1)))` MP_TAC THENL
       [CONJ_TAC THENL
         [FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(i:num) IN J`) o check (fun th ->
            is_forall (concl th) &&
            can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_neck_chart"))
                (concl th))) THEN SIMP_TAC[];
          FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(k:num) IN J`) o check (fun th ->
            is_forall (concl th) &&
            can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_neck_chart"))
                (concl th))) THEN SIMP_TAC[]];
        SET_TAC[]]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`E:real^3->A`; `LR:real`; `f:real^3->real^3`; `f':real^3->real^3`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `apx_slab (--inv ep) (L0 + inv ep)` THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN REWRITE_TAC[OPEN_ANNULUS];
    X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(N:int->real^3->A) (&0) w` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN UNDISCH_TAC `(w:real^3) IN annulus (&1) (&3 / &2)` THEN
  UNDISCH_TAC `annulus (&1) (&3 / &2) SUBSET apx_slab (--inv ep) (inv(&8 * ep))` THEN SET_TAC[];
    X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN USE_THEN "end" MATCH_MP_TAC THEN
  UNDISCH_TAC `(w:real^3) IN annulus (LR / &2) LR` THEN
  UNDISCH_TAC `annulus (LR / &2) LR SUBSET apx_slab (L0 - inv(&8 * ep)) (L0 + inv ep)` THEN
  SET_TAC[];
    REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN X_GEN_TAC `j:num` THEN
  EQ_TAC THENL [ALL_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
  DISCH_TAC THEN ASM_CASES_TAC `j:num = i` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `j:num = k` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(e:num->real^3->A) j (basis 1) IN IMAGE (e j) (sphere(vec 0,&1)) /\
                basis 1:real^3 IN sphere(vec 0,&1)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `q /\ (q ==> p) ==> p /\ q`) THEN CONJ_TAC THENL
     [SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH]; SIMP_TAC[FUN_IN_IMAGE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e:num->real^3->A) j (basis 1) IN top closure_of P` MP_TAC THENL
   [FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (let tq1 = `top closure_of (P:A->bool)` in
       fun th -> is_eq(concl th) &&
      lhs(concl th) = tq1)) THEN
    REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN DISJ2_TAC THEN
    EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o check (let tq1 = `Q:A->bool = P` in fun th -> concl th = tq1)) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `DISJOINT (Q:A->bool) (IMAGE ((e:num->real^3->A) j) (sphere(vec 0,&1)))`
  MP_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `sphere(vec 0:real^3,&1) SUBSET annulus (&1 / &2) (&2)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (IMAGE ((e:num->real^3->A) j) (annulus (&1 / &2) (&2)))
                         (IMAGE (e i) (annulus (&1 / &2) (&2))) /\
                DISJOINT (IMAGE ((e:num->real^3->A) j) (annulus (&1 / &2) (&2)))
                         (IMAGE (e k) (annulus (&1 / &2) (&2)))` MP_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check
     (let tq1 = `annulus (&1 / &2) (&2):real^3->bool` in fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = tq1)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `top closure_of Q SUBSET
               Q UNION IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1)) UNION
               IMAGE (e k) (sphere(vec 0,&1))` THEN
  UNDISCH_TAC `(e:num->real^3->A) j (basis 1) IN top closure_of Q` THEN
  UNDISCH_TAC `(e:num->real^3->A) j (basis 1) IN IMAGE (e j) (sphere(vec 0,&1))` THEN
  UNDISCH_TAC `sphere(vec 0:real^3,&1) SUBSET annulus (&1 / &2) (&2)` THEN
  SET_TAC[];
    FIRST_ASSUM(SUBST1_TAC o SYM o check (let tq1 = `Q:A->bool = P` in fun th -> concl th = tq1)) THEN
  EXPAND_TAC "Q" THEN REFL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The cap stop, part 1.  The rescaled extended core                         *)
(* b2 w = apx_bext(|yz| w) of a ball cap is a ball chart inside the cap,     *)
(* its unit balls and sphere are the extended core balls of radius |yz|      *)
(* and the e'-sphere of radius |yz|, and it matches e' radially beyond the  *)
(* unit sphere (through the inverse of the cap's sphere diffeomorphism).    *)
(* ------------------------------------------------------------------------- *)

let APX_BCAP_SCALED_CHART = prove
 (`!top atlas (g:A->real^3^3) C eps U (bb:real^3->A) e' fU fU' yz.
     hausdorff_space top /\ &0 < eps /\ eps <= &1 / &8 /\
     apx_bcap (top,atlas) g C eps U bb e' fU /\ sphere_diffeo fU fU' /\
     yz IN rfs_neck_dom eps /\ &0 < apx_sval yz /\
     &2 * norm yz <= exp(inv eps / sqrt(&2))
     ==> &1 < norm yz /\
         mfd_ball_chart top atlas (\w. apx_bext bb e' fU (norm yz % w)) /\
         IMAGE (\w. apx_bext bb e' fU (norm yz % w)) (ball(vec 0,&2)) SUBSET U /\
         IMAGE (\w. apx_bext bb e' fU (norm yz % w)) (ball(vec 0,&1)) =
           IMAGE (apx_bext bb e' fU) (ball(vec 0,norm yz)) /\
         IMAGE (\w. apx_bext bb e' fU (norm yz % w)) (cball(vec 0,&1)) =
           IMAGE (apx_bext bb e' fU) (cball(vec 0,norm yz)) /\
         IMAGE (\w. apx_bext bb e' fU (norm yz % w)) (sphere(vec 0,&1)) =
           IMAGE e' (sphere(vec 0,norm yz)) /\
         (!t v. &1 < t /\ v IN sphere(vec 0,&1)
                ==> apx_bext bb e' fU (norm yz % (t % fU' v)) = e'((norm yz * t) % v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[apx_bcap] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_bcap")) (concl th))) THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
                mfd_param top atlas (rfs_neck_dom eps) (e':real^3->A)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `bb:real^3->A`;
                 `e':real^3->A`; `fU:real^3->real^3`; `fU':real^3->real^3`; `eps:real`]
                APX_BEXT_FACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `mfd_ball_chart top atlas (bb:real^3->A)` THEN SIMP_TAC[mfd_ball_chart];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`e':real^3->A`; `yz:real^3`; `eps:real`] APX_CP_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 < norm(yz:real^3)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `exp(apx_sval(yz:real^3) / sqrt(&2)) = norm yz`)) THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LT] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH];
    ALL_TAC] THEN
  ABBREV_TAC `c = norm(yz:real^3)` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(\w. apx_bext (bb:real^3->A) e' fU (c % w)) =
                apx_bext bb e' fU o (\w:real^3. c % w)` ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^3->bool. IMAGE (\w. apx_bext (bb:real^3->A) e' fU (c % w)) s =
                                IMAGE (apx_bext bb e' fU) (IMAGE (\w:real^3. c % w) s)`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[IMAGE_o]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM(MATCH_MP BALL_SCALING (ASSUME `&0 < c`));
              GSYM(MATCH_MP CBALL_SCALING (ASSUME `&0 < c`));
              GSYM(MATCH_MP SPHERE_SCALING (ASSUME `&0 < c`))] THEN
  REWRITE_TAC[REAL_MUL_RID; VECTOR_MUL_RZERO] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[mfd_ball_chart] THEN MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
    MAP_EVERY EXISTS_TAC [`ball(vec 0:real^3,exp(inv eps / sqrt(&2)))`;
                          `ball(vec 0:real^3,c * &2)`; `\w:real^3. inv c % w`] THEN
    ASM_SIMP_TAC[SMT_DIFFEO_SCALING_BALL] THEN
    REWRITE_TAC[SUBSET; IN_BALL_0] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC APX_BEXT_IN_U THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:A->real^3^3`; `C:real`; `eps:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC APX_BEXT_SPHERE THEN EXISTS_TAC `fU':real^3->real^3` THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`t:real`; `v:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(fU':real^3->real^3) v IN sphere(vec 0,&1) /\ fU(fU' v) = v`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `sphere_diffeo (fU:real^3->real^3) fU'` THEN
      REWRITE_TAC[sphere_diffeo] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `&1 < norm((c * t) % (fU':real^3->real^3) v)` ASSUME_TAC THENL
     [UNDISCH_TAC `(fU':real^3->real^3) v IN sphere(vec 0,&1)` THEN
      REWRITE_TAC[IN_SPHERE_0; NORM_MUL] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[REAL_MUL_RID] THEN
      SUBGOAL_THEN `&0 < c * t` (fun th -> REWRITE_TAC[MATCH_MP (REAL_ARITH
        `&0 < x ==> abs x = x`) th]) THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `&1 * &1 < c * t ==> &1 < c * t`) THEN
      MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `&0 < c * t` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[SMT_RADIAL_EXT_HOMOG; SMT_RADIAL_EXT_SPHERE]]);;

(* The cap stop.  A stopped chain whose last neck is the reversed copy of a  *)
(* ball cap's boundary neck e' at level s(yz) in (0, 4/ep) gives the REGION *)
(* one-sphere conclusion: J = {i}, P = E(annulus(1,L)) plus the closed ball  *)
(* b2(cball 1) with b2 w = apx_bext(|yz| w), disjoint, E radial onto b2 at  *)
(* the end through f2 = fU' o f0.  The tube misses the closed ball: it is   *)
(* connected, misses the sphere b2(sphere 1) = E(sphere L), and has a point *)
(* at an e'-level above s(yz).                                              *)

let APX_RG_CAP_FINAL = prove
 (`!top atlas (g:A->real^3^3) C eps dl ep J (e:num->real^3->A) P i b x N U
    (bb:real^3->A) e' fU yz.
     apx_rgc (top,atlas) g C eps dl ep J e P /\ apx_a13_ctx top atlas g ep /\ i IN J /\
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
           J = {i} /\ mfd_ball_chart top atlas b2 /\ IMAGE b2 (ball(vec 0,&2)) SUBSET P /\
           P = IMAGE E (annulus (&1) L) UNION IMAGE b2 (cball(vec 0,&1)) /\
           DISJOINT (IMAGE E (annulus (&1) L)) (IMAGE b2 (cball(vec 0,&1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_RG_CTX_SCALES) THEN
  SUBGOAL_THEN `apx_rg (top,atlas) (g:A->real^3^3) C eps dl J (e:num->real^3->A) P`
  ASSUME_TAC THENL
   [UNDISCH_TAC `apx_rgc (top,atlas) (g:A->real^3^3) C eps dl ep J (e:num->real^3->A) P` THEN
    SIMP_TAC[apx_rgc];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_RG_BASICS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_RG_PARTS) THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET P` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_RG_CAP_IN_P THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `C:real`; `eps:real`; `dl:real`; `J:num->bool`; `e:num->real^3->A`;
      `IMAGE (bb:real^3->A) (ball(vec 0,&1))`] THEN
    UNDISCH_TAC `apx_bcap (top,atlas) (g:A->real^3^3) C eps U bb e' fU` THEN
    REWRITE_TAC[apx_bcap] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      UNDISCH_TAC `apx_rgc (top,atlas) (g:A->real^3^3) C eps dl ep J (e:num->real^3->A) P` THEN
      REWRITE_TAC[apx_rgc] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `IMAGE (bb:real^3->A) (ball(vec 0,&1))` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `(e':real^3->A) yz` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term (fun t -> t = `rfs_neck_dom eps`)) (concl th) &&
        can (find_term (fun t -> t = `U:A->bool`)) (concl th))) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?fU'. sphere_diffeo (fU:real^3->real^3) fU'` (X_CHOOSE_TAC `fU':real^3->real^3`)
  THENL [ASM_MESON_TAC[apx_bcap]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (e':real^3->A) (rfs_neck_dom eps) SUBSET U /\
                (!k. k IN J ==> DISJOINT (U:A->bool)
                   (IMAGE ((e:num->real^3->A) k) (apx_slab (--inv(&2 * dl)) (inv(&2 * dl)))))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[apx_bcap]; ALL_TAC] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    UNDISCH_TAC `apx_rgc (top,atlas) (g:A->real^3^3) C eps dl ep J (e:num->real^3->A) P` THEN
    REWRITE_TAC[apx_rgc] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `IMAGE (bb:real^3->A) (ball(vec 0,&1))` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[apx_bcap];
    ALL_TAC] THEN
  APX_UNFOLD_ASM_TAC "apx_rgc" apx_rgc THEN
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
    SUBGOAL_THEN `IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1)) SUBSET U` MP_TAC THENL
     [UNDISCH_TAC `IMAGE (E:real^3->A) (sphere(vec 0,&1)) =
                   IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1))` THEN
      UNDISCH_TAC `IMAGE (E:real^3->A) (sphere(vec 0,LL)) =
                   IMAGE (e':real^3->A) (sphere(vec 0,norm(yz:real^3)))` THEN
      FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> concl th = `LL = &1`)) THEN
      DISCH_THEN SUBST1_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `IMAGE (\w. apx_bext (bb:real^3->A) e' fU (norm(yz:real^3) % w))
                               (sphere(vec 0,&1))`)) THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (\w. apx_bext (bb:real^3->A) e' fU (norm(yz:real^3) % w))
                        (ball(vec 0,&2))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; IN_SPHERE_0; IN_BALL_0] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(i:num) IN J`) o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `inv(&2 * dl)`)) (concl th))) THEN
    SUBGOAL_THEN `IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1)) SUBSET
                  IMAGE (e i) (apx_slab (--inv(&2 * dl)) (inv(&2 * dl)))` MP_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; IN_SPHERE_0; APX_SLAB_SVAL; apx_sval] THEN
      X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN ASM_REWRITE_TAC[LOG_1; REAL_MUL_RZERO] THEN
      CONJ_TAC THENL
       [DISCH_THEN(MP_TAC o AP_TERM `norm:real^3->real`) THEN ASM_REWRITE_TAC[NORM_0] THEN
        REAL_ARITH_TAC;
        SUBGOAL_THEN `&0 < inv(&2 * dl)` MP_TAC THENL
         [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(e:num->real^3->A) i (basis 1) IN IMAGE (e i) (sphere(vec 0,&1))` MP_TAC
    THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH];
      SET_TAC[]];
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
    SUBGOAL_THEN `(Q1:A->bool) SUBSET IMAGE (E:real^3->A) (apx_slab (--inv ep) (L0 + inv ep))`
    MP_TAC THENL
     [EXPAND_TAC "Q1" THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_eq(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_chain_union"))
          (concl th))) THEN
    REWRITE_TAC[apx_chain_union; SUBSET; IN_UNIONS; IN_ELIM_THM] THEN DISCH_TAC THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    X_GEN_TAC `q:A` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `q:A`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:A->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `m:int` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    UNDISCH_TAC `(q:A) IN t` THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THENL
     [ASM_REWRITE_TAC[APX_SLAB_NECK_DOM] THEN DISCH_TAC THEN
      SUBGOAL_THEN `(q:A) IN U` ASSUME_TAC THENL
       [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
          can (find_term (fun t -> t = `rfs_neck_dom eps`)) (concl th) &&
          can (find_term (fun t -> t = `U:A->bool`)) (concl th) &&
          not (is_forall (concl th)))) THEN
        UNDISCH_TAC `(q:A) IN IMAGE (e':real^3->A)
                       (apx_slab (apx_sval(yz:real^3) - inv ep) (apx_sval yz - --inv ep))` THEN
        MATCH_MP_TAC(SET_RULE `(s:real^3->bool) SUBSET t ==> (x:A) IN IMAGE (f:real^3->A) s ==> x IN IMAGE f t`) THEN
        REWRITE_TAC[APX_SLAB_NECK_DOM] THEN MATCH_MP_TAC APX_SLAB_SUBSET THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(j:num) IN J`) o check (fun th ->
        is_forall (concl th) && can (find_term (fun t -> t = `inv(&2 * dl)`)) (concl th) &&
        can (find_term (fun t -> t = `U:A->bool`)) (concl th))) THEN
      SUBGOAL_THEN `IMAGE ((e:num->real^3->A) j) (sphere(vec 0,&1)) SUBSET
                    IMAGE (e j) (apx_slab (--inv(&2 * dl)) (inv(&2 * dl)))` MP_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN
        REWRITE_TAC[SUBSET; IN_SPHERE_0; APX_SLAB_SVAL; apx_sval] THEN
        X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN ASM_REWRITE_TAC[LOG_1; REAL_MUL_RZERO] THEN
        CONJ_TAC THENL
         [DISCH_THEN(MP_TAC o AP_TERM `norm:real^3->real`) THEN ASM_REWRITE_TAC[NORM_0] THEN
          REAL_ARITH_TAC;
          SUBGOAL_THEN `&0 < inv(&2 * dl)` MP_TAC THENL
           [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
        ALL_TAC] THEN
      UNDISCH_TAC `(q:A) IN U` THEN
      UNDISCH_TAC `(q:A) IN IMAGE ((e:num->real^3->A) j) (sphere(vec 0,&1))` THEN
      SET_TAC[];
      DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`m:int`; `j:num`] o check (fun th ->
        is_forall (concl th) && can (find_term (fun t -> t = `N:int->real^3->A`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th))) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `m:int <= b + &1` THEN UNDISCH_TAC `~(m:int = b + &1)` THEN INT_ARITH_TAC;
        ALL_TAC] THEN
      UNDISCH_TAC `(q:A) IN IMAGE ((N:int->real^3->A) m) (rfs_neck_dom ep)` THEN
      UNDISCH_TAC `(q:A) IN IMAGE ((e:num->real^3->A) j) (sphere(vec 0,&1))` THEN
      SET_TAC[]];
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
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `U:A->bool` THEN
      CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (\w. apx_bext (bb:real^3->A) e' fU (norm(yz:real^3) % w))
                        (ball(vec 0,&2))` THEN
      CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC];
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
  SUBGOAL_THEN `J = {i:num}` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN X_GEN_TAC `j:num` THEN
    EQ_TAC THENL [ALL_TAC; DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]] THEN
    DISCH_TAC THEN ASM_CASES_TAC `j:num = i` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(e:num->real^3->A) j (basis 1) IN IMAGE (e j) (sphere(vec 0,&1))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH];
      ALL_TAC] THEN
    SUBGOAL_THEN `(e:num->real^3->A) j (basis 1) IN top closure_of P` MP_TAC THENL
     [FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `top closure_of (P:A->bool)`)) THEN
      REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN DISJ2_TAC THEN
      EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `P:A->bool` &&
      can (find_term (fun t -> t = `Q1:A->bool`)) (lhs(concl th)))) THEN
    REWRITE_TAC[CLOSURE_OF_UNION] THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `top closure_of
                         (IMAGE (\w. apx_bext (bb:real^3->A) e' fU (norm(yz:real^3) % w))
                                (cball(vec 0,&1)))`)) THEN
    SUBGOAL_THEN `DISJOINT (P:A->bool) (IMAGE ((e:num->real^3->A) j) (sphere(vec 0,&1)))`
    MP_TAC THENL
     [FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(j:num) IN J`) o check (fun th ->
        is_forall (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_neck_chart"))
            (concl th))) THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `DISJOINT (IMAGE ((e:num->real^3->A) j) (sphere(vec 0,&1)))
                           (IMAGE (e i) (sphere(vec 0,&1)))` MP_TAC THENL
     [SUBGOAL_THEN `sphere(vec 0:real^3,&1) SUBSET annulus (&1 / &2) (&2)` ASSUME_TAC THENL
       [REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC(SET_RULE `!a b c d:A->bool. a SUBSET c /\ b SUBSET d /\ DISJOINT c d
                                               ==> DISJOINT a b`) THEN
      MAP_EVERY EXISTS_TAC [`IMAGE ((e:num->real^3->A) j) (annulus (&1 / &2) (&2))`;
                            `IMAGE ((e:num->real^3->A) i) (annulus (&1 / &2) (&2))`] THEN
      ASM_SIMP_TAC[IMAGE_SUBSET] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> t = `annulus (&1 / &2) (&2):real^3->bool`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `top closure_of Q1 SUBSET
                 Q1 UNION IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1)) UNION
                 IMAGE (e':real^3->A) (sphere(vec 0,norm(yz:real^3)))` THEN
    UNDISCH_TAC `(Q1:A->bool) SUBSET P` THEN
    UNDISCH_TAC `IMAGE (\w. apx_bext (bb:real^3->A) e' fU (norm(yz:real^3) % w))
                       (cball(vec 0,&1)) SUBSET P` THEN
    UNDISCH_TAC `IMAGE (\w. apx_bext (bb:real^3->A) e' fU (norm(yz:real^3) % w))
                       (cball(vec 0,&1)) =
                 IMAGE (\w. apx_bext bb e' fU (norm yz % w)) (ball(vec 0,&1)) UNION
                 IMAGE (e':real^3->A) (sphere(vec 0,norm yz))` THEN
    UNDISCH_TAC `(e:num->real^3->A) j (basis 1) IN IMAGE (e j) (sphere(vec 0,&1))` THEN
    MATCH_ACCEPT_TAC(SET_RULE
     `!(x:A) Sj Q2 B1 Sg P Q1 C Si.
        x IN Sj ==> Q2 = B1 UNION Sg ==> Q2 SUBSET P ==> Q1 SUBSET P ==>
        C SUBSET Q1 UNION Si UNION Sg ==> DISJOINT Sj Si ==> DISJOINT P Sj ==>
        ~(x IN C UNION Q2)`);
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
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `U:A->bool` THEN
  CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `P:A->bool` &&
    can (find_term (fun t -> t = `Q1:A->bool`)) (lhs(concl th)))) THEN
  EXPAND_TAC "Q1" THEN REFL_TAC;
    FIRST_ASSUM(SUBST1_TAC o check (fun th ->
    concl th = `IMAGE (E:real^3->A) (annulus (&1) LL) = Q1`)) THEN
  FIRST_ASSUM ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The region theorem in the growth context: a stopped chain                 *)
(* exists, and either stop gives the REGION conclusion.                     *)
(* ------------------------------------------------------------------------- *)

let APX_RG_MAIN = prove
 (`!top atlas (g:A->real^3^3) C eps dl ep J (e:num->real^3->A) P i.
     apx_rgc (top,atlas) g C eps dl ep J e P /\ apx_a13_ctx top atlas g ep /\ i IN J
     ==> ?i E L f f' b2.
            i IN J /\ &1 < L /\ sphere_diffeo f f' /\
            mfd_param top atlas (annulus (&1) L) E /\
            (!x. x IN annulus (&1) (&3 / &2) ==> E x = e i x) /\
            (!x. x IN annulus (L / &2) L ==> E x = b2((L / norm x) % f(inv(norm x) % x))) /\
            ((J = {i} /\ mfd_ball_chart top atlas b2 /\ IMAGE b2 (ball(vec 0,&2)) SUBSET P /\
              P = IMAGE E (annulus (&1) L) UNION IMAGE b2 (cball(vec 0,&1)) /\
              DISJOINT (IMAGE E (annulus (&1) L)) (IMAGE b2 (cball(vec 0,&1)))) \/
             (?j. j IN J /\ ~(j = i) /\ J = {i,j} /\ b2 = e j /\
                  P = IMAGE E (annulus (&1) L)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL APX_RG_GROW) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:int` (X_CHOOSE_THEN `x:int->A` (X_CHOOSE_THEN
    `N:int->real^3->A` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
  DISCH_THEN(DISJ_CASES_THEN2 MP_TAC MP_TAC) THENL
   [DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `bb:real^3->A`
      (X_CHOOSE_THEN `e':real^3->A` (X_CHOOSE_THEN `fU:real^3->real^3`
      (X_CHOOSE_THEN `yz:real^3` STRIP_ASSUME_TAC))))) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `C:real`; `eps:real`; `dl:real`; `ep:real`;
                   `J:num->bool`; `e:num->real^3->A`; `P:A->bool`; `i:num`; `b:int`;
                   `x:int->A`; `N:int->real^3->A`; `U:A->bool`; `bb:real^3->A`;
                   `e':real^3->A`; `fU:real^3->real^3`; `yz:real^3`] APX_RG_CAP_FINAL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `E:real^3->A` (X_CHOOSE_THEN `L:real`
      (X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `f':real^3->real^3`
      (X_CHOOSE_THEN `b2:real^3->A` STRIP_ASSUME_TAC))))) THEN
    MAP_EVERY EXISTS_TAC [`i:num`; `E:real^3->A`; `L:real`; `f:real^3->real^3`;
                          `f':real^3->real^3`; `b2:real^3->A`] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY];
    DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `yk:real^3` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `C:real`; `eps:real`; `dl:real`; `ep:real`;
                   `J:num->bool`; `e:num->real^3->A`; `P:A->bool`; `i:num`; `b:int`;
                   `x:int->A`; `N:int->real^3->A`; `k:num`; `yk:real^3`]
                  APX_RG_SPHERE_FINAL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `E:real^3->A` (X_CHOOSE_THEN `L:real`
      (X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `f':real^3->real^3`
       STRIP_ASSUME_TAC)))) THEN
    MAP_EVERY EXISTS_TAC [`i:num`; `E:real^3->A`; `L:real`; `f:real^3->real^3`;
                          `f':real^3->real^3`; `(e:num->real^3->A) k`] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN DISJ2_TAC THEN EXISTS_TAC `k:num` THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY]]);;

(* ------------------------------------------------------------------------- *)
(* REGION from the tight-shell statement.  When two cut                      *)
(* spheres are close (S_k meets the middle of the e_j-neck) the tight-shell *)
(* statement gives the product directly; otherwise the cut spheres are far  *)
(* apart (no close pairs at the chain scale ep = apx_kc eps) and the growth *)
(* argument APX_RG_MAIN applies.  The twisted case is APX_RG_TWISTED.       *)
(* ------------------------------------------------------------------------- *)

(* The tight-shell statement: two dl-necks of the region data whose cut     *)
(* spheres are close (S_k meets the middle of the e_j-neck).  The product   *)
(* starts at S_k (E = e_k near it) and ends radially at S_j.  It is a pure  *)
(* neck statement (no canonical neighbourhood hypothesis), proved as         *)
(* APX_TIGHT_SHELL in pc_apx_tight.                                          *)

let APX_TIGHT_SHELL_STATEMENT = new_definition
 `APX_TIGHT_SHELL_STATEMENT (u:A->bool) <=>
    ?dl0. &0 < dl0 /\
      !top atlas g dl J e P j k.
         hausdorff_space top /\
         smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
         riemannian_metric atlas g /\ apx_sphere_sep top atlas /\
         &0 < dl /\ dl <= dl0 /\ FINITE J /\
         (!i:num. i IN J ==> ?y. rfs_neck (top,atlas) g dl y (e i)) /\
         (!i j. i IN J /\ j IN J /\ ~(i = j)
                ==> DISJOINT (IMAGE (e i) (annulus (&1 / &2) (&2)))
                             (IMAGE (e j) (annulus (&1 / &2) (&2)))) /\
         open_in top P /\ connected_in top P /\
         compact_in top (top closure_of P) /\
         top closure_of P = P UNION UNIONS {IMAGE (e i) (sphere(vec 0,&1)) | i IN J} /\
         (!i. i IN J
              ==> P INTER IMAGE (e i) (annulus (&1 / &2) (&2)) =
                  IMAGE (e i) (annulus (&1) (&2))) /\
         j IN J /\ k IN J /\ ~(j = k) /\
         ~DISJOINT (IMAGE (e k) (sphere(vec 0,&1)))
                   (IMAGE (e j) (apx_slab (--inv(&64 * dl)) (inv(&64 * dl))))
         ==> ?E L f f'. &1 < L /\ sphere_diffeo f f' /\
                mfd_param top atlas (annulus (&1) L) E /\
                (!x. x IN annulus (&1) (&3 / &2) ==> E x = e k x) /\
                (!x. x IN annulus (L / &2) L
                     ==> E x = e j ((L / norm x) % f(inv(norm x) % x))) /\
                J = {j,k} /\ P = IMAGE E (annulus (&1) L)`;;

let APX_REGION_FROM_TIGHT = prove
 (`!u:A->bool. APX_TIGHT_SHELL_STATEMENT u ==> APX_REGION_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[APX_TIGHT_SHELL_STATEMENT; APX_REGION_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `dlT:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tight"))) THEN
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
  MP_TAC(ISPEC `u:A->bool` APX_CAP_FAR_UNCOND) THEN REWRITE_TAC[APX_CAP_FAR_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `e6:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "far"))) THEN
  MP_TAC APX_KC_GE THEN DISCH_TAC THEN
  ABBREV_TAC `m0 = min (min (min e1 e2) (min e3 e4)) e5` THEN
  SUBGOAL_THEN `&0 < m0 /\ m0 <= e1 /\ m0 <= e2 /\ m0 <= e3 /\ m0 <= e4 /\ m0 <= e5`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "m0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `min (m0 / apx_kc) e6` THEN
  SUBGOAL_THEN `&0 < m0 / apx_kc` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`] THEN STRIP_TAC THEN
  USE_THEN "far" (MP_TAC o SPECL [`C:real`; `eps:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dF:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "farC"))) THEN
  EXISTS_TAC `min (min dF dlT) (min eps (&1 / &8))` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `dl:real`; `J:num->bool`; `e:num->real^3->A`;
                       `P:A->bool`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `dl <= dF /\ dl <= dlT /\ dl <= eps /\ dl <= &1 / &8` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!U Y k. rfs_cap (top,atlas) (g:A->real^3^3) C eps U Y /\ k IN J
                        ==> DISJOINT U (IMAGE ((e:num->real^3->A) k)
                                          (apx_slab (--inv(&2 * dl)) (inv(&2 * dl))))`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`U:A->bool`; `Y:A->bool`; `k:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `?y. rfs_neck (top,atlas) (g:A->real^3^3) dl y ((e:num->real^3->A) k)`
    (X_CHOOSE_TAC `y:A`) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    USE_THEN "farC" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:A->real^3^3`; `y:A`; `Y:A->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `apx_rg (top,atlas) (g:A->real^3^3) C eps dl J (e:num->real^3->A) P`
  ASSUME_TAC THENL [REWRITE_TAC[apx_rg] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `?U Y p. rfs_cap (top,atlas) (g:A->real^3^3) C eps U Y /\
                         rfs_twisted_chart top atlas (p:real^3->A) /\
                         IMAGE p (annulus (&1 / &4) (&4)) SUBSET U /\
                         ~DISJOINT U (top closure_of P)` THENL
   [DISJ1_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `Y:A->bool`
      (X_CHOOSE_THEN `p:real^3->A` STRIP_ASSUME_TAC))) THEN
    MATCH_MP_TAC APX_RG_TWISTED THEN
    MAP_EVERY EXISTS_TAC [`g:A->real^3^3`; `C:real`; `eps:real`; `dl:real`; `J:num->bool`;
                          `e:num->real^3->A`; `U:A->bool`; `Y:A->bool`; `p:real^3->A`] THEN
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[];
    DISJ2_TAC] THEN
  ABBREV_TAC `ep = apx_kc * eps` THEN
  SUBGOAL_THEN `&0 < ep /\ ep <= m0 /\ &512 * dl <= ep` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ep" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `eps <= m0 / apx_kc` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < apx_kc` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SIMP_TAC[REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&512 * eps` THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `?j k. j IN J /\ k IN J /\ ~(j = k) /\
                       ~DISJOINT (IMAGE ((e:num->real^3->A) k) (sphere(vec 0,&1)))
                                 (IMAGE (e j) (apx_slab (--(&8 / ep)) (&8 / ep)))` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC)) THEN
    USE_THEN "tight" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `dl:real`; `J:num->bool`; `e:num->real^3->A`; `P:A->bool`;
      `j:num`; `k:num`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~DISJOINT (IMAGE ((e:num->real^3->A) k) (sphere(vec 0,&1)))
                             (IMAGE (e j) (apx_slab (--(&8 / ep)) (&8 / ep)))` THEN
      MATCH_MP_TAC(SET_RULE `!s t u:A->bool. t SUBSET u ==> ~DISJOINT s t ==> ~DISJOINT s u`) THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC APX_SLAB_SUBSET THEN
      SUBGOAL_THEN `&8 / ep <= inv(&64 * dl)` (fun th -> MP_TAC th THEN REAL_ARITH_TAC) THEN
      REWRITE_TAC[real_div; REAL_MUL_LID] THEN
      SUBGOAL_THEN `inv(&64 * dl) = inv(&8) * inv(&8 * dl)` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM REAL_INV_MUL] THEN AP_TERM_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `inv ep <= inv(&512 * dl)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_INV_MUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `E:real^3->A` (X_CHOOSE_THEN `L:real`
      (X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `f':real^3->real^3`
       STRIP_ASSUME_TAC)))) THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `E:real^3->A`; `L:real`; `f:real^3->real^3`;
                          `f':real^3->real^3`; `(e:num->real^3->A) j`] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN DISJ2_TAC THEN EXISTS_TAC `j:num` THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; INSERT_AC];
    ALL_TAC] THEN
  SUBGOAL_THEN `?i:num. i IN J` (X_CHOOSE_TAC `i:num`) THENL
   [ASM_REWRITE_TAC[MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `apx_rgc (top,atlas) (g:A->real^3^3) C eps dl ep J (e:num->real^3->A) P`
  ASSUME_TAC THENL
   [REWRITE_TAC[apx_rgc] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `eps <= m0` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `ep:real` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "ep" THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
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
      USE_THEN "ctx" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
        `g:A->real^3^3`; `dl:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      USE_THEN "rat" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th) &&
        can (find_term (fun t -> t = `&8 / ep`)) (concl th))) THEN
      REWRITE_TAC[NOT_EXISTS_THM] THEN MESON_TAC[];
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_twisted_chart"))
            (concl th))) THEN
      FIRST_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `top closure_of (P:A->bool)`)) THEN
      REWRITE_TAC[NOT_EXISTS_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `dl:real`; `ep:real`; `J:num->bool`;
                 `e:num->real^3->A`; `P:A->bool`; `i:num`] APX_RG_MAIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "a13" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    SIMP_TAC[]]);;


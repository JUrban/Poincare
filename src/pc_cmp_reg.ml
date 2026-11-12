(* ========================================================================= *)
(* Unit pc_cmp_reg (comparison-geometry layer CMP): regularity of shortest   *)
(* curves, without completeness.  A unit-speed curve c on [0,R] realizing    *)
(* the distance between any two of its points is the geodesic r |->          *)
(* exp_y(r u) from y = c(0) (CMPRG_CORE); hence the image of a C^1 shortest  *)
(* curve (length = distance on every subinterval, stops allowed) is the      *)
(* minimizing segment exp_y(s w), 0 <= s <= 1, from its start to its end     *)
(* (CMPRG_SHORTEST).  Local step: in a uniformly normal neighbourhood        *)
(* (MFD_UNIFORMLY_NORMAL) a distance-realizing curve is radial from its      *)
(* first point (CMPRG_LRAD, from GEOH_BROKEN_RADIAL and injectivity of exp); *)
(* the global step continues the maximal geodesic past the supremum of the   *)
(* times up to which it agrees with c (MFD_GEO_SHIFT).  Used by the local    *)
(* Toponogov theorem in convex regions of incomplete manifolds (pc_cmp_ltpg) *)
(* and the splitting theorem for lines (pc_cmp_split).                       *)
(* ========================================================================= *)

needs "src/pc_cmp_mgeo.ml";;
needs "src/pc_grg_distcont.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The local step.  If every point of W has an injectivity                   *)
(* ball of radius rho containing W in its exp image, then a curve c in W     *)
(* realizing distances on [r0,r2], 0 < r2 - r0 < rho, is radial from c(r0):  *)
(* c(r) = exp_(c r0)((r - r0) u) with |u| = 1.                               *)
(* ========================================================================= *)

let CMPRG_LRAD = prove
 (`!top atlas (g:A->real^N^N) W rho (c:real->A) r0 r2.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ &0 < rho /\ W SUBSET topspace top /\
        (!y. y IN W
             ==> mfd_inj_ball (top,atlas) g y rho /\
                 W SUBSET IMAGE (mfd_exp (top,atlas) g y) (mfd_tball g y rho)) /\
        r0 < r2 /\ r2 - r0 < rho /\
        (!r. r0 <= r /\ r <= r2 ==> c r IN W) /\
        (!s t. r0 <= s /\ s <= r2 /\ r0 <= t /\ t <= r2
               ==> mfd_joinable (top,atlas) (c s) (c t) /\
                   mfd_dist (top,atlas) g (c s) (c t) = abs(t - s))
        ==> ?u. mfd_tnorm g (c r0) u = &1 /\
                !r. r0 <= r /\ r <= r2
                    ==> (r - r0) % u IN mfd_exp_dom (top,atlas) g (c r0) /\
                        c r = mfd_exp (top,atlas) g (c r0) ((r - r0) % u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `p = (c:real->A) r0` THEN
  SUBGOAL_THEN `(p:A) IN W` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(p:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_inj_ball (top,atlas) (g:A->real^N^N) p rho` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_tball (g:A->real^N^N) p rho SUBSET mfd_exp_dom (top,atlas) g p`
  ASSUME_TAC THENL [ASM_MESON_TAC[mfd_inj_ball]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(c:real->A) r2 IN W` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?wz. mfd_tnorm (g:A->real^N^N) p wz < rho /\
                     mfd_exp (top,atlas) g p wz = (c:real->A) r2`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(c:real->A) r2 IN IMAGE (mfd_exp (top,atlas) (g:A->real^N^N) p)
                                          (mfd_tball g p rho)`
    MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; mfd_tball; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) p wz = r2 - r0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`; `rho:real`; `wz:real^N`] MFD_EXP_DIST) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
    EXPAND_TAC "p" THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`r0:real`; `r2:real`] o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> try fst(dest_const t) = "mfd_dist"
                                                       with Failure _ -> false)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `u = inv(r2 - r0) % (wz:real^N)` THEN
  SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) p u = &1` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN ASM_REWRITE_TAC[REAL_ABS_INV] THEN
    SUBGOAL_THEN `&0 < r2 - r0` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `(r2 - r0) % (u:real^N) = wz` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `(r2 - r0) * inv(r2 - r0) = &1` (fun th -> REWRITE_TAC[th; VECTOR_MUL_LID]) THEN
    MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `u:real^N` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(r - r0) % (u:real^N) IN mfd_exp_dom (top,atlas) (g:A->real^N^N) p`
  ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_tball (g:A->real^N^N) p rho SUBSET mfd_exp_dom (top,atlas) g p` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[mfd_tball; IN_ELIM_THM; REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `r:real = r0` THENL
   [ASM_REWRITE_TAC[REAL_SUB_REFL; VECTOR_MUL_LZERO] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`] MFD_EXP_DOM) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `r:real = r2` THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `r0 < r /\ r < r2` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `q = (c:real->A) r` THEN
  SUBGOAL_THEN `(q:A) IN W` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(q:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?wq. mfd_tnorm (g:A->real^N^N) p wq < rho /\
                     mfd_exp (top,atlas) g p wq = q`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(q:A) IN IMAGE (mfd_exp (top,atlas) (g:A->real^N^N) p) (mfd_tball g p rho)`
    MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; mfd_tball; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) p wq = r - r0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`; `rho:real`; `wq:real^N`] MFD_EXP_DIST) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
    REWRITE_TAC[SYM(ASSUME `(c:real->A) r0 = p`); SYM(ASSUME `(c:real->A) r = q`)] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`r0:real`; `r:real`] o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> try fst(dest_const t) = "mfd_dist"
                                                       with Failure _ -> false)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_inj_ball (top,atlas) (g:A->real^N^N) q rho` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?w0. mfd_tnorm (g:A->real^N^N) q w0 < rho /\
                     mfd_exp (top,atlas) g q w0 = (c:real->A) r2`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(c:real->A) r2 IN IMAGE (mfd_exp (top,atlas) (g:A->real^N^N) q)
                                          (mfd_tball g q rho)`
    MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; mfd_tball; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) q w0 = r2 - r` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `q:A`; `rho:real`; `w0:real^N`] MFD_EXP_DIST) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
    REWRITE_TAC[SYM(ASSUME `(c:real->A) r = q`)] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`r:real`; `r2:real`] o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> try fst(dest_const t) = "mfd_dist"
                                                       with Failure _ -> false)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `up = inv(r - r0) % (wq:real^N)` THEN
  SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) p up = &1 /\ (r - r0) % up = wq`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "up" THEN ASM_REWRITE_TAC[REAL_ABS_INV; VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `(r - r0) * inv(r - r0) = &1` (fun th -> REWRITE_TAC[th; VECTOR_MUL_LID]) THENL
     [MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < r - r0` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `rho:real`; `up:real^N`; `r - r0`; `r2 - r`;
                 `q:A`; `w0:real^N`; `(c:real->A) r2`] GEOH_BROKEN_RADIAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `mfd_tball (g:A->real^N^N) q rho SUBSET mfd_exp_dom (top,atlas) g q`
      MP_TAC THENL [ASM_MESON_TAC[mfd_inj_ball]; ALL_TAC] THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[mfd_tball; IN_ELIM_THM] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `q:A`] GEOD_TNORM_BASIC) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `abs t * (r2 - r) <= &1 * (r2 - r)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      EXPAND_TAC "p" THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`r0:real`; `r2:real`] o check (fun th ->
        is_forall(concl th) && can (find_term (fun t -> try fst(dest_const t) = "mfd_dist"
                                                         with Failure _ -> false)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      EXPAND_TAC "p" THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`r0:real`; `r2:real`] o check (fun th ->
        is_forall(concl th) && can (find_term (fun t -> try fst(dest_const t) = "mfd_dist"
                                                         with Failure _ -> false)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `(r - r0) + (r2 - r) = r2 - r0`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(r2 - r0) % (up:real^N) = wz` ASSUME_TAC THENL
   [MATCH_MP_TAC CMPS_INJ_BALL_INJ THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `g:A->real^N^N`; `p:A`; `rho:real`] THEN
    ASM_REWRITE_TAC[REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(up:real^N) = u` SUBST_ALL_TAC THENL
   [EXPAND_TAC "u" THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `inv(r2 - r0) * (r2 - r0) = &1` (fun th -> REWRITE_TAC[th; VECTOR_MUL_LID]) THEN
    MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The global step.  CMPRG_NBHD packages a uniformly normal                  *)
(* neighbourhood with a metric ball inside it; CMPRG_STEP continues the      *)
(* agreement of the maximal geodesic geo(c 0,u) with c past any time Tm up   *)
(* to which it holds; CMPRG_CORE takes the supremum.                         *)
(* ========================================================================= *)

let CMPRG_NBHD = prove
 (`!top atlas (g:A->real^N^N) (x:A).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top
        ==> ?W rho e. W SUBSET topspace top /\ &0 < rho /\ &0 < e /\
                      (!y. y IN W
                           ==> mfd_inj_ball (top,atlas) g y rho /\
                               W SUBSET IMAGE (mfd_exp (top,atlas) g y) (mfd_tball g y rho)) /\
                      (!y. mfd_joinable (top,atlas) x y /\ mfd_dist (top,atlas) g x y < e
                           ==> y IN W)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] MFD_UNIFORMLY_NORMAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:A->bool` (X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `W:A->bool`] MFD_OPEN_IN_BALLS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`W:A->bool`; `rho:real`; `e:real`] THEN
  ASM_SIMP_TAC[] THEN X_GEN_TAC `y:A` THEN STRIP_TAC THEN
  UNDISCH_TAC `mfd_ball (top,atlas) (g:A->real^N^N) x e SUBSET W` THEN
  REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

let CMPRG_STEP = prove
 (`!top atlas (g:A->real^N^N) (c:real->A) u R Tm.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ c(&0) IN topspace top /\
        mfd_tnorm g (c(&0)) u = &1 /\
        (!s t. &0 <= s /\ s <= R /\ &0 <= t /\ t <= R
               ==> mfd_joinable (top,atlas) (c s) (c t) /\
                   mfd_dist (top,atlas) g (c s) (c t) = abs(t - s)) /\
        &0 < Tm /\ Tm <= R /\
        (!t. &0 <= t /\ t < Tm
             ==> real_interval[&0,t] SUBSET mfd_geo_maxint (top,atlas) g (c(&0)) u /\
                 !r. &0 <= r /\ r <= t ==> mfd_geo (top,atlas) g (c(&0)) u r = c r)
        ==> ?t'. Tm <= t' /\ t' <= R /\ (Tm < t' \/ t' = R) /\
                 real_interval[&0,t'] SUBSET mfd_geo_maxint (top,atlas) g (c(&0)) u /\
                 !r. &0 <= r /\ r <= t' ==> mfd_geo (top,atlas) g (c(&0)) u r = c r`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "dist")
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "agree"))))))))) THEN
  ABBREV_TAC `y = (c:real->A)(&0)` THEN
  SUBGOAL_THEN `!r. &0 <= r /\ r <= R ==> (c:real->A) r IN topspace top` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "dist" (MP_TAC o SPECL [`&0`; `r:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(c:real->A) Tm`] CMPRG_NBHD) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`W:A->bool`; `rho:real`; `e:real`] THEN STRIP_TAC THEN
  ABBREV_TAC `h = min e rho / &4` THEN
  SUBGOAL_THEN `&0 < h /\ &2 * h < rho /\ h < e` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `r0 = Tm - min h (Tm / &2)` THEN
  ABBREV_TAC `r1 = Tm - min h (Tm / &2) / &2` THEN
  ABBREV_TAC `r2 = min R (Tm + h)` THEN
  SUBGOAL_THEN `&0 < r0 /\ r0 < r1 /\ r1 < Tm /\ Tm <= r2 /\ r2 <= R /\
                r2 - r0 < rho /\ Tm - r0 <= h /\ r2 - Tm <= h`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["r0"; "r1"; "r2"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `Tm < r2 \/ r2 = R` ASSUME_TAC THENL
   [EXPAND_TAC "r2" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!r. r0 <= r /\ r <= r2 ==> (c:real->A) r IN W` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    USE_THEN "dist" (MP_TAC o SPECL [`Tm:real`; `r:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `W:A->bool`; `rho:real`; `c:real->A`;
                 `r0:real`; `r2:real`] CMPRG_LRAD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN USE_THEN "dist" MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `p = (c:real->A) r0` THEN
  DISCH_THEN(X_CHOOSE_THEN `up:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(p:A) IN W /\ p IN topspace top` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "agree" (MP_TAC o SPEC `r1:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "val1")) THEN
  SUBGOAL_THEN `r0 IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) y u /\
                r1 IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) y u`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (find_term ((=) `r1:real`)) (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "mfd_geo_maxint"
                               with Failure _ -> false)) (concl th))) THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_geo (top,atlas) (g:A->real^N^N) y u r0 = p` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN USE_THEN "val1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `y:A`; `u:real^N`; `r0:real`] MFD_GEO_SHIFT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `vp = mfd_vel (atlas:((A->bool)#(A->real^N))->bool)
                     (mfd_geo (top,atlas) (g:A->real^N^N) y u) r0` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "shift")) THEN
  SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) p vp = &1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `y:A`; `u:real^N`] MFD_GEO_MAXIMAL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `mfd_geo (top,atlas) (g:A->real^N^N) y u`;
                   `mfd_geo_maxint (top,atlas) (g:A->real^N^N) y u`; `r0:real`; `&0`]
      MFD_GEODESIC_SPEED) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `vp:real^N = up` SUBST_ALL_TAC THENL
   [SUBGOAL_THEN `r1 - r0 IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) p vp` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      REWRITE_TAC[REAL_ARITH `r0 + (r1 - r0) = r1`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`; `vp:real^N`; `r1 - r0`] MFD_EXP_RADIAL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `mfd_exp (top,atlas) (g:A->real^N^N) p ((r1 - r0) % vp) = (c:real->A) r1`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      USE_THEN "shift" (MP_TAC o SPEC `r1 - r0`) THEN
      REWRITE_TAC[REAL_ARITH `r0 + (r1 - r0) = r1`] THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST1_TAC THEN USE_THEN "val1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `mfd_exp (top,atlas) (g:A->real^N^N) p ((r1 - r0) % up) = (c:real->A) r1`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `r1:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `up:real^N`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(ACCEPT_TAC o SYM o CONJUNCT2);
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`] GEOD_TNORM_BASIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(r1 - r0) % (vp:real^N) = (r1 - r0) % up` MP_TAC THENL
     [MATCH_MP_TAC CMPS_INJ_BALL_INJ THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                            `g:A->real^N^N`; `p:A`; `rho:real`] THEN
      REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[];
        ASM_REWRITE_TAC[REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
        TRANS_TAC EQ_TRANS `(c:real->A) r1` THEN CONJ_TAC THENL
         [FIRST_ASSUM ACCEPT_TAC; CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC]];
      REWRITE_TAC[VECTOR_MUL_LCANCEL] THEN
      ASM_SIMP_TAC[REAL_ARITH `r0 < r1 ==> ~(r1 - r0 = &0)`]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. r0 <= r /\ r <= r2
                    ==> r IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) y u /\
                        mfd_geo (top,atlas) g y u r = (c:real->A) r`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `r - r0 IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) p up` MP_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `p:A`; `up:real^N`; `r - r0`] MFD_EXP_RADIAL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `up:real^N`)) (concl th) &&
        can (find_term ((=) `r2:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `r IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) y u` ASSUME_TAC THENL
     [UNDISCH_TAC `r - r0 IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) p up` THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN REWRITE_TAC[REAL_ARITH `r0 + (r - r0) = r`];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "shift" (MP_TAC o SPEC `r - r0`) THEN
    REWRITE_TAC[REAL_ARITH `r0 + (r - r0) = r`] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`; `up:real^N`; `r - r0`] MFD_EXP_RADIAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `up:real^N`)) (concl th) &&
      can (find_term ((=) `r2:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `r2:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `r <= r1` THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term ((=) `r1:real`)) (concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "mfd_geo_maxint"
                                 with Failure _ -> false)) (concl th) &&
        not(is_forall(concl th)))) THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `r2:real`)) (concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "mfd_geo"
                                 with Failure _ -> false)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `r <= r1` THENL
     [USE_THEN "val1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `r2:real`)) (concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "mfd_geo"
                                 with Failure _ -> false)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]]]);;

let CMPRG_CORE = prove
 (`!top atlas (g:A->real^N^N) (c:real->A) R.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ &0 < R /\ c(&0) IN topspace top /\
        (!s t. &0 <= s /\ s <= R /\ &0 <= t /\ t <= R
               ==> mfd_joinable (top,atlas) (c s) (c t) /\
                   mfd_dist (top,atlas) g (c s) (c t) = abs(t - s))
        ==> ?u. mfd_tnorm g (c(&0)) u = &1 /\
                real_interval[&0,R] SUBSET mfd_geo_maxint (top,atlas) g (c(&0)) u /\
                !r. &0 <= r /\ r <= R ==> mfd_geo (top,atlas) g (c(&0)) u r = c r`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dist")))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(c:real->A)(&0)`] CMPRG_NBHD) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`W:A->bool`; `rho:real`; `e:real`] THEN STRIP_TAC THEN
  ABBREV_TAC `r2 = min R (min e rho / &2)` THEN
  SUBGOAL_THEN `&0 < r2 /\ r2 <= R /\ r2 < rho /\ r2 < e` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r2" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `W:A->bool`; `rho:real`; `c:real->A`;
                 `&0`; `r2:real`] CMPRG_LRAD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      USE_THEN "dist" (MP_TAC o SPECL [`&0`; `r:real`]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REPEAT GEN_TAC THEN STRIP_TAC THEN USE_THEN "dist" MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `u:real^N` THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `S = {t | &0 <= t /\ t <= R /\
                       real_interval[&0,t] SUBSET
                         mfd_geo_maxint (top,atlas) (g:A->real^N^N) ((c:real->A)(&0)) u /\
                       !r. &0 <= r /\ r <= t ==> mfd_geo (top,atlas) g (c(&0)) u r = c r}` THEN
  SUBGOAL_THEN
   `!t. t IN S <=> &0 <= t /\ t <= R /\
                   real_interval[&0,t] SUBSET
                     mfd_geo_maxint (top,atlas) (g:A->real^N^N) ((c:real->A)(&0)) u /\
                   !r. &0 <= r /\ r <= t ==> mfd_geo (top,atlas) g (c(&0)) u r = c r`
  (LABEL_TAC "S") THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `(r2:real) IN S` ASSUME_TAC THENL
   [USE_THEN "S" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `(c:real->A)(&0)`; `u:real^N`; `r:real`]
        MFD_EXP_RADIAL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN
      ASM_SIMP_TAC[];
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `(c:real->A)(&0)`; `u:real^N`; `r:real`]
        MFD_EXP_RADIAL) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(S:real->bool = {}) /\ (!t. t IN S ==> t <= R)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; USE_THEN "S" (fun th -> SIMP_TAC[th])]; ALL_TAC] THEN
  MP_TAC(ISPEC `S:real->bool` SUP) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `Tm = sup(S:real->bool)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `r2 <= Tm /\ Tm <= R` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. &0 <= t /\ t < Tm
        ==> real_interval[&0,t] SUBSET
              mfd_geo_maxint (top,atlas) (g:A->real^N^N) ((c:real->A)(&0)) u /\
            !r. &0 <= r /\ r <= t ==> mfd_geo (top,atlas) g (c(&0)) u r = c r`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `?t''. t'' IN S /\ t < t''` STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
      DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM;
        TAUT `~(p /\ q) <=> p ==> ~q`; REAL_NOT_LT]) THEN
      SUBGOAL_THEN `Tm <= t` MP_TAC THENL [ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    USE_THEN "S" (MP_TAC o SPEC `t'':real`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `real_interval[&0,t'']` THEN
      ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `c:real->A`; `u:real^N`; `R:real`; `Tm:real`]
    CMPRG_STEP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t':real` STRIP_ASSUME_TAC) THENL
   [SUBGOAL_THEN `(t':real) IN S` ASSUME_TAC THENL
     [USE_THEN "S" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `t' <= Tm` MP_TAC THENL [ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC];
    FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Shortest C^1 curves.  The arc-length reparametrization c of               *)
(* a C^1 curve gamma on [0,1] with length = distance on every subinterval    *)
(* (stops allowed) realizes distances, so by CMPRG_CORE the minimizing       *)
(* segment exp_y(s w), 0 <= s <= 1, from y = gamma 0 to gamma 1 runs through *)
(* points of gamma.                                                          *)
(* ========================================================================= *)

let CMPRG_SHORTEST = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
        (!s t. &0 <= s /\ s <= t /\ t <= &1
               ==> mfd_length atlas g gamma s t =
                   mfd_dist (top,atlas) g (gamma s) (gamma t))
        ==> ?w. w IN mfd_exp_dom (top,atlas) g (gamma(&0)) /\
                mfd_exp (top,atlas) g (gamma(&0)) w = gamma(&1) /\
                mfd_tnorm g (gamma(&0)) w = mfd_dist (top,atlas) g (gamma(&0)) (gamma(&1)) /\
                !s. &0 <= s /\ s <= &1
                    ==> s % w IN mfd_exp_dom (top,atlas) g (gamma(&0)) /\
                        ?t. &0 <= t /\ t <= &1 /\
                            mfd_exp (top,atlas) g (gamma(&0)) (s % w) = gamma t`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "short"))))) THEN
  SUBGOAL_THEN `!t. &0 <= t /\ t <= &1 ==> (gamma:real->A) t IN topspace top`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_C1_CURVE_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `&0`; `&1`] THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s t. &0 <= s /\ s <= t /\ t <= &1
                      ==> mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool)
                                           ((gamma:real->A) s) (gamma t)`
  (LABEL_TAC "join") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_C1_CURVE_JOINABLE THEN
    MATCH_MP_TAC GRGD_C1_CURVE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `y = (gamma:real->A)(&0)` THEN
  ABBREV_TAC `R = mfd_dist (top,atlas) (g:A->real^N^N) y (gamma(&1))` THEN
  SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `S = \t. real_integral (real_interval[&0,t])
                        (mfd_speed atlas (g:A->real^N^N) (gamma:real->A) (&0) (&1))` THEN
  SUBGOAL_THEN `!t. &0 <= t /\ t <= &1
                    ==> mfd_length atlas (g:A->real^N^N) (gamma:real->A) (&0) t = S t`
  (LABEL_TAC "LS") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "S" THEN
    MATCH_MP_TAC GRGD_LENGTH_SUBINTERVAL THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s t. &0 <= s /\ s <= t /\ t <= &1
                      ==> mfd_dist (top,atlas) (g:A->real^N^N) ((gamma:real->A) s) (gamma t) =
                          S t - S s`
  (LABEL_TAC "dS") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "short" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th
      (ASSUME `&0 <= s /\ s <= t /\ t <= &1`))]) THEN
    POP_ASSUM STRIP_ASSUME_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `&0`; `s:real`; `t:real`]
      MFD_LENGTH_COMBINE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC GRGD_C1_CURVE_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    STRIP_TAC THEN
    USE_THEN "LS" (MP_TAC o SPEC `s:real`) THEN
    USE_THEN "LS" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_length atlas (g:A->real^N^N) (gamma:real->A) (&0) (&1) = R`
  ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN EXPAND_TAC "y" THEN
    USE_THEN "short" (MP_TAC o SPECL [`&0`; `&1`]) THEN
    REWRITE_TAC[REAL_POS; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(S:real->real)(&0) = &0 /\ S(&1) = R` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "S" THEN REWRITE_TAC[REAL_INTEGRAL_REFL];
      USE_THEN "LS" (MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_POS; REAL_LE_REFL] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s t. &0 <= s /\ s <= t /\ t <= &1 ==> (S:real->real) s <= S t`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "dS" (MP_TAC o SPECL [`s:real`; `t:real`]) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `(gamma:real->A) s`; `(gamma:real->A) t`]
      MFD_DIST_POS_LE) THEN
    ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= R` ASSUME_TAC THENL
   [MP_TAC(ASSUME `!s t. &0 <= s /\ s <= t /\ t <= &1 ==> (S:real->real) s <= S t`) THEN
    DISCH_THEN(MP_TAC o SPECL [`&0`; `&1`]) THEN
    REWRITE_TAC[REAL_POS; REAL_LE_REFL] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `R = &0` THENL
   [SUBGOAL_THEN `(gamma:real->A)(&1) = y` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `y:A`; `(gamma:real->A)(&1)`] MFD_DIST_EQ_0) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [EXPAND_TAC "y" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC;
        MESON_TAC[]];
      ALL_TAC] THEN
    EXISTS_TAC `vec 0:real^N` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `y:A`] MFD_EXP_DOM) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `y:A`] GEOD_TNORM_BASIC) THEN
    ASM_SIMP_TAC[VECTOR_MUL_RZERO] THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[REAL_LE_REFL; REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < R` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(S:real->real) real_continuous_on real_interval[&0,&1]` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    X_GEN_TAC `r:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_WITHINREAL THEN
    EXISTS_TAC `mfd_speed atlas (g:A->real^N^N) (gamma:real->A) (&0) (&1) r` THEN
    MP_TAC(ISPECL [`mfd_speed atlas (g:A->real^N^N) (gamma:real->A) (&0) (&1)`;
                   `&0`; `&1`] REAL_INTEGRAL_HAS_REAL_DERIVATIVE) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC MFD_SPEED_CONTINUOUS THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?tr. !r. &0 <= r /\ r <= R
                         ==> &0 <= tr r /\ tr r <= &1 /\ (S:real->real)(tr r) = r`
  (X_CHOOSE_THEN `tr:real->real` (LABEL_TAC "tr")) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
    X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`S:real->real`; `&0`; `&1`; `r:real`] REAL_IVT_INCREASING) THEN
    ASM_REWRITE_TAC[REAL_POS; IN_REAL_INTERVAL] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s t. &0 <= s /\ s <= R /\ &0 <= t /\ t <= R
          ==> mfd_joinable (top,atlas) ((gamma:real->A)(tr s)) (gamma(tr t)) /\
              mfd_dist (top,atlas) (g:A->real^N^N) (gamma(tr s)) (gamma(tr t)) = abs(t - s)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `!s t. &0 <= s /\ s <= R /\ &0 <= t /\ t <= R /\ tr s <= (tr:real->real) t
            ==> mfd_joinable (top,atlas) ((gamma:real->A)(tr s)) (gamma(tr t)) /\
                mfd_dist (top,atlas) (g:A->real^N^N) (gamma(tr s)) (gamma(tr t)) =
                abs(t - s)`
    ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN STRIP_TAC THEN
      SUBGOAL_THEN `&0 <= (tr:real->real) s /\ tr t <= &1 /\
                    (S:real->real)(tr s) = s /\ S(tr t) = t`
      STRIP_ASSUME_TAC THENL
       [USE_THEN "tr" (fun th ->
          MP_TAC(MATCH_MP th (CONJ (ASSUME `&0 <= s`) (ASSUME `s <= R`))) THEN
          MP_TAC(MATCH_MP th (CONJ (ASSUME `&0 <= t`) (ASSUME `t <= R`)))) THEN
        SIMP_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [USE_THEN "join" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        SUBGOAL_THEN
         `mfd_dist (top,atlas) (g:A->real^N^N) ((gamma:real->A)(tr s)) (gamma(tr t)) =
          (S:real->real)(tr t) - S((tr:real->real) s)`
        SUBST1_TAC THENL
         [USE_THEN "dS" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `(S:real->real)(tr s) <= S((tr:real->real) t)` MP_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
            can (find_term ((=) `S:real->real`)) (concl th) &&
            not(can (find_term ((=) `R:real`)) (concl th)))) THEN
          ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]];
      ALL_TAC] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    DISJ_CASES_TAC(REAL_ARITH `(tr:real->real) s <= tr t \/ tr t <= tr s`) THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `s:real`]) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[MFD_JOINABLE_SYM];
      ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC MFD_DIST_SYM THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (tr:real->real)(&0) /\ tr(&0) <= &1 /\ (S:real->real)(tr(&0)) = &0 /\
                &0 <= tr R /\ tr R <= &1 /\ S(tr R) = R`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "tr" (fun th -> MP_TAC(SPEC `&0` th) THEN MP_TAC(SPEC `R:real` th)) THEN
    REWRITE_TAC[REAL_LE_REFL; ASSUME `&0 <= R`] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A)((tr:real->real)(&0)) = y` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `(gamma:real->A)(&0)`; `(gamma:real->A)(tr(&0))`]
      MFD_DIST_EQ_0) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      USE_THEN "join" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    TRANS_TAC EQ_TRANS `(S:real->real)(tr(&0)) - S(&0)` THEN CONJ_TAC THENL
     [USE_THEN "dS" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL];
      ASM_REWRITE_TAC[REAL_SUB_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A)((tr:real->real) R) = gamma(&1)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `(gamma:real->A)(tr(R:real))`; `(gamma:real->A)(&1)`]
      MFD_DIST_EQ_0) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      USE_THEN "join" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    TRANS_TAC EQ_TRANS `(S:real->real)(&1) - S((tr:real->real) R)` THEN CONJ_TAC THENL
     [USE_THEN "dS" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL];
      ASM_REWRITE_TAC[REAL_SUB_REFL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `\r. (gamma:real->A)((tr:real->real) r)`; `R:real`]
    CMPRG_CORE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `R % (u:real^N)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `y:A`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!r. &0 <= r /\ r <= R
                    ==> r % (u:real^N) IN mfd_exp_dom (top,atlas) (g:A->real^N^N) y /\
                        mfd_exp (top,atlas) g y (r % u) = (gamma:real->A)(tr r)`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `y:A`; `u:real^N`; `r:real`] MFD_EXP_RADIAL) THEN
    SUBGOAL_THEN `r IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) y u` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term (fun t -> try fst(dest_const t) = "mfd_geo_maxint"
                                 with Failure _ -> false)) (concl th) &&
        not(is_forall(concl th)))) THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL];
      ALL_TAC] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[REAL_LE_REFL; REAL_LT_IMP_LE];
    ASM_MESON_TAC[REAL_LE_REFL; REAL_LT_IMP_LE];
    ASM_REWRITE_TAC[REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `&0 <= s * R /\ s * R <= R` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `s * R <= &1 * R ==> s * R <= R`) THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN EXISTS_TAC `(tr:real->real)(s * R)` THEN ASM_MESON_TAC[]]);;


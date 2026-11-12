(* ========================================================================= *)
(* Unit pc_cmp_soul (comparison-geometry layer CMP): the Gromoll-Meyer core  *)
(* CMP_R5_SOUL (Petersen Thm 12.4.1, MT Thm 2.7 positive case).  On a        *)
(* complete connected noncompact 3-manifold with sec > 0 there is a point p  *)
(* such that every other point is regular for d_p.  Route:                   *)
(* - f = sup of the Busemann functions of the rays from p0 (cmp_bsup) is    *)
(*   convex, 1-Lipschitz, 0 at p0 and proper (limits of segments to points  *)
(*   with f bounded are rays along which f is bounded, but f(gamma s) >= s),*)
(*   so it has a minimum point p;                                            *)
(* - f is not strictly convex, but the minimum is unique: on a segment of   *)
(*   minimum points, a near-maximizing ray gamma and a far point gamma(T)    *)
(*   make h = T - d(., gamma T) nearly constant, hence (semiconvexity) with  *)
(*   small barrier slopes, hence (the strict barrier CMPSH_DIST_BARRIER with *)
(*   sec >= k0 > 0 near the segment) uniformly convex: a contradiction;      *)
(* - for x <> p a ray gamma with b(x) > b(p) exists, and the asymptote of   *)
(*   gamma at x is obtuse to every minimizing direction to p (hinge          *)
(*   comparison CMPA_HINGE at x with a far point of the asymptote).          *)
(* The uniform curvature bound on compact balls uses the continuity of       *)
(* mfd_sec_min in 3D (pc_rfa_secmin, pc_rfa_secpres).                        *)
(* ========================================================================= *)

needs "src/pc_cmp_shup.ml";;
needs "src/pc_rfa_secpres.ml";;
needs "src/pc_cmp_pdefs.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Minimizing segments from a point, limits of segments are                  *)
(* rays, and rays from p0 exist on a complete connected noncompact manifold. *)
(* ========================================================================= *)

let CMPSO_SEGMENT = prove
 (`!top atlas (g:A->real^N^N) (p0:A) x.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        p0 IN topspace top /\ mfd_joinable (top,atlas) p0 x /\ ~(x = p0)
        ==> &0 < mfd_dist (top,atlas) g p0 x /\
            ?u. mfd_tnorm g p0 u = &1 /\
                mfd_geo (top,atlas) g p0 u (mfd_dist (top,atlas) g p0 x) = x /\
                !s. &0 <= s /\ s <= mfd_dist (top,atlas) g p0 x
                    ==> mfd_dist (top,atlas) g p0 (mfd_geo (top,atlas) g p0 u s) = s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `l = mfd_dist (top,atlas) (g:A->real^N^N) p0 x` THEN
  SUBGOAL_THEN `&0 < l` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p0:A`; `x:A`] MFD_DIST_EQ_0) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p0:A`; `x:A`] MFD_DIST_POS_LE) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[REAL_LT_LE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p0:A`; `x:A`] MFD_COMPLETE_MINIMIZING_GEODESIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p0:A`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `inv l % (v:real^N)` THEN
  SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) p0 (inv l % v) = &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < l ==> abs l = l`; REAL_MUL_LINV; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p0:A`; `inv l % (v:real^N)`] CMPB_GEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_geo (top,atlas) (g:A->real^N^N) p0 (inv l % v) l = x` ASSUME_TAC THENL
   [SUBGOAL_THEN `mfd_geo (top,atlas) (g:A->real^N^N) p0 (inv l % v) l =
                  mfd_exp (top,atlas) g p0 (l % inv l % v)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  ABBREV_TAC `y = mfd_geo (top,atlas) (g:A->real^N^N) p0 (inv l % v) s` THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) p0 y /\
                mfd_dist (top,atlas) (g:A->real^N^N) p0 y <= s /\
                mfd_joinable (top,atlas) y x /\ mfd_dist (top,atlas) g y x <= l - s`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPECL [`&0`; `s:real`] o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "mfd_joinable"
                               with Failure _ -> false)) (concl th))) THEN
    FIRST_ASSUM(MP_TAC o SPECL [`s:real`; `l:real`] o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "mfd_joinable"
                               with Failure _ -> false)) (concl th))) THEN
    REWRITE_TAC[ASSUME `mfd_geo (top,atlas) (g:A->real^N^N) p0 (inv l % v) (&0) = p0`;
                ASSUME `mfd_geo (top,atlas) (g:A->real^N^N) p0 (inv l % v) s = y`;
                ASSUME `mfd_geo (top,atlas) (g:A->real^N^N) p0 (inv l % v) l = x`] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p0:A`; `y:A`; `x:A`] MFD_DIST_TRIANGLE) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Limits of segments from p0 of lengths at least n are rays. *)

let CMPSO_LIMIT_RAY = prove
 (`!top atlas (g:A->real^N^N) (p0:A) (un:num->real^N) (ll:num->real).
        hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ p0 IN topspace top /\
        (!n. mfd_tnorm g p0 (un n) = &1) /\ (!n. &n <= ll n) /\
        (!n s. &0 <= s /\ s <= ll n
               ==> mfd_dist (top,atlas) g p0 (mfd_geo (top,atlas) g p0 (un n) s) = s)
        ==> ?u (sub:num->num).
              mfd_tnorm g p0 u = &1 /\ (!n. n <= sub n) /\
              cmp_ray (top,atlas) g (mfd_geo (top,atlas) g p0 u) /\
              !r d. &0 < d
                    ==> ?N. !n. N <= n
                            ==> mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p0 u r)
                                  (mfd_geo (top,atlas) g p0 (un(sub n)) r) < d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!n s. mfd_geo (top,atlas) (g:A->real^N^N) p0 ((un:num->real^N) n) s IN topspace top /\
          mfd_exp (top,atlas) g p0 (s % un n) = mfd_geo (top,atlas) g p0 (un n) s`
  (LABEL_TAC "eg") THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p0:A`; `(un:num->real^N) n`] CMPB_GEO_FACTS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n s t. &0 <= s /\ &0 <= t /\ s <= (ll:num->real) n /\ t <= ll n
            ==> mfd_dist (top,atlas) (g:A->real^N^N)
                  (mfd_geo (top,atlas) g p0 ((un:num->real^N) n) s)
                  (mfd_geo (top,atlas) g p0 (un n) t) = abs(t - s)`
  (LABEL_TAC "seg") THENL
   [SUBGOAL_THEN
     `!n s t. &0 <= s /\ s <= t /\ t <= (ll:num->real) n
              ==> mfd_dist (top,atlas) (g:A->real^N^N)
                    (mfd_geo (top,atlas) g p0 ((un:num->real^N) n) s)
                    (mfd_geo (top,atlas) g p0 (un n) t) = t - s`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `p0:A`; `(un:num->real^N) n`] CMPB_GEO_FACTS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "g0") (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "js")))) THEN
      USE_THEN "js" (MP_TAC o SPECL [`s:real`; `t:real`]) THEN
      USE_THEN "js" (MP_TAC o SPECL [`&0`; `s:real`]) THEN
      USE_THEN "g0" (fun th -> REWRITE_TAC[th]) THEN REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `p0:A`;
                     `mfd_geo (top,atlas) (g:A->real^N^N) p0 ((un:num->real^N) n) s`;
                     `mfd_geo (top,atlas) (g:A->real^N^N) p0 ((un:num->real^N) n) t`]
        MFD_DIST_TRIANGLE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      FIRST_ASSUM(MP_TAC o SPECL [`n:num`; `s:real`] o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `ll:num->real`)) (concl th) &&
        not(can (find_term ((=) `abs:real->real`)) (concl th)))) THEN
      FIRST_ASSUM(MP_TAC o SPECL [`n:num`; `t:real`] o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `ll:num->real`)) (concl th) &&
        not(can (find_term ((=) `abs:real->real`)) (concl th)))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    DISJ_CASES_TAC(REAL_ARITH `s <= t \/ t <= s`) THENL
     [ASM_SIMP_TAC[REAL_ARITH `s <= t ==> abs(t - s) = t - s`]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `abs(t - s) = abs(s - t)`] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) p0 ((un:num->real^N) n) s`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) p0 ((un:num->real^N) n) t`]
      MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[REAL_ARITH `t <= s ==> abs(s - t) = s - t`];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p0:A`; `un:num->real^N`] CMPB_DIR_SUBSEQ) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `sub:num->num` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p0:A`; `u:real^N`] CMPB_GEO_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "gtop")
    (CONJUNCTS_THEN2 (LABEL_TAC "ug") (LABEL_TAC "ujs")))) THEN
  SUBGOAL_THEN
   `!r d. &0 < d
          ==> ?N. !n. N <= n
                  ==> mfd_dist (top,atlas) (g:A->real^N^N) (mfd_geo (top,atlas) g p0 u r)
                        (mfd_geo (top,atlas) g p0 ((un:num->real^N)((sub:num->num) n)) r) < d`
  (LABEL_TAC "conv") THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `sub:num->num`)) (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "mfd_exp" with Failure _ -> false))
          (concl th))) THEN
    USE_THEN "ug" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "eg" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. n <= (sub:num->num) n` ASSUME_TAC THENL
   [MP_TAC(SPEC `sub:num->num` MONOTONE_BIGGER) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`u:real^N`; `sub:num->num`] THEN
  ASM_REWRITE_TAC[cmp_ray] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `t:real`] THEN STRIP_TAC THEN
  USE_THEN "ujs" (MP_TAC o SPECL [`s:real`; `t:real`]) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CMPB_LE_EPS THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  USE_THEN "conv" (MP_TAC o SPECL [`s:real`; `e / &2`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1")) THEN
  USE_THEN "conv" (MP_TAC o SPECL [`t:real`; `e / &2`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "N2")) THEN
  MP_TAC(SPEC `max s t` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_THEN `N3:num` ASSUME_TAC) THEN
  USE_THEN "N1" (MP_TAC o SPEC `N1 + N2 + N3:num`) THEN
  USE_THEN "N2" (MP_TAC o SPEC `N1 + N2 + N3:num`) THEN
  REWRITE_TAC[ARITH_RULE `N2 <= N1 + N2 + N3:num /\ N1 <= N1 + N2 + N3`] THEN
  ABBREV_TAC `m = (sub:num->num)(N1 + N2 + N3)` THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `max s t <= (ll:num->real) m` ASSUME_TAC THENL
   [SUBGOAL_THEN `N1 + N2 + N3 <= (m:num)` MP_TAC THENL
     [EXPAND_TAC "m" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_ADD] THEN
    MP_TAC(SPEC `m:num` (ASSUME `!n. &n <= (ll:num->real) n`)) THEN
    MP_TAC(SPEC `N1:num` REAL_POS) THEN MP_TAC(SPEC `N2:num` REAL_POS) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "seg" (MP_TAC o SPECL [`m:num`; `s:real`; `t:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ABBREV_TAC `ys = mfd_geo (top,atlas) (g:A->real^N^N) p0 ((un:num->real^N) m) s` THEN
  ABBREV_TAC `yt = mfd_geo (top,atlas) (g:A->real^N^N) p0 ((un:num->real^N) m) t` THEN
  ABBREV_TAC `xs = mfd_geo (top,atlas) (g:A->real^N^N) p0 u s` THEN
  ABBREV_TAC `xt = mfd_geo (top,atlas) (g:A->real^N^N) p0 u t` THEN
  SUBGOAL_THEN `(ys:A) IN topspace top /\ (yt:A) IN topspace top /\
                (xs:A) IN topspace top /\ (xt:A) IN topspace top`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ys"; "yt"; "xs"; "xt"] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!a b:A. a IN topspace top /\ b IN topspace top
                        ==> mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) a b`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `ys:A`; `xs:A`; `yt:A`] MFD_DIST_TRIANGLE) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `xs:A`; `xt:A`; `yt:A`] MFD_DIST_TRIANGLE) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `ys:A`; `xs:A`] MFD_DIST_SYM) THEN
  ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC);;

let CMPSO_RAY_EXISTS = prove
 (`!top atlas (g:A->real^N^N) (p0:A).
        hausdorff_space top /\ connected_space top /\ ~compact_space top /\
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_complete (top,atlas) g /\ p0 IN topspace top
        ==> ?u. mfd_tnorm g p0 u = &1 /\ cmp_ray (top,atlas) g (mfd_geo (top,atlas) g p0 u)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!n. ?x:A. x IN topspace top /\ &n + &1 <= mfd_dist (top,atlas) (g:A->real^N^N) p0 x`
  MP_TAC THENL
   [X_GEN_TAC `n:num` THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    PURE_REWRITE_TAC[NOT_EXISTS_THM; DE_MORGAN_THM; REAL_NOT_LE] THEN DISCH_TAC THEN
    UNDISCH_TAC `~compact_space (top:A topology)` THEN REWRITE_TAC[compact_space] THEN
    SUBGOAL_THEN `topspace top =
                  mfd_cball (top,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) p0
                    (&n + &1)`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; mfd_cball; IN_ELIM_THM] THEN X_GEN_TAC `y:A` THEN
      EQ_TAC THENL
       [DISCH_TAC THEN CONJ_TAC THENL
         [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
          FIRST_X_ASSUM(MP_TAC o SPEC `y:A`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
        MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]];
      ALL_TAC] THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC GEOH_CBALL_COMPACT THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p0:A`; `p0:A`] MFD_COMPLETE_MINIMIZING_GEODESIC) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
      MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `xx:num->A` (LABEL_TAC "xx")) THEN
  SUBGOAL_THEN
   `!n. ?v. mfd_tnorm (g:A->real^N^N) p0 v = &1 /\
            !s. &0 <= s /\ s <= mfd_dist (top,atlas) g p0 ((xx:num->A) n)
                ==> mfd_dist (top,atlas) g p0 (mfd_geo (top,atlas) g p0 v s) = s`
  MP_TAC THENL
   [X_GEN_TAC `n:num` THEN USE_THEN "xx" (MP_TAC o SPEC `n:num`) THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p0:A`; `(xx:num->A) n`] CMPSO_SEGMENT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
        DISCH_TAC THEN
        USE_THEN "xx" (MP_TAC o CONJUNCT2 o SPEC `n:num`) THEN
        REWRITE_TAC[ASSUME `(xx:num->A) n = p0`] THEN
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `g:A->real^N^N`; `p0:A`] MFD_DIST_REFL) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        MP_TAC(SPEC `n:num` REAL_POS) THEN REAL_ARITH_TAC];
      MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `un:num->real^N` (LABEL_TAC "un")) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p0:A`; `un:num->real^N`;
                 `\n. mfd_dist (top,atlas) (g:A->real^N^N) p0 ((xx:num->A) n)`]
    CMPSO_LIMIT_RAY) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `n:num` THEN USE_THEN "xx" (MP_TAC o SPEC `n:num`) THEN REAL_ARITH_TAC;
    MESON_TAC[]]);;

(* ========================================================================= *)
(* The supremum of the Busemann functions of the rays from p0.               *)
(* On a complete connected manifold with a ray from p0 it is bounded by      *)
(* d(x, p0), approximated by single Busemann functions, 1-Lipschitz, zero at *)
(* p0, at least s at gamma(s) for a ray gamma from p0, and convex along      *)
(* unit geodesics when sec >= 0.                                             *)
(* ========================================================================= *)

let cmp_bsup = new_definition
 `cmp_bsup (top:A topology,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
           (p0:A) (x:A) =
    sup {cmp_busemann (top,atlas) g gamma x | gamma |
         cmp_ray (top,atlas) g gamma /\ gamma(&0) = p0}`;;

let CMPSO_BSUP_BASIC = prove
 (`!top atlas (g:A->real^N^N) (p0:A) x.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        (?gamma. cmp_ray (top,atlas) g gamma /\ gamma(&0) = p0) /\
        mfd_joinable (top,atlas) x p0
        ==> (!gamma. cmp_ray (top,atlas) g gamma /\ gamma(&0) = p0
                     ==> cmp_busemann (top,atlas) g gamma x <= cmp_bsup (top,atlas) g p0 x) /\
            cmp_bsup (top,atlas) g p0 x <= mfd_dist (top,atlas) g x p0 /\
            (!e. &0 < e
                 ==> ?gamma. cmp_ray (top,atlas) g gamma /\ gamma(&0) = p0 /\
                             cmp_bsup (top,atlas) g p0 x - e <
                             cmp_busemann (top,atlas) g gamma x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `{cmp_busemann (top,atlas) (g:A->real^N^N) gamma (x:A) | gamma |
                 cmp_ray (top,atlas) g gamma /\ gamma(&0) = (p0:A)}` SUP) THEN
  REWRITE_TAC[GSYM cmp_bsup] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      EXISTS_TAC `mfd_dist (top,atlas) (g:A->real^N^N) x p0` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `b:real` THEN
      DISCH_THEN(X_CHOOSE_THEN `gam:real->A` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `gam:real->A`; `x:A`] CMPB_SUP) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ub") (LABEL_TAC "lub")) THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `gam:real->A` THEN STRIP_TAC THEN
    USE_THEN "ub" MATCH_MP_TAC THEN EXISTS_TAC `gam:real->A` THEN ASM_REWRITE_TAC[];
    USE_THEN "lub" MATCH_MP_TAC THEN X_GEN_TAC `b:real` THEN
    DISCH_THEN(X_CHOOSE_THEN `gam:real->A` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gam:real->A`; `x:A`] CMPB_SUP) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    USE_THEN "lub" (MP_TAC o SPEC `cmp_bsup (top,atlas) (g:A->real^N^N) p0 x - e`) THEN
    ANTS_TAC THENL
     [X_GEN_TAC `b:real` THEN
      DISCH_THEN(X_CHOOSE_THEN `gam:real->A` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `gam:real->A` o REWRITE_RULE[NOT_EXISTS_THM]) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC]]);;

let CMPSO_BSUP_AT_P0 = prove
 (`!top atlas (g:A->real^N^N) (p0:A).
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        p0 IN topspace top /\
        (?gamma. cmp_ray (top,atlas) g gamma /\ gamma(&0) = p0)
        ==> cmp_bsup (top,atlas) g p0 p0 = &0`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  DISCH_THEN(X_CHOOSE_THEN `gam:real->A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) (p0:A) p0`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPECL [`&0`; `&0`] o CONJUNCT2 o GEN_REWRITE_RULE I [cmp_ray]) THEN
    ASM_SIMP_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p0:A`; `p0:A`] CMPSO_BSUP_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `gam:real->A`) (MP_TAC o CONJUNCT1)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p0:A`] MFD_DIST_REFL) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gam:real->A`; `&0`] CMPB_ON_RAY) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN REAL_ARITH_TAC);;

let CMPSO_BSUP_ON_RAY = prove
 (`!top atlas (g:A->real^N^N) (p0:A) gamma s.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        cmp_ray (top,atlas) g gamma /\ gamma(&0) = p0 /\ &0 <= s
        ==> s <= cmp_bsup (top,atlas) g p0 (gamma s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p0:A`; `(gamma:real->A) s`] CMPSO_BSUP_BASIC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`s:real`; `&0`] o CONJUNCT2 o GEN_REWRITE_RULE I [cmp_ray]) THEN
    ASM_SIMP_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `gamma:real->A` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `s:real`] CMPB_ON_RAY) THEN
  ASM_SIMP_TAC[]);;

let CMPSO_BSUP_LIPSCHITZ = prove
 (`!top atlas (g:A->real^N^N) (p0:A) x y.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        (?gamma. cmp_ray (top,atlas) g gamma /\ gamma(&0) = p0) /\
        mfd_joinable (top,atlas) x p0 /\ mfd_joinable (top,atlas) y p0 /\
        mfd_joinable (top,atlas) x y
        ==> abs(cmp_bsup (top,atlas) g p0 x - cmp_bsup (top,atlas) g p0 y) <=
            mfd_dist (top,atlas) g x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x y:A. mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) x p0 /\
            mfd_joinable (top,atlas) y p0 /\ mfd_joinable (top,atlas) x y
            ==> cmp_bsup (top,atlas) (g:A->real^N^N) p0 x <=
                cmp_bsup (top,atlas) g p0 y + mfd_dist (top,atlas) g x y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CMPB_LE_EPS THEN X_GEN_TAC `e:real` THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p0:A`; `x':A`] CMPSO_BSUP_BASIC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `e:real` o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `gam:real->A` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p0:A`; `y':A`] CMPSO_BSUP_BASIC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `gam:real->A` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gam:real->A`; `x':A`; `y':A`] CMPB_LIPSCHITZ) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b + d /\ b <= a + d ==> abs(a - b) <= d`) THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `y:A`] MFD_DIST_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[MFD_JOINABLE_SYM]);;

let CMPSO_BSUP_CONVEX = prove
 (`!top atlas (g:A->real^N^N) (p0:A) p u a c x.
        hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        (!y a c. y IN topspace top /\ ~collinear {vec 0,a,c}
                 ==> &0 <= mfd_sectional atlas g y a c) /\
        (?gamma. cmp_ray (top,atlas) g gamma /\ gamma(&0) = p0) /\
        p0 IN topspace top /\ p IN topspace top /\ mfd_tnorm g p u = &1 /\
        a < c /\ a <= x /\ x <= c
        ==> cmp_bsup (top,atlas) g p0 (mfd_geo (top,atlas) g p u x) <=
            cmp_bsup (top,atlas) g p0 (mfd_geo (top,atlas) g p u a) +
            (x - a) / (c - a) *
            (cmp_bsup (top,atlas) g p0 (mfd_geo (top,atlas) g p u c) -
             cmp_bsup (top,atlas) g p0 (mfd_geo (top,atlas) g p u a))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `u:real^N`] CMPB_GEO_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `!s. mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool)
                      (mfd_geo (top,atlas) (g:A->real^N^N) p u s) p0`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) p (p0:A)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `l = (x - a) / (c - a)` THEN
  SUBGOAL_THEN `&0 <= l /\ l <= &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_SUB_LT] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC CMPB_LE_EPS THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p0:A`; `mfd_geo (top,atlas) (g:A->real^N^N) p u x`]
    CMPSO_BSUP_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real` o CONJUNCT2 o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `gam:real->A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gam:real->A`; `p:A`; `u:real^N`; `a:real`; `c:real`;
                 `x:real`] CMPB_CONVEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MAP_EVERY (fun t -> MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p0:A`; t] CMPSO_BSUP_BASIC))
   [`mfd_geo (top,atlas) (g:A->real^N^N) p u a`; `mfd_geo (top,atlas) (g:A->real^N^N) p u c`] THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `gam:real->A` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `gam:real->A` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  ABBREV_TAC `Ba = cmp_busemann (top,atlas) (g:A->real^N^N) gam (mfd_geo (top,atlas) g p u a)` THEN
  ABBREV_TAC `Bc = cmp_busemann (top,atlas) (g:A->real^N^N) gam (mfd_geo (top,atlas) g p u c)` THEN
  ABBREV_TAC `Fa = cmp_bsup (top,atlas) (g:A->real^N^N) p0 (mfd_geo (top,atlas) g p u a)` THEN
  ABBREV_TAC `Fc = cmp_bsup (top,atlas) (g:A->real^N^N) p0 (mfd_geo (top,atlas) g p u c)` THEN
  SUBGOAL_THEN `l * Bc <= l * Fc /\ (&1 - l) * Ba <= (&1 - l) * Fa` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* 1-Lipschitz functions are continuous; the Busemann supremum               *)
(* is proper (sec >= 0: segments from p0 to far points of a sublevel set     *)
(* converge to a ray along which it stays bounded, but it is at least s at   *)
(* gamma(s)) and attains its minimum.                                        *)
(* ========================================================================= *)

let CMPSO_LIP_CONTINUOUS = prove
 (`!top atlas (g:A->real^N^N) (f:A->real).
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        (!x y. x IN topspace top /\ y IN topspace top
               ==> abs(f x - f y) <= mfd_dist (top,atlas) g x y)
        ==> continuous_map (top,euclideanreal) f`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM MTOPOLOGY_REAL_EUCLIDEAN_METRIC; CONTINUOUS_MAP_TO_METRIC] THEN
  REWRITE_TAC[IN_MBALL; REAL_EUCLIDEAN_METRIC; IN_UNIV] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN X_GEN_TAC `r:real` THEN DISCH_TAC THEN
  EXISTS_TAC `{y:A | y IN topspace top /\
                     mfd_dist (top,atlas) (g:A->real^N^N) x y IN {z:real | z < r}}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN EXISTS_TAC `euclideanreal` THEN
    REWRITE_TAC[GSYM REAL_OPEN_IN; REAL_OPEN_HALFSPACE_LT] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] MFD_DIST_CONTINUOUS_RIGHT) THEN
    ASM_REWRITE_TAC[ETA_AX];
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[MFD_DIST_REFL];
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `y:A` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `y:A`]) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

let CMPSO_BSUP_CONT = prove
 (`!top atlas (g:A->real^N^N) (p0:A).
        connected_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ p0 IN topspace top /\
        (?gamma. cmp_ray (top,atlas) g gamma /\ gamma(&0) = p0)
        ==> continuous_map (top,euclideanreal) (cmp_bsup (top,atlas) g p0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CMPSO_LIP_CONTINUOUS THEN
  MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CMPSO_BSUP_LIPSCHITZ THEN ASM_SIMP_TAC[MFD_JOINABLE_CONNECTED] THEN
  ASM_MESON_TAC[]);;

let CMPSO_BSUP_PROPER = prove
 (`!top atlas (g:A->real^N^N) (p0:A) a.
        hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        (!y a c. y IN topspace top /\ ~collinear {vec 0,a,c}
                 ==> &0 <= mfd_sectional atlas g y a c) /\
        p0 IN topspace top /\ (?gamma. cmp_ray (top,atlas) g gamma /\ gamma(&0) = p0)
        ==> ?R. !x. x IN topspace top /\ cmp_bsup (top,atlas) g p0 x <= a
                    ==> mfd_dist (top,atlas) g p0 x <= R`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  PURE_REWRITE_TAC[NOT_EXISTS_THM; NOT_FORALL_THM; NOT_IMP; REAL_NOT_LE] THEN
  DISCH_THEN(MP_TAC o GEN `n:num` o SPEC `&n + &1`) THEN REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `xx:num->A` (LABEL_TAC "xx")) THEN
  SUBGOAL_THEN `!x:A. x IN topspace top ==> mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) p0 x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. ?v. mfd_tnorm (g:A->real^N^N) p0 v = &1 /\
            mfd_geo (top,atlas) g p0 v (mfd_dist (top,atlas) g p0 ((xx:num->A) n)) = xx n /\
            !s. &0 <= s /\ s <= mfd_dist (top,atlas) g p0 (xx n)
                ==> mfd_dist (top,atlas) g p0 (mfd_geo (top,atlas) g p0 v s) = s`
  MP_TAC THENL
   [X_GEN_TAC `n:num` THEN USE_THEN "xx" (MP_TAC o SPEC `n:num`) THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p0:A`; `(xx:num->A) n`] CMPSO_SEGMENT) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN DISCH_TAC THEN
      UNDISCH_TAC `&n + &1 < mfd_dist (top,atlas) (g:A->real^N^N) p0 ((xx:num->A) n)` THEN
      REWRITE_TAC[ASSUME `(xx:num->A) n = p0`] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `p0:A`] MFD_DIST_REFL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      MP_TAC(SPEC `n:num` REAL_POS) THEN REAL_ARITH_TAC;
      MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `un:num->real^N` (LABEL_TAC "un")) THEN
  ABBREV_TAC `ll = \n. mfd_dist (top,atlas) (g:A->real^N^N) p0 ((xx:num->A) n)` THEN
  SUBGOAL_THEN `!n. &n + &1 <= (ll:num->real) n` ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN EXPAND_TAC "ll" THEN USE_THEN "xx" (MP_TAC o SPEC `n:num`) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p0:A`; `un:num->real^N`; `ll:num->real`]
    CMPSO_LIMIT_RAY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `ll:num->real`)) (concl th))) THEN REAL_ARITH_TAC;
      EXPAND_TAC "ll" THEN REWRITE_TAC[] THEN USE_THEN "un" (fun th -> SIMP_TAC[th])];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `sub:num->num` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `A0 = max a (&0)` THEN
  SUBGOAL_THEN
   `!n r. &0 <= r /\ r <= (ll:num->real) n
          ==> cmp_bsup (top,atlas) (g:A->real^N^N) p0
                (mfd_geo (top,atlas) g p0 ((un:num->real^N) n) r) <= A0`
  (LABEL_TAC "fb") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `&0 < (ll:num->real) n` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `ll:num->real`)) (concl th) &&
        not(can (find_term ((=) `sub:num->num`)) (concl th)))) THEN
      MP_TAC(SPEC `n:num` REAL_POS) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p0:A`; `p0:A`; `(un:num->real^N) n`; `&0`;
                   `(ll:num->real) n`; `r:real`] CMPSO_BSUP_CONVEX) THEN
    ANTS_TAC THENL [USE_THEN "un" (fun th -> ASM_REWRITE_TAC[th]) THEN ASM_MESON_TAC[];
                    ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p0:A`; `(un:num->real^N) n`] CMPB_GEO_FACTS) THEN
    ANTS_TAC THENL [USE_THEN "un" (fun th -> ASM_REWRITE_TAC[th]); ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p0:A`] CMPSO_BSUP_AT_P0) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `mfd_geo (top,atlas) (g:A->real^N^N) p0 ((un:num->real^N) n) ((ll:num->real) n) =
                  (xx:num->A) n` SUBST1_TAC THENL
     [EXPAND_TAC "ll" THEN USE_THEN "un" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_RZERO; REAL_ADD_LID] THEN
    SUBGOAL_THEN `&0 <= r / (ll:num->real) n /\ r / ll n <= &1` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    USE_THEN "xx" (MP_TAC o SPEC `n:num`) THEN STRIP_TAC THEN
    SUBGOAL_THEN `r / (ll:num->real) n * cmp_bsup (top,atlas) (g:A->real^N^N) p0 ((xx:num->A) n) <=
                  r / ll n * A0`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "A0" THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `r / (ll:num->real) n * A0 <= &1 * A0` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "A0" THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `s = A0 + &2` THEN
  SUBGOAL_THEN `&0 <= A0` ASSUME_TAC THENL [EXPAND_TAC "A0" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `&1`] o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `sub:num->num`)) (concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "mfd_dist" with Failure _ -> false))
        (concl th))) THEN
  REWRITE_TAC[REAL_LT_01] THEN DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  MP_TAC(SPEC `s:real` REAL_ARCH_SIMPLE) THEN DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N1 + N2:num`) THEN REWRITE_TAC[LE_ADD] THEN
  ABBREV_TAC `m = (sub:num->num)(N1 + N2)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `s <= (ll:num->real) m` ASSUME_TAC THENL
   [SUBGOAL_THEN `N1 + N2 <= (m:num)` MP_TAC THENL
     [EXPAND_TAC "m" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_ADD] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `ll:num->real`)) (concl th) &&
      not(can (find_term ((=) `sub:num->num`)) (concl th)) &&
      not(can (find_term ((=) `un:num->real^N`)) (concl th)))) THEN
    MP_TAC(SPEC `N1:num` REAL_POS) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "fb" (MP_TAC o SPECL [`m:num`; `s:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p0:A`; `u:real^N`] CMPB_GEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p0:A`; `mfd_geo (top,atlas) (g:A->real^N^N) p0 u`; `s:real`]
    CMPSO_BSUP_ON_RAY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p0:A`; `mfd_geo (top,atlas) (g:A->real^N^N) p0 u s`;
                 `mfd_geo (top,atlas) (g:A->real^N^N) p0 ((un:num->real^N) m) s`]
    CMPSO_BSUP_LIPSCHITZ) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN `mfd_geo (top,atlas) (g:A->real^N^N) p0 ((un:num->real^N) m) s IN topspace top`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `p0:A`; `(un:num->real^N) m`] CMPB_GEO_FACTS) THEN
      ANTS_TAC THENL [USE_THEN "un" (fun th -> ASM_REWRITE_TAC[th]); SIMP_TAC[]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[MFD_JOINABLE_CONNECTED] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let CMPSO_BSUP_MIN = prove
 (`!top atlas (g:A->real^N^N) (p0:A).
        hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        (!y a c. y IN topspace top /\ ~collinear {vec 0,a,c}
                 ==> &0 <= mfd_sectional atlas g y a c) /\
        p0 IN topspace top /\ (?gamma. cmp_ray (top,atlas) g gamma /\ gamma(&0) = p0)
        ==> ?p. p IN topspace top /\
                !x. x IN topspace top
                    ==> cmp_bsup (top,atlas) g p0 p <= cmp_bsup (top,atlas) g p0 x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p0:A`; `&0`] CMPSO_BSUP_PROPER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `R:real`) THEN
  SUBGOAL_THEN `cmp_bsup (top,atlas) (g:A->real^N^N) p0 p0 = &0` ASSUME_TAC THENL
   [MATCH_MP_TAC CMPSO_BSUP_AT_P0 THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(p0:A) IN mfd_cball (top,atlas) (g:A->real^N^N) p0 R` ASSUME_TAC THENL
   [REWRITE_TAC[mfd_cball; IN_ELIM_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `cmp_bsup (top,atlas) (g:A->real^N^N) p0`;
                 `mfd_cball (top,atlas) (g:A->real^N^N) p0 R`] RFA_CMAP_COMPACT_MIN) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CMPSO_BSUP_CONT THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC GEOH_CBALL_COMPACT THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `p0:A`; `p0:A`] MFD_COMPLETE_MINIMIZING_GEODESIC) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
        MESON_TAC[]];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `p:A` THEN CONJ_TAC THENL
   [UNDISCH_TAC `(p:A) IN mfd_cball (top,atlas) (g:A->real^N^N) p0 R` THEN
    REWRITE_TAC[mfd_cball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
    ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  ASM_CASES_TAC `cmp_bsup (top,atlas) (g:A->real^N^N) p0 x <= &0` THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[mfd_cball; IN_ELIM_THM] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    FIRST_X_ASSUM(MP_TAC o SPEC `p0:A` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "mfd_cball" with Failure _ -> false))
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The regular direction.  If b(x) > b(p) for the Busemann                   *)
(* function b of a ray, the initial vector v of the asymptote of the ray at  *)
(* x is obtuse to every minimizing vector w from x to p: with d = |w| and    *)
(* A = b(x) - b(p), b(exp_x(t v)) = b(x) + t gives d(exp_x(t v), p) >= t + A *)
(* and the hinge comparison CMPA_HINGE at x gives d(exp_x(t v), p)^2 <=      *)
(* t^2 + d^2 - 2 t <v, w>; at t = d^2/A this forces <v, w> < 0.              *)
(* ========================================================================= *)

let CMPSO_REGULAR_DIR = prove
 (`!top atlas (g:A->real^N^N) gamma (p:A) x.
        hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        (!y a c. y IN topspace top /\ ~collinear {vec 0,a,c}
                 ==> &0 <= mfd_sectional atlas g y a c) /\
        cmp_ray (top,atlas) g gamma /\ p IN topspace top /\ x IN topspace top /\
        cmp_busemann (top,atlas) g gamma p < cmp_busemann (top,atlas) g gamma x
        ==> ?v. !w. w IN mfd_exp_dom (top,atlas) g x /\
                    mfd_exp (top,atlas) g x w = p /\
                    mfd_tnorm g x w = mfd_dist (top,atlas) g x p
                    ==> v dot (g x ** w) < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(gamma:real->A)(&0) IN topspace top` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `&0` o CONJUNCT1 o GEN_REWRITE_RULE I [cmp_ray]) THEN
    REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a b:A. a IN topspace top /\ b IN topspace top
                        ==> mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) a b`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `x:A`] CMPB_ASYMPTOTE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `x:A`; `u:real^N`] CMPB_ASYMPTOTE_RAY) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_TAC] THEN
  EXISTS_TAC `u:real^N` THEN X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `u:real^N`] CMPB_GEO_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `d = mfd_dist (top,atlas) (g:A->real^N^N) x p` THEN
  ABBREV_TAC `A0 = cmp_busemann (top,atlas) (g:A->real^N^N) gamma x -
                   cmp_busemann (top,atlas) g gamma p` THEN
  SUBGOAL_THEN `&0 < A0` ASSUME_TAC THENL [EXPAND_TAC "A0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `p:A`] MFD_DIST_EQ_0) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `p:A`] MFD_DIST_POS_LE) THEN
    ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `~(x:A = p)` (fun th -> REWRITE_TAC[th]) THENL
     [DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `t = d pow 2 / A0` THEN
  SUBGOAL_THEN `&0 < t /\ &2 * t * A0 = &2 * d pow 2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_POW_LT];
      UNDISCH_TAC `&0 < A0` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `u:real^N`; `inv d % (w:real^N)`; `t:real`;
                 `d:real`] CMPA_HINGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < d ==> abs d = d`; REAL_MUL_LINV; REAL_LT_IMP_NZ;
                 REAL_LT_IMP_LE] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`&0`; `t:real`] o CONJUNCT2 o
      GEN_REWRITE_RULE I [cmp_ray]) THEN
    ASM_SIMP_TAC[REAL_LE_REFL; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_RMUL] THEN
  ABBREV_TAC `q = mfd_geo (top,atlas) (g:A->real^N^N) x u t` THEN DISCH_TAC THEN
  SUBGOAL_THEN `t + A0 <= mfd_dist (top,atlas) (g:A->real^N^N) q p` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `q:A`; `p:A`] CMPB_LIPSCHITZ) THEN
    SUBGOAL_THEN `(q:A) IN topspace top` ASSUME_TAC THENL
     [EXPAND_TAC "q" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `cmp_busemann (top,atlas) (g:A->real^N^N) gamma q =
                  cmp_busemann (top,atlas) g gamma x + t`
    SUBST1_TAC THENL
     [EXPAND_TAC "q" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `cmp_busemann (top,atlas) (g:A->real^N^N) gamma x -
                 cmp_busemann (top,atlas) g gamma p = A0` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `(&0 <= y ==> F) ==> y < &0`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `(t + A0) pow 2 <= mfd_dist (top,atlas) (g:A->real^N^N) q p pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= t * ((u:real^N) dot ((g:A->real^N^N) x ** w))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < A0 pow 2` MP_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  UNDISCH_TAC `mfd_dist (top,atlas) (g:A->real^N^N) q p pow 2 <=
               t pow 2 + d pow 2 - &2 * t * d * inv d * ((u:real^N) dot (g x ** w))` THEN
  SUBGOAL_THEN `t * d * inv d * ((u:real^N) dot ((g:A->real^N^N) x ** w)) =
                t * (u dot (g x ** w))` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < d` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MP_TAC(SPEC `d:real` REAL_LE_POW_2) THEN
  UNDISCH_TAC `&2 * t * A0 = &2 * d pow 2` THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Strict convexity of t - d(., gamma T) along a geodesic.                   *)
(* The slope of an upper barrier D of F at t0 lies between the one-sided    *)
(* growth rates of F (CMPSO_SLOPE_BOUND).  If t - d(sigma s, gamma T) is    *)
(* nearly constant and semiconvex on [a', c'], the barrier slopes on [a, c] *)
(* are small, so the strict barrier CMPSH_DIST_BARRIER (sec >= k0 on the     *)
(* ew-balls) has second derivative <= -mu, and CMPA_CALABI gives the strict *)
(* chord inequality with constant mu on [a, c].                              *)
(* ========================================================================= *)

let CMPSO_SLOPE_BOUND = prove
 (`!(FF:real->real) D D' t0 d K1 K2.
        &0 < d /\ (D has_real_derivative D') (atreal t0) /\ D t0 = FF t0 /\
        (!s. abs(s - t0) < d ==> FF s <= D s) /\
        (!u. &0 < u /\ u < d ==> FF t0 - K1 * u <= FF(t0 + u)) /\
        (!u. &0 < u /\ u < d ==> FF t0 - K2 * u <= FF(t0 - u))
        ==> --K1 <= D' /\ D' <= K2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `((D:real->real) has_real_derivative D') (atreal t0)` THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_ATREAL; REALLIM_ATREAL] THEN DISCH_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `(~(a <= b) ==> F) ==> a <= b`) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `--K1 - D'` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `D':real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `u = min d e / &2` THEN
    SUBGOAL_THEN `&0 < u /\ u < d /\ u < e` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "u" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t0 + u`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `(t0 + u) - t0 = u`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `((D:real->real)(t0 + u) - D t0) / u < --K1` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `--K1 * u <= (D:real->real)(t0 + u) - D t0` ASSUME_TAC THENL
     [SUBGOAL_THEN `(FF:real->real)(t0 + u) <= D(t0 + u)` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(FF:real->real) t0 - K1 * u <= FF(t0 + u)` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `((D:real->real)(t0 + u) - D t0) / u < --K1` THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `(~(a <= b) ==> F) ==> a <= b`) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `D' - K2` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `D':real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `u = min d e / &2` THEN
    SUBGOAL_THEN `&0 < u /\ u < d /\ u < e` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "u" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t0 - u`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `(t0 - u) - t0 = --u`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `K2 < ((D:real->real) t0 - D(t0 - u)) / u` ASSUME_TAC THENL
     [SUBGOAL_THEN `((D:real->real)(t0 - u) - D t0) / --u = (D t0 - D(t0 - u)) / u`
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [UNDISCH_TAC `&0 < u` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(D:real->real) t0 - D(t0 - u) <= K2 * u` ASSUME_TAC THENL
     [SUBGOAL_THEN `(FF:real->real)(t0 - u) <= D(t0 - u)` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(FF:real->real) t0 - K2 * u <= FF(t0 - u)` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `K2 < ((D:real->real) t0 - D(t0 - u)) / u` THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC]);;

(* One-sided growth bounds of a nearly constant semiconvex function. *)

let CMPSO_SEMI_SLOPE = prove
 (`!(h:real->real) a' c' t0 m del eta.
        a' < t0 /\ t0 < c' /\ &0 <= eta /\
        (!x1 x2 x. a' <= x1 /\ x1 < x2 /\ x2 <= c' /\ x1 <= x /\ x <= x2
                   ==> h x <= h x1 + (x - x1) / (x2 - x1) * (h x2 - h x1) +
                              eta * (x - x1) * (x2 - x)) /\
        (!s. a' <= s /\ s <= c' ==> h s <= m) /\ m - del <= h t0
        ==> (!u. &0 < u /\ u <= c' - t0
                 ==> h(t0 + u) <= h t0 + u * (del / (c' - t0) + eta * (c' - a'))) /\
            (!u. &0 < u /\ u <= t0 - a'
                 ==> h(t0 - u) <= h t0 + u * (del / (t0 - a') + eta * (c' - a')))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN X_GEN_TAC `u:real` THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`t0:real`; `c':real`; `t0 + u`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `eta:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `(t0 + u) - t0 = u`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(h:real->real) c' <= m` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `u / (c' - t0) * ((h:real->real) c' - h t0) <= u * (del / (c' - t0))`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `u * del / (c' - t0) = u / (c' - t0) * del` SUBST1_TAC THENL
       [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[GSYM real_div] THEN
      SUBGOAL_THEN `u * del / (c' - t0) = u / (c' - t0) * del` SUBST1_TAC THENL
       [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `eta * u * (c' - (t0 + u)) <= u * (eta * (c' - a'))` ASSUME_TAC THENL
     [SUBGOAL_THEN `eta * u * (c' - (t0 + u)) = u * (eta * (c' - (t0 + u)))` SUBST1_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPECL [`a':real`; `t0:real`; `t0 - u`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `eta:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(h:real->real) a' <= m` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(t0 - u - a') / (t0 - a') = &1 - u / (t0 - a')`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [SUBGOAL_THEN `~(t0 - a' = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    SUBGOAL_THEN `u / (t0 - a') * ((h:real->real) a' - h t0) <= u * (del / (t0 - a'))`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `u * del / (t0 - a') = u / (t0 - a') * del` SUBST1_TAC THENL
       [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[GSYM real_div] THEN
      SUBGOAL_THEN `u * del / (t0 - a') = u / (t0 - a') * del` SUBST1_TAC THENL
       [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `eta * (t0 - u - a') * (t0 - (t0 - u)) <= u * (eta * (c' - a'))`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `eta * (t0 - u - a') * (t0 - (t0 - u)) = u * (eta * (t0 - u - a'))`
      SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC]);;

(* Semiconvexity of t - d(., gamma Tm) along sigma on all subintervals of   *)
(* [a', c'] with the constant of [a', c'].                                   *)

let CMPSO_SEMI_UNIFORM = prove
 (`!top atlas (g:A->real^N^N) gamma (p:A) u a' c' Tm.
        hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        (!y a c. y IN topspace top /\ ~collinear {vec 0,a,c}
                 ==> &0 <= mfd_sectional atlas g y a c) /\
        cmp_ray (top,atlas) g gamma /\ p IN topspace top /\ mfd_tnorm g p u = &1 /\
        &0 <= Tm /\
        mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u a') (gamma(&0)) + (c' - a') < Tm
        ==> !x1 x2 x. a' <= x1 /\ x1 < x2 /\ x2 <= c' /\ x1 <= x /\ x <= x2
              ==> Tm - mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u x) (gamma Tm) <=
                  (Tm - mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u x1) (gamma Tm)) +
                  (x - x1) / (x2 - x1) *
                  ((Tm - mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u x2) (gamma Tm)) -
                   (Tm - mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u x1) (gamma Tm))) +
                  inv(Tm - (mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u a') (gamma(&0)) +
                           (c' - a'))) * (x - x1) * (x2 - x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `u:real^N`] CMPB_GEO_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A)(&0) IN topspace top` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `&0` o CONJUNCT1 o GEN_REWRITE_RULE I [cmp_ray]) THEN
    REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a b:A. a IN topspace top /\ b IN topspace top
                        ==> mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) a b`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_dist (top,atlas) (g:A->real^N^N) (mfd_geo (top,atlas) g p u x1) (gamma(&0)) +
    (x2 - x1) <=
    mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u a') (gamma(&0)) + (c' - a')`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `mfd_geo (top,atlas) (g:A->real^N^N) p u x1`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) p u a'`; `(gamma:real->A)(&0)`]
      MFD_DIST_TRIANGLE) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `mfd_geo (top,atlas) (g:A->real^N^N) p u x1`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) p u a'`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a':real`; `x1:real`] o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "mfd_joinable"
                               with Failure _ -> false)) (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "real_abs"
                               with Failure _ -> false)) (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `p:A`; `u:real^N`; `x1:real`; `x2:real`;
                 `Tm:real`] CMPB_SEMICONVEX) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `c <= d ==> a <= b + e + c ==> a <= b + e + d`) THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]);;

(* The strict barrier at an interior point t0 of [a, c]. *)

let CMPSO_STRICT_BARRIER = prove
 (`!top atlas (g:A->real^N^N) gamma (p:A) u a' a c c' Tm m del k0 ew t0.
        hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        (!y a c. y IN topspace top /\ ~collinear {vec 0,a,c}
                 ==> &0 <= mfd_sectional atlas g y a c) /\
        cmp_ray (top,atlas) g gamma /\ p IN topspace top /\ mfd_tnorm g p u = &1 /\
        a' < a /\ a < c /\ c < c' /\ &0 <= Tm /\
        mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u a') (gamma(&0)) + (c' - a') < Tm /\
        (!s. a' <= s /\ s <= c'
             ==> Tm - mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u s) (gamma Tm) <= m) /\
        (!s. a <= s /\ s <= c
             ==> m - del <=
                 Tm - mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u s) (gamma Tm)) /\
        del / (a - a') +
        inv(Tm - (mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u a') (gamma(&0)) +
                 (c' - a'))) * (c' - a') <= &1 / &2 /\
        del / (c' - c) +
        inv(Tm - (mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u a') (gamma(&0)) +
                 (c' - a'))) * (c' - a') <= &1 / &2 /\
        &0 < ew /\
        (!t0 y a1 c1. a <= t0 /\ t0 <= c /\ y IN topspace top /\
                      mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u t0) y <= ew /\
                      ~collinear {vec 0,a1,c1}
                      ==> k0 <= mfd_sectional atlas g y a1 c1) /\
        (!t0. a <= t0 /\ t0 <= c
              ==> &4 * ew <=
                  mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u t0) (gamma Tm) /\
                  &16 <= k0 * ew *
                         mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u t0) (gamma Tm)) /\
        a < t0 /\ t0 < c
        ==> ?d bf bf' bf2.
              &0 < d /\
              (!s. abs(s - t0) < d ==> (bf has_real_derivative bf'(s)) (atreal s)) /\
              (bf' has_real_derivative bf2) (atreal t0) /\ bf2 <= &0 /\
              bf t0 = mfd_dist (top,atlas) g (gamma Tm) (mfd_geo (top,atlas) g p u t0) - Tm -
                      --(k0 * ew / &2) / &2 * t0 pow 2 /\
              (!s. abs(s - t0) < d
                   ==> mfd_dist (top,atlas) g (gamma Tm) (mfd_geo (top,atlas) g p u s) - Tm -
                       --(k0 * ew / &2) / &2 * s pow 2 <= bf s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `gamma:real->A`; `p:A`; `u:real^N`; `a':real`; `c':real`; `Tm:real`]
    CMPSO_SEMI_UNIFORM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "semi")] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `u:real^N`] CMPB_GEO_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) Tm IN topspace top` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `Tm:real` o CONJUNCT1 o GEN_REWRITE_RULE I [cmp_ray]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `sigma = mfd_geo (top,atlas) (g:A->real^N^N) p u` THEN
  ABBREV_TAC `eta = inv(Tm - (mfd_dist (top,atlas) (g:A->real^N^N) ((sigma:real->A) a')
                                (gamma(&0)) + (c' - a')))` THEN
  SUBGOAL_THEN `&0 <= eta` ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= del` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `a:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `del:real`)) (concl th))) THEN
    FIRST_ASSUM(MP_TAC o SPEC `a:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `m:real`)) (concl th) &&
      not(can (find_term ((=) `del:real`)) (concl th)))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `u:real^N`; `t0:real`; `(gamma:real->A) Tm`;
                 `k0:real`; `ew:real`] CMPSH_DIST_BARRIER) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM(MP_TAC o SPEC `t0:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `&16`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      REPEAT STRIP_TAC THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `k0:real`)) (concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "mfd_sectional"
                                 with Failure _ -> false)) (concl th))) THEN
      EXISTS_TAC `t0:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`d:real`; `D:real->real`; `D':real->real`; `D2:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!s. mfd_dist (top,atlas) (g:A->real^N^N) ((gamma:real->A) Tm)
                      ((sigma:real->A) s) =
                    mfd_dist (top,atlas) g (sigma s) (gamma Tm)`
  (LABEL_TAC "sym") THENL
   [GEN_TAC THEN MATCH_MP_TAC MFD_DIST_SYM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "sym" (fun th -> REWRITE_TAC[th]) THEN
  ABBREV_TAC `K1 = del / (c' - t0) + eta * (c' - a')` THEN
  ABBREV_TAC `K2 = del / (t0 - a') + eta * (c' - a')` THEN
  MP_TAC(ISPECL [`\s. Tm - mfd_dist (top,atlas) (g:A->real^N^N) ((sigma:real->A) s)
                             ((gamma:real->A) Tm)`;
                 `a':real`; `c':real`; `t0:real`; `m:real`; `del:real`; `eta:real`]
    CMPSO_SEMI_SLOPE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[];
      USE_THEN "semi" ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `del:real`)) (concl th))) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "gr") (LABEL_TAC "gl")) THEN
  MP_TAC(ISPECL [`\s. mfd_dist (top,atlas) (g:A->real^N^N) ((sigma:real->A) s)
                        ((gamma:real->A) Tm)`;
                 `D:real->real`; `(D':real->real) t0`; `t0:real`;
                 `min d (min (t0 - a') (c' - t0))`; `K1:real`; `K2:real`]
    CMPSO_SLOPE_BOUND) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC;
      FIRST_ASSUM(MP_TAC o SPEC `t0:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `D':real->real`)) (concl th))) THEN
      REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      X_GEN_TAC `s:real` THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `D:real->real`)) (concl th) &&
        not(can (find_term ((=) `D':real->real`)) (concl th)))) THEN
      USE_THEN "sym" (fun th -> REWRITE_TAC[th]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      X_GEN_TAC `v:real` THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
      USE_THEN "gr" (MP_TAC o SPEC `v:real`) THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      X_GEN_TAC `v:real` THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
      USE_THEN "gl" (MP_TAC o SPEC `v:real`) THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
    STRIP_TAC] THEN
  SUBGOAL_THEN `K1 <= &1 / &2 /\ K2 <= &1 / &2` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["K1"; "K2"] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `!y. x <= y /\ y + z <= h ==> x + z <= h`) THEN
      EXISTS_TAC `del / (c' - c)` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `!y. x <= y /\ y + z <= h ==> x + z <= h`) THEN
      EXISTS_TAC `del / (a - a')` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(D':real->real) t0 pow 2 <= &1 / &4` ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 / &4 = (&1 / &2) pow 2` SUBST1_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < mfd_dist (top,atlas) (g:A->real^N^N) ((sigma:real->A) t0) ((gamma:real->A) Tm) /\
    &16 <= k0 * ew * mfd_dist (top,atlas) g (sigma t0) (gamma Tm)`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `t0:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `&16`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `L = mfd_dist (top,atlas) (g:A->real^N^N) ((sigma:real->A) t0)
                    ((gamma:real->A) Tm)` THEN
  SUBGOAL_THEN `&4 / L <= k0 * ew / &4` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= k0 * ew` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN PURE_REWRITE_TAC[REAL_NOT_LE] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(k0 * ew) * L < &0 * L` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_LZERO; GSYM REAL_MUL_ASSOC] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&3 / &4) * (k0 * ew) <= (k0 * ew) * (&1 - (D':real->real) t0 pow 2)`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `K = --(k0 * ew / &2)` THEN
  MAP_EVERY EXISTS_TAC [`d:real`; `\s. (D:real->real) s - Tm - K / &2 * s pow 2`;
                        `\s. (D':real->real) s - K * s`; `D2 - K`] THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN MATCH_MP_TAC CMPB_SHIFT_DERIV1 THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC CMPB_SHIFT_DERIV2 THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `D2 <= &4 / L - k0 * ew * (&1 - (D':real->real) t0 pow 2)` THEN
    EXPAND_TAC "K" THEN
    SUBGOAL_THEN `k0 * ew * (&1 - (D':real->real) t0 pow 2) =
                  (k0 * ew) * (&1 - D' t0 pow 2)` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> x - Tm - k <= y - Tm - k`) THEN
    FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `D:real->real`)) (concl th) &&
      not(can (find_term ((=) `D':real->real`)) (concl th)))) THEN
    USE_THEN "sym" (fun th -> REWRITE_TAC[th]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]]);;

(* The strict chord inequality on [a, c]. *)

let CMPSO_STRICT_CHORD = prove
 (`!top atlas (g:A->real^N^N) gamma (p:A) u a' a c c' Tm m del k0 ew.
        hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        (!y a c. y IN topspace top /\ ~collinear {vec 0,a,c}
                 ==> &0 <= mfd_sectional atlas g y a c) /\
        cmp_ray (top,atlas) g gamma /\ p IN topspace top /\ mfd_tnorm g p u = &1 /\
        a' < a /\ a < c /\ c < c' /\ &0 <= Tm /\
        mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u a') (gamma(&0)) + (c' - a') < Tm /\
        (!s. a' <= s /\ s <= c'
             ==> Tm - mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u s) (gamma Tm) <= m) /\
        (!s. a <= s /\ s <= c
             ==> m - del <=
                 Tm - mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u s) (gamma Tm)) /\
        del / (a - a') +
        inv(Tm - (mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u a') (gamma(&0)) +
                 (c' - a'))) * (c' - a') <= &1 / &2 /\
        del / (c' - c) +
        inv(Tm - (mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u a') (gamma(&0)) +
                 (c' - a'))) * (c' - a') <= &1 / &2 /\
        &0 < ew /\
        (!t0 y a1 c1. a <= t0 /\ t0 <= c /\ y IN topspace top /\
                      mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u t0) y <= ew /\
                      ~collinear {vec 0,a1,c1}
                      ==> k0 <= mfd_sectional atlas g y a1 c1) /\
        (!t0. a <= t0 /\ t0 <= c
              ==> &4 * ew <=
                  mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u t0) (gamma Tm) /\
                  &16 <= k0 * ew *
                         mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u t0) (gamma Tm))
        ==> !x. a <= x /\ x <= c
                ==> Tm - mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u x) (gamma Tm) <=
                    (Tm - mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u a) (gamma Tm)) +
                    (x - a) / (c - a) *
                    ((Tm - mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u c) (gamma Tm)) -
                     (Tm - mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u a) (gamma Tm))) -
                    (k0 * ew / &4) * (x - a) * (c - x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`] MFD_HOPF_RINOW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "max" o CONJUNCT2) THEN
  SUBGOAL_THEN `mfd_geo_maxint (top,atlas) (g:A->real^N^N) p u = (:real)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `u:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(gamma:real->A) Tm IN topspace top` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `Tm:real` o CONJUNCT1 o GEN_REWRITE_RULE I [cmp_ray]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\s. mfd_dist (top,atlas) (g:A->real^N^N) ((gamma:real->A) Tm)
                         (mfd_geo (top,atlas) g p u s) - Tm -
                       --(k0 * ew / &2) / &2 * s pow 2`;
                 `a:real`; `c:real`] CMPA_CALABI) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
        REWRITE_TAC[GSYM GRGD_CONTINUOUS_MAP_REAL] THEN
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                       `mfd_geo (top,atlas) (g:A->real^N^N) p u`; `(:real)`]
          GEOL_GEODESIC_BASIC) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN EXISTS_TAC `(:real)` THEN
        REWRITE_TAC[SUBSET_UNIV] THEN
        SUBGOAL_THEN `(\s. mfd_dist (top,atlas) (g:A->real^N^N) ((gamma:real->A) Tm)
                             (mfd_geo (top,atlas) g p u s)) =
                      (\y. mfd_dist (top,atlas) g (gamma Tm) y) o mfd_geo (top,atlas) g p u`
        SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `top:A topology` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_DIST_CONTINUOUS_RIGHT THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN
        REWRITE_TAC[REAL_CONTINUOUS_ON_ID]];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`t0:real`; `e:real`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `gamma:real->A`; `p:A`; `u:real^N`; `a':real`; `a:real`; `c:real`;
                   `c':real`; `Tm:real`; `m:real`; `del:real`; `k0:real`; `ew:real`;
                   `t0:real`] CMPSO_STRICT_BARRIER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`d:real`; `bf:real->real`; `bf':real->real`; `bf2:real`] THEN
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`d:real`; `bf:real->real`; `bf':real->real`; `bf2:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "cal") THEN X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  USE_THEN "cal" (fun th -> MP_TAC(MATCH_MP th (CONJ (ASSUME `a <= x`) (ASSUME `x <= c`)))) THEN
  REWRITE_TAC[] THEN
  MAP_EVERY (fun v -> MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; v; `(gamma:real->A) Tm`] MFD_DIST_SYM))
   [`mfd_geo (top,atlas) (g:A->real^N^N) p u a`; `mfd_geo (top,atlas) (g:A->real^N^N) p u c`;
    `mfd_geo (top,atlas) (g:A->real^N^N) p u x`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  ABBREV_TAC `K = --(k0 * ew / &2)` THEN
  ABBREV_TAC `l = (x - a) / (c - a)` THEN
  SUBGOAL_THEN `l * (c pow 2 - a pow 2) = (x - a) * (c + a)` ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN UNDISCH_TAC `a < c` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `k0 * ew / &4 = --(K / &2)` SUBST1_TAC THENL
   [EXPAND_TAC "K" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `da = mfd_dist (top,atlas) (g:A->real^N^N) ((gamma:real->A) Tm)
                     (mfd_geo (top,atlas) g p u a)` THEN
  ABBREV_TAC `dc = mfd_dist (top,atlas) (g:A->real^N^N) ((gamma:real->A) Tm)
                     (mfd_geo (top,atlas) g p u c)` THEN
  ABBREV_TAC `dx = mfd_dist (top,atlas) (g:A->real^N^N) ((gamma:real->A) Tm)
                     (mfd_geo (top,atlas) g p u x)` THEN
  SUBGOAL_THEN `--(K / &2) * (x - a) * (c - x) =
                --(K / &2) * (a pow 2 + (x - a) * (c + a) - x pow 2)`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `l * (c pow 2 - a pow 2)`)) THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The minimum point of the Busemann supremum is unique when                 *)
(* sec >= k0 > 0 on every ball.  A segment between two minimum points       *)
(* carries f = m; a near-maximizing ray gamma at the midpoint and a far      *)
(* point gamma(T) make h = T - d(., gamma T) nearly constant on the middle   *)
(* half (CMPSO_NEAR_CONST, from semiconvexity), and CMPSO_STRICT_CHORD then *)
(* pushes h below m at the midpoint by k0 L^2 / 128.                        *)
(* ========================================================================= *)

let CMPSO_NEAR_CONST = prove
 (`!(h:real->real) L m eps eta.
        &0 < L /\ &0 <= eta /\ &0 <= eps /\
        (!x1 x2 x. &0 <= x1 /\ x1 < x2 /\ x2 <= L /\ x1 <= x /\ x <= x2
                   ==> h x <= h x1 + (x - x1) / (x2 - x1) * (h x2 - h x1) +
                              eta * (x - x1) * (x2 - x)) /\
        (!s. &0 <= s /\ s <= L ==> h s <= m) /\ m - eps <= h(L / &2)
        ==> !x. L / &4 <= x /\ x <= &3 * L / &4
                ==> m - &2 * (eps + eta * L pow 2) <= h x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= eta * L pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  ASM_CASES_TAC `x = L / &2` THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `x < L / &2 \/ L / &2 < x` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN DISJ_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`x:real`; `L:real`; `L / &2`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `eta:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `lm = (L / &2 - x) / (L - x)` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= lm /\ lm <= &1 / &3` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "lm" THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `&0 < L - x` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `eta * (L / &2 - x) * (L - L / &2) <= eta * L pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `L * L` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_POW_2; REAL_LE_REFL]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(h:real->real) L <= m` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `lm * (h:real->real) L <= lm * m` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `m - &2 * (eps + eta * L pow 2) <= (h:real->real) x` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= (&1 - lm - &2 / &3) * (m - (h:real->real) x)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPECL [`&0`; `x:real`; `L / &2`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `eta:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_RZERO] THEN
    ABBREV_TAC `lm = (L / &2) / x` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&2 / &3 <= lm /\ lm <= &1` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 < x` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      EXPAND_TAC "lm" THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `eta * (L / &2) * (x - L / &2) <= eta * L pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `L * L` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_POW_2; REAL_LE_REFL]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(h:real->real) (&0) <= m` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(&1 - lm) * (h:real->real) (&0) <= (&1 - lm) * m` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `m - &2 * (eps + eta * L pow 2) <= (h:real->real) x` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= (lm - &2 / &3) * (m - (h:real->real) x)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC]);;

let CMPSO_UNIQUE_MIN = prove
 (`!top atlas (g:A->real^N^N) (p0:A) p q.
        hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        (!y a c. y IN topspace top /\ ~collinear {vec 0,a,c}
                 ==> &0 <= mfd_sectional atlas g y a c) /\
        (!x R. x IN topspace top
               ==> ?k0. &0 < k0 /\
                        !y a c. y IN topspace top /\ mfd_dist (top,atlas) g x y <= R /\
                                ~collinear {vec 0,a,c}
                                ==> k0 <= mfd_sectional atlas g y a c) /\
        p0 IN topspace top /\ (?gamma. cmp_ray (top,atlas) g gamma /\ gamma(&0) = p0) /\
        p IN topspace top /\ q IN topspace top /\
        (!x. x IN topspace top
             ==> cmp_bsup (top,atlas) g p0 p <= cmp_bsup (top,atlas) g p0 x) /\
        cmp_bsup (top,atlas) g p0 q = cmp_bsup (top,atlas) g p0 p
        ==> q = p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `!a b:A. a IN topspace top /\ b IN topspace top
                        ==> mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) a b`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `m = cmp_bsup (top,atlas) (g:A->real^N^N) p0 p` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `q:A`] CMPSO_SEGMENT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `L = mfd_dist (top,atlas) (g:A->real^N^N) p q` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `u:real^N`] CMPB_GEO_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "gtop")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gjs")))) THEN
  SUBGOAL_THEN
   `!s. &0 <= s /\ s <= L
        ==> cmp_bsup (top,atlas) (g:A->real^N^N) p0 (mfd_geo (top,atlas) g p u s) = m`
  (LABEL_TAC "fm") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `p0:A`; `p:A`; `u:real^N`; `&0`; `L:real`; `s:real`]
        CMPSO_BSUP_CONVEX) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_ADD_RID];
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p:A`; `L + &1`] o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "mfd_sectional" with Failure _ -> false))
        (concl th) &&
    can (find_term (fun t -> try fst(dest_var t) = "R" with Failure _ -> false)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "curv"))) THEN
  ABBREV_TAC `eps = min (L / &32) (k0 * L pow 2 / &256)` THEN
  SUBGOAL_THEN `&0 < k0 * L pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < eps /\ eps <= L / &32 /\ eps <= k0 * L pow 2 / &256`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eps" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p0:A`; `mfd_geo (top,atlas) (g:A->real^N^N) p u (L / &2)`]
    CMPSO_BSUP_BASIC) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `eps / &2` o CONJUNCT2 o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gam:real->A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `cmp_bsup (top,atlas) (g:A->real^N^N) p0
                  (mfd_geo (top,atlas) g p u (L / &2)) = m` ASSUME_TAC THENL
   [USE_THEN "fm" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(gam:real->A)(&0) IN topspace top` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `&0` o CONJUNCT1 o GEN_REWRITE_RULE I [cmp_ray]) THEN
    REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gam:real->A`;
                 `mfd_geo (top,atlas) (g:A->real^N^N) p u (L / &2)`] CMPB_SUP) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `eps / &2` o CONJUNCT1 o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `T0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "T0"))) THEN
  ABBREV_TAC `C0 = mfd_dist (top,atlas) (g:A->real^N^N) p p0 + L` THEN
  ABBREV_TAC `Tm = max T0 (C0 + &36 * L + &32 / k0 + &3)` THEN
  SUBGOAL_THEN `&0 <= mfd_dist (top,atlas) (g:A->real^N^N) p p0`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &32 / k0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Tm /\ T0 <= Tm /\ C0 + &36 * L + &32 / k0 + &3 <= Tm`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Tm" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < Tm - C0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `eta = inv(Tm - C0)` THEN
  SUBGOAL_THEN `&0 <= eta /\ eta * (&36 * L) <= &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC;
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `gam:real->A`; `p:A`; `u:real^N`; `&0`; `L:real`; `Tm:real`]
    CMPSO_SEMI_UNIFORM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN DISCH_THEN(LABEL_TAC "semi") THEN
  SUBGOAL_THEN
   `!s. &0 <= s /\ s <= L
        ==> Tm - mfd_dist (top,atlas) (g:A->real^N^N) (mfd_geo (top,atlas) g p u s)
                         ((gam:real->A) Tm) <= m`
  (LABEL_TAC "hm") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gam:real->A`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) p u s`] CMPB_SUP) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `Tm:real` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p0:A`; `mfd_geo (top,atlas) (g:A->real^N^N) p u s`]
      CMPSO_BSUP_BASIC) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `gam:real->A` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "fm" (fun th -> MP_TAC(MATCH_MP th
      (CONJ (ASSUME `&0 <= s`) (ASSUME `s <= L`)))) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `m - eps <= Tm - mfd_dist (top,atlas) (g:A->real^N^N)
                     (mfd_geo (top,atlas) g p u (L / &2)) ((gam:real->A) Tm)`
  ASSUME_TAC THENL
   [USE_THEN "T0" (fun th -> MP_TAC(MATCH_MP th (ASSUME `T0 <= Tm`))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL
   [`\s. Tm - mfd_dist (top,atlas) (g:A->real^N^N) (mfd_geo (top,atlas) g p u s)
                       ((gam:real->A) Tm)`;
    `L:real`; `m:real`; `eps:real`; `eta:real`] CMPSO_NEAR_CONST)) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC;
      USE_THEN "semi" ACCEPT_TAC; USE_THEN "hm" ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC];
    DISCH_THEN(LABEL_TAC "nc")] THEN
  SUBGOAL_THEN `(&8 * eps) / L <= &1 / &4` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&2 * (eps + eta * L pow 2)) / (L / &4) = (&8 * eps) / L + &8 * eta * L`
  ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < L` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `!t0. &0 <= t0 /\ t0 <= L
                     ==> Tm - C0 <= mfd_dist (top,atlas) (g:A->real^N^N)
                                      (mfd_geo (top,atlas) g p u t0) ((gam:real->A) Tm)`
  (LABEL_TAC "far") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(gam:real->A) Tm IN topspace top` ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPEC `Tm:real` o CONJUNCT1 o GEN_REWRITE_RULE I [cmp_ray]) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) p0 ((gam:real->A) Tm) = Tm`
    ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPECL [`&0`; `Tm:real`] o CONJUNCT2 o
        GEN_REWRITE_RULE I [cmp_ray]) THEN
      ASM_SIMP_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p0:A`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) p u t0`; `(gam:real->A) Tm`]
      MFD_DIST_TRIANGLE) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p0:A`; `p:A`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) p u t0`] MFD_DIST_TRIANGLE) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p0:A`; `p:A`] MFD_DIST_SYM) THEN
    ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `gam:real->A`; `p:A`; `u:real^N`; `&0`; `L / &4`; `&3 * L / &4`; `L:real`;
                 `Tm:real`; `m:real`; `&2 * (eps + eta * L pow 2)`; `k0:real`; `&1 / &2`]
    CMPSO_STRICT_CHORD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `(&2 * (eps + eta * L pow 2)) / (L - &3 * L / &4) =
                    (&8 * eps) / L + &8 * eta * L` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < L` THEN CONV_TAC REAL_FIELD; ASM_REAL_ARITH_TAC];
      CONV_TAC REAL_RAT_REDUCE_CONV;
      REPEAT STRIP_TAC THEN USE_THEN "curv" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `p:A`; `mfd_geo (top,atlas) (g:A->real^N^N) p u t0`;
                     `y:A`] MFD_DIST_TRIANGLE) THEN
      ASM_SIMP_TAC[] THEN
      MP_TAC(SPEC `t0:real` (ASSUME
       `!s. &0 <= s /\ s <= L
            ==> mfd_dist (top,atlas) (g:A->real^N^N) p (mfd_geo (top,atlas) g p u s) = s`)) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `t0:real` THEN STRIP_TAC THEN
      USE_THEN "far" (MP_TAC o SPEC `t0:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
      SUBGOAL_THEN `&32 / k0 <= mfd_dist (top,atlas) (g:A->real^N^N)
                                 (mfd_geo (top,atlas) g p u t0) ((gam:real->A) Tm)`
      ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&32 <= k0 * mfd_dist (top,atlas) (g:A->real^N^N)
                              (mfd_geo (top,atlas) g p u t0) ((gam:real->A) Tm)`
      ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `k0 * &32 / k0` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < k0` THEN CONV_TAC REAL_FIELD;
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `L / &2`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(L / &2 - L / &4) / (&3 * L / &4 - L / &4) = &1 / &2` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < L` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  USE_THEN "hm" (MP_TAC o SPEC `L / &4`) THEN USE_THEN "hm" (MP_TAC o SPEC `&3 * L / &4`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* In dimension 3, sec > 0 gives a positive lower bound of the               *)
(* sectional curvature on every closed ball (mfd_sec_min is continuous,     *)
(* RFA_SECMIN_CONTINUOUS_GEN for the constant family, positive at each      *)
(* point, and attains its minimum on the compact ball).                     *)
(* ========================================================================= *)

let CMPSO_SECMIN_CONT = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3).
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g
     ==> continuous_map (top,euclideanreal) (mfd_sec_min atlas g)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(BETA_RULE(ISPECL
    [`subtopology euclideanreal {t | &0 <= t /\ t < &1}`;
     `subtopology (top:A topology) (topspace top)`;
     `\t:real x. mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) (x:A)`;
     `&0`] RFA_SLICE_CONTINUOUS)) THEN
  REWRITE_TAC[ETA_AX; SUBTOPOLOGY_TOPSPACE] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL; IN_INTER; IN_UNIV;
                IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `&0`; `&1`; `\t:real. (g:A->real^3^3)`] RFA_SECMIN_CONTINUOUS_GEN)) THEN
  REWRITE_TAC[SUBTOPOLOGY_TOPSPACE] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `c:(A->bool)#(A->real^3)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `smooth_map_on (IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c))
      ((vectorize:real^3^3->real^(3,3)finite_prod) o metric_local atlas c (g:A->real^3^3))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)` THEN
    REWRITE_TAC[riemannian_metric; metric_field] THEN
    DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^3)`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `&1` THEN
  EXISTS_TAC `((vectorize:real^3^3->real^(3,3)finite_prod) o
               metric_local atlas c (g:A->real^3^3)) o
              (sndcart:real^(1,3)finite_sum->real^3)` THEN
  REWRITE_TAC[REAL_LT_01; o_THM; SNDCART_PASTECART] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_PCROSS THEN ASM_REWRITE_TAC[OPEN_INTERVAL];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; SNDCART_PASTECART] THEN
    SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `(sndcart:real^(1,3)finite_sum->real^3) o (\x. x)` THEN
    REWRITE_TAC[o_THM] THEN MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
    REWRITE_TAC[LINEAR_SNDCART; SMOOTH_MAP_ON_ID] THEN
    MATCH_MP_TAC OPEN_PCROSS THEN ASM_REWRITE_TAC[OPEN_INTERVAL]]);;

let CMPSO_UNIFORM_CURV = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3).
     hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
     (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
              ==> &0 < mfd_sectional atlas g x u v)
     ==> !x R. x IN topspace top
               ==> ?k0. &0 < k0 /\
                        !y a c. y IN topspace top /\ mfd_dist (top,atlas) g x y <= R /\
                                ~collinear {vec 0,a,c}
                                ==> k0 <= mfd_sectional atlas g y a c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!y:A. y IN topspace top ==> mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) x y` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= R` THENL
   [ALL_TAC;
    EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `x:A`; `y:A`] MFD_DIST_POS_LE) THEN
    ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool)
                                    (g:A->real^3^3)`;
                 `mfd_cball (top,atlas) (g:A->real^3^3) x R`] RFA_CMAP_COMPACT_MIN) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CMPSO_SECMIN_CONT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC GEOH_CBALL_COMPACT THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `x:A`; `x:A`] MFD_COMPLETE_MINIMIZING_GEODESIC) THEN
      ASM_SIMP_TAC[] THEN MESON_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; mfd_cball; IN_ELIM_THM] THEN EXISTS_TAC `x:A` THEN
      ASM_SIMP_TAC[MFD_DIST_REFL]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y0:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y0:A) IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `(y0:A) IN mfd_cball (top,atlas) (g:A->real^3^3) x R` THEN
    REWRITE_TAC[mfd_cball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
    ALL_TAC] THEN
  EXISTS_TAC `mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) y0` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RFA_SECMIN_POS THEN EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) y` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[mfd_cball; IN_ELIM_THM] THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC RFA_SEC_GE_SECMIN THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The soul point (general A, N, given positive lower bounds of sec on       *)
(* balls), then the statement constant CMP_R5_SOUL_STATEMENT and its proof   *)
(* CMP_R5_SOUL.                                                              *)
(* ========================================================================= *)

let CMPSO_SOUL_GEN = prove
 (`!top atlas (g:A->real^N^N).
        hausdorff_space top /\ connected_space top /\ ~compact_space top /\
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_complete (top,atlas) g /\
        (!y a c. y IN topspace top /\ ~collinear {vec 0,a,c}
                 ==> &0 <= mfd_sectional atlas g y a c) /\
        (!x R. x IN topspace top
               ==> ?k0. &0 < k0 /\
                        !y a c. y IN topspace top /\ mfd_dist (top,atlas) g x y <= R /\
                                ~collinear {vec 0,a,c}
                                ==> k0 <= mfd_sectional atlas g y a c)
        ==> ?p. p IN topspace top /\
                !x. x IN topspace top /\ ~(x = p)
                    ==> ?v. !w. w IN mfd_exp_dom (top,atlas) g x /\
                                mfd_exp (top,atlas) g x w = p /\
                                mfd_tnorm g x w = mfd_dist (top,atlas) g x p
                                ==> v dot (g x ** w) < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?p0:A. p0 IN topspace top` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN DISCH_TAC THEN
    UNDISCH_TAC `~compact_space (top:A topology)` THEN
    ASM_REWRITE_TAC[compact_space; COMPACT_IN_EMPTY];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p0:A`] CMPSO_RAY_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `u0:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?gamma. cmp_ray (top,atlas) (g:A->real^N^N) gamma /\ gamma(&0) = p0`
  ASSUME_TAC THENL
   [EXISTS_TAC `mfd_geo (top,atlas) (g:A->real^N^N) p0 u0` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p0:A`; `u0:real^N`] MFD_GEO_MAXIMAL) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p0:A`] CMPSO_BSUP_MIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `p:A` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  SUBGOAL_THEN `cmp_bsup (top,atlas) (g:A->real^N^N) p0 p < cmp_bsup (top,atlas) g p0 x`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `a <= b /\ ~(b = a) ==> a < b`) THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN UNDISCH_TAC `~(x:A = p)` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC CMPSO_UNIQUE_MIN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `g:A->real^N^N`; `p0:A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p0:A`; `x:A`] CMPSO_BSUP_BASIC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `cmp_bsup (top,atlas) (g:A->real^N^N) p0 x -
                            cmp_bsup (top,atlas) g p0 p` o CONJUNCT2 o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gam:real->A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p0:A`; `p:A`] CMPSO_BSUP_BASIC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `gam:real->A` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC CMPSO_REGULAR_DIR THEN EXISTS_TAC `gam:real->A` THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let CMP_R5_SOUL_STATEMENT = new_definition
 `CMP_R5_SOUL_STATEMENT (w:B->bool) <=>
    !top atlas g.
       hausdorff_space top /\ connected_space top /\ ~compact_space top /\
       smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool) /\
       riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
       (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                ==> &0 < mfd_sectional atlas g x u v)
       ==> ?p. p IN topspace top /\
               !x. x IN topspace top /\ ~(x = p) ==> p2b_dist_regular (top,atlas) g p x`;;

let CMP_R5_SOUL = prove
 (`!w:B->bool. CMP_R5_SOUL_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[CMP_R5_SOUL_STATEMENT; p2b_dist_regular] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CMPSO_SOUL_GEN THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC CMPSO_UNIFORM_CURV THEN ASM_REWRITE_TAC[]]);;


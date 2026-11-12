(* ========================================================================= *)
(* pc_p2b_shsplit: the splitting step of SPLIT_ROUND, P2B_SHRINKER_SPLIT_CYL *)
(* |- !w. P2B_SHRINKER_SPLIT_CYL_STATEMENT w (statement in                   *)
(* pc_p2b_shsplitreq): a complete connected shrinker slice with sec >= 0,    *)
(* bounded R, R > 0 somewhere, p2b_lorient and a global unit parallel field  *)
(* Y is the one-to-one round cylinder model with Y the axial field.          *)
(* Route: h = 2 Y(f) has gradient Y; the flow of Y and the level set N of h, *)
(* a compact connected 2-d shrinker of constant curvature k > 0;             *)
(* stereographic model, Cartan pair glued by the Mobius map, N covered;      *)
(* Psi_F z = Phi_(z3)(F(z1,z2)) and the slab chart give the glued local      *)
(* isometry p from (real^3 - 0, (c^2/|y|^2) I), c = sqrt(1/k); pullback,     *)
(* onto, Y clause; fibres: y2 = y1 or p(-y) = p y; the antipodal case        *)
(* contradicts p2b_lorient (generic orientation obstruction                  *)
(* P2BSS_ANTIPODAL_ORIENT); the main theorem at the end.                     *)
(* ========================================================================= *)

needs "src/pc_p2b_shsplitreq.ml";;
needs "src/pc_mfd_level4.ml";;
needs "src/pc_p2b_kfl.ml";;
needs "src/pc_rfa_s2.ml";;
needs "src/pc_cmp_index.ml";;
needs "src/pc_geo_lisom.ml";;
needs "src/pc_top_cover.ml";;
needs "src/pc_mfd_embed.ml";;
needs "src/pc_p2b_p946s.ml";;
needs "src/pc_moi_pd2_loc.ml";;
needs "src/pc_p2b_poinc.ml";;
needs "src/pc_cmp_pmfd.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Derivatives of functions on a manifold in different charts, and the       *)
(* directional derivative Y(f) in any chart.                                 *)
(* ========================================================================= *)

let P2BSS_DF_CHART = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (Ff:A->real^K) c c' x w.
     smooth_manifold_atlas top atlas /\ mfd_smooth atlas Ff /\
     c IN atlas /\ c' IN atlas /\ x IN FST c /\ x IN FST c'
     ==> frechet_derivative (Ff o chart_inv c) (at (SND c x)) w =
         frechet_derivative (Ff o chart_inv c') (at (SND c' x)) (chart_jac c c' x w)`,
  REPEAT GEN_TAC THEN
  MAP_EVERY (fun t -> SUBST1_TAC(GSYM(ISPEC t PAIR)))
    [`c:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`] THEN
  MAP_EVERY (fun (v,t) -> SPEC_TAC(t,v))
   [(`psi:A->real^N`,`SND(c':(A->bool)#(A->real^N))`);
    (`V:A->bool`,`FST(c':(A->bool)#(A->real^N))`);
    (`phi:A->real^N`,`SND(c:(A->bool)#(A->real^N))`);
    (`U:A->bool`,`FST(c:(A->bool)#(A->real^N))`)] THEN
  REWRITE_TAC[FST; SND] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(U:A->bool,phi:A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(V:A->bool,psi:A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open (IMAGE (phi:A->real^N) (U INTER V))` ASSUME_TAC THENL
   [MATCH_MP_TAC CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U:A->bool`] THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(((Ff:A->real^K) o chart_inv (V,psi)) has_derivative
     frechet_derivative (Ff o chart_inv (V:A->bool,psi:A->real^N)) (at (psi x))) (at (psi x))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`IMAGE (psi:A->real^N) V`; `(Ff:A->real^K) o chart_inv (V:A->bool,psi:A->real^N)`]
           SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (Ff:A->real^K)` THEN REWRITE_TAC[mfd_smooth] THEN
      DISCH_THEN(MP_TAC o SPEC `(V:A->bool,psi:A->real^N)`) THEN ASM_REWRITE_TAC[FST; SND];
      DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((Ff:A->real^K) o chart_inv (U,phi) has_derivative
     frechet_derivative (Ff o chart_inv (V:A->bool,psi:A->real^N)) (at (psi x)) o
     chart_jac (U:A->bool,phi:A->real^N) (V,psi) x) (at (phi x))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    MAP_EVERY EXISTS_TAC [`((Ff:A->real^K) o chart_inv (V:A->bool,psi:A->real^N)) o
                           chart_trans (U:A->bool,phi:A->real^N) (V,psi)`;
                          `IMAGE (phi:A->real^N) (U INTER V)`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
      REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER; o_THM; chart_trans] THEN
      X_GEN_TAC `z:A` THEN STRIP_TAC THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
       [MATCH_MP_TAC CHART_TRANS_HAS_DERIVATIVE THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
        ASM_REWRITE_TAC[IN_INTER];
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`; `x:A`]
               CHART_TRANS_AT) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN REWRITE_TAC[o_THM]);;

let P2BSS_YF_CHART = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (f:A->real) (Y:A->real^N) c x.
     smooth_manifold_atlas top atlas /\ mfd_smooth atlas (\x. lift(f x)) /\
     c IN atlas /\ x IN FST c
     ==> frechet_derivative (\y. lift(f(chart_inv (chart_at atlas x) y)))
           (at (SND(chart_at atlas x) x)) (Y x) =
         frechet_derivative (\y. lift(f(chart_inv c y))) (at (SND c x))
           (mfd_vrep atlas Y c (SND c x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `\x:A. lift(f x)`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`;
                 `c:(A->bool)#(A->real^N)`; `x:A`; `(Y:A->real^N) x`] P2BSS_DF_CHART) THEN
  ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[mfd_vrep]);;

(* ========================================================================= *)
(* h = 2 Y(f) is a primitive of g(Y,.) (Ric(Y,.) = 0 and the shrinker        *)
(* equation give Hess f(Y,.) = g(Y,.)/2).                                    *)
(* ========================================================================= *)

let p2bss_dirf = new_definition
 `p2bss_dirf (atlas:((A->bool)#(A->real^N))->bool) (f:A->real) (Y:A->real^N) (x:A) =
    drop(frechet_derivative (\y. lift(f(chart_inv (chart_at atlas x) y)))
                            (at (SND(chart_at atlas x) x)) (Y x))`;;

let P2BSS_DIRF_CHART = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (f:A->real) (Y:A->real^N) c v.
     smooth_manifold_atlas top atlas /\ mfd_smooth atlas (\x. lift(f x)) /\
     c IN atlas /\ v IN IMAGE (SND c) (FST c)
     ==> p2bss_dirf atlas f Y (chart_inv c v) =
         drop(frechet_derivative (\y. lift(f(chart_inv c y))) (at v) (mfd_vrep atlas Y c v))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) v IN FST c /\ SND c (chart_inv c v) = v`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[p2bss_dirf] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `f:A->real`;
                 `Y:A->real^N`; `c:(A->bool)#(A->real^N)`; `chart_inv (c:(A->bool)#(A->real^N)) v`]
         P2BSS_YF_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

let P2BSS_SMOOTH_TOPSPACE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (Ff:A->real^K).
     smooth_manifold_atlas top atlas /\ mfd_smooth_on atlas (topspace top) Ff
     ==> mfd_smooth atlas Ff`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_smooth_on; mfd_smooth] THEN STRIP_TAC THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[SET_RULE `(s:A->bool) INTER t = s <=> s SUBSET t`] THEN
  ASM_MESON_TAC[MFDM_CHART; OPEN_IN_SUBSET]);;

(* The key identity of S3: Hess f(Y,.) = g(Y,.)/2, so h = 2 Y(f) has        *)
(* differential g(Y,.) in every chart.                                       *)

let P2BSS_DH_CHART = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f (Y:A->real^N) c u.
     p2b_shrinker (top,atlas) g f /\ p2b_parallel_on atlas g (topspace top) Y /\
     c IN atlas /\ u IN IMAGE (SND c) (FST c)
     ==> ((\v. lift(&2 * p2bss_dirf atlas f Y (chart_inv c v))) has_derivative
          (\w. lift(mfd_vrep atlas Y c u dot (metric_local atlas c g u ** w)))) (at u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  SUBGOAL_THEN `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x:A. lift(f x))` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BSS_SMOOTH_TOPSPACE THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER topspace top) =
                IMAGE (SND c) (FST c)` ASSUME_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[SET_RULE `(s:A->bool) INTER t = s <=> s SUBSET t`] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))
                             (metric_local atlas c (g:A->real^N^N))` ASSUME_TAC THENL
   [UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_parallel_on] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2b_parallel_on")) (concl th))) THEN
  SUBGOAL_THEN
   `smooth_map_on (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)) (mfd_vrep atlas (Y:A->real^N) c) /\
    !y z. y IN IMAGE (SND c) (FST c)
          ==> frechet_derivative (mfd_vrep atlas Y c) (at y) z +
              christoffel (metric_local atlas c (g:A->real^N^N)) y z (mfd_vrep atlas Y c y) = vec 0`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `c:(A->bool)#(A->real^N)` o check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "smooth_map_on" with Failure _ -> false))
            (concl th))) THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))
                  (\y. lift((f:A->real)(chart_inv c y)))` ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x:A. lift(f x))` THEN REWRITE_TAC[mfd_smooth; o_DEF] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
  MAP_EVERY EXISTS_TAC
   [`\v. &2 % frechet_derivative (\y. lift((f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y)))
                 (at v) (mfd_vrep atlas (Y:A->real^N) c v)`;
    `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `f:A->real`;
                   `Y:A->real^N`; `c:(A->bool)#(A->real^N)`; `v:real^N`] P2BSS_DIRF_CHART) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[LIFT_CMUL; LIFT_DROP];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z. frechet_derivative (\y. lift((f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y)))
                        (at z)`;
                 `mfd_vrep atlas (Y:A->real^N) (c:(A->bool)#(A->real^N))`;
                 `frechet_derivative (mfd_vrep atlas (Y:A->real^N) (c:(A->bool)#(A->real^N))) (at u)`;
                 `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`; `u:real^N`]
         LRG_HAS_DERIVATIVE_LINFAM) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
      ASM_MESON_TAC[SMOOTH_MAP_ON_DIFFERENTIABLE];
      REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`;
                     `\y. lift((f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y))`;
                     `u:real^N`; `basis i:real^N`] LRG_SMOOTH_FRECHET_DIFFERENTIABLE) THEN
      ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`;
                     `mfd_vrep atlas (Y:A->real^N) (c:(A->bool)#(A->real^N))`]
             SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `&2` o MATCH_MP HAS_DERIVATIVE_CMUL) THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `w:real^N` THEN
  SUBGOAL_THEN `frechet_derivative (mfd_vrep atlas (Y:A->real^N) c) (at u) w =
                --(christoffel (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)) u w
                     (mfd_vrep atlas Y c u))`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N`; `w:real^N`] o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "christoffel")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "frechet_derivative")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(frechet_derivative (\y. lift((f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y))) (at u))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_MESON_TAC[SMOOTH_MAP_ON_DIFFERENTIABLE];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LINEAR_NEG] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`; `f:A->real`;
                 `c:(A->bool)#(A->real^N)`] RFA_SHRINKER_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`u:real^N`;
    `\m:num. if m = 1 then mfd_vrep atlas (Y:A->real^N) (c:(A->bool)#(A->real^N)) u else (w:real^N)`]) THEN
  ASM_REWRITE_TAC[lric2; lmetric2; lnabla; ARITH; SUM_SING_NUMSEG] THEN
  REWRITE_TAC[LIFT_DROP; ETA_AX] THEN
  MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`;
                 `metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)`;
                 `mfd_vrep atlas (Y:A->real^N) (c:(A->bool)#(A->real^N))`; `u:real^N`]
         P2BX0_LRICCI_PAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
  REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; DROP_ADD; DROP_NEG; LIFT_DROP] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The function h = 2 Y(f).  It is smooth, has differential g(Y,.) in every  *)
(* chart, is regular, has zero Hessian, and its unit normal is Y.            *)
(* ========================================================================= *)

let p2bss_h = new_definition
 `p2bss_h (atlas:((A->bool)#(A->real^N))->bool) (f:A->real) (Y:A->real^N) (x:A) =
    &2 * p2bss_dirf atlas f Y x`;;

let P2BSS_SMOOTH_DERIV_APPLY = prove
 (`!s (Ff:real^M->real^P) (V:real^M->real^M).
     open s /\ smooth_map_on s Ff /\ smooth_map_on s V
     ==> smooth_map_on s (\v. frechet_derivative Ff (at v) (V v))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `\v. vsum(1..dimindex(:M))
                    (\k. drop(lift((V:real^M->real^M) v$k)) %
                         frechet_derivative (Ff:real^M->real^P) (at v) (basis k))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `v:real^M` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC LINEAR_APPLY_EXPAND THEN
    REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    ASM_MESON_TAC[SMOOTH_MAP_ON_DIFFERENTIABLE];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_LIFT_COMPONENT; SMOOTH_MAP_ON_FRECHET_DERIVATIVE]);;

let P2BSS_H_CHART = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f (Y:A->real^N) c v.
     p2b_shrinker (top,atlas) g f /\ c IN atlas /\ v IN IMAGE (SND c) (FST c)
     ==> p2bss_h atlas f Y (chart_inv c v) =
         &2 * drop(frechet_derivative (\y. lift(f(chart_inv c y))) (at v)
                                      (mfd_vrep atlas Y c v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  REWRITE_TAC[p2bss_h] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC P2BSS_DIRF_CHART THEN EXISTS_TAC `top:A topology` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BSS_SMOOTH_TOPSPACE THEN
  EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]);;

(* Smoothness of h on the whole manifold. *)

let P2BSS_H_SMOOTH = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f (Y:A->real^N).
     p2b_shrinker (top,atlas) g f /\ p2b_parallel_on atlas g (topspace top) Y
     ==> mfd_smooth atlas (\x. lift(p2bss_h atlas f Y x)) /\
         mfd_smooth_on atlas (topspace top) (\x. lift(p2bss_h atlas f Y x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  SUBGOAL_THEN `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x:A. lift(f x))` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BSS_SMOOTH_TOPSPACE THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool)
                           (\x. lift(p2bss_h atlas f (Y:A->real^N) x))` ASSUME_TAC THENL
   [REWRITE_TAC[mfd_smooth] THEN X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `\v. &2 % frechet_derivative (\y. lift((f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y)))
                         (at v) (mfd_vrep atlas (Y:A->real^N) c v)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                     `f:A->real`; `Y:A->real^N`; `c:(A->bool)#(A->real^N)`; `v:real^N`]
             P2BSS_H_CHART) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[LIFT_CMUL; LIFT_DROP];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2BSS_SMOOTH_DERIV_APPLY THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x:A. lift(f x))` THEN
      REWRITE_TAC[mfd_smooth; o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[ETA_AX] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_parallel_on] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2b_parallel_on")) (concl th))) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c:(A->bool)#(A->real^N)` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "smooth_map_on" with Failure _ -> false))
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[SET_RULE `(s:A->bool) INTER t = s <=> s SUBSET t`] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool)
                          (\x. lift(p2bss_h atlas f (Y:A->real^N) x))` THEN
  REWRITE_TAC[mfd_smooth; mfd_smooth_on] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
  REWRITE_TAC[SET_RULE `(s:A->bool) INTER t = s <=> s SUBSET t`] THEN
  ASM_MESON_TAC[MFDM_CHART; OPEN_IN_SUBSET]);;

(* The differential of h in a chart: dh = g(Y,.). *)

let P2BSS_H_DERIV = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f (Y:A->real^N) c u.
     p2b_shrinker (top,atlas) g f /\ p2b_parallel_on atlas g (topspace top) Y /\
     c IN atlas /\ u IN IMAGE (SND c) (FST c)
     ==> ((\v. lift(p2bss_h atlas f Y (chart_inv c v))) has_derivative
          (\w. lift(mfd_vrep atlas Y c u dot (metric_local atlas c g u ** w)))) (at u) /\
         frechet_derivative (\v. lift(p2bss_h atlas f Y (chart_inv c v))) (at u) =
         (\w. lift(mfd_vrep atlas Y c u dot (metric_local atlas c g u ** w)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `((\v. lift(p2bss_h atlas f (Y:A->real^N) (chart_inv (c:(A->bool)#(A->real^N)) v))) has_derivative
     (\w. lift(mfd_vrep atlas Y c u dot (metric_local atlas c (g:A->real^N^N) u ** w)))) (at u)`
  ASSUME_TAC THENL
   [REWRITE_TAC[p2bss_h] THEN MATCH_MP_TAC P2BSS_DH_CHART THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    ASM_REWRITE_TAC[]]);;

(* The Hessian of h vanishes (Y is parallel). *)

let P2BSS_H_HESS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f (Y:A->real^N) c u a b.
     p2b_shrinker (top,atlas) g f /\ p2b_parallel_on atlas g (topspace top) Y /\
     c IN atlas /\ u IN IMAGE (SND c) (FST c)
     ==> cmp_lhess (metric_local atlas c g) (\y. p2bss_h atlas f Y (chart_inv c y)) u a b =
         &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))
                             (metric_local atlas c (g:A->real^N^N))` ASSUME_TAC THENL
   [UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER topspace top) =
                IMAGE (SND c) (FST c)` ASSUME_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[SET_RULE `(s:A->bool) INTER t = s <=> s SUBSET t`] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_parallel_on] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2b_parallel_on")) (concl th))) THEN
  SUBGOAL_THEN
   `smooth_map_on (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)) (mfd_vrep atlas (Y:A->real^N) c) /\
    !y z. y IN IMAGE (SND c) (FST c)
          ==> frechet_derivative (mfd_vrep atlas Y c) (at y) z +
              christoffel (metric_local atlas c (g:A->real^N^N)) y z (mfd_vrep atlas Y c y) = vec 0`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `c:(A->bool)#(A->real^N)` o check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "smooth_map_on" with Failure _ -> false))
            (concl th))) THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)
        ==> frechet_derivative (\x. lift(p2bss_h atlas f (Y:A->real^N) (chart_inv c x))) (at z) =
            (\w. lift(mfd_vrep atlas Y c z dot (metric_local atlas c (g:A->real^N^N) z ** w)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `f:A->real`; `Y:A->real^N`; `c:(A->bool)#(A->real^N)`; `z:real^N`]
           P2BSS_H_DERIV) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\z. lift(drop(frechet_derivative
                     (\x. lift(p2bss_h atlas f (Y:A->real^N) (chart_inv (c:(A->bool)#(A->real^N)) x)))
                     (at z) a))) has_derivative
     (\w. lift(frechet_derivative (mfd_vrep atlas Y c) (at u) w dot
               (metric_local atlas c (g:A->real^N^N) u ** a) +
               mfd_vrep atlas Y c u dot (mderiv (metric_local atlas c g) u w ** a)))) (at u)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    EXISTS_TAC `\z. lift(mfd_vrep atlas (Y:A->real^N) (c:(A->bool)#(A->real^N)) z dot
                         (metric_local atlas c (g:A->real^N^N) z ** a))` THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
    ASM_SIMP_TAC[LIFT_DROP] THEN
    MP_TAC(ISPECL [`metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)`;
                   `frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                        metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))
                                       (at u)`;
                   `mfd_vrep atlas (Y:A->real^N) (c:(A->bool)#(A->real^N))`;
                   `frechet_derivative (mfd_vrep atlas (Y:A->real^N) (c:(A->bool)#(A->real^N))) (at u)`;
                   `(\z:real^N. (a:real^N))`; `(\w:real^N. vec 0:real^N)`; `u:real^N`]
           LRG_HAS_DERIVATIVE_DOT_MATVEC) THEN
    REWRITE_TAC[HAS_DERIVATIVE_CONST; MATRIX_VECTOR_MUL_RZERO; VECTOR_ADD_RID] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
        EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
        ASM_MESON_TAC[metric_field];
        MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`;
                       `mfd_vrep atlas (Y:A->real^N) (c:(A->bool)#(A->real^N))`]
               SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
        ASM_SIMP_TAC[]];
      REWRITE_TAC[mderiv]];
    ALL_TAC] THEN
  REWRITE_TAC[cmp_lhess; lnabla] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SUM_SING_NUMSEG] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  ASM_SIMP_TAC[LIFT_DROP] THEN
  SUBGOAL_THEN `frechet_derivative (mfd_vrep atlas (Y:A->real^N) (c:(A->bool)#(A->real^N))) (at u) b =
                --(christoffel (metric_local atlas c (g:A->real^N^N)) u b (mfd_vrep atlas Y c u))`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N`; `b:real^N`] o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "christoffel")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "frechet_derivative")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`;
                 `metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)`; `u:real^N`;
                 `mfd_vrep atlas (Y:A->real^N) (c:(A->bool)#(A->real^N)) u`; `b:real^N`; `a:real^N`]
         LRG_MDERIV_CHRISTOFFEL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `transp(metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N) u) =
                metric_local atlas c g u` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP P2BKF_SYM_DOT th]) THEN
  REWRITE_TAC[DOT_LNEG; DOT_RNEG; MATRIX_VECTOR_MUL_RNEG] THEN REAL_ARITH_TAC);;

(* At a point, in the preferred chart. *)

let P2BSS_H_DERIV_AT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f (Y:A->real^N) x.
     p2b_shrinker (top,atlas) g f /\ p2b_parallel_on atlas g (topspace top) Y /\
     x IN topspace top
     ==> frechet_derivative (\y. lift(p2bss_h atlas f Y (chart_inv (chart_at atlas x) y)))
                            (at (SND(chart_at atlas x) x)) =
         (\w. lift(Y x dot (g x ** w)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `Y:A->real^N`; `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) x`] P2BSS_H_DERIV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `Y:A->real^N`; `x:A`]
         P2BX0_VREP_AT) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`; `x:A`]
         METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN REWRITE_TAC[]);;

(* g x is symmetric and positive definite (preferred chart). *)

let P2BSS_G_AT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top
     ==> transp(g x) = g x /\ (!v. ~(v = vec 0) ==> &0 < v dot (g x ** v)) /\
         invertible(g x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                                    (FST(chart_at atlas x)))
                             (metric_local atlas (chart_at atlas x) (g:A->real^N^N))` ASSUME_TAC THENL
   [UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) x IN
                IMAGE (SND(chart_at atlas x)) (FST(chart_at atlas x))` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`; `x:A`]
         METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_MESON_TAC[metric_field; LRG_METRIC_INVERTIBLE]);;

(* Regularity of every level set of h. *)

let P2BSS_H_REGULAR = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f (Y:A->real^3) u.
     p2b_shrinker (top,atlas) g f /\ p2b_parallel_on atlas g (topspace top) Y /\
     (!x. x IN topspace top ==> Y x dot (g x ** Y x) = &1)
     ==> lvs_regular atlas (topspace top) (p2bss_h atlas f Y) u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[lvs_regular; lvs_set; IN_ELIM_THM] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `Y:A->real^3`] P2BSS_H_SMOOTH) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `Y:A->real^3`; `x:A`] P2BSS_H_DERIV_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  DISCH_THEN(MP_TAC o C AP_THM `(Y:A->real^3) x`) THEN
  ASM_SIMP_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN REAL_ARITH_TAC);;

(* The unit normal of the level sets of h is Y. *)

let P2BSS_H_NORMAL = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f (Y:A->real^3) x.
     p2b_shrinker (top,atlas) g f /\ p2b_parallel_on atlas g (topspace top) Y /\
     (!x. x IN topspace top ==> Y x dot (g x ** Y x) = &1) /\ x IN topspace top
     ==> lvs_df atlas (p2bss_h atlas f Y) x = g x ** Y x /\
         lvs_normal atlas g (p2bss_h atlas f Y) x = Y x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `x:A`]
         P2BSS_G_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lvs_df atlas (p2bss_h atlas f (Y:A->real^3)) x = (g:A->real^3^3) x ** Y x`
  ASSUME_TAC THENL
   [REWRITE_TAC[lvs_df] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `f:A->real`; `Y:A->real^3`; `x:A`] P2BSS_H_DERIV_AT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `!w. (Y:A->real^3) x dot ((g:A->real^3^3) x ** w) = (g x ** Y x) dot w`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN
      GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o LAND_CONV)
        [GSYM(ASSUME `transp((g:A->real^3^3) x) = g x`)] THEN
      REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL];
      ALL_TAC] THEN
    SIMP_TAC[CART_EQ; LAMBDA_BETA; LIFT_DROP; DOT_BASIS];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[lvs_normal] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `p2bss_h atlas f (Y:A->real^3)`; `x:A`] LVS_GRAD2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MATRIX_INV th]) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LID] THEN ONCE_REWRITE_TAC[DOT_SYM] THEN
  ASM_SIMP_TAC[SQRT_1; REAL_INV_1; VECTOR_MUL_LID]);;

(* The second fundamental form of the level sets of h vanishes. *)

let P2BSS_H_II = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f (Y:A->real^3) u x.
     p2b_shrinker (top,atlas) g f /\ p2b_parallel_on atlas g (topspace top) Y /\
     x IN topspace top
     ==> lvs_II top atlas g (topspace top) (p2bss_h atlas f Y) u x = mat 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!a b. cmp_lhess (metric_local atlas (chart_at atlas x) (g:A->real^3^3))
                    (\y. p2bss_h atlas f (Y:A->real^3)
                           (chart_inv (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) y))
                    (SND(chart_at atlas x) x) a b = &0`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC P2BSS_H_HESS THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[lvs_II] THEN SIMP_TAC[CART_EQ; LAMBDA_BETA; MAT_COMPONENT; COND_ID] THEN
  ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO]);;

(* ========================================================================= *)
(* h along the flow of Y.  h(Phi_r y) = h y + r; the projection onto a level *)
(* set of h and its continuity; the level sets are nonempty and connected.   *)
(* ========================================================================= *)

let P2BSS_VDIFF_CHAIN = prove
 (`!(f:real^1->real^M) (g:real^M->real^P) f' g' x.
     (f has_vector_derivative f') (at x) /\ (g has_derivative g') (at (f x))
     ==> ((g o f) has_vector_derivative g' f') (at x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_vector_derivative] THEN STRIP_TAC THEN
  SUBGOAL_THEN `linear (g':real^M->real^P)` ASSUME_TAC THENL
   [ASM_MESON_TAC[has_derivative]; ALL_TAC] THEN
  SUBGOAL_THEN `(\x:real^1. drop x % (g':real^M->real^P) f') = g' o (\x. drop x % f')`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN ASM_SIMP_TAC[LINEAR_CMUL];
    MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[]]);;

let P2BSS_H_ORBIT0 = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f (Y:A->real^N) y.
     hausdorff_space top /\ p2b_shrinker (top,atlas) g f /\ mfd_complete (top,atlas) g /\
     p2b_parallel_on atlas g (topspace top) Y /\
     (!x. x IN topspace top ==> Y x dot (g x ** Y x) = &1) /\ y IN topspace top
     ==> ((\t. lift(p2bss_h atlas f Y (mfd_geo (top,atlas) g y (Y y) (drop t))))
          has_vector_derivative lift(&1)) (at (lift(&0)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `y:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `Y:A->real^N`; `y:A`] P2BKF_ORBIT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `y:A`; `(Y:A->real^N) y`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?d. &0 < d /\
        !s. abs(s - &0) < d
            ==> s IN (:real) /\
                mfd_geo (top,atlas) (g:A->real^N^N) y ((Y:A->real^N) y) s IN
                FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) y)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC P2BKF_EVENTUALLY_IN THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[REAL_OPEN_UNIV; IN_UNIV] THEN
    UNDISCH_TAC `mfd_geodesic (top,atlas) (g:A->real^N^N)
                   (mfd_geo (top,atlas) g y ((Y:A->real^N) y)) (:real)` THEN
    SIMP_TAC[mfd_geodesic; ETA_AX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `Y:A->real^N`; `y:A`] P2BKF_ORBIT_VEL0) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `Y:A->real^N`; `chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A)`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A)) y`] P2BSS_H_DERIV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `Y:A->real^N`; `y:A`]
         P2BX0_VREP_AT) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`; `y:A`]
         METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN DISCH_TAC THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `(\v. lift(p2bss_h atlas f (Y:A->real^N)
                       (chart_inv (chart_at (atlas:((A->bool)#(A->real^N))->bool) y) v))) o
              (\s. SND(chart_at atlas y) (mfd_geo (top,atlas) (g:A->real^N^N) y (Y y) (drop s)))` THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `t:real^1` THEN REWRITE_TAC[DIST_LIFT; o_THM] THEN DISCH_TAC THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `drop t`) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `dist(t:real^1,lift(&0)) < d` THEN
      REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN REAL_ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `lift(&1) = (\w. lift((Y:A->real^N) y dot ((g:A->real^N^N) y ** w))) (Y y)`
  SUBST1_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC P2BSS_VDIFF_CHAIN THEN ASM_REWRITE_TAC[LIFT_DROP]);;

(* h(Phi_s y) = h y + s. *)

let P2BSS_H_ORBIT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f (Y:A->real^N) y s.
     hausdorff_space top /\ p2b_shrinker (top,atlas) g f /\ mfd_complete (top,atlas) g /\
     p2b_parallel_on atlas g (topspace top) Y /\
     (!x. x IN topspace top ==> Y x dot (g x ** Y x) = &1) /\ y IN topspace top
     ==> p2bss_h atlas f Y (mfd_geo (top,atlas) g y (Y y) s) = p2bss_h atlas f Y y + s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `Y:A->real^N`; `y:A`] P2BKF_ORBIT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `Y:A->real^N`; `y:A`] P2BKF_ORBIT_SHIFT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `y:A`; `(Y:A->real^N) y`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!s0. ((\s. p2bss_h atlas f (Y:A->real^N) (mfd_geo (top,atlas) (g:A->real^N^N) y (Y y) s))
          has_real_derivative &1) (atreal s0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s0:real` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `f:A->real`; `Y:A->real^N`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) y ((Y:A->real^N) y) s0`] P2BSS_H_ORBIT0) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `((\t. p2bss_h atlas f (Y:A->real^N) (mfd_geo (top,atlas) (g:A->real^N^N) y (Y y) (s0 + t)))
       has_real_derivative &1) (atreal (&0))`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF; LIFT_DROP]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\s. p2bss_h atlas f (Y:A->real^N) (mfd_geo (top,atlas) (g:A->real^N^N) y (Y y) s)) =
      (\t. p2bss_h atlas f Y (mfd_geo (top,atlas) g y (Y y) (s0 + t))) o (\s. s - s0)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&1 = &1 * &1` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_DIFF_CHAIN_ATREAL THEN CONJ_TAC THENL
     [REAL_DIFF_TAC THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[REAL_SUB_REFL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\s. p2bss_h atlas f (Y:A->real^N)
                        (mfd_geo (top,atlas) (g:A->real^N^N) y (Y y) s) - s`; `(:real)`]
         HAS_REAL_DERIVATIVE_ZERO_CONSTANT) THEN
  REWRITE_TAC[IS_REALINTERVAL_UNIV; IN_UNIV; WITHINREAL_UNIV] THEN
  ANTS_TAC THENL
   [X_GEN_TAC `s0:real` THEN SUBGOAL_THEN `&0 = &1 - &1` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN ASM_REWRITE_TAC[HAS_REAL_DERIVATIVE_ID];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` (fun th -> MP_TAC(SPEC `s:real` th) THEN
                                               MP_TAC(SPEC `&0` th))) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let P2BSS_H_PHI = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f (Y:A->real^N) r y.
     hausdorff_space top /\ p2b_shrinker (top,atlas) g f /\ mfd_complete (top,atlas) g /\
     p2b_parallel_on atlas g (topspace top) Y /\
     (!x. x IN topspace top ==> Y x dot (g x ** Y x) = &1) /\ y IN topspace top
     ==> p2bss_h atlas f Y (p2bkf_phi (top,atlas) g Y r y) = p2bss_h atlas f Y y + r`,
  REWRITE_TAC[p2bkf_phi] THEN MESON_TAC[P2BSS_H_ORBIT]);;

(* Continuity of h. *)

let P2BSS_H_CONTINUOUS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f (Y:A->real^N).
     p2b_shrinker (top,atlas) g f /\ p2b_parallel_on atlas g (topspace top) Y
     ==> continuous_map (top,euclideanreal) (p2bss_h atlas f Y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONTINUOUS_MAP_EQ_LIFT; o_DEF] THEN
  MATCH_MP_TAC GRGE_MFD_SMOOTH_CONTINUOUS THEN
  EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN
  ASM_MESON_TAC[P2BSS_H_SMOOTH; p2b_shrinker]);;

(* The projection along the flow onto the level set h = s0. *)

let p2bss_proj = new_definition
 `p2bss_proj (top:A topology,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
             (f:A->real) (Y:A->real^N) (s0:real) (x:A) =
    p2bkf_phi (top,atlas) g Y (s0 - p2bss_h atlas f Y x) x`;;

let P2BSS_PROJ_FACTS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f (Y:A->real^N) s0 x.
     hausdorff_space top /\ p2b_shrinker (top,atlas) g f /\ mfd_complete (top,atlas) g /\
     p2b_parallel_on atlas g (topspace top) Y /\
     (!x. x IN topspace top ==> Y x dot (g x ** Y x) = &1) /\ x IN topspace top
     ==> p2bss_proj (top,atlas) g f Y s0 x IN topspace top /\
         p2bss_h atlas f Y (p2bss_proj (top,atlas) g f Y s0 x) = s0 /\
         p2bss_proj (top,atlas) g f Y s0 x IN lvs_set (topspace top) (p2bss_h atlas f Y) s0 /\
         p2bkf_phi (top,atlas) g Y (p2bss_h atlas f Y x - s0)
                   (p2bss_proj (top,atlas) g f Y s0 x) = x /\
         (p2bss_h atlas f Y x = s0 ==> p2bss_proj (top,atlas) g f Y s0 x = x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `Y:A->real^N`; `s0 - p2bss_h atlas f (Y:A->real^N) x`; `x:A`]
         P2BKF_PHI_INVERSE) THEN
  ASM_REWRITE_TAC[REAL_NEG_SUB] THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2bss_h atlas f (Y:A->real^N) (p2bss_proj (top,atlas) (g:A->real^N^N) f Y s0 x) = s0`
  ASSUME_TAC THENL
   [REWRITE_TAC[p2bss_proj] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `f:A->real`; `Y:A->real^N`; `s0 - p2bss_h atlas f (Y:A->real^N) x`; `x:A`]
           P2BSS_H_PHI) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[lvs_set; IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[p2bss_proj] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[REAL_SUB_REFL; p2bkf_phi] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`; `(Y:A->real^N) x`] MFD_GEO_MAXIMAL) THEN
  ASM_SIMP_TAC[]);;

let P2BSS_PROJ_CONTINUOUS = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f (Y:A->real^3) s0.
     hausdorff_space top /\ p2b_shrinker (top,atlas) g f /\ mfd_complete (top,atlas) g /\
     p2b_parallel_on atlas g (topspace top) Y /\
     (!x. x IN topspace top ==> Y x dot (g x ** Y x) = &1)
     ==> continuous_map (top,top) (p2bss_proj (top,atlas) g f Y s0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  MATCH_MP_TAC TOPC_CONTINUOUS_MAP_LOCAL THEN X_GEN_TAC `x0:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(g:A->real^3^3) x0 ** (Y:A->real^3) x0`; `(Y:A->real^3) x0`]
         P2BKF_HCOMPLEMENT) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^3` (X_CHOOSE_THEN `u2:real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `Y:A->real^3`; `x0:A`; `u1:real^3`; `u2:real^3`] P2BKF_FMAP_PARAM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `Y:A->real^3`; `x0:A`; `u1:real^3`; `u2:real^3`] P2BKF_FMAP_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `Y:A->real^3`; `x0:A`; `u1:real^3`; `u2:real^3`; `vec 0:real^3`] P2BKF_FMAP_D0) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN
   `!z r. p2bkf_fmap (top,atlas) (g:A->real^3^3) Y x0 u1 u2 (z + r % basis 3) =
          p2bkf_phi (top,atlas) g Y r (p2bkf_fmap (top,atlas) g (Y:A->real^3) x0 u1 u2 z)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC P2BKF_FMAP_SHIFT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `Fm = p2bkf_fmap (top,atlas) (g:A->real^3^3) Y x0 u1 u2` THEN
  UNDISCH_TAC `mfd_param top (atlas:((A->bool)#(A->real^3))->bool) V (Fm:real^3->A)` THEN
  REWRITE_TAC[mfd_param; mfd_diffeo; HOMEOMORPHIC_MAPS_MAP] THEN
  DISCH_THEN(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (Fm:real^3->A) V` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
  EXISTS_TAC `(Fm:real^3->A) o
              (\z. z + (s0 - p2bss_h atlas f (Y:A->real^3) (Fm z)) % basis 3) o (e':A->real^3)` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `y:A` THEN REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN STRIP_TAC THEN
    REWRITE_TAC[o_THM; p2bss_proj] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(Fm:real^3->A)((e':A->real^3) y) = y` (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `!y. y IN topspace (subtopology top (IMAGE (Fm:real^3->A) V))
                     ==> Fm((e':A->real^3) y) = y` THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `euclidean:(real^3)topology` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `euclidean:(real^3)topology` THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `homeomorphic_map (subtopology top (IMAGE (Fm:real^3->A) V),
                                   subtopology euclidean V) (e':A->real^3)` THEN
    REWRITE_TAC[HOMEOMORPHIC_MAP_MAPS; homeomorphic_maps; CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_VECTOR_ADD THEN REWRITE_TAC[CONTINUOUS_MAP_ID] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_VECTOR_MUL THEN REWRITE_TAC[CONTINUOUS_MAP_CONST] THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN
  SUBGOAL_THEN `(\z. p2bss_h atlas f (Y:A->real^3) ((Fm:real^3->A) z)) = p2bss_h atlas f Y o Fm`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `top:A topology` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BSS_H_CONTINUOUS THEN
  EXISTS_TAC `g:A->real^3^3` THEN ASM_REWRITE_TAC[]);;

(* The level sets of h are connected (images of the connected manifold). *)

let P2BSS_LEVEL_CONNECTED = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f (Y:A->real^3) s0.
     hausdorff_space top /\ connected_space top /\
     p2b_shrinker (top,atlas) g f /\ mfd_complete (top,atlas) g /\
     p2b_parallel_on atlas g (topspace top) Y /\
     (!x. x IN topspace top ==> Y x dot (g x ** Y x) = &1)
     ==> connected_space (subtopology top (lvs_set (topspace top) (p2bss_h atlas f Y) s0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CONNECTED_SPACE_SUBTOPOLOGY THEN
  SUBGOAL_THEN
   `lvs_set (topspace top) (p2bss_h atlas f (Y:A->real^3)) s0 =
    IMAGE (p2bss_proj (top,atlas) (g:A->real^3^3) f Y s0) (topspace top)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN CONJ_TAC THENL
     [X_GEN_TAC `x:A` THEN REWRITE_TAC[lvs_set; IN_ELIM_THM; IN_IMAGE] THEN STRIP_TAC THEN
      EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `f:A->real`; `Y:A->real^3`; `s0:real`; `x:A`] P2BSS_PROJ_FACTS) THEN
      ASM_SIMP_TAC[];
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `f:A->real`; `Y:A->real^3`; `s0:real`; `x:A`] P2BSS_PROJ_FACTS) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN EXISTS_TAC `top:A topology` THEN
  ASM_REWRITE_TAC[CONNECTED_IN_TOPSPACE] THEN MATCH_MP_TAC P2BSS_PROJ_CONTINUOUS THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* In dimension 3, if the curvature kills a parallel unit field W, then on   *)
(* the orthogonal complement of W the Ricci form is R/2 times the metric.    *)
(* ========================================================================= *)

let P2BSS_RIC_HORIZ = prove
 (`!U (G:real^3->real^3^3) (W:real^3->real^3) y u v a b.
     metric_field U G /\ smooth_map_on U W /\
     (!z w. z IN U ==> frechet_derivative W (at z) w + christoffel G z w (W z) = vec 0) /\
     y IN U /\
     u dot (G y ** u) = &1 /\ v dot (G y ** v) = &1 /\ W y dot (G y ** W y) = &1 /\
     u dot (G y ** v) = &0 /\ u dot (G y ** W y) = &0 /\ v dot (G y ** W y) = &0 /\
     a dot (G y ** W y) = &0 /\ b dot (G y ** W y) = &0
     ==> lricci G y a b = lscalar G y / &2 * (a dot (G y ** b))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!p q. lriemann (G:real^3->real^3^3) y p q ((W:real^3->real^3) y) = vec 0`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC P2BX0_LRIEMANN_PARALLEL THEN
    EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. lricci (G:real^3->real^3^3) y ((W:real^3->real^3) y) w = &0 /\
                    lricci G y w (W y) = &0`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX0_LRICCI_PAR THEN EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `n = (W:real^3->real^3) y` THEN
  MP_TAC(ISPECL [`(G:real^3->real^3^3) y`; `u:real^3`; `v:real^3`; `n:real^3`]
         RFA_ORTHO3_MATRIX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN MATCH_MP_TAC LRG_METRIC_SYM THEN
    EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `S:real^3^3` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `!p w. lriemann (G:real^3->real^3^3) y p p w = vec 0` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `p:real^3`; `p:real^3`;
                   `w:real^3`] LRIEMANN_ANTISYM) THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!p q z. z dot ((G:real^3->real^3^3) y ** lriemann G y p q z) = &0`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `p:real^3`; `q:real^3`;
                   `z:real^3`; `z:real^3`] LRIEMANN_METRIC_ANTISYM) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!p z. n dot ((G:real^3->real^3^3) y ** lriemann G y n p z) = &0`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `n:real^3`; `p:real^3`;
                   `z:real^3`; `n:real^3`] LRIEMANN_METRIC_ANTISYM) THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_NEG_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `u dot ((G:real^3->real^3^3) y ** lriemann G y u v v) =
                v dot (G y ** lriemann G y v u u)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `u:real^3`; `v:real^3`;
                   `v:real^3`; `u:real^3`] LRIEMANN_METRIC_ANTISYM) THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `u:real^3`; `v:real^3`;
                   `u:real^3`] LRIEMANN_ANTISYM) THEN
    REWRITE_TAC[ASSUME `metric_field U (G:real^3->real^3^3)`; ASSUME `(y:real^3) IN U`] THEN
    DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_RNEG; DOT_RNEG];
    ALL_TAC] THEN
  ABBREV_TAC `K = v dot ((G:real^3->real^3^3) y ** lriemann G y v u u)` THEN
  SUBGOAL_THEN `lricci (G:real^3->real^3^3) y u v = &0 /\ lricci G y u u = K /\
                lricci G y v v = K`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `!p q. lricci (G:real^3->real^3^3) y p q =
                        u dot (G y ** lriemann G y u p q) + v dot (G y ** lriemann G y v p q) +
                        n dot (G y ** lriemann G y n p q)`
    (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN
      MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`;
                     `p:real^3`; `q:real^3`] RFA_RIC_FRAME_RM) THEN
      ASM_REWRITE_TAC[DIMINDEX_3; SUM_3; lrm4] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_ADD_LID; REAL_ADD_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN `lricci (G:real^3->real^3^3) y v u = &0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `v:real^3`;
                   `u:real^3`] LRICCI_SYM) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lscalar (G:real^3->real^3^3) y = &2 * K` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`]
           RFA_SCAL_FRAME) THEN
    ASM_REWRITE_TAC[DIMINDEX_3; SUM_3; MATRIX_VECTOR_MUL_RZERO; DOT_RZERO] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`;
                 `a:real^3`; `b:real^3`] RFA_FRAME3_RIC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC `~(i:num = j)` THEN
    SUBGOAL_THEN `(i = 1 \/ i = 2 \/ i = 3) /\ (j = 1 \/ j = 2 \/ j = 3)` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC)
                               (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_ADD_LID; REAL_ADD_RID];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`(G:real^3->real^3^3) y`; `S:real^3^3`; `a:real^3`; `b:real^3`]
         RFA_FRAME3_DOT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] LRG_METRIC_INVERTIBLE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `n dot ((G:real^3->real^3^3) y ** a) = &0` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `n:real^3`;
                   `a:real^3`] LRG_METRIC_SYM) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The level sets of h are totally geodesic, have the scalar curvature of    *)
(* the ambient manifold, and are two-dimensional shrinkers for the           *)
(* restriction of f.                                                         *)
(* ========================================================================= *)

(* The chart facts of a parallel field on the whole manifold. *)

let P2BSS_PAR_CHART = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (Y:A->real^N) c.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     p2b_parallel_on atlas g (topspace top) Y /\ c IN atlas
     ==> metric_field (IMAGE (SND c) (FST c)) (metric_local atlas c g) /\
         smooth_map_on (IMAGE (SND c) (FST c)) (mfd_vrep atlas Y c) /\
         !y z. y IN IMAGE (SND c) (FST c)
               ==> frechet_derivative (mfd_vrep atlas Y c) (at y) z +
                   christoffel (metric_local atlas c g) y z (mfd_vrep atlas Y c y) = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER topspace top) =
                IMAGE (SND c) (FST c)` ASSUME_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[SET_RULE `(s:A->bool) INTER t = s <=> s SUBSET t`] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_parallel_on] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2b_parallel_on")) (concl th))) THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `c:(A->bool)#(A->real^N)` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "smooth_map_on" with Failure _ -> false))
          (concl th))) THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* Ric(Y,.) = 0 on the manifold. *)

let P2BSS_RIC_Y = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (Y:A->real^N) x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     p2b_parallel_on atlas g (topspace top) Y /\ x IN topspace top
     ==> !w. mfd_ricci atlas g x (Y x) w = &0 /\ mfd_ricci atlas g x w (Y x) = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `Y:A->real^N`; `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`]
         P2BSS_PAR_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `Y:A->real^N`; `x:A`]
         P2BX0_VREP_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[mfd_ricci] THEN MATCH_MP_TAC P2BX0_LRICCI_PAR THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                    (FST(chart_at atlas x))` THEN
  REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
  ASM_REWRITE_TAC[]);;

(* Tangent vectors of the level sets are orthogonal to Y. *)

let P2BSS_CONG_DOT = prove
 (`!(Dm:real^M^N) (g0:real^N^N) (p:real^M) q.
     (Dm ** p) dot (g0 ** (Dm ** q)) = p dot ((transp Dm ** g0 ** Dm) ** q)`,
  REWRITE_TAC[GSYM DOT_MATRIX_TRANSP_RMUL; MATRIX_VECTOR_MUL_ASSOC; MATRIX_MUL_ASSOC]);;

let P2BSS_JAC_TANGENT = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f (Y:A->real^3) s0 x z.
     p2b_shrinker (top,atlas) g f /\ p2b_parallel_on atlas g (topspace top) Y /\
     (!x. x IN topspace top ==> Y x dot (g x ** Y x) = &1) /\
     x IN lvs_set (topspace top) (p2bss_h atlas f Y) s0
     ==> lvs_jac top atlas (topspace top) (p2bss_h atlas f Y) s0 x z dot (g x ** Y x) = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:A) IN lvs_set (topspace top) (p2bss_h atlas f (Y:A->real^3)) s0` THEN
    SIMP_TAC[lvs_set; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `lvs_regular (atlas:((A->bool)#(A->real^3))->bool) (topspace top)
                            (p2bss_h atlas f (Y:A->real^3)) s0` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BSS_H_REGULAR THEN EXISTS_TAC `g:A->real^3^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `topspace top:A->bool`; `p2bss_h atlas f (Y:A->real^3)`; `s0:real`; `x:A`]
         LVS_POINT_FORM) THEN
  ASM_REWRITE_TAC[OPEN_IN_TOPSPACE] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3->bool` (X_CHOOSE_THEN `G:real^3->real^3^3`
    (X_CHOOSE_THEN `z0:real^2` (X_CHOOSE_THEN `D:real^3->real^3` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `Y:A->real^3`; `x:A`] P2BSS_H_NORMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `invertible(transp(matrix(D:real^3->real^3)) ** (g:A->real^3^3) x ** matrix D)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `invertible((G:real^3->real^3^3)(lvs_iota z0))` MP_TAC THENL
     [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(Y:A->real^3) x =
    inv(sqrt(basis 3 dot (matrix_inv(transp(matrix(D:real^3->real^3)) ** (g:A->real^3^3) x **
                                     matrix D) ** basis 3))) %
    D(matrix_inv(transp(matrix D) ** g x ** matrix D) ** basis 3)`
  SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_RMUL; REAL_ENTIRE] THEN DISJ2_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP MATRIX_WORKS th)]) THEN
  REWRITE_TAC[P2BSS_CONG_DOT; MATRIX_VECTOR_MUL_ASSOC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MATRIX_INV th]) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LID] THEN
  SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH; LVS_IOTA_COMPONENT]);;

(* Ric = (R/2) g on vectors orthogonal to Y, at the points of a level set. *)

let P2BSS_RIC_TANGENT = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f (Y:A->real^3) s0 x a b.
     p2b_shrinker (top,atlas) g f /\ p2b_parallel_on atlas g (topspace top) Y /\
     (!x. x IN topspace top ==> Y x dot (g x ** Y x) = &1) /\
     x IN lvs_set (topspace top) (p2bss_h atlas f Y) s0 /\
     a dot (g x ** Y x) = &0 /\ b dot (g x ** Y x) = &0
     ==> mfd_ricci atlas g x a b = mfd_scalar atlas g x / &2 * (a dot (g x ** b))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:A) IN lvs_set (topspace top) (p2bss_h atlas f (Y:A->real^3)) s0` THEN
    SIMP_TAC[lvs_set; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `lvs_regular (atlas:((A->bool)#(A->real^3))->bool) (topspace top)
                            (p2bss_h atlas f (Y:A->real^3)) s0` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BSS_H_REGULAR THEN EXISTS_TAC `g:A->real^3^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `topspace top:A->bool`; `p2bss_h atlas f (Y:A->real^3)`; `s0:real`; `x:A`]
         LVS_GAUSS_FRAME) THEN
  ASM_REWRITE_TAC[OPEN_IN_TOPSPACE] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `Y:A->real^3`; `x:A`] P2BSS_H_NORMAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:real^2` (X_CHOOSE_THEN `v2:real^2` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `Y:A->real^3`; `chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)`]
         P2BSS_PAR_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[mfd_ricci; mfd_scalar] THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                        (FST(chart_at atlas x))`;
                 `metric_local atlas (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A))
                               (g:A->real^3^3)`;
                 `mfd_vrep atlas (Y:A->real^3) (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) x`;
                 `lvs_jac top atlas (topspace top) (p2bss_h atlas f (Y:A->real^3)) s0 x v1`;
                 `lvs_jac top atlas (topspace top) (p2bss_h atlas f (Y:A->real^3)) s0 x v2`;
                 `a:real^3`; `b:real^3`] P2BSS_RIC_HORIZ) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `Y:A->real^3`; `x:A`]
         P2BX0_VREP_AT) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `x:A`]
         METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
                  REWRITE_TAC[]]);;

(* The scalar curvature of a level set is that of the manifold. *)

let P2BSS_LEVEL_SCALAR = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f (Y:A->real^3) s0 x.
     p2b_shrinker (top,atlas) g f /\ p2b_parallel_on atlas g (topspace top) Y /\
     (!x. x IN topspace top ==> Y x dot (g x ** Y x) = &1) /\
     x IN lvs_set (topspace top) (p2bss_h atlas f Y) s0
     ==> mfd_scalar (lvs_atlas top atlas (topspace top) (p2bss_h atlas f Y) s0)
                    (lvs_metric top atlas g (topspace top) (p2bss_h atlas f Y) s0) x =
         mfd_scalar atlas g x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:A) IN lvs_set (topspace top) (p2bss_h atlas f (Y:A->real^3)) s0` THEN
    SIMP_TAC[lvs_set; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `lvs_regular (atlas:((A->bool)#(A->real^3))->bool) (topspace top)
                            (p2bss_h atlas f (Y:A->real^3)) s0` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BSS_H_REGULAR THEN EXISTS_TAC `g:A->real^3^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `topspace top:A->bool`; `p2bss_h atlas f (Y:A->real^3)`; `s0:real`; `x:A`]
         LVS_GAUSS) THEN
  ASM_REWRITE_TAC[OPEN_IN_TOPSPACE] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `Y:A->real^3`; `x:A`] P2BSS_H_NORMAL) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `Y:A->real^3`; `s0:real`; `x:A`] P2BSS_H_II) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `Y:A->real^3`; `x:A`] P2BSS_RIC_Y) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_THEN SUBST1_TAC THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  ASM_REWRITE_TAC[MATRIX_MUL_RZERO; DET_0] THEN REAL_ARITH_TAC);;

(* The manifold Hessian is the chart Hessian in the preferred chart. *)

let P2BSS_HESS_CMP = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f x u v.
     p2b_mfd_hess atlas g f x u v =
     cmp_lhess (metric_local atlas (chart_at atlas x) g)
               (\y. f(chart_inv (chart_at atlas x) y)) (SND(chart_at atlas x) x) u v`,
  REWRITE_TAC[p2b_mfd_hess; cmp_lhess]);;

(* In dimension 2, Ric = (R/2) g. *)

let P2BSS_EINSTEIN2_MFD = prove
 (`!top (atlas:((A->bool)#(A->real^2))->bool) (g:A->real^2^2) x u v.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top
     ==> mfd_ricci atlas g x u v = mfd_scalar atlas g x / &2 * (u dot (g x ** v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^2))->bool) (x:A)))
                                    (FST(chart_at atlas x)))
                             (metric_local atlas (chart_at atlas x) (g:A->real^2^2))` ASSUME_TAC THENL
   [UNDISCH_TAC `riemannian_metric atlas (g:A->real^2^2)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^2))->bool) (x:A)))
                        (FST(chart_at atlas x))`;
                 `metric_local atlas (chart_at (atlas:((A->bool)#(A->real^2))->bool) (x:A))
                               (g:A->real^2^2)`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^2))->bool) (x:A)) x`] RFA_S2_EINSTEIN2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
                  ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`u:real^2`; `v:real^2`] o CONJUNCT1) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`; `x:A`]
         METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[mfd_ricci; mfd_scalar]);;

(* The level sets of h are two-dimensional shrinkers for f. *)

let P2BSS_LEVEL_SHRINKER = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f (Y:A->real^3) s0.
     p2b_shrinker (top,atlas) g f /\ p2b_parallel_on atlas g (topspace top) Y /\
     (!x. x IN topspace top ==> Y x dot (g x ** Y x) = &1)
     ==> p2b_shrinker
           (subtopology top (lvs_set (topspace top) (p2bss_h atlas f Y) s0),
            lvs_atlas top atlas (topspace top) (p2bss_h atlas f Y) s0)
           (lvs_metric top atlas g (topspace top) (p2bss_h atlas f Y) s0) f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  SUBGOAL_THEN `lvs_regular (atlas:((A->bool)#(A->real^3))->bool) (topspace top)
                            (p2bss_h atlas f (Y:A->real^3)) s0` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BSS_H_REGULAR THEN EXISTS_TAC `g:A->real^3^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (subtopology top (lvs_set (topspace top) (p2bss_h atlas f (Y:A->real^3)) s0))
                          (lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) (topspace top)
                                     (p2bss_h atlas f Y) s0) /\
    riemannian_metric (lvs_atlas top atlas (topspace top) (p2bss_h atlas f Y) s0)
                      (lvs_metric top atlas (g:A->real^3^3) (topspace top) (p2bss_h atlas f Y) s0) /\
    topspace (subtopology top (lvs_set (topspace top) (p2bss_h atlas f Y) s0)) =
    lvs_set (topspace top) (p2bss_h atlas f Y) s0`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[LVS_MANIFOLD; LVS_RIEMANNIAN; OPEN_IN_TOPSPACE; LVS_TOPSPACE]; ALL_TAC] THEN
  REWRITE_TAC[p2b_shrinker] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LVS_SMOOTH_RESTRICT THEN ASM_REWRITE_TAC[OPEN_IN_TOPSPACE]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `a:real^2`; `b:real^2`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:A) IN lvs_set (topspace top) (p2bss_h atlas f (Y:A->real^3)) s0` THEN
    SIMP_TAC[lvs_set; IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology top (lvs_set (topspace top) (p2bss_h atlas f (Y:A->real^3)) s0)`;
                 `lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) (topspace top)
                            (p2bss_h atlas f (Y:A->real^3)) s0`;
                 `lvs_metric top atlas (g:A->real^3^3) (topspace top) (p2bss_h atlas f (Y:A->real^3)) s0`;
                 `x:A`; `a:real^2`; `b:real^2`] P2BSS_EINSTEIN2_MFD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `Y:A->real^3`; `s0:real`; `x:A`] P2BSS_LEVEL_SCALAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `topspace top:A->bool`; `p2bss_h atlas f (Y:A->real^3)`; `s0:real`; `f:A->real`;
                 `x:A`; `a:real^2`; `b:real^2`] LVS_HESS) THEN
  ASM_REWRITE_TAC[OPEN_IN_TOPSPACE; GSYM P2BSS_HESS_CMP] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `Y:A->real^3`; `s0:real`; `x:A`] P2BSS_H_II) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LZERO; DOT_RZERO; REAL_MUL_RZERO; REAL_SUB_RZERO] THEN
  DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC `J = lvs_jac top (atlas:((A->bool)#(A->real^3))->bool) (topspace top)
                          (p2bss_h atlas f (Y:A->real^3)) s0 x` THEN
  SUBGOAL_THEN `linear (J:real^2->real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `topspace top:A->bool`;
                   `p2bss_h atlas f (Y:A->real^3)`; `s0:real`; `x:A`] LVS_JAC_FACTS) THEN
    ASM_SIMP_TAC[OPEN_IN_TOPSPACE];
    ALL_TAC] THEN
  SUBGOAL_THEN `a dot (lvs_metric top atlas (g:A->real^3^3) (topspace top)
                         (p2bss_h atlas f (Y:A->real^3)) s0 x ** b) =
                (J:real^2->real^3) a dot (g x ** J b)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[lvs_metric] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP MATRIX_WORKS th)]) THEN
    REWRITE_TAC[P2BSS_CONG_DOT];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. (J:real^2->real^3) z dot ((g:A->real^3^3) x ** (Y:A->real^3) x) = &0`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "J" THEN MATCH_MP_TAC P2BSS_JAC_TANGENT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `Y:A->real^3`; `s0:real`; `x:A`;
                 `(J:real^2->real^3) a`; `(J:real^2->real^3) b`] P2BSS_RIC_TANGENT) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `(J:real^2->real^3) a`; `(J:real^2->real^3) b`] o check (fun th ->
    can (find_term (fun t -> try fst(dest_const t) = "p2b_mfd_hess" with Failure _ -> false))
        (concl th) && is_forall(concl th))) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* On a connected 2-d shrinker, d(R exp(-f)) = 0, so R = C exp f (no         *)
(* positivity assumption).                                                   *)
(* ========================================================================= *)

let P2BSS_REXPF_DERIV0 = prove
 (`!U (G:real^2->real^2^2) (pf:real^2->real) z.
     metric_field U G /\ z IN U /\ smooth_map_on U (\w. lift(pf w)) /\
     rfa_eqon U (lnabla 1 G (rfa_sh_df pf)) (\y u. inv(&2) * lmetric2 G y u - lric2 G y u)
     ==> ((\w. lift(lscalar G w * exp(--(pf w)))) has_derivative (\v. vec 0)) (at z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^2->bool)` ASSUME_TAC THENL [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\w. lift(lscalar (G:real^2->real^2^2) w)) has_derivative
     frechet_derivative (\x. lift(lscalar G x)) (at z)) (at z)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^2->bool` THEN
    ASM_SIMP_TAC[LRG_LSCALAR_SMOOTH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\w. lift((pf:real^2->real) w)) has_derivative
     frechet_derivative (\x. lift(pf x)) (at z)) (at z)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\w. lift(exp(--((pf:real^2->real) w)))) has_derivative
     (\h. exp(--(pf z)) % --(frechet_derivative (\x. lift(pf x)) (at z) h))) (at z)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\w. lift(exp(--((pf:real^2->real) w)))) =
                  (lift o exp o drop) o (\w. --(lift(pf w)))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; DROP_NEG; LIFT_DROP]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\h. exp(--((pf:real^2->real) z)) % --(frechet_derivative (\x. lift(pf x)) (at z) h)) =
      (\x. exp(--(pf z)) % x) o (\h. --(frechet_derivative (\x. lift(pf x)) (at z) h))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_NEG THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM LIFT_NEG; GSYM HAS_REAL_FRECHET_DERIVATIVE_AT;
                  HAS_REAL_DERIVATIVE_EXP]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`lscalar (G:real^2->real^2^2)`;
                 `\h. drop(frechet_derivative (\x. lift(lscalar (G:real^2->real^2^2) x)) (at z) h)`;
                 `\w. lift(exp(--((pf:real^2->real) w)))`;
                 `\h. exp(--((pf:real^2->real) z)) % --(frechet_derivative (\x. lift(pf x)) (at z) h)`;
                 `z:real^2`] HAS_DERIVATIVE_MUL_AT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; LIFT_CMUL];
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `h:real^2` THEN
    REWRITE_TAC[GSYM DROP_EQ; DROP_ADD; DROP_CMUL; DROP_NEG; DROP_VEC; LIFT_DROP] THEN
    MP_TAC(ISPECL [`U:real^2->bool`; `G:real^2->real^2^2`; `pf:real^2->real`; `z:real^2`;
                   `h:real^2`] RFA_S2_DR_DF) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC]);;

let P2BSS_S2_SCAL_EXPF = prove
 (`!top (atlas:((A->bool)#(A->real^2))->bool) (g:A->real^2^2) (f:A->real).
     connected_space top /\ p2b_shrinker (top,atlas) g f
     ==> ?C. !x. x IN topspace top ==> mfd_scalar atlas g x = C * exp(f x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                 `\x:A. mfd_scalar atlas (g:A->real^2^2) x * exp(--((f:A->real) x))`]
                RFA_S2_LOCCONST_CHART) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^2)`; `z:real^2`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                   `f:A->real`; `c:(A->bool)#(A->real^2)`] RFA_SH_CHART_DATA) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                   `c:(A->bool)#(A->real^2)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!w. w IN IMAGE (SND (c:(A->bool)#(A->real^2))) (FST c)
          ==> mfd_scalar atlas (g:A->real^2^2) (chart_inv c w) =
              lscalar (metric_local atlas c g) w`
    ASSUME_TAC THENL
     [X_GEN_TAC `w:real^2` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                     `c:(A->bool)#(A->real^2)`; `chart_inv (c:(A->bool)#(A->real^2)) w`]
                    RFA_SH_QR_CHART) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    EXISTS_TAC `\w. lift(lscalar (metric_local atlas c (g:A->real^2^2)) w *
                         exp(--((\y. (f:A->real)(chart_inv (c:(A->bool)#(A->real^2)) y)) w)))` THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^2))) (FST c)` THEN
    ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC P2BSS_REXPF_DERIV0 THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^2))) (FST c)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`;
                 `\x:A. mfd_scalar atlas (g:A->real^2^2) x * exp(--((f:A->real) x))`]
                RFA_SH_LOCCONST_CONNECTED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC `topspace top:A->bool = {}` THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY]; ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `x0:A` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  EXISTS_TAC `mfd_scalar atlas (g:A->real^2^2) x0 * exp(--((f:A->real) x0))` THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x0:A`; `x:A`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC; GSYM REAL_EXP_ADD] THEN
  REWRITE_TAC[REAL_ARITH `--x + x = &0`; REAL_EXP_0; REAL_MUL_RID]);;

(* ========================================================================= *)
(* A compact level set of h is a round surface (RFA_P2B_REQ_SHRINKER_ROUND,  *)
(* 2-d clause); scaling its metric by the curvature gives curvature 1.       *)
(* ========================================================================= *)

let P2BSS_SEC_SCALE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) q x u v.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top /\
     &0 < q
     ==> mfd_sectional atlas (\z. q %% g z) x u v = mfd_sectional atlas g x u v / q`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                                    (FST(chart_at atlas x)))
                             (metric_local atlas (chart_at atlas x) (g:A->real^N^N))` ASSUME_TAC THENL
   [UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_sectional; METRIC_LOCAL_CMUL; lsectional] THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                        (FST(chart_at atlas x))`;
                 `metric_local atlas (chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))
                               (g:A->real^N^N)`;
                 `q:real`; `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) x`;
                 `u:real^N`; `v:real^N`; `v:real^N`] LRIEMANN_SCALE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
                  DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL] THEN
  ABBREV_TAC `D = (u dot (metric_local atlas (chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))
                          (g:A->real^N^N) (SND(chart_at atlas x) x) ** u)) *
                  (v dot (metric_local atlas (chart_at atlas x) g (SND(chart_at atlas x) x) ** v)) -
                  (u dot (metric_local atlas (chart_at atlas x) g (SND(chart_at atlas x) x) ** v))
                  pow 2` THEN
  REWRITE_TAC[REAL_ARITH `(q * a) * (q * b) - (q * c) pow 2 = q pow 2 * (a * b - c pow 2)`] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `D = &0` THENL
   [ASM_REWRITE_TAC[REAL_MUL_RZERO; real_div; REAL_INV_0; REAL_MUL_RZERO; REAL_MUL_LZERO];
    UNDISCH_TAC `~(D = &0)` THEN UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD]);;

(* The compact level set through a point of positive scalar curvature is  *)
(* round.                                                                    *)

let P2BSS_LEVEL_ROUND = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f (Y:A->real^3) s0 C.
     hausdorff_space top /\ connected_space top /\
     p2b_shrinker (top,atlas) g f /\ mfd_complete (top,atlas) g /\
     p2b_parallel_on atlas g (topspace top) Y /\
     (!x. x IN topspace top ==> Y x dot (g x ** Y x) = &1) /\
     compact_in top (lvs_set (topspace top) (p2bss_h atlas f Y) s0) /\ &0 < C /\
     (!x. x IN lvs_set (topspace top) (p2bss_h atlas f Y) s0
          ==> mfd_scalar atlas g x = C * exp(f x))
     ==> p2b_round (subtopology top (lvs_set (topspace top) (p2bss_h atlas f Y) s0),
                    lvs_atlas top atlas (topspace top) (p2bss_h atlas f Y) s0)
                   (lvs_metric top atlas g (topspace top) (p2bss_h atlas f Y) s0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `Y:A->real^3`; `s0:real`] P2BSS_LEVEL_SHRINKER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `(:A)` RFA_P2B_REQ_SHRINKER_ROUND) THEN
  REWRITE_TAC[P2B_REQ_RFA_SHRINKER_ROUND_STATEMENT] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN EXISTS_TAC `f:A->real` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `topspace (subtopology top (lvs_set (topspace top) (p2bss_h atlas f (Y:A->real^3)) s0)) =
                lvs_set (topspace top) (p2bss_h atlas f Y) s0` ASSUME_TAC THENL
   [MATCH_MP_TAC LVS_TOPSPACE THEN REWRITE_TAC[OPEN_IN_TOPSPACE]; ALL_TAC] THEN
  ASM_SIMP_TAC[LVS_HAUSDORFF; LVS_COMPACT] THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2BSS_LEVEL_CONNECTED THEN EXISTS_TAC `g:A->real^3^3` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology top (lvs_set (topspace top) (p2bss_h atlas f (Y:A->real^3)) s0)`;
                 `lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) (topspace top)
                            (p2bss_h atlas f (Y:A->real^3)) s0`;
                 `lvs_metric top atlas (g:A->real^3^3) (topspace top) (p2bss_h atlas f (Y:A->real^3)) s0`;
                 `x:A`; `u:real^2`; `v:real^2`] RFA_S2_MFD_SEC_SCAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `p2b_shrinker
       (subtopology top (lvs_set (topspace top) (p2bss_h atlas f (Y:A->real^3)) s0),
        lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) (topspace top) (p2bss_h atlas f Y) s0)
       (lvs_metric top atlas (g:A->real^3^3) (topspace top) (p2bss_h atlas f Y) s0) f` THEN
    SIMP_TAC[p2b_shrinker];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `Y:A->real^3`; `s0:real`; `x:A`] P2BSS_LEVEL_SCALAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `mfd_scalar atlas (g:A->real^3^3) x = C * exp((f:A->real) x)` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < a ==> &0 < a / &2`) THEN
  ASM_SIMP_TAC[REAL_LT_MUL; REAL_EXP_POS_LT]);;

(* ========================================================================= *)
(* In dimension 3, sec >= 0 gives R >= 0 and 0 <= Ric(w,w) <= R |w|^2.       *)
(* ========================================================================= *)

let P2BSS_ORTHO_PAIR_NONCOLL = prove
 (`!(G0:real^N^N) u v.
     u dot (G0 ** u) = &1 /\ v dot (G0 ** v) = &1 /\ u dot (G0 ** v) = &0
     ==> ~collinear {vec 0,u,v}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[COLLINEAR_LEMMA] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; DOT_LZERO;
                              MATRIX_VECTOR_MUL_RMUL; DOT_RMUL; DOT_LMUL]) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN CONV_TAC REAL_RING);;

let P2BSS_ONB3_COMPLETE = prove
 (`!(G0:real^3^3) w.
     (!a b. a dot (G0 ** b) = b dot (G0 ** a)) /\
     (!a. ~(a = vec 0) ==> &0 < a dot (G0 ** a)) /\
     w dot (G0 ** w) = &1
     ==> ?u v. u dot (G0 ** u) = &1 /\ v dot (G0 ** v) = &1 /\ u dot (G0 ** v) = &0 /\
               u dot (G0 ** w) = &0 /\ v dot (G0 ** w) = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(G0:real^3^3) ** w`; `w:real^3`] P2BKF_HCOMPLEMENT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^3` (X_CHOOSE_THEN `u2:real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "indep"))))) THEN
  SUBGOAL_THEN `~(u1:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    USE_THEN "indep" (MP_TAC o SPECL [`&1`; `&0`; `&0`]) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_RZERO; VECTOR_ADD_LID]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `n1 = sqrt(u1 dot ((G0:real^3^3) ** u1))` THEN
  SUBGOAL_THEN `&0 < n1 /\ n1 pow 2 = u1 dot ((G0:real^3^3) ** u1)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "n1" THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC SQRT_POW_2 THEN ASM_MESON_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  ABBREV_TAC `u = inv(n1) % (u1:real^3)` THEN
  SUBGOAL_THEN `u dot ((G0:real^3^3) ** u) = &1 /\ u dot (G0 ** w) = &0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_RMUL; DOT_LMUL] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < n1` THEN UNDISCH_TAC `n1 pow 2 = u1 dot ((G0:real^3^3) ** u1)` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ABBREV_TAC `v1 = u2 - (u2 dot ((G0:real^3^3) ** u)) % (u:real^3)` THEN
  SUBGOAL_THEN `~(v1:real^3 = vec 0)` ASSUME_TAC THENL
   [EXPAND_TAC "v1" THEN EXPAND_TAC "u" THEN
    ABBREV_TAC `k1 = u2 dot ((G0:real^3^3) ** (inv n1 % (u1:real^3)))` THEN DISCH_TAC THEN
    USE_THEN "indep" (MP_TAC o SPECL [`--(k1 * inv n1)`; `&1`; `&0`]) THEN ANTS_TAC THENL
     [UNDISCH_TAC `u2 - k1 % inv n1 % (u1:real^3) = vec 0` THEN VECTOR_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `n2 = sqrt(v1 dot ((G0:real^3^3) ** v1))` THEN
  SUBGOAL_THEN `&0 < n2 /\ n2 pow 2 = v1 dot ((G0:real^3^3) ** v1)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "n2" THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC SQRT_POW_2 THEN ASM_MESON_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `v1 dot ((G0:real^3^3) ** u) = &0 /\ v1 dot (G0 ** w) = &0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "v1" THEN
    REWRITE_TAC[DOT_LSUB; DOT_LMUL] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `u2 dot ((G0:real^3^3) ** w) = &0` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`u:real^3`; `inv(n2) % (v1:real^3)`] THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_RMUL; DOT_LMUL] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `&0 < n2` THEN UNDISCH_TAC `n2 pow 2 = v1 dot ((G0:real^3^3) ** v1)` THEN
    CONV_TAC REAL_FIELD;
    ONCE_ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[REAL_MUL_RZERO];
    REAL_ARITH_TAC]);;

let P2BSS_LRIC_SEC3 = prove
 (`!U (G:real^3->real^3^3) y.
     metric_field U G /\ y IN U /\
     (!u v. ~collinear {vec 0,u,v} ==> &0 <= lsectional G y u v)
     ==> &0 <= lscalar G y /\
         !w. &0 <= lricci G y w w /\ lricci G y w w <= lscalar G y / &2 * (w dot (G y ** w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!a b. a dot ((G:real^3->real^3^3) y ** b) = b dot (G y ** a)` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC LRG_METRIC_SYM THEN
    EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a. ~(a = vec 0) ==> &0 < a dot ((G:real^3->real^3^3) y ** a)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. e dot ((G:real^3->real^3^3) y ** e) = &1
        ==> &0 <= lscalar G y /\ &0 <= lricci G y e e /\ lricci G y e e <= lscalar G y / &2`
  ASSUME_TAC THENL
   [X_GEN_TAC `e:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`(G:real^3->real^3^3) y`; `e:real^3`] P2BSS_ONB3_COMPLETE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^3` (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `v dot ((G:real^3->real^3^3) y ** u) = &0 /\ e dot (G y ** u) = &0 /\
                  e dot (G y ** v) = &0` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN
      FIRST_ASSUM((fun th -> ONCE_REWRITE_TAC[th]) o check (fun th ->
        is_forall(concl th) && not (is_imp(snd(strip_forall(concl th)))))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`(G:real^3->real^3^3) y`; `u:real^3`; `v:real^3`; `e:real^3`]
           RFA_ORTHO3_MATRIX) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S:real^3^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `lscalar (G:real^3->real^3^3) y =
                  lricci G y u u + lricci G y v v + lricci G y e e` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`]
             RFA_SCAL_FRAME) THEN
      ASM_REWRITE_TAC[DIMINDEX_3; SUM_3];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `lsectional (G:real^3->real^3^3) y u v = lscalar G y / &2 - lricci G y e e /\
      lsectional G y u e = lscalar G y / &2 - lricci G y v v /\
      lsectional G y v e = lscalar G y / &2 - lricci G y u u`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `u:real^3`;
                       `v:real^3`; `e:real^3`] RFA_LSECTIONAL_PCURV_3D);
        MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `u:real^3`;
                       `e:real^3`; `v:real^3`] RFA_LSECTIONAL_PCURV_3D);
        MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `v:real^3`;
                       `e:real^3`; `u:real^3`] RFA_LSECTIONAL_PCURV_3D)] THEN
      ASM_REWRITE_TAC[lpcurv; lmetric2; lric2] THEN DISCH_THEN SUBST1_TAC THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= lsectional (G:real^3->real^3^3) y u v /\ &0 <= lsectional G y u e /\
                  &0 <= lsectional G y v e` MP_TAC THENL
     [REPEAT CONJ_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> try fst(dest_const t) = "collinear" with Failure _ -> false))
            (concl th))) THEN
      MATCH_MP_TAC P2BSS_ORTHO_PAIR_NONCOLL THEN EXISTS_TAC `(G:real^3->real^3^3) y` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `lscalar (G:real^3->real^3^3) y =
                 lricci G y u u + lricci G y v v + lricci G y e e` THEN
    UNDISCH_TAC `lsectional (G:real^3->real^3^3) y u v = lscalar G y / &2 - lricci G y e e` THEN
    UNDISCH_TAC `lsectional (G:real^3->real^3^3) y u e = lscalar G y / &2 - lricci G y v v` THEN
    UNDISCH_TAC `lsectional (G:real^3->real^3^3) y v e = lscalar G y / &2 - lricci G y u u` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!c a b. lricci (G:real^3->real^3^3) y (c % a) b = c * lricci G y a b /\
                        lricci G y a (c % b) = c * lricci G y a b` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] LRG_LRICCI_LINEAR) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th ->
      MP_TAC(SPECL [`c:real`; `a:real^3`]
        (MATCH_MP LINEAR_CMUL (SPEC `b:real^3` (CONJUNCT1 th)))) THEN
      MP_TAC(SPECL [`c:real`; `b:real^3`]
        (MATCH_MP LINEAR_CMUL (SPEC `a:real^3` (CONJUNCT2 th))))) THEN
    REWRITE_TAC[GSYM LIFT_CMUL; LIFT_EQ] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `b1 = inv(sqrt(basis 1 dot ((G:real^3->real^3^3) y ** basis 1))) % (basis 1:real^3)` THEN
  SUBGOAL_THEN `b1 dot ((G:real^3->real^3^3) y ** b1) = &1` ASSUME_TAC THENL
   [EXPAND_TAC "b1" THEN REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_RMUL; DOT_LMUL] THEN
    SUBGOAL_THEN `&0 < basis 1 dot ((G:real^3->real^3^3) y ** basis 1)` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH]; ALL_TAC] THEN
    MP_TAC(SPEC `basis 1 dot ((G:real^3->real^3^3) y ** basis 1)` SQRT_POW_2) THEN
    MP_TAC(SPEC `basis 1 dot ((G:real^3->real^3^3) y ** basis 1)` SQRT_POS_LT) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `w:real^3` THEN ASM_CASES_TAC `w:real^3 = vec 0` THENL
   [ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_MUL_RZERO] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`&0`; `vec 0:real^3`; `vec 0:real^3`]) THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; REAL_MUL_LZERO] THEN SIMP_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  ABBREV_TAC `n = sqrt(w dot ((G:real^3->real^3^3) y ** w))` THEN
  SUBGOAL_THEN `&0 < n /\ n pow 2 = w dot ((G:real^3->real^3^3) y ** w)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC SQRT_POW_2 THEN ASM_MESON_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^3) = n % (inv n % w)` SUBST1_TAC THENL
   [REWRITE_TAC[VECTOR_MUL_ASSOC] THEN ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ] THEN
    REWRITE_TAC[VECTOR_MUL_LID];
    ALL_TAC] THEN
  ABBREV_TAC `e = inv n % (w:real^3)` THEN
  SUBGOAL_THEN `e dot ((G:real^3->real^3^3) y ** e) = &1` ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_RMUL; DOT_LMUL] THEN
    UNDISCH_TAC `&0 < n` THEN UNDISCH_TAC `n pow 2 = w dot ((G:real^3->real^3^3) y ** w)` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real^3` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "lscalar" with Failure _ -> false))
        (concl th))) THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_RMUL; DOT_LMUL] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `lscalar (G:real^3->real^3^3) y / &2 * n * n * &1 = (n * n) * (lscalar G y / &2)`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE]);;

let P2BSS_MFD_RIC_SEC3 = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top /\
     (!u v. ~collinear {vec 0,u,v} ==> &0 <= mfd_sectional atlas g x u v)
     ==> &0 <= mfd_scalar atlas g x /\
         !w. &0 <= mfd_ricci atlas g x w w /\
             mfd_ricci atlas g x w w <= mfd_scalar atlas g x / &2 * (w dot (g x ** w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                                    (FST(chart_at atlas x)))
                             (metric_local atlas (chart_at atlas x) (g:A->real^3^3))` ASSUME_TAC THENL
   [UNDISCH_TAC `riemannian_metric atlas (g:A->real^3^3)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                        (FST(chart_at atlas x))`;
                 `metric_local atlas (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A))
                               (g:A->real^3^3)`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) x`] P2BSS_LRIC_SEC3) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM mfd_sectional] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `x:A`]
         METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[mfd_ricci; mfd_scalar]);;

(* A level set of h on which R = C exp f (C > 0) is compact: f is        *)
(* bounded above there and sublevel sets of f are compact (P2BX46_F_PROPER).*)

let P2BSS_LEVEL_COMPACT = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f (Y:A->real^3) s0 C K0.
     hausdorff_space top /\ connected_space top /\
     p2b_shrinker (top,atlas) g f /\ mfd_complete (top,atlas) g /\
     (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
              ==> &0 <= mfd_sectional atlas g x u v) /\
     (!x. x IN topspace top ==> mfd_scalar atlas g x <= K0) /\
     p2b_parallel_on atlas g (topspace top) Y /\
     &0 < C /\
     (!x. x IN lvs_set (topspace top) (p2bss_h atlas f Y) s0
          ==> mfd_scalar atlas g x = C * exp(f x))
     ==> compact_in top (lvs_set (topspace top) (p2bss_h atlas f Y) s0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  ASM_CASES_TAC `lvs_set (topspace top) (p2bss_h atlas f (Y:A->real^3)) s0 = {}` THENL
   [ASM_REWRITE_TAC[COMPACT_IN_EMPTY]; ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `z:A` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  SUBGOAL_THEN `(z:A) IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `(z:A) IN lvs_set (topspace top) (p2bss_h atlas f (Y:A->real^3)) s0` THEN
    SIMP_TAC[lvs_set; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < K0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `mfd_scalar atlas (g:A->real^3^3) z` THEN
    ASM_SIMP_TAC[REAL_LT_MUL; REAL_EXP_POS_LT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `K0 / &2`] P2BX46_F_PROPER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN
     `!x. x IN topspace top
          ==> &0 <= mfd_scalar atlas (g:A->real^3^3) x /\
              !w. &0 <= mfd_ricci atlas g x w w /\
                  mfd_ricci atlas g x w w <= mfd_scalar atlas g x / &2 * (w dot (g x ** w))`
    ASSUME_TAC THENL
     [X_GEN_TAC `x:A` THEN DISCH_TAC THEN MATCH_MP_TAC P2BSS_MFD_RIC_SEC3 THEN
      EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_MESON_TAC[];
      ASM_MESON_TAC[];
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:A`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `w:real^3`)) THEN
      STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `mfd_scalar atlas (g:A->real^3^3) y / &2 * (w dot (g y ** w))` THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 <= w dot ((g:A->real^3^3) y ** w)` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                       `y:A`] P2BSS_G_AT) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_CASES_TAC `w:real^3 = vec 0` THEN
        ASM_SIMP_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_LE_REFL; REAL_LT_IMP_LE];
        ALL_TAC] THEN
      SUBGOAL_THEN `mfd_scalar atlas (g:A->real^3^3) y <= K0` MP_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `&0 <= w dot ((g:A->real^3^3) y ** w)` THEN
      SPEC_TAC(`w dot ((g:A->real^3^3) y ** w)`,`q:real`) THEN
      SPEC_TAC(`mfd_scalar atlas (g:A->real^3^3) y`,`r:real`) THEN
      REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
      REWRITE_TAC[REAL_ARITH `&2 * K0 / &2 * q = K0 * q`;
                  REAL_ARITH `r / &2 * q = (r / &2) * q`] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `log(K0 / C)`) THEN DISCH_TAC THEN
  MATCH_MP_TAC CLOSED_COMPACT_IN THEN
  EXISTS_TAC `{x:A | x IN topspace top /\ f x <= log(K0 / C)}` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
     [UNDISCH_TAC `(x:A) IN lvs_set (topspace top) (p2bss_h atlas f (Y:A->real^3)) s0` THEN
      SIMP_TAC[lvs_set; IN_ELIM_THM];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `C * exp((f:A->real) x) <= K0` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `mfd_scalar atlas (g:A->real^3^3) x` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[REAL_LE_REFL]; ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(f:A->real) x = log(exp(f x))` SUBST1_TAC THENL
     [REWRITE_TAC[LOG_EXP]; ALL_TAC] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `topspace top:A->bool`; `p2bss_h atlas f (Y:A->real^3)`;
                 `s0:real`] LVS_CLOSED_IN) THEN
  REWRITE_TAC[OPEN_IN_TOPSPACE; SUBTOPOLOGY_TOPSPACE] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC P2BSS_H_CONTINUOUS THEN EXISTS_TAC `g:A->real^3^3` THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The level set of h through a point of positive scalar curvature is a      *)
(* compact connected 2-d shrinker of constant curvature k > 0, with R = C    *)
(* exp f on it.                                                              *)
(* ========================================================================= *)

let P2BSS_LEAF = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f (Y:A->real^3) x0 K0.
     hausdorff_space top /\ connected_space top /\
     p2b_shrinker (top,atlas) g f /\ mfd_complete (top,atlas) g /\
     (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
              ==> &0 <= mfd_sectional atlas g x u v) /\
     (!x. x IN topspace top ==> mfd_scalar atlas g x <= K0) /\
     x0 IN topspace top /\ &0 < mfd_scalar atlas g x0 /\
     p2b_parallel_on atlas g (topspace top) Y /\
     (!x. x IN topspace top ==> Y x dot (g x ** Y x) = &1)
     ==> x0 IN lvs_set (topspace top) (p2bss_h atlas f Y) (p2bss_h atlas f Y x0) /\
         compact_in top (lvs_set (topspace top) (p2bss_h atlas f Y) (p2bss_h atlas f Y x0)) /\
         connected_space
           (subtopology top (lvs_set (topspace top) (p2bss_h atlas f Y) (p2bss_h atlas f Y x0))) /\
         (?C. &0 < C /\
              !x. x IN lvs_set (topspace top) (p2bss_h atlas f Y) (p2bss_h atlas f Y x0)
                  ==> mfd_scalar atlas g x = C * exp(f x)) /\
         ?k. &0 < k /\
             !x u v. x IN lvs_set (topspace top) (p2bss_h atlas f Y) (p2bss_h atlas f Y x0) /\
                     ~collinear {vec 0,u,v}
                     ==> mfd_sectional
                           (lvs_atlas top atlas (topspace top) (p2bss_h atlas f Y)
                                      (p2bss_h atlas f Y x0))
                           (lvs_metric top atlas g (topspace top) (p2bss_h atlas f Y)
                                       (p2bss_h atlas f Y x0)) x u v = k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `s0 = p2bss_h atlas f (Y:A->real^3) x0` THEN
  SUBGOAL_THEN `(x0:A) IN lvs_set (topspace top) (p2bss_h atlas f (Y:A->real^3)) s0`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[lvs_set; IN_ELIM_THM]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `Y:A->real^3`; `s0:real`] P2BSS_LEVEL_CONNECTED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `Y:A->real^3`; `s0:real`] P2BSS_LEVEL_SHRINKER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `topspace (subtopology top (lvs_set (topspace top) (p2bss_h atlas f (Y:A->real^3)) s0)) =
                lvs_set (topspace top) (p2bss_h atlas f Y) s0` ASSUME_TAC THENL
   [MATCH_MP_TAC LVS_TOPSPACE THEN REWRITE_TAC[OPEN_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology top (lvs_set (topspace top) (p2bss_h atlas f (Y:A->real^3)) s0)`;
                 `lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) (topspace top)
                            (p2bss_h atlas f (Y:A->real^3)) s0`;
                 `lvs_metric top atlas (g:A->real^3^3) (topspace top) (p2bss_h atlas f (Y:A->real^3)) s0`;
                 `f:A->real`] P2BSS_S2_SCAL_EXPF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `C:real`) THEN
  SUBGOAL_THEN `!x. x IN lvs_set (topspace top) (p2bss_h atlas f (Y:A->real^3)) s0
                    ==> mfd_scalar atlas (g:A->real^3^3) x = C * exp((f:A->real) x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `f:A->real`; `Y:A->real^3`; `s0:real`; `x:A`] P2BSS_LEVEL_SCALAR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < C` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < C * exp((f:A->real) x0)` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_POS_LT; REAL_EXP_POS_LT] THEN
    MP_TAC(SPEC `(f:A->real) x0` REAL_EXP_POS_LT) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in top (lvs_set (topspace top) (p2bss_h atlas f (Y:A->real^3)) s0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BSS_LEVEL_COMPACT THEN
    MAP_EVERY EXISTS_TAC [`g:A->real^3^3`; `C:real`; `K0:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `Y:A->real^3`; `s0:real`; `C:real`] P2BSS_LEVEL_ROUND) THEN
  ASM_REWRITE_TAC[p2b_round] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `k:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The stereographic chart of the unit sphere as one Riemannian manifold,    *)
(* real^2 with Gs z = 4/(1+|z|^2)^2 I (curvature 1); its geodesics from 0    *)
(* are the rays t |-> tan(t |v|)/|v| v, and exp_0 is a parametrization of    *)
(* ball(0,pi/2) onto the whole plane.                                        *)
(* ========================================================================= *)

let p2bss_gs = new_definition
 `p2bss_gs (z:real^2) = (&4 / (&1 + norm z pow 2) pow 2) %% (mat 1:real^2^2)`;;

let P2BSS_GS_ETA = prove
 (`p2bss_gs = (\z:real^2. (&4 / (&1 + norm z pow 2) pow 2) %% mat 1)`,
  REWRITE_TAC[FUN_EQ_THM; p2bss_gs]);;

let P2BSS_GS_FACTS = prove
 (`hausdorff_space (euclidean:(real^2)topology) /\
   smooth_manifold_atlas euclidean (open_set_atlas (:real^2)) /\
   (!x:real^2. chart_at (open_set_atlas (:real^2)) x = ((:real^2),(\x. x))) /\
   metric_local (open_set_atlas (:real^2)) ((:real^2),(\x:real^2. x)) p2bss_gs = p2bss_gs /\
   riemannian_metric (open_set_atlas (:real^2)) p2bss_gs /\
   (!x u v. ~collinear {vec 0,u,v}
            ==> mfd_sectional (open_set_atlas (:real^2)) p2bss_gs x u v = &1)`,
  REWRITE_TAC[GEOL_EUCLID_FACTS; P2BSR_METRIC_LOCAL_EUCLID] THEN CONJ_TAC THENL
   [REWRITE_TAC[riemannian_metric; open_set_atlas; IN_SING] THEN GEN_TAC THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[GSYM open_set_atlas; P2BSR_METRIC_LOCAL_EUCLID] THEN
    REWRITE_TAC[IMAGE_ID; P2BSS_GS_ETA; LRG_SPH_METRIC];
    REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_sectional; GEOL_EUCLID_FACTS] THEN
    REWRITE_TAC[P2BSR_METRIC_LOCAL_EUCLID; P2BSS_GS_ETA] THEN
    MATCH_MP_TAC LSECTIONAL_ROUND_SPHERE_2 THEN ASM_REWRITE_TAC[]]);;

let P2BSS_GS_CHRISTOFFEL = prove
 (`!z a b:real^2.
     christoffel p2bss_gs z a b =
     (--(&2) / (&1 + norm z pow 2)) % ((z dot a) % b + (z dot b) % a - (a dot b) % z)`,
  REWRITE_TAC[P2BSS_GS_ETA; LRG_SPH_CHRISTOFFEL]);;

(* Derivatives along the rays. *)

let P2BSS_TAN_RAY_DERIV = prove
 (`!s t. &0 < s /\ abs(t * s) < pi / &2
         ==> ((\t. tan(t * s) / s) has_real_derivative inv(cos(t * s) pow 2)) (atreal t) /\
             ((\t. inv(cos(t * s) pow 2)) has_real_derivative
              (&2 * s * tan(t * s) * inv(cos(t * s) pow 2))) (atreal t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < cos(t * s)` ASSUME_TAC THENL
   [MATCH_MP_TAC COS_POS_PI THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `(\t. tan(t * s) / s) = (\x. x / s) o tan o (\t. t * s)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    SUBGOAL_THEN `inv(cos(t * s) pow 2) = (inv s) * (inv(cos(t * s) pow 2) * s)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < s` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_DIFF_CHAIN_ATREAL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_DIFF_CHAIN_ATREAL THEN CONJ_TAC THENL
       [REAL_DIFF_TAC THEN REAL_ARITH_TAC;
        REWRITE_TAC[] THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_TAN THEN
        ASM_SIMP_TAC[REAL_LT_IMP_NZ]];
      REWRITE_TAC[real_div] THEN REAL_DIFF_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REAL_DIFF_TAC THEN ASM_SIMP_TAC[REAL_POW_NZ; REAL_LT_IMP_NZ] THEN
  REWRITE_TAC[tan] THEN UNDISCH_TAC `&0 < cos(t * s)` THEN CONV_TAC REAL_FIELD);;

let P2BSS_RAY_VDERIV = prove
 (`!s t (v:real^N).
     &0 < s /\ abs(t * s) < pi / &2
     ==> ((\x. (tan(drop x * s) / s) % v) has_vector_derivative
          inv(cos(t * s) pow 2) % v) (at (lift t)) /\
         ((\x. inv(cos(drop x * s) pow 2) % v) has_vector_derivative
          (&2 * s * tan(t * s) * inv(cos(t * s) pow 2)) % v) (at (lift t))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BSS_TAN_RAY_DERIV) THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`\t. tan(t * s) / s`; `inv(cos(t * s) pow 2)`; `(\x:real^1. v:real^N)`;
                   `vec 0:real^N`; `t:real`] GEOS_VDERIV_SMUL);
    MP_TAC(ISPECL [`\t. inv(cos(t * s) pow 2)`; `&2 * s * tan(t * s) * inv(cos(t * s) pow 2)`;
                   `(\x:real^1. v:real^N)`; `vec 0:real^N`; `t:real`] GEOS_VDERIV_SMUL)] THEN
  ASM_REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST; VECTOR_MUL_RZERO; VECTOR_ADD_LID]);;

let P2BSS_GS_GEODESIC = prove
 (`!v:real^2. ~(v = vec 0)
     ==> mfd_geodesic (euclidean,open_set_atlas (:real^2)) p2bss_gs
           (\t. (tan(t * norm v) / norm v) % v)
           (real_interval(--(pi / (&2 * norm v)),pi / (&2 * norm v)))`,
  GEN_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `s = norm(v:real^2)` THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN ASM_SIMP_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN real_interval(--(pi / (&2 * s)),pi / (&2 * s)) <=>
                    abs(t * s) < pi / &2` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL; REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < s ==> abs s = s`] THEN
    SUBGOAL_THEN `pi / (&2 * s) = (pi / &2) / s` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < s` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_ARITH `abs t < a <=> --a < t /\ t < a`] THEN
    REWRITE_TAC[real_div; REAL_MUL_LNEG];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_geodesic; IS_REALINTERVAL_INTERVAL; REAL_OPEN_REAL_INTERVAL] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_DROP_EQ_GEN; CONTINUOUS_MAP_EUCLIDEAN; o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    X_GEN_TAC `x:real^1` THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE THEN
    EXISTS_TAC `inv(cos(t * s) pow 2) % (v:real^2)` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`s:real`; `t:real`; `v:real^2`] P2BSS_RAY_VDERIV) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!c. c IN open_set_atlas (:real^2) <=> c = ((:real^2),(\x:real^2. x))`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[open_set_atlas; IN_SING]; ALL_TAC] THEN
  REWRITE_TAC[FORALL_UNWIND_THM2; IN_UNIV; P2BSR_METRIC_LOCAL_EUCLID] THEN
  EXISTS_TAC `\t. inv(cos(t * s) pow 2) % (v:real^2)` THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `abs(t * s) < pi / &2` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real`; `t:real`; `v:real^2`] P2BSS_RAY_VDERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < cos(t * s)` ASSUME_TAC THENL
   [MATCH_MP_TAC COS_POS_PI THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `--(christoffel p2bss_gs ((tan(t * s) / s) % v) (inv(cos(t * s) pow 2) % v)
                   (inv(cos(t * s) pow 2) % (v:real^2))) =
    (&2 * s * tan(t * s) * inv(cos(t * s) pow 2)) % v`
  (fun th -> REWRITE_TAC[th] THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[P2BSS_GS_CHRISTOFFEL; DOT_LMUL; DOT_RMUL; NORM_MUL; REAL_POW_MUL] THEN
  SUBGOAL_THEN `(v:real^2) dot v = s pow 2 /\ norm(v:real^2) = s` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[NORM_POW_2]; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_ABS_DIV] THEN
  SUBGOAL_THEN `abs s = s` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_DIV; REAL_POW2_ABS] THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC; GSYM VECTOR_SUB_RDISTRIB; GSYM VECTOR_ADD_RDISTRIB;
              VECTOR_NEG_MINUS1] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[tan] THEN
  UNDISCH_TAC `&0 < cos(t * s)` THEN UNDISCH_TAC `&0 < s` THEN
  MP_TAC(SPEC `t * s` SIN_CIRCLE) THEN CONV_TAC REAL_FIELD);;

(* exp_0 of the model on ball(0,pi/2). *)

let P2BSS_GS_EXP = prove
 (`!v:real^2. norm v < pi / &2
     ==> v IN mfd_exp_dom (euclidean,open_set_atlas (:real^2)) p2bss_gs (vec 0) /\
         mfd_exp (euclidean,open_set_atlas (:real^2)) p2bss_gs (vec 0) v =
         (if v = vec 0 then vec 0 else (tan(norm v) / norm v) % v)`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`euclidean:(real^2)topology`; `open_set_atlas (:real^2)`; `p2bss_gs`;
                 `vec 0:real^2`] MFD_EXP_DOM) THEN
  REWRITE_TAC[P2BSS_GS_FACTS; TOPSPACE_EUCLIDEAN; IN_UNIV] THEN STRIP_TAC THEN
  COND_CASES_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `s = norm(v:real^2)` THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN ASM_SIMP_TAC[NORM_POS_LT]; ALL_TAC] THEN
  MP_TAC(SPEC `v:real^2` P2BSS_GS_GEODESIC) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`euclidean:(real^2)topology`; `open_set_atlas (:real^2)`; `p2bss_gs`;
                 `\t. (tan(t * s) / s) % (v:real^2)`;
                 `real_interval(--(pi / (&2 * s)),pi / (&2 * s))`; `vec 0:real^2`; `v:real^2`]
         MFD_GEO_MAXIMAL_UNIQUE) THEN
  ASM_REWRITE_TAC[P2BSS_GS_FACTS] THEN ANTS_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL; REAL_MUL_LZERO; TAN_0; real_div; REAL_MUL_LZERO;
                VECTOR_MUL_LZERO] THEN
    CONJ_TAC THENL
     [MP_TAC PI_POS THEN UNDISCH_TAC `&0 < s` THEN
      SIMP_TAC[REAL_LT_MUL; REAL_LT_INV_EQ; REAL_ARITH `&0 < &2`] THEN
      REWRITE_TAC[GSYM real_div] THEN
      MESON_TAC[REAL_LT_DIV; REAL_LT_MUL; REAL_ARITH `&0 < &2`;
                REAL_ARITH `&0 < x ==> --x < &0`];
      ALL_TAC] THEN
    REWRITE_TAC[mfd_vel; P2BSS_GS_FACTS] THEN
    MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
    MP_TAC(ISPECL [`s:real`; `&0`; `v:real^2`] P2BSS_RAY_VDERIV) THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ABS_0; PI_POS; REAL_HALF] THEN
    REWRITE_TAC[COS_0; REAL_POW_ONE; REAL_INV_1; VECTOR_MUL_LID] THEN
    SIMP_TAC[real_div; ETA_AX];
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&1 IN real_interval(--(pi / (&2 * s)),pi / (&2 * s))` ASSUME_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN
    SUBGOAL_THEN `&1 < pi / (&2 * s)` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LT_MUL; REAL_ARITH `&0 < &2`] THEN
      UNDISCH_TAC `s < pi / &2` THEN REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[mfd_exp_dom; IN_ELIM_THM] THEN ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[mfd_exp] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&1` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "mfd_geo" with Failure _ -> false))
        (concl th))) THEN
  ASM_REWRITE_TAC[REAL_MUL_LID] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[]);;

(* exp_0 is a parametrization of ball(0,pi/2) onto the whole plane. *)

let P2BSS_GS_EXP_INJ = prove
 (`!v w:real^2.
     norm v < pi / &2 /\ norm w < pi / &2 /\
     (if v = vec 0 then vec 0 else (tan(norm v) / norm v) % v) =
     (if w = vec 0 then vec 0 else (tan(norm w) / norm w) % w)
     ==> v = w`,
  SUBGOAL_THEN
   `!v:real^2. norm v < pi / &2
       ==> norm(if v = vec 0 then vec 0 else (tan(norm v) / norm v) % v) = tan(norm v) /\
           (~(v = vec 0) ==> &0 < tan(norm v) / norm v)`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[NORM_0; TAN_0; NORM_MUL] THEN
    SUBGOAL_THEN `&0 < norm(v:real^2)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[NORM_POS_LT]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < tan(norm(v:real^2))` ASSUME_TAC THENL
     [MATCH_MP_TAC TAN_POS_PI2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 < x ==> abs x = x`; REAL_DIV_RMUL;
                 REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `norm(v:real^2) = norm(w:real^2)` ASSUME_TAC THENL
   [SUBGOAL_THEN `tan(norm(v:real^2)) = tan(norm(w:real^2))` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `(x < y ==> a < b) /\ (y < x ==> b < a) ==> a = b ==> x = y`) THEN
    CONJ_TAC THEN DISCH_TAC THEN MATCH_MP_TAC TAN_MONO_LT THEN
    MP_TAC(ISPEC `v:real^2` NORM_POS_LE) THEN MP_TAC(ISPEC `w:real^2` NORM_POS_LE) THEN
    MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `v:real^2 = vec 0` THENL
   [UNDISCH_TAC `norm(v:real^2) = norm(w:real^2)` THEN ASM_REWRITE_TAC[NORM_0] THEN
    CONV_TAC(LAND_CONV SYM_CONV) THEN REWRITE_TAC[NORM_EQ_0] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(w:real^2 = vec 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[NORM_EQ_0]; ALL_TAC] THEN
  UNDISCH_TAC `(if v = vec 0 then vec 0 else (tan (norm v) / norm v) % v) =
               (if w = vec 0 then vec 0 else (tan (norm w) / norm w) % (w:real^2))` THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LCANCEL] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `w:real^2`) THEN ASM_REWRITE_TAC[] THEN
  MESON_TAC[REAL_LT_IMP_NZ]);;

let P2BSS_GS_EXP_PARAM = prove
 (`mfd_param euclidean (open_set_atlas (:real^2)) (ball(vec 0,pi / &2))
             (mfd_exp (euclidean,open_set_atlas (:real^2)) p2bss_gs (vec 0)) /\
   IMAGE (mfd_exp (euclidean,open_set_atlas (:real^2)) p2bss_gs (vec 0)) (ball(vec 0,pi / &2)) =
   (:real^2) /\
   ball(vec 0,pi / &2) SUBSET mfd_exp_dom (euclidean,open_set_atlas (:real^2)) p2bss_gs (vec 0)`,
  SUBGOAL_THEN `ball(vec 0:real^2,pi / &2) SUBSET
                mfd_exp_dom (euclidean,open_set_atlas (:real^2)) p2bss_gs (vec 0)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL_0] THEN MESON_TAC[P2BSS_GS_EXP]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC GEOS_INJECTIVE_PARAM THEN
    MP_TAC(ISPECL [`euclidean:(real^2)topology`; `open_set_atlas (:real^2)`; `p2bss_gs`;
                   `vec 0:real^2`] MFD_EXP_SMOOTH) THEN
    REWRITE_TAC[P2BSS_GS_FACTS; TOPSPACE_EUCLIDEAN; IN_UNIV; OPEN_BALL] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
      EXISTS_TAC `mfd_exp_dom (euclidean,open_set_atlas (:real^2)) p2bss_gs (vec 0)` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MFD_SMOOTH_MAP_SUBSET THEN
      EXISTS_TAC `mfd_exp_dom (euclidean,open_set_atlas (:real^2)) p2bss_gs (vec 0)` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_BALL_0] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC P2BSS_GS_EXP_INJ THEN ASM_MESON_TAC[P2BSS_GS_EXP];
      ALL_TAC] THEN
    REWRITE_TAC[IN_BALL_0] THEN MAP_EVERY X_GEN_TAC [`v:real^2`; `h:real^2`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`euclidean:(real^2)topology`; `open_set_atlas (:real^2)`; `p2bss_gs`;
                   `vec 0:real^2`; `v:real^2`; `h:real^2`] MFD_EXP_DIFFERENTIAL_CONST1) THEN
    ASM_SIMP_TAC[P2BSS_GS_FACTS; TOPSPACE_EUCLIDEAN; IN_UNIV; P2BSS_GS_EXP] THEN
    ASM_REWRITE_TAC[mfd_tnorm; MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; SQRT_0] THEN
    REWRITE_TAC[p2bss_gs; NORM_0; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID; DOT_RMUL] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_ARITH `&0 pow 2 = &0`] THEN
    SUBGOAL_THEN `sqrt(&4 * (h dot h)) pow 2 = &4 * ((h:real^2) dot h)` SUBST1_TAC THENL
     [SIMP_TAC[SQRT_POW_2; REAL_LE_MUL; DOT_POS_LE; REAL_POS]; ALL_TAC] THEN
    COND_CASES_TAC THENL
     [DISCH_THEN(MP_TAC o SYM) THEN REWRITE_TAC[REAL_ENTIRE; DOT_EQ_0] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
      ALL_TAC] THEN
    ABBREV_TAC `a = sqrt(&4 * ((v:real^2) dot v))` THEN
    SUBGOAL_THEN `&0 < (v:real^2) dot v` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[DOT_POS_LT]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < a /\ a pow 2 = &4 * ((v:real^2) dot v)` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "a" THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `a < pi` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2_REV THEN EXISTS_TAC `2` THEN
      SIMP_TAC[PI_POS; REAL_LT_IMP_LE] THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(v:real^2) dot v = norm v pow 2` SUBST1_TAC THENL
       [REWRITE_TAC[NORM_POW_2]; ALL_TAC] THEN
      MP_TAC(ISPEC `v:real^2` NORM_POS_LE) THEN UNDISCH_TAC `norm(v:real^2) < pi / &2` THEN
      SPEC_TAC(`norm(v:real^2)`,`r:real`) THEN GEN_TAC THEN REPEAT DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&4 * r pow 2 = (&2 * r) pow 2 /\ (&2 * r) pow 2 < pi pow 2
                               ==> &4 * r pow 2 < pi pow 2`) THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < sin a` ASSUME_TAC THENL
     [MATCH_MP_TAC SIN_POS_PI THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `((&4 * ((v:real^2) dot h)) / a) pow 2 <= &4 * (h dot h)` ASSUME_TAC THENL
     [SUBGOAL_THEN `((v:real^2) dot h) pow 2 <= (v dot v) * (h dot h)` ASSUME_TAC THENL
       [REWRITE_TAC[GSYM NORM_POW_2; GSYM REAL_POW_MUL] THEN
        ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
        REWRITE_TAC[REAL_ABS_POS; NORM_CAUCHY_SCHWARZ_ABS; REAL_ABS_MUL; REAL_ABS_NORM];
        ALL_TAC] THEN
      REWRITE_TAC[REAL_POW_DIV] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT] THEN
      ASM_REWRITE_TAC[REAL_POW_MUL] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN REWRITE_TAC[GSYM DOT_EQ_0] THEN
    SUBGOAL_THEN `&0 <= (sin a / a) pow 2 *
                       (&4 * ((h:real^2) dot h) - ((&4 * ((v:real^2) dot h)) / a) pow 2)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(sin a / a) pow 2 *
                  (&4 * ((h:real^2) dot h) - ((&4 * ((v:real^2) dot h)) / a) pow 2) = &0 /\
                  ((&4 * ((v:real^2) dot h)) / a) pow 2 = &0`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(SPEC `(&4 * ((v:real^2) dot h)) / a` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `(sin a / a) pow 2 *
                 (&4 * ((h:real^2) dot h) - ((&4 * ((v:real^2) dot h)) / a) pow 2) = &0` THEN
    REWRITE_TAC[ASSUME `((&4 * ((v:real^2) dot h)) / a) pow 2 = &0`;
                REAL_ENTIRE; REAL_POW_EQ_0; REAL_SUB_RZERO] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC(ASSUME `&0 < sin a`) THEN MP_TAC(ASSUME `&0 < a`) THEN
    REWRITE_TAC[REAL_DIV_EQ_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV; IN_BALL_0] THEN X_GEN_TAC `z:real^2` THEN
  ASM_CASES_TAC `z:real^2 = vec 0` THENL
   [EXISTS_TAC `vec 0:real^2` THEN ASM_SIMP_TAC[P2BSS_GS_EXP; NORM_0; PI_POS; REAL_HALF];
    ALL_TAC] THEN
  EXISTS_TAC `(atn(norm z) / norm z) % (z:real^2)` THEN
  SUBGOAL_THEN `&0 < norm(z:real^2)` ASSUME_TAC THENL [ASM_SIMP_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < atn(norm(z:real^2))` ASSUME_TAC THENL
   [MP_TAC(SPECL [`&0`; `norm(z:real^2)`] ATN_MONO_LT) THEN ASM_REWRITE_TAC[ATN_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm((atn(norm z) / norm z) % (z:real^2)) = atn(norm z)` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < x ==> abs x = x`; REAL_DIV_RMUL;
                 REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `atn(norm(z:real^2)) < pi / &2` ASSUME_TAC THENL
   [REWRITE_TAC[ATN_BOUNDS]; ALL_TAC] THEN
  ASM_SIMP_TAC[P2BSS_GS_EXP] THEN
  SUBGOAL_THEN `~((atn(norm z) / norm z) % (z:real^2) = vec 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[NORM_0; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  ASM_REWRITE_TAC[ATN_TAN; VECTOR_MUL_ASSOC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM VECTOR_MUL_LID] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `&0 < norm(z:real^2)` THEN UNDISCH_TAC `&0 < atn(norm(z:real^2))` THEN
  CONV_TAC REAL_FIELD);;

(* ========================================================================= *)
(* The Mobius map mu z = (1 + z)/(1 - z) is a local isometry of the          *)
(* stereographic model on the plane minus 1 (the stereographic picture of a  *)
(* rotation of the sphere by pi/2; mu(-1) = 0).                              *)
(* ========================================================================= *)

let p2bss_mob = new_definition
 `p2bss_mob (z:complex) = (Cx(&1) + z) / (Cx(&1) - z)`;;

let P2BSS_MOB_DERIV = prove
 (`!z. ~(z = Cx(&1))
       ==> (p2bss_mob has_complex_derivative (Cx(&2) / (Cx(&1) - z) pow 2)) (at z)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(Cx(&1) - z = Cx(&0))` ASSUME_TAC THENL
   [REWRITE_TAC[COMPLEX_SUB_0] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `p2bss_mob = \z. (Cx(&1) + z) / (Cx(&1) - z)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; p2bss_mob]; ALL_TAC] THEN
  COMPLEX_DIFF_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~(Cx(&1) - z = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD);;

let P2BSS_MOB_SMOOTH = prove
 (`open((:complex) DIFF {Cx(&1)}) /\
   smooth_map_on ((:complex) DIFF {Cx(&1)}) p2bss_mob`,
  SUBGOAL_THEN `open((:complex) DIFF {Cx(&1)})` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM closed; CLOSED_SING]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_PDL_HOLOMORPHIC_SMOOTH THEN
  ASM_SIMP_TAC[HOLOMORPHIC_ON_OPEN] THEN
  REWRITE_TAC[IN_DIFF; IN_UNIV; IN_SING] THEN MESON_TAC[P2BSS_MOB_DERIV]);;

let P2BSS_MOB_FDERIV = prove
 (`!z. ~(z = Cx(&1))
       ==> frechet_derivative p2bss_mob (at z) = (\h. (Cx(&2) / (Cx(&1) - z) pow 2) * h)`,
  GEN_TAC THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  REWRITE_TAC[GSYM has_complex_derivative] THEN ASM_SIMP_TAC[P2BSS_MOB_DERIV]);;

(* The conformal factor identity. *)

let P2BSS_MOB_FACTOR = prove
 (`!z. ~(z = Cx(&1))
       ==> &4 / (&1 + norm(p2bss_mob z) pow 2) pow 2 *
           norm(Cx(&2) / (Cx(&1) - z) pow 2) pow 2 =
           &4 / (&1 + norm z pow 2) pow 2`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < norm(Cx(&1) - z)` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[p2bss_mob; COMPLEX_NORM_DIV; COMPLEX_NORM_POW; COMPLEX_NORM_CX] THEN
  SUBGOAL_THEN `norm(Cx(&1) + z) pow 2 + norm(Cx(&1) - z) pow 2 = &2 * (&1 + norm z pow 2)`
  MP_TAC THENL
   [REWRITE_TAC[NORM_POW_2; DOT_LADD; DOT_RADD; DOT_LSUB; DOT_RSUB] THEN
    SUBGOAL_THEN `Cx(&1) dot Cx(&1) = &1` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM NORM_POW_2; COMPLEX_NORM_CX] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[DOT_SYM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `&0 < norm(Cx(&1) - z)` THEN
  SPEC_TAC(`norm(Cx(&1) - z)`,`d:real`) THEN SPEC_TAC(`norm(Cx(&1) + z)`,`e:real`) THEN
  SPEC_TAC(`norm(z:complex)`,`r:real`) THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[REAL_ABS_NUM] THEN
  SUBGOAL_THEN `&1 + (e / d) pow 2 = (&2 * (&1 + r pow 2)) / d pow 2` SUBST1_TAC THENL
   [UNDISCH_TAC `e pow 2 + d pow 2 = &2 * (&1 + r pow 2)` THEN UNDISCH_TAC `&0 < d` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 + r pow 2` MP_TAC THENL
   [MP_TAC(SPEC `r:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `&0 < d` THEN CONV_TAC REAL_FIELD);;

let P2BSS_MOB_LISOM = prove
 (`mfd_local_isometry (euclidean,open_set_atlas (:real^2)) p2bss_gs
                      (euclidean,open_set_atlas (:real^2)) p2bss_gs
                      ((:real^2) DIFF {Cx(&1)}) p2bss_mob`,
  MP_TAC P2BSS_MOB_SMOOTH THEN STRIP_TAC THEN
  MATCH_MP_TAC GEOI_LISOM_FROM_DIFF THEN REWRITE_TAC[P2BSS_GS_FACTS; GSYM OPEN_IN] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[MFD_SMOOTH_MAP_OPEN_SET_ATLAS; IN_UNIV; INTER_UNIV] THEN
    REWRITE_TAC[SET_RULE `{x:real^2 | x IN s} = s`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^2` THEN REWRITE_TAC[IN_DIFF; IN_UNIV; IN_SING] THEN DISCH_TAC THEN
  REWRITE_TAC[MFD_DIFFERENTIAL_OPEN_SET_ATLAS; P2BSS_GS_FACTS] THEN
  REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[P2BSS_MOB_FDERIV] THEN
  MATCH_MP_TAC GEOI_QUAD_EQ THEN
  REWRITE_TAC[p2bss_gs; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID; DOT_RMUL] THEN
  REWRITE_TAC[MATRIX_MUL_LMUL; MATRIX_MUL_RMUL; MATRIX_MUL_LID; GSYM MATRIX_VECTOR_MUL_ASSOC;
              MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID; DOT_RMUL] THEN
  ABBREV_TAC `w = Cx(&2) / (Cx(&1) - z) pow 2` THEN
  SUBGOAL_THEN `linear (\h:complex. w * h)` ASSUME_TAC THENL
   [REWRITE_TAC[linear; COMPLEX_ADD_LDISTRIB; COMPLEX_CMUL] THEN
    REPEAT STRIP_TAC THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  REWRITE_TAC[DOT_MATRIX_TRANSP_RMUL] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MATRIX_WORKS th]) THEN
  REWRITE_TAC[DOT_RMUL] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[DOT_SYM];
    REWRITE_TAC[DOT_SYM];
    GEN_TAC THEN REWRITE_TAC[GSYM NORM_POW_2; COMPLEX_NORM_MUL; REAL_POW_MUL] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN EXPAND_TAC "w" THEN MATCH_MP_TAC P2BSS_MOB_FACTOR THEN
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Cartan maps from the stereographic model into a compact surface of        *)
(* curvature 1, their 1-jet at the centre, composition of local isometries.  *)
(* ========================================================================= *)

let p2bss_expinv = new_definition
 `p2bss_expinv (y:real^2) =
    @v. v IN ball(vec 0,pi / &2) /\
        mfd_exp (euclidean,open_set_atlas (:real^2)) p2bss_gs (vec 0) v = y`;;

let P2BSS_EXPINV = prove
 (`(!y. p2bss_expinv y IN ball(vec 0,pi / &2) /\
        mfd_exp (euclidean,open_set_atlas (:real^2)) p2bss_gs (vec 0) (p2bss_expinv y) = y) /\
   (!v. v IN ball(vec 0,pi / &2)
        ==> p2bss_expinv (mfd_exp (euclidean,open_set_atlas (:real^2)) p2bss_gs (vec 0) v) = v) /\
   p2bss_expinv (vec 0) = vec 0`,
  SUBGOAL_THEN
   `!y. p2bss_expinv y IN ball(vec 0,pi / &2) /\
        mfd_exp (euclidean,open_set_atlas (:real^2)) p2bss_gs (vec 0) (p2bss_expinv y) = y`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[p2bss_expinv] THEN CONV_TAC SELECT_CONV THEN
    MP_TAC P2BSS_GS_EXP_PARAM THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!v. v IN ball(vec 0,pi / &2)
        ==> p2bss_expinv (mfd_exp (euclidean,open_set_atlas (:real^2)) p2bss_gs (vec 0) v) = v`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC
      `mfd_exp (euclidean,open_set_atlas (:real^2)) p2bss_gs (vec 0) v`) THEN
    STRIP_TAC THEN MATCH_MP_TAC P2BSS_GS_EXP_INJ THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_BALL_0]) THEN ASM_SIMP_TAC[GSYM P2BSS_GS_EXP];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `vec 0:real^2`) THEN
  REWRITE_TAC[IN_BALL_0; NORM_0; PI_POS; REAL_HALF] THEN
  MP_TAC(SPEC `vec 0:real^2` P2BSS_GS_EXP) THEN REWRITE_TAC[NORM_0; PI_POS; REAL_HALF] THEN
  SIMP_TAC[]);;

let p2bss_cartan = new_definition
 `p2bss_cartan (top:B topology,atlas:((B->bool)#(B->real^2))->bool) (g:B->real^2^2)
               (p:B) (L:real^2^2) =
    \y. mfd_exp (top,atlas) g p (L ** p2bss_expinv y)`;;

let P2BSS_CARTAN_LISOM = prove
 (`!top (atlas:((B->bool)#(B->real^2))->bool) (g:B->real^2^2) p L.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     compact_space top /\
     (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
              ==> mfd_sectional atlas g x u v = &1) /\
     p IN topspace top /\ transp L ** g p ** L = p2bss_gs (vec 0)
     ==> mfd_local_isometry (euclidean,open_set_atlas (:real^2)) p2bss_gs (top,atlas) g
                            (:real^2) (p2bss_cartan (top,atlas) g p L)`,
  REPEAT STRIP_TAC THEN
  MP_TAC P2BSS_GS_EXP_PARAM THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`euclidean:(real^2)topology`; `open_set_atlas (:real^2)`; `p2bss_gs`;
                 `top:B topology`; `atlas:((B->bool)#(B->real^2))->bool`; `g:B->real^2^2`;
                 `vec 0:real^2`; `p:B`; `L:real^2^2`; `ball(vec 0:real^2,pi / &2)`]
         MFD_CARTAN_CONST1) THEN
  ASM_REWRITE_TAC[P2BSS_GS_FACTS; TOPSPACE_EUCLIDEAN; IN_UNIV] THEN ANTS_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^2))->bool`; `g:B->real^2^2`;
                   `p:B`; `vec 0:real^2`] MFD_COMPACT_GEO_COMPLETE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[p2bss_cartan; p2bss_expinv]);;

(* Local isometries compose. *)

let P2BSS_LISOM_COMPOSE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
    top' (atlas':((B->bool)#(B->real^N))->bool) (g':B->real^N^N)
    top'' (atlas'':((C->bool)#(C->real^N))->bool) (g'':C->real^N^N) W W' f h.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     smooth_manifold_atlas top' atlas' /\ riemannian_metric atlas' g' /\
     smooth_manifold_atlas top'' atlas'' /\ riemannian_metric atlas'' g'' /\
     mfd_local_isometry (top,atlas) g (top',atlas') g' W f /\
     mfd_local_isometry (top',atlas') g' (top'',atlas'') g'' W' h /\
     (!x. x IN W ==> f x IN W')
     ==> mfd_local_isometry (top,atlas) g (top'',atlas'') g'' W (h o f)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[mfd_local_isometry] (ASSUME
    `mfd_local_isometry (top,atlas) (g:A->real^N^N) (top',atlas') (g':B->real^N^N) W f`)) THEN
  MP_TAC(REWRITE_RULE[mfd_local_isometry] (ASSUME
    `mfd_local_isometry (top',atlas') (g':B->real^N^N) (top'',atlas'') (g'':C->real^N^N) W' h`)) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `continuous_map (subtopology top W,top'') ((h:B->C) o (f:A->B))` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `subtopology top' (W':B->bool)` THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_smooth_map (atlas:((A->bool)#(A->real^N))->bool)
                                (atlas'':((C->bool)#(C->real^N))->bool) W ((h:B->C) o (f:A->B))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_SMOOTH_MAP_COMPOSE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `top':B topology`;
                          `atlas':((B->bool)#(B->real^N))->bool`; `top'':C topology`;
                          `W':B->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC GEOI_LISOM_FROM_DIFF THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `top'':C topology`; `atlas'':((C->bool)#(C->real^N))->bool`;
                 `W:A->bool`; `W':B->bool`; `f:A->B`; `h:B->C`; `x:A`] GEOI_DIFF_COMPOSE) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `g':B->real^N^N`;
                 `W:A->bool`; `f:A->B`; `x:A`] GEOH_LISOM_DIFF) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `g':B->real^N^N`;
                 `top'':C topology`; `atlas'':((C->bool)#(C->real^N))->bool`; `g'':C->real^N^N`;
                 `W':B->bool`; `h:B->C`; `(f:A->B) x`] GEOH_LISOM_DIFF) THEN
  ASM_SIMP_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `linear(mfd_differential (atlas:((A->bool)#(A->real^N))->bool)
                                       (atlas':((B->bool)#(B->real^N))->bool) (f:A->B) x) /\
                linear(mfd_differential atlas' (atlas'':((C->bool)#(C->real^N))->bool) (h:B->C) (f x))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC GEOI_DIFF_LINEAR THENL
     [MAP_EVERY EXISTS_TAC [`top:A topology`; `top':B topology`; `W:A->bool`];
      MAP_EVERY EXISTS_TAC [`top':B topology`; `top'':C topology`; `W':B->bool`]] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_COMPOSE; MATRIX_TRANSP_MUL] THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[MATRIX_MUL_ASSOC; o_THM]);;

(* The 1-jet of a Cartan map at the centre. *)

let P2BSS_CARTAN_AT0 = prove
 (`!top (atlas:((B->bool)#(B->real^2))->bool) (g:B->real^2^2) p L.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     compact_space top /\
     (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
              ==> mfd_sectional atlas g x u v = &1) /\
     p IN topspace top /\ transp L ** g p ** L = p2bss_gs (vec 0)
     ==> p2bss_cartan (top,atlas) g p L (vec 0) = p /\
         mfd_differential (open_set_atlas (:real^2)) atlas (p2bss_cartan (top,atlas) g p L)
                          (vec 0) = (\h. L ** h)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^2))->bool`; `g:B->real^2^2`;
                 `p:B`] MFD_EXP_DOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^2))->bool`; `g:B->real^2^2`;
                 `p:B`; `vec 0:real^2`] MFD_COMPACT_GEO_COMPLETE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[p2bss_cartan; P2BSS_EXPINV; MATRIX_VECTOR_MUL_RZERO]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^2))->bool`; `g:B->real^2^2`;
                 `p:B`; `L:real^2^2`] P2BSS_CARTAN_LISOM) THEN
  ASM_REWRITE_TAC[mfd_local_isometry; SUBTOPOLOGY_UNIV] THEN STRIP_TAC THEN
  MP_TAC P2BSS_GS_EXP_PARAM THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`euclidean:(real^2)topology`; `open_set_atlas (:real^2)`; `p2bss_gs`;
                 `vec 0:real^2`] MFD_EXP_SMOOTH) THEN
  REWRITE_TAC[P2BSS_GS_FACTS; TOPSPACE_EUCLIDEAN; IN_UNIV] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^2))->bool`; `g:B->real^2^2`;
                 `p:B`] MFD_EXP_SMOOTH) THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV] THEN STRIP_TAC THEN
  ABBREV_TAC `E = mfd_exp (euclidean,open_set_atlas (:real^2)) p2bss_gs (vec 0)` THEN
  ABBREV_TAC `C = p2bss_cartan (top,atlas) (g:B->real^2^2) p L` THEN
  SUBGOAL_THEN `continuous_map (subtopology euclidean (ball(vec 0:real^2,pi / &2)),euclidean) E /\
                mfd_smooth_map (open_set_atlas (:real^2)) (open_set_atlas (:real^2))
                               (ball(vec 0,pi / &2)) E`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
      EXISTS_TAC `mfd_exp_dom (euclidean,open_set_atlas (:real^2)) p2bss_gs (vec 0)` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MFD_SMOOTH_MAP_SUBSET THEN
      EXISTS_TAC `mfd_exp_dom (euclidean,open_set_atlas (:real^2)) p2bss_gs (vec 0)` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(E:real^2->real^2) (vec 0) = vec 0` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN SIMP_TAC[P2BSS_GS_EXP; NORM_0; PI_POS; REAL_HALF]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_differential (open_set_atlas (:real^2)) (open_set_atlas (:real^2))
                  (E:real^2->real^2) (vec 0) = (\h. h)` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN MATCH_MP_TAC MFD_EXP_DIFFERENTIAL_ZERO THEN
    REWRITE_TAC[P2BSS_GS_FACTS; TOPSPACE_EUCLIDEAN; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `vec 0 IN ball(vec 0:real^2,pi / &2)` ASSUME_TAC THENL
   [REWRITE_TAC[CENTRE_IN_BALL; PI_POS; REAL_HALF]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_differential (open_set_atlas (:real^2)) (atlas:((B->bool)#(B->real^2))->bool)
                     ((C:real^2->B) o (E:real^2->real^2)) (vec 0) =
    mfd_differential (open_set_atlas (:real^2)) atlas C (vec 0)`
  MP_TAC THENL
   [MP_TAC(ISPECL [`euclidean:(real^2)topology`; `open_set_atlas (:real^2)`;
                   `euclidean:(real^2)topology`; `open_set_atlas (:real^2)`;
                   `top:B topology`; `atlas:((B->bool)#(B->real^2))->bool`;
                   `ball(vec 0:real^2,pi / &2)`; `(:real^2)`; `E:real^2->real^2`; `C:real^2->B`;
                   `vec 0:real^2`] GEOI_DIFF_COMPOSE) THEN
    ASM_REWRITE_TAC[P2BSS_GS_FACTS; GSYM OPEN_IN; OPEN_BALL; OPEN_UNIV; IN_UNIV;
                    SUBTOPOLOGY_UNIV] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_differential (open_set_atlas (:real^2)) (atlas:((B->bool)#(B->real^2))->bool)
                     ((C:real^2->B) o (E:real^2->real^2)) (vec 0) =
    mfd_differential (open_set_atlas (:real^2)) atlas
                     (mfd_exp (top,atlas) (g:B->real^2^2) p o (\v. L ** v)) (vec 0)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC GEOI_DIFFERENTIAL_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`euclidean:(real^2)topology`; `ball(vec 0:real^2,pi / &2)`] THEN
    ASM_REWRITE_TAC[P2BSS_GS_FACTS; GSYM OPEN_IN; OPEN_BALL] THEN
    X_GEN_TAC `v:real^2` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    EXPAND_TAC "C" THEN REWRITE_TAC[p2bss_cartan] THEN EXPAND_TAC "E" THEN
    ASM_SIMP_TAC[P2BSS_EXPINV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^2)topology`; `open_set_atlas (:real^2)`;
                 `euclidean:(real^2)topology`; `open_set_atlas (:real^2)`;
                 `top:B topology`; `atlas:((B->bool)#(B->real^2))->bool`;
                 `(:real^2)`; `(:real^2)`; `\v:real^2. (L:real^2^2) ** v`;
                 `mfd_exp (top,atlas) (g:B->real^2^2) p`; `vec 0:real^2`] GEOI_DIFF_COMPOSE) THEN
  ASM_REWRITE_TAC[P2BSS_GS_FACTS; GSYM OPEN_IN; OPEN_UNIV; IN_UNIV; SUBTOPOLOGY_UNIV] THEN
  ANTS_TAC THENL
   [SIMP_TAC[GEOI_LINEAR_SMOOTH; OPEN_UNIV; CONTINUOUS_MAP_EUCLIDEAN_EUCLIDEAN;
             LINEAR_CONTINUOUS_ON; MATRIX_VECTOR_MUL_LINEAR];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[GEOI_DIFF_LINEAR_MAP; MATRIX_VECTOR_MUL_RZERO; MFD_EXP_DIFFERENTIAL_ZERO] THEN
  REWRITE_TAC[o_DEF] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[ETA_AX]);;

(* A second Cartan map, centred at the image of -1, agrees with the first   *)
(* one through the Mobius map: together they cover the whole sphere.        *)

let P2BSS_CARTAN_PAIR = prove
 (`!top (atlas:((B->bool)#(B->real^2))->bool) (g:B->real^2^2) p L.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     compact_space top /\
     (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
              ==> mfd_sectional atlas g x u v = &1) /\
     p IN topspace top /\ transp L ** g p ** L = p2bss_gs (vec 0)
     ==> ?q L2. q IN topspace top /\ transp L2 ** g q ** L2 = p2bss_gs (vec 0) /\
                !z. ~(z = Cx(&1))
                    ==> p2bss_cartan (top,atlas) g q L2 (p2bss_mob z) =
                        p2bss_cartan (top,atlas) g p L z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `FS = p2bss_cartan (top,atlas) (g:B->real^2^2) p L` THEN
  SUBGOAL_THEN `mfd_local_isometry (euclidean,open_set_atlas (:real^2)) p2bss_gs (top,atlas)
                                   (g:B->real^2^2) (:real^2) FS` ASSUME_TAC THENL
   [EXPAND_TAC "FS" THEN MATCH_MP_TAC P2BSS_CARTAN_LISOM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `D = mfd_differential (open_set_atlas (:real^2)) (atlas:((B->bool)#(B->real^2))->bool)
                                   (FS:real^2->B) (--Cx(&1))` THEN
  SUBGOAL_THEN `linear(D:real^2->real^2)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC GEOI_DIFF_LINEAR THEN
    MAP_EVERY EXISTS_TAC [`euclidean:(real^2)topology`; `top:B topology`; `(:real^2)`] THEN
    REWRITE_TAC[P2BSS_GS_FACTS; GSYM OPEN_IN; OPEN_UNIV; IN_UNIV] THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[mfd_local_isometry];
    ALL_TAC] THEN
  SUBGOAL_THEN `(FS:real^2->B) (--Cx(&1)) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`euclidean:(real^2)topology`; `open_set_atlas (:real^2)`; `p2bss_gs`;
                   `top:B topology`; `atlas:((B->bool)#(B->real^2))->bool`; `g:B->real^2^2`;
                   `(:real^2)`; `FS:real^2->B`; `--Cx(&1)`] GEOH_LISOM_POINTS) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `transp(&2 %% matrix(D:real^2->real^2)) ** (g:B->real^2^2) ((FS:real^2->B) (--Cx(&1))) **
                (&2 %% matrix D) = p2bss_gs (vec 0)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`euclidean:(real^2)topology`; `open_set_atlas (:real^2)`; `p2bss_gs`;
                   `top:B topology`; `atlas:((B->bool)#(B->real^2))->bool`; `g:B->real^2^2`;
                   `(:real^2)`; `FS:real^2->B`; `--Cx(&1)`] GEOH_LISOM_DIFF) THEN
    ASM_REWRITE_TAC[P2BSS_GS_FACTS; IN_UNIV] THEN DISCH_TAC THEN
    REWRITE_TAC[TRANSP_MATRIX_CMUL; MATRIX_MUL_LMUL; MATRIX_MUL_RMUL] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[p2bss_gs; NORM_0; NORM_NEG; COMPLEX_NORM_CX; MATRIX_CMUL_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`(FS:real^2->B) (--Cx(&1))`; `&2 %% matrix(D:real^2->real^2)`] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `FN = p2bss_cartan (top,atlas) (g:B->real^2^2) ((FS:real^2->B) (--Cx(&1)))
                                (&2 %% matrix(D:real^2->real^2))` THEN
  SUBGOAL_THEN `mfd_local_isometry (euclidean,open_set_atlas (:real^2)) p2bss_gs (top,atlas)
                                   (g:B->real^2^2) (:real^2) FN` ASSUME_TAC THENL
   [EXPAND_TAC "FN" THEN MATCH_MP_TAC P2BSS_CARTAN_LISOM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^2))->bool`; `g:B->real^2^2`;
                 `(FS:real^2->B) (--Cx(&1))`; `&2 %% matrix(D:real^2->real^2)`] P2BSS_CARTAN_AT0) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC P2BSS_MOB_SMOOTH THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2bss_mob(--Cx(&1)) = vec 0` ASSUME_TAC THENL
   [REWRITE_TAC[p2bss_mob; COMPLEX_ADD_RINV; complex_div; COMPLEX_MUL_LZERO; COMPLEX_VEC_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(--Cx(&1) = Cx(&1))` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM CX_NEG; CX_INJ] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN (:real^2) DIFF {Cx(&1)}
                    ==> ((FN:real^2->B) o p2bss_mob) x = (FS:real^2->B) x`
  (fun th -> X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN MP_TAC(SPEC `z:real^2` th) THEN
             ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; IN_SING; o_THM]) THEN
  SUBGOAL_THEN `mfd_local_isometry (euclidean,open_set_atlas (:real^2)) p2bss_gs (top,atlas)
                  (g:B->real^2^2) ((:real^2) DIFF {Cx(&1)}) ((FN:real^2->B) o p2bss_mob)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BSS_LISOM_COMPOSE THEN
    MAP_EVERY EXISTS_TAC [`euclidean:(real^2)topology`; `open_set_atlas (:real^2)`; `p2bss_gs`;
                          `(:real^2)`] THEN
    ASM_REWRITE_TAC[P2BSS_GS_FACTS; P2BSS_MOB_LISOM; IN_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^2)topology`; `open_set_atlas (:real^2)`; `p2bss_gs`;
                 `top:B topology`; `atlas:((B->bool)#(B->real^2))->bool`; `g:B->real^2^2`;
                 `(:real^2) DIFF {Cx(&1)}`; `(FN:real^2->B) o p2bss_mob`; `FS:real^2->B`;
                 `--Cx(&1)`] MFD_LOCAL_ISOMETRY_RIGID) THEN
  ASM_REWRITE_TAC[P2BSS_GS_FACTS; IN_DIFF; IN_UNIV; IN_SING; o_THM; CONNECTED_IN_EUCLIDEAN] THEN
  ANTS_TAC THENL
   [SIMP_TAC[CONNECTED_PUNCTURED_UNIVERSE; DIMINDEX_2; LE_REFL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC GEOH_LISOM_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV; GSYM OPEN_IN];
      ALL_TAC] THEN
    MP_TAC(REWRITE_RULE[mfd_local_isometry] P2BSS_MOB_LISOM) THEN STRIP_TAC THEN
    MP_TAC(REWRITE_RULE[mfd_local_isometry] (ASSUME
      `mfd_local_isometry (euclidean,open_set_atlas (:real^2)) p2bss_gs (top,atlas)
                          (g:B->real^2^2) (:real^2) (FN:real^2->B)`)) THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`euclidean:(real^2)topology`; `open_set_atlas (:real^2)`;
                   `euclidean:(real^2)topology`; `open_set_atlas (:real^2)`;
                   `top:B topology`; `atlas:((B->bool)#(B->real^2))->bool`;
                   `(:real^2) DIFF {Cx(&1)}`; `(:real^2)`; `p2bss_mob`; `FN:real^2->B`;
                   `--Cx(&1)`] GEOI_DIFF_COMPOSE) THEN
    ASM_REWRITE_TAC[P2BSS_GS_FACTS; IN_DIFF; IN_UNIV; IN_SING] THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[MFD_DIFFERENTIAL_OPEN_SET_ATLAS; P2BSS_GS_FACTS] THEN
    REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[P2BSS_MOB_FDERIV] THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM; MATRIX_VECTOR_LMUL] THEN X_GEN_TAC `h:real^2` THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MATRIX_WORKS th]) THEN
    SUBGOAL_THEN `Cx(&2) / (Cx(&1) - --Cx(&1)) pow 2 * h = inv(&2) % (h:real^2)` SUBST1_TAC THENL
     [REWRITE_TAC[COMPLEX_CMUL; CX_INV] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      CONV_TAC COMPLEX_FIELD;
      ALL_TAC] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[VECTOR_MUL_LID];
    SIMP_TAC[]]);;

(* ========================================================================= *)
(* Flowing a map along Y.  For E : real^3 -> M independent of z$3, Psi z =   *)
(* Phi_(z$3)(E z) has d Psi(e3) = Y and d Psi(a) = d Phi(d E(a)) for         *)
(* horizontal a; Phi_r maps Y to Y.                                          *)
(* ========================================================================= *)

let P2BSS_ISOMETRY_LOCAL = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
    top' (atlas':((B->bool)#(B->real^N))->bool) (g':B->real^N^N) f f'.
     mfd_isometry (top,atlas) g (top',atlas') g' f f'
     ==> mfd_local_isometry (top,atlas) g (top',atlas') g' (topspace top) f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_isometry; mfd_local_isometry; mfd_diffeo] THEN
  REWRITE_TAC[homeomorphic_maps; SUBTOPOLOGY_TOPSPACE; CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[OPEN_IN_TOPSPACE] THEN
  MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^N)`; `c':(B->bool)#(B->real^N)`; `y:real^N`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`c:(A->bool)#(A->real^N)`; `c':(B->bool)#(B->real^N)`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  UNDISCH_TAC `y IN IMAGE (SND (c:(A->bool)#(A->real^N)))
                 {x | x IN FST c INTER topspace top /\ (f:A->B) x IN FST (c':(B->bool)#(B->real^N))}` THEN
  SPEC_TAC(`SND (c:(A->bool)#(A->real^N))`,`ph:A->real^N`) THEN GEN_TAC THEN SET_TAC[]);;

let P2BSS_PHI_Y = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) (Y:A->real^3) r x.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) Y /\
     (!x. x IN topspace top ==> Y x dot (g x ** Y x) = &1) /\ x IN topspace top
     ==> mfd_differential atlas atlas (p2bkf_phi (top,atlas) g Y r) x (Y x) =
         Y(p2bkf_phi (top,atlas) g Y r x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `g:A->real^3^3`; `Y:A->real^3`; `r:real`] P2BKF_PHI_ISOMETRY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o MATCH_MP P2BSS_ISOMETRY_LOCAL) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `Y:A->real^3`; `x:A`] P2BKF_ORBIT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `Y:A->real^3`; `x:A`] P2BKF_ORBIT_SHIFT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `x:A`; `(Y:A->real^3) x`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `topspace top:A->bool`; `p2bkf_phi (top,atlas) (g:A->real^3^3) Y r`;
                 `mfd_geo (top,atlas) (g:A->real^3^3) x ((Y:A->real^3) x)`; `(:real)`]
         MFD_LOCAL_ISOMETRY_GEODESIC) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN
  DISCH_THEN(MP_TAC o SPEC `&0` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `p2bkf_phi (top,atlas) (g:A->real^3^3) Y r o mfd_geo (top,atlas) g x ((Y:A->real^3) x) =
                mfd_geo (top,atlas) g (p2bkf_phi (top,atlas) g Y r x)
                        (Y(p2bkf_phi (top,atlas) g Y r x))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; p2bkf_phi] THEN X_GEN_TAC `t:real` THEN
    ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `Y:A->real^3`; `p2bkf_phi (top,atlas) (g:A->real^3^3) Y r x`] P2BKF_ORBIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[p2bkf_phi]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `p2bkf_phi (top,atlas) (g:A->real^3^3) Y r x`;
                 `(Y:A->real^3)(p2bkf_phi (top,atlas) g Y r x)`] MFD_GEO_MAXIMAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[p2bkf_phi]; SIMP_TAC[]]);;

let P2BSS_PSI_FACTS = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) (Y:A->real^3) (E:real^3->A).
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) Y /\
     (!x. x IN topspace top ==> Y x dot (g x ** Y x) = &1) /\
     continuous_map (euclidean,top) E /\
     mfd_smooth_map (open_set_atlas (:real^3)) atlas (:real^3) E /\
     (!z t. E(z + t % basis 3) = E z)
     ==> continuous_map (euclidean,top) (\z. mfd_geo (top,atlas) g (E z) (Y(E z)) (z$3)) /\
         mfd_smooth_map (open_set_atlas (:real^3)) atlas (:real^3)
                        (\z. mfd_geo (top,atlas) g (E z) (Y(E z)) (z$3)) /\
         (!z. mfd_differential (open_set_atlas (:real^3)) atlas
                (\z. mfd_geo (top,atlas) g (E z) (Y(E z)) (z$3)) z (basis 3) =
              Y(mfd_geo (top,atlas) g (E z) (Y(E z)) (z$3))) /\
         (!z a. a$3 = &0
                ==> mfd_differential (open_set_atlas (:real^3)) atlas
                      (\z. mfd_geo (top,atlas) g (E z) (Y(E z)) (z$3)) z a =
                    mfd_differential atlas atlas (p2bkf_phi (top,atlas) g Y (z$3)) (E z)
                      (mfd_differential (open_set_atlas (:real^3)) atlas E z a))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `Y:A->real^3`; `E:real^3->A`; `3`] P2BKF_ORBITMAP_SMOOTH) THEN
  REWRITE_TAC[DIMINDEX_3; ARITH] THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!w:real^3. (E:real^3->A) w IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `continuous_map (euclidean,top) (E:real^3->A)` THEN
    REWRITE_TAC[CONTINUOUS_MAP; SUBSET; FORALL_IN_IMAGE; TOPSPACE_EUCLIDEAN; IN_UNIV] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `z:real^3` THEN MATCH_MP_TAC P2BKF_DIFF_ALONG_CURVE THEN
    EXISTS_TAC `mfd_geo (top,atlas) (g:A->real^3^3)
                  (mfd_geo (top,atlas) g ((E:real^3->A) z) ((Y:A->real^3)(E z)) (z$3))
                  (Y(mfd_geo (top,atlas) g (E z) (Y(E z)) (z$3)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2BKF_SMOOTH_DIFFABLE THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[ETA_AX];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN
      SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
      REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID; REAL_MUL_RID] THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `Y:A->real^3`; `(E:real^3->A) z`] P2BKF_ORBIT_SHIFT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]);
      ALL_TAC] THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC P2BKF_ORBIT_VEL0 THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `Y:A->real^3`; `(E:real^3->A) z`] P2BKF_ORBIT) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`z:real^3`; `a:real^3`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `Y:A->real^3`; `(z:real^3)$3`] P2BKF_PHI_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `continuous_map (euclidean,top)
                  (p2bkf_phi (top,atlas) (g:A->real^3^3) Y ((z:real^3)$3) o (E:real^3->A)) /\
                mfd_smooth_map (open_set_atlas (:real^3)) atlas (:real^3)
                  (p2bkf_phi (top,atlas) (g:A->real^3^3) Y ((z:real^3)$3) o (E:real^3->A))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                     `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `(:real^3)`; `topspace top:A->bool`; `E:real^3->A`;
                     `p2bkf_phi (top,atlas) (g:A->real^3^3) Y ((z:real^3)$3)`]
             MFD_SMOOTH_MAP_COMPOSE) THEN
      ASM_REWRITE_TAC[GEOI_EUCLIDEAN_ATLAS; GSYM OPEN_IN; OPEN_UNIV; OPEN_IN_TOPSPACE;
                      SUBTOPOLOGY_UNIV; SUBTOPOLOGY_TOPSPACE] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `E:real^3->A`; `p2bkf_phi (top,atlas) (g:A->real^3^3) Y ((z:real^3)$3)`;
                 `topspace top:A->bool`; `z:real^3`] P2BKF_MDIFF_CHAIN) THEN
  ASM_REWRITE_TAC[OPEN_IN_TOPSPACE; SUBTOPOLOGY_TOPSPACE] THEN DISCH_TAC THEN
  MATCH_MP_TAC P2BKF_DIFF_ALONG_CURVE THEN
  EXISTS_TAC `\t. (p2bkf_phi (top,atlas) (g:A->real^3^3) Y ((z:real^3)$3) o (E:real^3->A))
                  (z + t % a)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2BKF_SMOOTH_DIFFABLE THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN REWRITE_TAC[o_THM; p2bkf_phi] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `mfd_geo (top,atlas) (g:A->real^3^3) ((E:real^3->A) z) ((Y:A->real^3)(E z)) (z$3) =
                (p2bkf_phi (top,atlas) g Y (z$3) o E) z` SUBST1_TAC THENL
   [REWRITE_TAC[o_THM; p2bkf_phi]; ALL_TAC] THEN
  REWRITE_TAC[GSYM MFD_DIFFERENTIAL_OPEN_SET_ATLAS] THEN
  MP_TAC(ISPECL [`\y. SND(chart_at (atlas:((A->bool)#(A->real^3))->bool)
                             ((p2bkf_phi (top,atlas) (g:A->real^3^3) Y ((z:real^3)$3) o (E:real^3->A)) z))
                         ((p2bkf_phi (top,atlas) g Y (z$3) o E) y)`;
                 `z:real^3`; `a:real^3`] P2BKF_MAP_CURVE_DERIV) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC P2BKF_SMOOTH_DIFFABLE THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MFD_DIFFERENTIAL_OPEN_SET_ATLAS] THEN ASM_REWRITE_TAC[o_THM]);;

(* Phi_r preserves inner products. *)

let P2BSS_PHI_DOT = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) (Y:A->real^3) r x u w.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) Y /\
     (!x. x IN topspace top ==> Y x dot (g x ** Y x) = &1) /\ x IN topspace top
     ==> mfd_differential atlas atlas (p2bkf_phi (top,atlas) g Y r) x u dot
         (g(p2bkf_phi (top,atlas) g Y r x) **
          mfd_differential atlas atlas (p2bkf_phi (top,atlas) g Y r) x w) =
         u dot (g x ** w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `g:A->real^3^3`; `Y:A->real^3`; `r:real`; `x:A`] P2BKF_PHI_PULLBACK) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `Y:A->real^3`; `r:real`; `x:A`] P2BKF_PHI_INVERSE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `p2bkf_phi (top,atlas) (g:A->real^3^3) Y r`; `g:A->real^3^3`; `x:A`]
         P2BKF_PULLBACK_FORMULA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `Y:A->real^3`; `r:real`] P2BKF_PHI_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `linear(mfd_differential atlas atlas
                  (p2bkf_phi (top,atlas) (g:A->real^3^3) (Y:A->real^3) r) x)` ASSUME_TAC THENL
   [MATCH_MP_TAC GEOI_DIFF_LINEAR THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `top:A topology`; `topspace top:A->bool`] THEN
    ASM_REWRITE_TAC[OPEN_IN_TOPSPACE; SUBTOPOLOGY_TOPSPACE];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP MATRIX_WORKS th)]) THEN
  REWRITE_TAC[P2BSS_CONG_DOT]);;

(* The inner products of the coordinate fields of Psi. *)

let P2BSS_PSI_METRIC = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) (Y:A->real^3) (E:real^3->A).
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) Y /\
     (!x. x IN topspace top ==> Y x dot (g x ** Y x) = &1) /\
     continuous_map (euclidean,top) E /\
     mfd_smooth_map (open_set_atlas (:real^3)) atlas (:real^3) E /\
     (!z t. E(z + t % basis 3) = E z)
     ==> !z a b.
           a$3 = &0 /\ b$3 = &0
           ==> mfd_differential (open_set_atlas (:real^3)) atlas
                 (\z. mfd_geo (top,atlas) g (E z) (Y(E z)) (z$3)) z a dot
               (g(mfd_geo (top,atlas) g (E z) (Y(E z)) (z$3)) **
                mfd_differential (open_set_atlas (:real^3)) atlas
                  (\z. mfd_geo (top,atlas) g (E z) (Y(E z)) (z$3)) z b) =
               mfd_differential (open_set_atlas (:real^3)) atlas E z a dot
               (g(E z) ** mfd_differential (open_set_atlas (:real^3)) atlas E z b) /\
               mfd_differential (open_set_atlas (:real^3)) atlas
                 (\z. mfd_geo (top,atlas) g (E z) (Y(E z)) (z$3)) z a dot
               (g(mfd_geo (top,atlas) g (E z) (Y(E z)) (z$3)) **
                mfd_differential (open_set_atlas (:real^3)) atlas
                  (\z. mfd_geo (top,atlas) g (E z) (Y(E z)) (z$3)) z (basis 3)) =
               mfd_differential (open_set_atlas (:real^3)) atlas E z a dot
               (g(E z) ** Y(E z)) /\
               mfd_differential (open_set_atlas (:real^3)) atlas
                 (\z. mfd_geo (top,atlas) g (E z) (Y(E z)) (z$3)) z (basis 3) dot
               (g(mfd_geo (top,atlas) g (E z) (Y(E z)) (z$3)) **
                mfd_differential (open_set_atlas (:real^3)) atlas
                  (\z. mfd_geo (top,atlas) g (E z) (Y(E z)) (z$3)) z (basis 3)) = &1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BSS_PSI_FACTS) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj(concl th))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!w:real^3. (E:real^3->A) w IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `continuous_map (euclidean,top) (E:real^3->A)` THEN
    REWRITE_TAC[CONTINUOUS_MAP; SUBSET; FORALL_IN_IMAGE; TOPSPACE_EUCLIDEAN; IN_UNIV] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `mfd_geo (top,atlas) (g:A->real^3^3) ((E:real^3->A) z) ((Y:A->real^3)(E z)) (z$3) =
                p2bkf_phi (top,atlas) g Y (z$3) (E z)` SUBST1_TAC THENL
   [REWRITE_TAC[p2bkf_phi]; ALL_TAC] THEN
  SUBGOAL_THEN `(Y:A->real^3)(p2bkf_phi (top,atlas) (g:A->real^3^3) Y ((z:real^3)$3) ((E:real^3->A) z)) =
                mfd_differential atlas atlas (p2bkf_phi (top,atlas) g Y (z$3)) (E z) (Y(E z))`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2BSS_PHI_Y THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[P2BSS_PHI_DOT]);;

(* ========================================================================= *)
(* The product metric Bc = q Gs(z1,z2) + dz3^2 on real^3 and the cylinder    *)
(* metric G0 y = (q/|y|^2) I on real^3 minus the origin.                     *)
(* ========================================================================= *)

let p2bss_bc = new_definition
 `p2bss_bc (q:real) (z:real^3) =
    (lambda i j. if i = 3 /\ j = 3 then &1
                 else if i = j then q * (&4 / (&1 + norm(lvs_proj z) pow 2) pow 2)
                 else &0):real^3^3`;;

let p2bss_g0 = new_definition
 `p2bss_g0 (q:real) (y:real^3) = (q / norm y pow 2) %% (mat 1:real^3^3)`;;

let P2BSS_BC_DOT = prove
 (`!q z a b. a dot (p2bss_bc q z ** b) =
             q * (&4 / (&1 + norm(lvs_proj z) pow 2) pow 2) * (lvs_proj a dot lvs_proj b) +
             a$3 * b$3`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[p2bss_bc; DOT_3; DOT_2; LVS_PROJ_COMPONENT; matrix_vector_mul; LAMBDA_BETA;
           DIMINDEX_3; ARITH; SUM_3] THEN
  REAL_ARITH_TAC);;

let P2BSS_GSF_SMOOTH3 = prove
 (`smooth_map_on (:real^3) (\z. lift(&4 / (&1 + norm(lvs_proj z) pow 2) pow 2))`,
  SUBGOAL_THEN `(\z:real^3. lift(&4 / (&1 + norm(lvs_proj z) pow 2) pow 2)) =
                (\x:real^2. lift(&4 / (&1 + norm x pow 2) pow 2)) o lvs_proj` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^2)` THEN
  REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; LRG_SPH_SMOOTH_C] THEN
  SIMP_TAC[LVS_PROJ_SMOOTH; OPEN_UNIV]);;

let P2BSS_BC_METRIC = prove
 (`!q. &0 < q
       ==> metric_field (:real^3) (p2bss_bc q) /\
           riemannian_metric (open_set_atlas (:real^3)) (p2bss_bc q)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `metric_field (:real^3) (p2bss_bc q)` ASSUME_TAC THENL
   [REWRITE_TAC[metric_field; OPEN_UNIV; IN_UNIV] THEN CONJ_TAC THENL
     [SIMP_TAC[LRG_SMOOTH_VECTORIZE; OPEN_UNIV] THEN REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[p2bss_bc; LAMBDA_BETA; DIMINDEX_3] THEN
      ASM_CASES_TAC `i = 3 /\ j = 3` THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
      ASM_CASES_TAC `i:num = j` THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
      REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
      REWRITE_TAC[OPEN_UNIV; P2BSS_GSF_SMOOTH3];
      ALL_TAC] THEN
    X_GEN_TAC `z:real^3` THEN CONJ_TAC THENL
     [SIMP_TAC[CART_EQ; TRANSP_COMPONENT; p2bss_bc; LAMBDA_BETA; DIMINDEX_3] THEN
      REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN REWRITE_TAC[P2BSS_BC_DOT] THEN
    SUBGOAL_THEN `&0 < q * (&4 / (&1 + norm(lvs_proj(z:real^3)) pow 2) pow 2)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_DIV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      MATCH_MP_TAC REAL_POW_LT THEN REWRITE_TAC[LRG_SPH_POS];
      ALL_TAC] THEN
    UNDISCH_TAC `~(v:real^3 = vec 0)` THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VEC_COMPONENT; DOT_2; LVS_PROJ_COMPONENT] THEN
    DISCH_TAC THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= c * x /\ &0 <= y /\ (&0 < c * x \/ &0 < y)
                             ==> &0 < c * x + y`) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 <= a + b`) THEN
      REWRITE_TAC[REAL_LE_SQUARE];
      REWRITE_TAC[REAL_LE_SQUARE];
      ASM_CASES_TAC `(v:real^3)$3 = &0` THENL
       [DISJ1_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `~((v:real^3)$1 = &0) \/ ~(v$2 = &0)` MP_TAC THENL
         [ASM_MESON_TAC[]; ALL_TAC] THEN
        STRIP_TAC THENL
         [MP_TAC(SPEC `(v:real^3)$2` REAL_LE_SQUARE) THEN
          MP_TAC(SPEC `(v:real^3)$1` REAL_LT_SQUARE) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
          MP_TAC(SPEC `(v:real^3)$1` REAL_LE_SQUARE) THEN
          MP_TAC(SPEC `(v:real^3)$2` REAL_LT_SQUARE) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
        DISJ2_TAC THEN ASM_REWRITE_TAC[REAL_LT_SQUARE]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[riemannian_metric; open_set_atlas; IN_SING] THEN GEN_TAC THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[GSYM open_set_atlas; P2BSR_METRIC_LOCAL_EUCLID] THEN
  ASM_REWRITE_TAC[IMAGE_ID]);;

let P2BSS_G0_METRIC = prove
 (`!q. &0 < q
       ==> open {y:real^3 | ~(y = vec 0)} /\
           metric_field {y:real^3 | ~(y = vec 0)} (p2bss_g0 q) /\
           riemannian_metric (open_set_atlas {y:real^3 | ~(y = vec 0)}) (p2bss_g0 q)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `open {y:real^3 | ~(y = vec 0)}` ASSUME_TAC THENL
   [REWRITE_TAC[SET_RULE `{y:real^3 | ~(y = vec 0)} = (:real^3) DIFF {vec 0}`] THEN
    REWRITE_TAC[GSYM closed; CLOSED_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field {y:real^3 | ~(y = vec 0)} (p2bss_g0 q)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[metric_field; IN_ELIM_THM] THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `(vectorize:real^3^3->real^(3,3)finite_prod) o p2bss_g0 q =
        (\z. drop((\x:real^3. lift(q / norm x pow 2)) z) % vectorize(mat 1:real^3^3))`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM; p2bss_g0; VECTORIZE_CMUL; LIFT_DROP]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
      MP_TAC(ISPECL [`{y:real^3 | ~(y = vec 0)}`; `\x:real^3. lift q`;
                     `\x:real^3. lift(norm x pow 2)`] SMOOTH_MAP_ON_LIFT_DIV) THEN
      ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; LIFT_DROP; IN_ELIM_THM] THEN
      DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`{y:real^3 | ~(y = vec 0)}`; `\x:real^3. x`] SMOOTH_MAP_ON_NORM_POW2_OPEN) THEN
        ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID];
        GEN_TAC THEN REWRITE_TAC[REAL_POW_EQ_0; NORM_EQ_0] THEN ARITH_TAC];
      ALL_TAC] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    REWRITE_TAC[p2bss_g0; TRANSP_MATRIX_CMUL; TRANSP_MAT; MATRIX_VECTOR_LMUL;
                MATRIX_VECTOR_MUL_LID; DOT_RMUL] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[DOT_POS_LT] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[NORM_POS_LT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[riemannian_metric; open_set_atlas; IN_SING] THEN GEN_TAC THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IMAGE_ID] THEN
  MATCH_MP_TAC MFDR_METRIC_FIELD_EQ THEN EXISTS_TAC `p2bss_g0 q` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`{y:real^3 | ~(y = vec 0)}`; `p2bss_g0 q`; `y:real^3`]
         RFB_OPEN_SET_METRIC_LOCAL) THEN
  ASM_REWRITE_TAC[GSYM open_set_atlas]);;

(* ========================================================================= *)
(* Inverse stereographic map sinv : real^2 -> unit sphere (from the north    *)
(* pole basis 3) and the map Xi z = exp(z$3/c) sinv(z$1,z$2) from real^3 to  *)
(* real^3 minus 0.                                                           *)
(* ========================================================================= *)

let p2bss_sinv = new_definition
 `p2bss_sinv (w:real^2) =
    basis 3 + (&2 / (&1 + norm w pow 2)) % (lvs_iota w - basis 3)`;;

let P2BSS_IOTA_DOTS = prove
 (`!w h:real^2. lvs_iota h dot lvs_iota w = h dot w /\ lvs_iota h dot basis 3 = &0 /\
                basis 3 dot lvs_iota h = &0 /\ (basis 3:real^3) dot basis 3 = &1`,
  SIMP_TAC[DOT_3; DOT_2; LVS_IOTA_COMPONENT; BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
  REAL_ARITH_TAC);;

let P2BSS_SINV_DERIV = prove
 (`!w:real^2.
     (p2bss_sinv has_derivative
      (\h. (&2 / (&1 + norm w pow 2)) % lvs_iota h +
           (--(&4) * (w dot h) / (&1 + norm w pow 2) pow 2) % (lvs_iota w - basis 3)))
     (at w)`,
  GEN_TAC THEN
  SUBGOAL_THEN `p2bss_sinv = (\z. basis 3 + (&2 / (&1 + norm z pow 2)) % (lvs_iota z - basis 3))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; p2bss_sinv]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`(\z. basis 3):real^2->real^3`; `(\h. vec 0):real^2->real^3`;
    `\z:real^2. (&2 / (&1 + norm z pow 2)) % (lvs_iota z - basis 3)`;
    `\h:real^2. (&2 / (&1 + norm w pow 2)) % lvs_iota h +
                (--(&4) * (w dot h) / (&1 + norm w pow 2) pow 2) % (lvs_iota w - basis 3)`;
    `at (w:real^2)`] HAS_DERIVATIVE_ADD) THEN
  REWRITE_TAC[HAS_DERIVATIVE_CONST; VECTOR_ADD_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL
   [`\z:real^2. &2 / (&1 + norm z pow 2)`;
    `\h:real^2. --(&4) * (w dot h) / (&1 + norm w pow 2) pow 2`;
    `\z:real^2. lvs_iota z - basis 3`; `\h:real^2. lvs_iota h`; `w:real^2`]
   HAS_DERIVATIVE_MUL_AT) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPEC `w:real^2` LRG_SPH_G_DERIV) THEN
      DISCH_THEN(MP_TAC o MATCH_MP HAS_DERIVATIVE_NEG) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THEN
      REWRITE_TAC[FUN_EQ_THM; o_THM; GSYM LIFT_NEG] THEN GEN_TAC THEN
      AP_TERM_TAC THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
      MP_TAC(ISPECL [`lvs_iota`; `lvs_iota`; `(\z. basis 3):real^2->real^3`;
                     `(\h. vec 0):real^2->real^3`; `at (w:real^2)`] HAS_DERIVATIVE_SUB) THEN
      REWRITE_TAC[HAS_DERIVATIVE_CONST; VECTOR_SUB_RZERO; ETA_AX] THEN
      DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
      REWRITE_TAC[LVS_IOTA_LINEAR]];
    ALL_TAC] THEN
  REWRITE_TAC[]);;

let P2BSS_SINV_FACTS = prove
 (`!w h:real^2.
     p2bss_sinv w dot p2bss_sinv w = &1 /\
     ((&2 / (&1 + norm w pow 2)) % lvs_iota h +
      (--(&4) * (w dot h) / (&1 + norm w pow 2) pow 2) % (lvs_iota w - basis 3)) dot
     p2bss_sinv w = &0 /\
     ((&2 / (&1 + norm w pow 2)) % lvs_iota h +
      (--(&4) * (w dot h) / (&1 + norm w pow 2) pow 2) % (lvs_iota w - basis 3)) dot
     ((&2 / (&1 + norm w pow 2)) % lvs_iota h +
      (--(&4) * (w dot h) / (&1 + norm w pow 2) pow 2) % (lvs_iota w - basis 3)) =
     (&4 / (&1 + norm w pow 2) pow 2) * (h dot h) /\
     ~(p2bss_sinv w = basis 3)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bss_sinv; NORM_POW_2] THEN
  REWRITE_TAC[DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL; DOT_LSUB; DOT_RSUB; P2BSS_IOTA_DOTS] THEN
  REWRITE_TAC[DOT_SYM] THEN
  MP_TAC(ISPEC `w:real^2` DOT_POS_LE) THEN
  SPEC_TAC(`(w:real^2) dot w`,`n:real`) THEN SPEC_TAC(`(h:real^2) dot w`,`m:real`) THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(&1 + n = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `~(&1 + n = &0)` THEN CONV_TAC REAL_FIELD;
    UNDISCH_TAC `~(&1 + n = &0)` THEN CONV_TAC REAL_FIELD;
    UNDISCH_TAC `~(&1 + n = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ARITH `(b:real^3) + c % (x - b) = b <=> c % (x - b) = vec 0`] THEN
  REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN
  SUBGOAL_THEN `~(lvs_iota w = basis 3)` (fun th -> REWRITE_TAC[th]) THENL
   [DISCH_THEN(MP_TAC o AP_TERM `\v:real^3. v$3`) THEN
    SIMP_TAC[LVS_IOTA_COMPONENT; BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_DIV_EQ_0] THEN REAL_ARITH_TAC);;

let p2bss_xi = new_definition
 `p2bss_xi (c:real) (z:real^3) = exp(z$3 / c) % p2bss_sinv (lvs_proj z)`;;

let P2BSS_XI_DERIV = prove
 (`!c z. ~(c = &0)
         ==> (p2bss_xi c has_derivative
              (\h. exp(z$3 / c) %
                   ((&2 / (&1 + norm(lvs_proj z) pow 2)) % lvs_iota(lvs_proj h) +
                    (--(&4) * (lvs_proj z dot lvs_proj h) / (&1 + norm(lvs_proj z) pow 2) pow 2) %
                    (lvs_iota(lvs_proj z) - basis 3)) +
                   (exp(z$3 / c) * h$3 / c) % p2bss_sinv(lvs_proj z))) (at z)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `p2bss_xi c = (\z. (\z:real^3. exp(z$3 / c)) z % (p2bss_sinv o lvs_proj) z)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; p2bss_xi; o_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\z:real^3. exp(z$3 / c)`; `\h:real^3. exp((z:real^3)$3 / c) * h$3 / c`;
                 `p2bss_sinv o lvs_proj`;
                 `\h:real^3. (&2 / (&1 + norm(lvs_proj z) pow 2)) % lvs_iota(lvs_proj h) +
                             (--(&4) * (lvs_proj z dot lvs_proj h) /
                              (&1 + norm(lvs_proj z) pow 2) pow 2) %
                             (lvs_iota(lvs_proj z) - basis 3)`;
                 `z:real^3`] HAS_DERIVATIVE_MUL_AT) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `lift o (\z:real^3. exp(z$3 / c)) = (lift o exp o drop) o (\z. lift(z$3 / c))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
      SUBGOAL_THEN `lift o (\h:real^3. exp((z:real^3)$3 / c) * h$3 / c) =
                    (\x. exp(z$3 / c) % x) o (\h:real^3. lift(h$3 / c))` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_CMUL] THEN REWRITE_TAC[real_div; REAL_MUL_ASSOC];
        ALL_TAC] THEN
      MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
       [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
        REWRITE_TAC[linear; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
        REWRITE_TAC[GSYM LIFT_ADD; GSYM LIFT_CMUL; LIFT_EQ] THEN REAL_ARITH_TAC;
        REWRITE_TAC[GSYM HAS_REAL_FRECHET_DERIVATIVE_AT; HAS_REAL_DERIVATIVE_EXP]];
      SUBGOAL_THEN
       `(\h:real^3. (&2 / (&1 + norm(lvs_proj z) pow 2)) % lvs_iota(lvs_proj h) +
                    (--(&4) * (lvs_proj z dot lvs_proj h) / (&1 + norm(lvs_proj z) pow 2) pow 2) %
                    (lvs_iota(lvs_proj z) - basis 3)) =
        (\h:real^2. (&2 / (&1 + norm(lvs_proj z) pow 2)) % lvs_iota h +
                    (--(&4) * (lvs_proj z dot h) / (&1 + norm(lvs_proj z) pow 2) pow 2) %
                    (lvs_iota(lvs_proj z) - basis 3)) o lvs_proj`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
       [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LVS_PROJ_LINEAR];
        REWRITE_TAC[P2BSS_SINV_DERIV]]];
    ALL_TAC] THEN
  REWRITE_TAC[o_THM] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REWRITE_TAC[]);;

let P2BSS_XI_NORM = prove
 (`!c z. norm(p2bss_xi c z) = exp(z$3 / c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bss_xi; NORM_MUL; REAL_ABS_EXP] THEN
  REWRITE_TAC[vector_norm; P2BSS_SINV_FACTS; SQRT_1; REAL_MUL_RID]);;

let P2BSS_XI_FDERIV = prove
 (`!c z. ~(c = &0)
         ==> frechet_derivative (p2bss_xi c) (at z) =
             (\h. exp(z$3 / c) %
                  ((&2 / (&1 + norm(lvs_proj z) pow 2)) % lvs_iota(lvs_proj h) +
                   (--(&4) * (lvs_proj z dot lvs_proj h) / (&1 + norm(lvs_proj z) pow 2) pow 2) %
                   (lvs_iota(lvs_proj z) - basis 3)) +
                  (exp(z$3 / c) * h$3 / c) % p2bss_sinv(lvs_proj z))`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  ASM_SIMP_TAC[P2BSS_XI_DERIV]);;

let P2BSS_XI_QUAD = prove
 (`!c z h. &0 < c
           ==> frechet_derivative (p2bss_xi c) (at z) h dot
               (p2bss_g0 (c pow 2) (p2bss_xi c z) ** frechet_derivative (p2bss_xi c) (at z) h) =
               h dot (p2bss_bc (c pow 2) z ** h)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[P2BSS_XI_FDERIV; REAL_LT_IMP_NZ] THEN
  REWRITE_TAC[p2bss_g0; P2BSS_XI_NORM; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID] THEN
  MP_TAC(ISPECL [`lvs_proj(z:real^3)`; `lvs_proj(h:real^3)`] P2BSS_SINV_FACTS) THEN
  ABBREV_TAC `A = (&2 / (&1 + norm(lvs_proj(z:real^3)) pow 2)) % lvs_iota(lvs_proj(h:real^3)) +
                  (--(&4) * (lvs_proj z dot lvs_proj h) / (&1 + norm(lvs_proj z) pow 2) pow 2) %
                  (lvs_iota(lvs_proj z) - basis 3)` THEN
  ABBREV_TAC `s = p2bss_sinv(lvs_proj(z:real^3))` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(s:real^3) dot A = &0` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[P2BSS_BC_DOT; DOT_RMUL; DOT_LMUL; DOT_LADD; DOT_RADD] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `(z:real^3)$3 / c` REAL_EXP_POS_LT) THEN
  SPEC_TAC(`exp((z:real^3)$3 / c)`,`e:real`) THEN
  SPEC_TAC(`&4 / (&1 + norm(lvs_proj(z:real^3)) pow 2) pow 2`,`k:real`) THEN
  SPEC_TAC(`lvs_proj(h:real^3) dot lvs_proj h`,`r:real`) THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  UNDISCH_TAC `&0 < c` THEN UNDISCH_TAC `&0 < e` THEN CONV_TAC REAL_FIELD);;

(* ========================================================================= *)
(* The slab chart.  p2bss_xi c is the slab chart p2bpc_ann_n of pc_p2b_poinc *)
(* with z$3 scaled by 1/c; its inverse p2bss_theta c off the closed north    *)
(* ray (explicit, smooth); Xi pulls the model metric G0 = (c^2/|y|^2) I back *)
(* to Bc = c^2 Gs + dz3^2, so theta is a local isometry from (Zn,G0) to      *)
(* (real^3,Bc).                                                              *)
(* ========================================================================= *)

let p2bss_theta = new_definition
 `p2bss_theta (c:real) (y:real^3) =
    vector[p2bpc_ann_n_inv y$1; p2bpc_ann_n_inv y$2; c * p2bpc_ann_n_inv y$3]:real^3`;;

let P2BSS_SINV_STEREO = prove
 (`!w:real^2. p2bss_sinv w = stereo2_n_inv w`,
  GEN_TAC THEN REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3] THEN
  SIMP_TAC[p2bss_sinv; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_SUB_COMPONENT;
           BASIS_COMPONENT; DIMINDEX_3; ARITH; LVS_IOTA_COMPONENT;
           STEX_STEREO2_N_INV_COMPONENTS] THEN
  MP_TAC(SPEC `norm(w:real^2) pow 2` (REAL_ARITH `!q. &0 <= q ==> ~(&1 + q = &0) /\ ~(q + &1 = &0)`)) THEN
  ANTS_TAC THENL [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  SPEC_TAC(`norm(w:real^2) pow 2`,`q:real`) THEN GEN_TAC THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THEN REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD);;

let P2BSS_XI_ANN = prove
 (`!c z. p2bss_xi c z = p2bpc_ann_n (vector[z$1; z$2; z$3 / c])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bss_xi; p2bpc_ann_n; VECTOR_3; P2BSS_SINV_STEREO] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; LVS_PROJ_COMPONENT; P2BPC_PR2_COMPONENTS;
              VECTOR_3]);;

let P2BSS_XI_THETA = prove
 (`!c y. ~(c = &0) /\ ~(norm y = y$3) ==> p2bss_xi c (p2bss_theta c y) = y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[P2BSS_XI_ANN; p2bss_theta; VECTOR_3] THEN
  SUBGOAL_THEN
   `vector[p2bpc_ann_n_inv y$1; p2bpc_ann_n_inv y$2; (c * p2bpc_ann_n_inv y$3) / c]:real^3 =
    p2bpc_ann_n_inv y`
  SUBST1_TAC THENL
   [REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
    UNDISCH_TAC `~(c = &0)` THEN CONV_TAC REAL_FIELD;
    ASM_SIMP_TAC[P2BPC_ANN_N_RIGHT]]);;

let P2BSS_THETA_XI = prove
 (`!c z. ~(c = &0) ==> p2bss_theta c (p2bss_xi c z) = z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[P2BSS_XI_ANN; p2bss_theta; P2BPC_ANN_N_LEFT; VECTOR_3] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
  UNDISCH_TAC `~(c = &0)` THEN CONV_TAC REAL_FIELD);;

let P2BSS_XI_ZN = prove
 (`!c z. ~(c = &0) ==> ~(norm(p2bss_xi c z) = p2bss_xi c z$3)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[P2BSS_XI_NORM] THEN
  REWRITE_TAC[p2bss_xi; VECTOR_MUL_COMPONENT; P2BSS_SINV_STEREO;
              STEX_STEREO2_N_INV_COMPONENTS] THEN
  MP_TAC(SPEC `(z:real^3)$3 / c` REAL_EXP_POS_LT) THEN
  MP_TAC(SPEC `norm(lvs_proj(z:real^3)) pow 2` (REAL_ARITH `!q. &0 <= q ==> &0 < q + &1`)) THEN
  ANTS_TAC THENL [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  SPEC_TAC(`norm(lvs_proj(z:real^3)) pow 2`,`q:real`) THEN
  SPEC_TAC(`exp((z:real^3)$3 / c)`,`e:real`) THEN REPEAT GEN_TAC THEN
  DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(q - &1) / (q + &1) = &1 - &2 / (q + &1)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < q + &1` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 / (q + &1)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`&2 / (q + &1)`,`t:real`) THEN GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < e * t` MP_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_LDISTRIB; REAL_MUL_RID] THEN REAL_ARITH_TAC);;

let P2BSS_THETA_SMOOTH = prove
 (`!c. smooth_map_on {y:real^3 | ~(norm y = y$3)} (p2bss_theta c)`,
  GEN_TAC THEN
  SUBGOAL_THEN `p2bss_theta c = (\v:real^3. vector[v$1; v$2; c * v$3]:real^3) o p2bpc_ann_n_inv`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; p2bss_theta]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
  REWRITE_TAC[P2BPC_OFF_RAY_OPEN; P2BPC_ANN_N_INV_SMOOTH] THEN
  REWRITE_TAC[linear; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC);;

let P2BSS_CONJ_SCALAR_DOT = prove
 (`!(M:real^N^N) s u v.
     u dot ((transp M ** (s %% mat 1) ** M) ** v) = s * ((M ** u) dot (M ** v))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
  REWRITE_TAC[DOT_MATRIX_TRANSP_RMUL; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID; DOT_RMUL]);;

let P2BSS_XI_METRIC = prove
 (`!c z. &0 < c
         ==> transp(matrix(frechet_derivative (p2bss_xi c) (at z))) **
             p2bss_g0 (c pow 2) (p2bss_xi c z) **
             matrix(frechet_derivative (p2bss_xi c) (at z)) =
             p2bss_bc (c pow 2) z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `linear(frechet_derivative (p2bss_xi c) (at (z:real^3)))` ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN REWRITE_TAC[differentiable] THEN
    ASM_MESON_TAC[P2BSS_XI_DERIV; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  MATCH_MP_TAC GEOI_QUAD_EQ THEN REWRITE_TAC[p2bss_g0; P2BSS_CONJ_SCALAR_DOT] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN AP_TERM_TAC THEN MATCH_ACCEPT_TAC DOT_SYM;
    REPEAT GEN_TAC THEN REWRITE_TAC[P2BSS_BC_DOT] THEN
    SUBGOAL_THEN `lvs_proj (v:real^3) dot lvs_proj (u:real^3) = lvs_proj u dot lvs_proj v`
    SUBST1_TAC THENL [MATCH_ACCEPT_TAC DOT_SYM; REAL_ARITH_TAC];
    X_GEN_TAC `u:real^3` THEN
    MP_TAC(SPECL [`c:real`; `z:real^3`; `u:real^3`] P2BSS_XI_QUAD) THEN
    ASM_REWRITE_TAC[p2bss_g0; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID; DOT_RMUL] THEN
    ASM_SIMP_TAC[MATRIX_WORKS]]);;

let P2BSS_THETA_HAS_DERIV = prove
 (`!c y. ~(norm y = y$3)
         ==> (p2bss_theta c has_derivative frechet_derivative (p2bss_theta c) (at y)) (at y)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
  EXISTS_TAC `{y:real^3 | ~(norm y = y$3)}` THEN
  ASM_REWRITE_TAC[P2BPC_OFF_RAY_OPEN; P2BSS_THETA_SMOOTH; IN_ELIM_THM]);;

let P2BSS_XI_HAS_DERIV = prove
 (`!c z. ~(c = &0)
         ==> (p2bss_xi c has_derivative frechet_derivative (p2bss_xi c) (at z)) (at z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS; differentiable] THEN
  ASM_MESON_TAC[P2BSS_XI_DERIV]);;

let P2BSS_XI_THETA_DERIV = prove
 (`!c y. ~(c = &0) /\ ~(norm y = y$3)
         ==> frechet_derivative (p2bss_xi c) (at (p2bss_theta c y)) o
             frechet_derivative (p2bss_theta c) (at y) = (\h. h)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_AT THEN
  EXISTS_TAC `p2bss_xi c o p2bss_theta c` THEN EXISTS_TAC `y:real^3` THEN CONJ_TAC THENL
   [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_SIMP_TAC[P2BSS_THETA_HAS_DERIV; P2BSS_XI_HAS_DERIV];
    ALL_TAC] THEN
  MP_TAC(CONJUNCT1 P2BPC_OFF_RAY_OPEN) THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[IN_ELIM_THM; SUBSET; IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
  MAP_EVERY EXISTS_TAC [`\x:real^3. x`; `d:real`] THEN
  ASM_REWRITE_TAC[HAS_DERIVATIVE_ID; o_THM] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2BSS_XI_THETA THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[DIST_SYM]);;

let P2BSS_THETA_LISOM = prove
 (`!c. &0 < c
       ==> mfd_local_isometry
             (subtopology euclidean {y:real^3 | ~(norm y = y$3)},
              open_set_atlas {y:real^3 | ~(norm y = y$3)}) (p2bss_g0 (c pow 2))
             (euclidean,open_set_atlas (:real^3)) (p2bss_bc (c pow 2))
             {y:real^3 | ~(norm y = y$3)} (p2bss_theta c)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(c = &0) /\ &0 < c pow 2` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_NZ; REAL_POW_LT]; ALL_TAC] THEN
  ABBREV_TAC `Zn = {y:real^3 | ~(norm y = y$3)}` THEN
  SUBGOAL_THEN `open(Zn:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Zn" THEN REWRITE_TAC[P2BPC_OFF_RAY_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN `(Zn:real^3->bool) SUBSET {y:real^3 | ~(y = vec 0)}` ASSUME_TAC THENL
   [EXPAND_TAC "Zn" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN GEN_TAC THEN
    REWRITE_TAC[CONTRAPOS_THM] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[NORM_0; VEC_COMPONENT];
    ALL_TAC] THEN
  MATCH_MP_TAC GEOI_LISOM_FROM_DIFF THEN
  ASM_SIMP_TAC[OPEN_SET_ATLAS; GEOI_EUCLIDEAN_ATLAS; P2BSS_BC_METRIC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RFB_OPEN_SET_RIEMANNIAN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `{y:real^3 | ~(y = vec 0)}` THEN
    ASM_SIMP_TAC[P2BSS_G0_METRIC];
    REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN; SUBSET_UNIV];
    REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY; INTER_IDEMPOT; CONTINUOUS_MAP_EUCLIDEAN] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN EXPAND_TAC "Zn" THEN
    REWRITE_TAC[P2BSS_THETA_SMOOTH];
    REWRITE_TAC[MFD_SMOOTH_MAP_OPEN_SET_ATLAS; IN_UNIV; INTER_IDEMPOT] THEN
    REWRITE_TAC[SET_RULE `{x:real^3 | x IN s} = s`] THEN EXPAND_TAC "Zn" THEN
    REWRITE_TAC[P2BSS_THETA_SMOOTH];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[CMPW_PM_DIFF; MFDD_OPEN_SET_CHART_AT; IN_UNIV; ETA_AX] THEN
  SUBGOAL_THEN `~(norm(y:real^3) = y$3)` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN Zn` THEN EXPAND_TAC "Zn" THEN REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  ABBREV_TAC `D = frechet_derivative (p2bss_theta c) (at (y:real^3))` THEN
  ABBREV_TAC `X = frechet_derivative (p2bss_xi c) (at (p2bss_theta c y))` THEN
  SUBGOAL_THEN `linear(D:real^3->real^3) /\ linear(X:real^3->real^3)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["D"; "X"] THEN CONJ_TAC THEN
    MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN REWRITE_TAC[differentiable] THEN
    ASM_MESON_TAC[P2BSS_THETA_HAS_DERIV; P2BSS_XI_HAS_DERIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `matrix(X:real^3->real^3) ** matrix(D:real^3->real^3) = mat 1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM MATRIX_COMPOSE] THEN MAP_EVERY EXPAND_TAC ["D"; "X"] THEN
    ASM_SIMP_TAC[P2BSS_XI_THETA_DERIV; MATRIX_ID];
    ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `p2bss_theta c y`] P2BSS_XI_METRIC) THEN
  ASM_SIMP_TAC[P2BSS_XI_THETA] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[MATRIX_MUL_ASSOC; GSYM MATRIX_TRANSP_MUL] THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MATRIX_MUL_ASSOC; GSYM MATRIX_TRANSP_MUL] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[TRANSP_MAT; MATRIX_MUL_LID; MATRIX_MUL_RID]);;

(* ========================================================================= *)
(* The image of a local isometry defined on a whole manifold is open; a pair *)
(* of local isometries of the stereographic plane glued by the Mobius map mu *)
(* covers a connected Hausdorff surface (the image is the union of the       *)
(* images of two closed discs, hence compact).                               *)
(* ========================================================================= *)

let P2BSS_LISOM_IMAGE_OPEN = prove
 (`!top atlas (g:A->real^N^N) top' atlas' (g':B->real^N^N) f.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     hausdorff_space top' /\ smooth_manifold_atlas top' atlas' /\ riemannian_metric atlas' g' /\
     mfd_local_isometry (top,atlas) g (top',atlas') g' (topspace top) f
     ==> open_in top' (IMAGE f (topspace top))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `g':B->real^N^N`;
                 `f:A->B`; `x:A`] GEOH_LISOM_LOCAL_HOMEO) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `V:B->bool` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `V:B->bool` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_SURJECTIVE_MAP) THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET topspace top /\ (V:B->bool) SUBSET topspace top'`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `topspace top INTER U = (U:A->bool) /\ topspace top' INTER V = (V:B->bool)`
  (fun th -> REWRITE_TAC[th]) THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN CONJ_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]]);;

let P2BSS_MOB_BOUND = prove
 (`!z. &3 <= norm z ==> ~(z = Cx(&1)) /\ norm(p2bss_mob z) <= &3`,
  GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `&3 <= norm(Cx(&1))` THEN
    REWRITE_TAC[COMPLEX_NORM_CX] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[p2bss_mob; COMPLEX_NORM_DIV] THEN
  MP_TAC(ISPECL [`Cx(&1)`; `z:complex`] NORM_TRIANGLE) THEN
  MP_TAC(ONCE_REWRITE_RULE[NORM_SUB] (ISPECL [`z:complex`; `Cx(&1)`] NORM_TRIANGLE_SUB)) THEN
  REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 < norm(Cx(&1) - z)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

let P2BSS_MOB_INV = prove
 (`!w. &3 <= norm w
       ==> ~((w - Cx(&1)) / (w + Cx(&1)) = Cx(&1)) /\
           p2bss_mob ((w - Cx(&1)) / (w + Cx(&1))) = w /\
           norm((w - Cx(&1)) / (w + Cx(&1))) <= &3`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`w:complex`; `--Cx(&1)`] NORM_TRIANGLE_SUB) THEN
  MP_TAC(ISPECL [`w:complex`; `--Cx(&1)`] NORM_TRIANGLE) THEN
  REWRITE_TAC[NORM_NEG; COMPLEX_NORM_CX; REAL_ABS_NUM; COMPLEX_SUB_RNEG; GSYM complex_sub] THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 < norm(w + Cx(&1))` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(w + Cx(&1) = Cx(&0))` ASSUME_TAC THENL
   [DISCH_THEN(fun th -> UNDISCH_TAC `&0 < norm(w + Cx(&1))` THEN REWRITE_TAC[th]) THEN
    REWRITE_TAC[COMPLEX_NORM_CX] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `~(w + Cx(&1) = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD;
    REWRITE_TAC[p2bss_mob] THEN UNDISCH_TAC `~(w + Cx(&1) = Cx(&0))` THEN
    CONV_TAC COMPLEX_FIELD;
    REWRITE_TAC[COMPLEX_NORM_DIV] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC]);;

let P2BSS_PAIR_ONTO = prove
 (`!top (atlas:((B->bool)#(B->real^2))->bool) (g:B->real^2^2) FS FN.
     hausdorff_space top /\ connected_space top /\
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_local_isometry (euclidean,open_set_atlas (:real^2)) p2bss_gs (top,atlas) g
                        (:real^2) FS /\
     mfd_local_isometry (euclidean,open_set_atlas (:real^2)) p2bss_gs (top,atlas) g
                        (:real^2) FN /\
     (!z. ~(z = Cx(&1)) ==> FN(p2bss_mob z) = FS z)
     ==> IMAGE FS (:real^2) UNION IMAGE FN (:real^2) = topspace top`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `continuous_map (euclidean,top) (FS:real^2->B) /\
                continuous_map (euclidean,top) (FN:real^2->B)` STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[mfd_local_isometry; SUBTOPOLOGY_UNIV]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (IMAGE (FS:real^2->B) (:real^2) UNION IMAGE FN (:real^2))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(:real^2) = topspace euclidean` SUBST1_TAC THENL
     [REWRITE_TAC[TOPSPACE_EUCLIDEAN]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_UNION THEN CONJ_TAC THEN
    MATCH_MP_TAC(ISPECL [`euclidean:(real^2)topology`; `open_set_atlas (:real^2)`; `p2bss_gs`;
                         `top:B topology`; `atlas:((B->bool)#(B->real^2))->bool`;
                         `g:B->real^2^2`] P2BSS_LISOM_IMAGE_OPEN) THEN
    ASM_REWRITE_TAC[P2BSS_GS_FACTS; TOPSPACE_EUCLIDEAN];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (FS:real^2->B) (:real^2) UNION IMAGE FN (:real^2) =
    IMAGE FS (cball(vec 0,&3)) UNION IMAGE FN (cball(vec 0,&3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [ALL_TAC; MATCH_MP_TAC(SET_RULE
        `s SUBSET s' /\ t SUBSET t' ==> (s:B->bool) UNION t SUBSET s' UNION t'`) THEN
      CONJ_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET_UNIV]] THEN
    REWRITE_TAC[UNION_SUBSET] THEN
    CONJ_TAC THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV; IN_UNION; IN_IMAGE; IN_CBALL_0] THEN
    X_GEN_TAC `z:real^2` THENL
     [ASM_CASES_TAC `norm(z:real^2) <= &3` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      MP_TAC(SPEC `z:complex` P2BSS_MOB_BOUND) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN ASM_MESON_TAC[];
      ASM_CASES_TAC `norm(z:real^2) <= &3` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      MP_TAC(SPEC `z:complex` P2BSS_MOB_INV) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed_in top (IMAGE (FS:real^2->B) (:real^2) UNION IMAGE FN (:real^2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC COMPACT_IN_UNION THEN CONJ_TAC THEN
    MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `euclidean:(real^2)topology` THEN
    ASM_REWRITE_TAC[COMPACT_IN_EUCLIDEAN; COMPACT_CBALL];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONNECTED_SPACE_CLOPEN_IN]) THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (FS:real^2->B) (:real^2) UNION IMAGE FN (:real^2)`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `~a ==> a \/ b ==> b`) THEN
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; NOT_FORALL_THM; IN_UNION] THEN
  EXISTS_TAC `(FS:real^2->B) (vec 0)` THEN DISJ1_TAC THEN
  MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_UNIV; IN_CBALL_0; NORM_0] THEN REAL_ARITH_TAC);;

(* The leaf through a point of positive scalar curvature, with the metric   *)
(* k g_N of curvature 1, is covered by a Cartan pair glued by mu.           *)

let P2BSS_LEAF_PAIR = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f (Y:A->real^3) x0 K0.
     hausdorff_space top /\ connected_space top /\
     p2b_shrinker (top,atlas) g f /\ mfd_complete (top,atlas) g /\
     (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
              ==> &0 <= mfd_sectional atlas g x u v) /\
     (!x. x IN topspace top ==> mfd_scalar atlas g x <= K0) /\
     x0 IN topspace top /\ &0 < mfd_scalar atlas g x0 /\
     p2b_parallel_on atlas g (topspace top) Y /\
     (!x. x IN topspace top ==> Y x dot (g x ** Y x) = &1)
     ==> ?k FS FN.
           &0 < k /\
           mfd_local_isometry (euclidean,open_set_atlas (:real^2)) p2bss_gs
             (subtopology top (lvs_set (topspace top) (p2bss_h atlas f Y) (p2bss_h atlas f Y x0)),
              lvs_atlas top atlas (topspace top) (p2bss_h atlas f Y) (p2bss_h atlas f Y x0))
             (\x. k %% lvs_metric top atlas g (topspace top) (p2bss_h atlas f Y)
                                  (p2bss_h atlas f Y x0) x)
             (:real^2) FS /\
           mfd_local_isometry (euclidean,open_set_atlas (:real^2)) p2bss_gs
             (subtopology top (lvs_set (topspace top) (p2bss_h atlas f Y) (p2bss_h atlas f Y x0)),
              lvs_atlas top atlas (topspace top) (p2bss_h atlas f Y) (p2bss_h atlas f Y x0))
             (\x. k %% lvs_metric top atlas g (topspace top) (p2bss_h atlas f Y)
                                  (p2bss_h atlas f Y x0) x)
             (:real^2) FN /\
           (!z. ~(z = Cx(&1)) ==> FN(p2bss_mob z) = FS z) /\
           IMAGE FS (:real^2) UNION IMAGE FN (:real^2) =
           lvs_set (topspace top) (p2bss_h atlas f Y) (p2bss_h atlas f Y x0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `Y:A->real^3`; `x0:A`; `K0:real`] P2BSS_LEAF) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `N = lvs_set (topspace top) (p2bss_h atlas f (Y:A->real^3)) (p2bss_h atlas f Y x0)` THEN
  ABBREV_TAC `atlasN = lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) (topspace top)
                                 (p2bss_h atlas f (Y:A->real^3)) (p2bss_h atlas f Y x0)` THEN
  ABBREV_TAC `gN = lvs_metric top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)
                              (topspace top) (p2bss_h atlas f (Y:A->real^3))
                              (p2bss_h atlas f Y x0)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_TAC `C:real`)
      (X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC))))) THEN
  EXISTS_TAC `k:real` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `Y:A->real^3`; `p2bss_h atlas f (Y:A->real^3) x0`]
                P2BSS_LEVEL_SHRINKER) THEN
  ASM_REWRITE_TAC[p2b_shrinker] THEN STRIP_TAC THEN
  SUBGOAL_THEN `hausdorff_space(subtopology top (N:A->bool))` ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN MATCH_MP_TAC LVS_HAUSDORFF THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `topspace(subtopology top N) = (N:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN MATCH_MP_TAC LVS_TOPSPACE THEN REWRITE_TAC[OPEN_IN_TOPSPACE];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_space(subtopology top (N:A->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_SPACE_SUBTOPOLOGY THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (atlasN:((A->bool)#(A->real^2))->bool) (\x. k %% gN x)`
  ASSUME_TAC THENL [MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x u v. x IN topspace(subtopology top N) /\ ~collinear {vec 0,u,v}
            ==> mfd_sectional (atlasN:((A->bool)#(A->real^2))->bool) (\x. k %% gN x) x u v = &1`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`subtopology top (N:A->bool)`; `atlasN:((A->bool)#(A->real^2))->bool`;
                   `gN:A->real^2^2`; `k:real`; `x:A`; `u:real^2`; `v:real^2`] P2BSS_SEC_SCALE) THEN
    ASM_SIMP_TAC[REAL_DIV_REFL; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology top (N:A->bool)`; `atlasN:((A->bool)#(A->real^2))->bool`;
                 `\x:A. k %% (gN:A->real^2^2) x`; `x0:A`] GEOJ_ONB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `E:real^2^2`) THEN
  SUBGOAL_THEN `transp(&2 %% E) ** (k %% (gN:A->real^2^2) x0) ** (&2 %% E) =
                p2bss_gs (vec 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `transp(E:real^2^2) ** (k %% (gN:A->real^2^2) x0) ** E = mat 1` THEN
    REWRITE_TAC[TRANSP_MATRIX_CMUL; MATRIX_MUL_LMUL; MATRIX_MUL_RMUL; p2bss_gs; NORM_0] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `&2 %% k %% &2 %% (transp (E:real^2^2) ** (gN:A->real^2^2) x0 ** E) =
                  (&2 * &2) %% (k %% (transp E ** gN x0 ** E))` SUBST1_TAC THENL
     [REWRITE_TAC[MATRIX_CMUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[]] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology top (N:A->bool)`; `atlasN:((A->bool)#(A->real^2))->bool`;
                 `\x:A. k %% (gN:A->real^2^2) x`; `x0:A`; `&2 %% (E:real^2^2)`]
                P2BSS_CARTAN_PAIR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:A` (X_CHOOSE_THEN `L2:real^2^2` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC
   [`p2bss_cartan (subtopology top N,atlasN) (\x:A. k %% (gN:A->real^2^2) x) x0 (&2 %% E)`;
    `p2bss_cartan (subtopology top N,atlasN) (\x:A. k %% (gN:A->real^2^2) x) q L2`] THEN
  SUBGOAL_THEN
   `mfd_local_isometry (euclidean,open_set_atlas (:real^2)) p2bss_gs (subtopology top N,atlasN)
      (\x:A. k %% (gN:A->real^2^2) x) (:real^2)
      (p2bss_cartan (subtopology top N,atlasN) (\x:A. k %% gN x) x0 (&2 %% E)) /\
    mfd_local_isometry (euclidean,open_set_atlas (:real^2)) p2bss_gs (subtopology top N,atlasN)
      (\x:A. k %% (gN:A->real^2^2) x) (:real^2)
      (p2bss_cartan (subtopology top N,atlasN) (\x:A. k %% gN x) q L2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC P2BSS_CARTAN_LISOM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th] THEN ASSUME_TAC th) THEN
  MATCH_MP_TAC P2BSS_PAIR_ONTO THEN
  MAP_EVERY EXISTS_TAC [`atlasN:((A->bool)#(A->real^2))->bool`; `\x:A. k %% (gN:A->real^2^2) x`] THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The map E z = F(z$1,z$2) for a local isometry F of the stereographic      *)
(* plane into the leaf (N, k g_N): continuity, smoothness, invariance in     *)
(* z$3, values in N, and its differential through lvs_jac; its Gram matrix   *)
(* (inv k) Gs and orthogonality to Y; then Psi_F is a local isometry from    *)
(* (real^3, Bc(inv k)) to (M, g).                                            *)
(* ========================================================================= *)

let P2BSS_PROJ_SHIFT3 = prove
 (`!z t. lvs_proj(z + t % basis 3) = lvs_proj z`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; LVS_PROJ_COMPONENT] THEN
  SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
  REAL_ARITH_TAC);;

let P2BSS_PROJ_MDIFF = prove
 (`!z:real^3. mfd_differential (open_set_atlas (:real^3)) (open_set_atlas (:real^2)) lvs_proj z =
              lvs_proj`,
  GEN_TAC THEN REWRITE_TAC[MFD_DIFFERENTIAL_OPEN_SET_ATLAS] THEN
  SIMP_TAC[MFDD_OPEN_SET_CHART_AT; IN_UNIV; ETA_AX] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LVS_PROJ_LINEAR]);;

let P2BSS_INCL_MDIFF = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) W f u x.
     mfd_differential (lvs_atlas top atlas W f u) atlas (\x. x) x = lvs_jac top atlas W f u x`,
  REWRITE_TAC[mfd_differential; lvs_jac]);;

let P2BSS_E_FACTS = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f (Y:A->real^3) s0 k
    (Fc:real^2->A).
     p2b_shrinker (top,atlas) g f /\ p2b_parallel_on atlas g (topspace top) Y /\
     (!x. x IN topspace top ==> Y x dot (g x ** Y x) = &1) /\
     mfd_local_isometry (euclidean,open_set_atlas (:real^2)) p2bss_gs
       (subtopology top (lvs_set (topspace top) (p2bss_h atlas f Y) s0),
        lvs_atlas top atlas (topspace top) (p2bss_h atlas f Y) s0)
       (\x. k %% lvs_metric top atlas g (topspace top) (p2bss_h atlas f Y) s0 x) (:real^2) Fc
     ==> continuous_map (euclidean,top) (\z. Fc(lvs_proj z)) /\
         mfd_smooth_map (open_set_atlas (:real^3)) atlas (:real^3) (\z. Fc(lvs_proj z)) /\
         (!z t. Fc(lvs_proj(z + t % basis 3)) = Fc(lvs_proj z)) /\
         (!w. Fc w IN lvs_set (topspace top) (p2bss_h atlas f Y) s0) /\
         (!z a. mfd_differential (open_set_atlas (:real^3)) atlas (\z. Fc(lvs_proj z)) z a =
                lvs_jac top atlas (topspace top) (p2bss_h atlas f Y) s0 (Fc(lvs_proj z))
                  (mfd_differential (open_set_atlas (:real^2))
                     (lvs_atlas top atlas (topspace top) (p2bss_h atlas f Y) s0) Fc (lvs_proj z)
                     (lvs_proj a)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  ABBREV_TAC `N = lvs_set (topspace top) (p2bss_h atlas f (Y:A->real^3)) s0` THEN
  ABBREV_TAC `atlasN = lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) (topspace top)
                                 (p2bss_h atlas f (Y:A->real^3)) s0` THEN
  SUBGOAL_THEN `lvs_regular (atlas:((A->bool)#(A->real^3))->bool) (topspace top)
                            (p2bss_h atlas f (Y:A->real^3)) s0` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BSS_H_REGULAR THEN EXISTS_TAC `g:A->real^3^3` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (subtopology top N)
                  (atlasN:((A->bool)#(A->real^2))->bool)` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["N"; "atlasN"] THEN MATCH_MP_TAC LVS_MANIFOLD THEN
    ASM_REWRITE_TAC[OPEN_IN_TOPSPACE];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_smooth_map (atlasN:((A->bool)#(A->real^2))->bool) (atlas:((A->bool)#(A->real^3))->bool) N (\x:A. x)`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["N"; "atlasN"] THEN MATCH_MP_TAC LVS_INCLUSION_SMOOTH THEN
    ASM_REWRITE_TAC[OPEN_IN_TOPSPACE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(N:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN REWRITE_TAC[LVS_SET_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `open_in (euclidean:(real^2)topology) (:real^2) /\
                open_in (euclidean:(real^3)topology) (:real^3)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM OPEN_IN; OPEN_UNIV]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [mfd_local_isometry]) THEN
  REWRITE_TAC[SUBTOPOLOGY_UNIV] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!w. (Fc:real^2->A) w IN N` ASSUME_TAC THENL
   [GEN_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN; TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (euclidean,top) (Fc:real^2->A)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONTINUOUS_MAP_IN_SUBTOPOLOGY]) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (subtopology (subtopology top N) N,top) (\x:A. x)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY; INTER_IDEMPOT] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN REWRITE_TAC[CONTINUOUS_MAP_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology top N) (N:A->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_smooth_map (open_set_atlas (:real^2)) (atlas:((A->bool)#(A->real^3))->bool) (:real^2) (Fc:real^2->A)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(Fc:real^2->A) = (\x:A. x) o Fc` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC(ISPECL [`euclidean:(real^2)topology`; `open_set_atlas (:real^2)`;
                         `subtopology top (N:A->bool)`; `atlasN:((A->bool)#(A->real^2))->bool`;
                         `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                         `(:real^2)`; `N:A->bool`; `Fc:real^2->A`; `\x:A. x`]
                        MFD_SMOOTH_MAP_COMPOSE) THEN
    ASM_REWRITE_TAC[GEOI_EUCLIDEAN_ATLAS; SUBTOPOLOGY_UNIV] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z:real^3. (Fc:real^2->A)(lvs_proj z)) = Fc o lvs_proj` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_smooth_map (open_set_atlas (:real^3)) (open_set_atlas (:real^2)) (:real^3)
                               lvs_proj` ASSUME_TAC THENL
   [REWRITE_TAC[MFD_SMOOTH_MAP_OPEN_SET_ATLAS; IN_UNIV; INTER_UNIV] THEN
    REWRITE_TAC[SET_RULE `{x:real^3 | T} = UNIV`] THEN
    MATCH_MP_TAC LVS_PROJ_SMOOTH THEN REWRITE_TAC[OPEN_UNIV];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `euclidean:(real^2)topology` THEN
    ASM_REWRITE_TAC[LVS_PROJ_CONTINUOUS_MAP];
    MATCH_MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                         `euclidean:(real^2)topology`; `open_set_atlas (:real^2)`;
                         `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                         `(:real^3)`; `(:real^2)`; `lvs_proj`; `Fc:real^2->A`]
                        MFD_SMOOTH_MAP_COMPOSE) THEN
    ASM_REWRITE_TAC[GEOI_EUCLIDEAN_ATLAS; SUBTOPOLOGY_UNIV; LVS_PROJ_CONTINUOUS_MAP;
                    SUBSET_UNIV];
    REWRITE_TAC[P2BSS_PROJ_SHIFT3];
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `euclidean:(real^2)topology`; `open_set_atlas (:real^2)`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(:real^3)`; `(:real^2)`; `lvs_proj`; `Fc:real^2->A`; `z:real^3`]
                GEOI_DIFF_COMPOSE) THEN
  ASM_REWRITE_TAC[GEOI_EUCLIDEAN_ATLAS; SUBTOPOLOGY_UNIV; LVS_PROJ_CONTINUOUS_MAP; IN_UNIV] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_THM; P2BSS_PROJ_MDIFF] THEN
  MP_TAC(ISPECL [`euclidean:(real^2)topology`; `open_set_atlas (:real^2)`;
                 `subtopology top (N:A->bool)`; `atlasN:((A->bool)#(A->real^2))->bool`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(:real^2)`; `N:A->bool`; `Fc:real^2->A`; `\x:A. x`; `lvs_proj(z:real^3)`]
                GEOI_DIFF_COMPOSE) THEN
  ASM_REWRITE_TAC[GEOI_EUCLIDEAN_ATLAS; SUBTOPOLOGY_UNIV; IN_UNIV] THEN
  SUBGOAL_THEN `(\x:A. x) o (Fc:real^2->A) = Fc` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_THM] THEN
  EXPAND_TAC "atlasN" THEN REWRITE_TAC[P2BSS_INCL_MDIFF]);;

let P2BSS_E_GRAM = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f (Y:A->real^3) s0 k
    (Fc:real^2->A).
     p2b_shrinker (top,atlas) g f /\ p2b_parallel_on atlas g (topspace top) Y /\
     (!x. x IN topspace top ==> Y x dot (g x ** Y x) = &1) /\ &0 < k /\
     mfd_local_isometry (euclidean,open_set_atlas (:real^2)) p2bss_gs
       (subtopology top (lvs_set (topspace top) (p2bss_h atlas f Y) s0),
        lvs_atlas top atlas (topspace top) (p2bss_h atlas f Y) s0)
       (\x. k %% lvs_metric top atlas g (topspace top) (p2bss_h atlas f Y) s0 x) (:real^2) Fc
     ==> !z a.
           mfd_differential (open_set_atlas (:real^3)) atlas (\z. Fc(lvs_proj z)) z a dot
           (g(Fc(lvs_proj z)) **
            mfd_differential (open_set_atlas (:real^3)) atlas (\z. Fc(lvs_proj z)) z a) =
           inv k * (lvs_proj a dot (p2bss_gs (lvs_proj z) ** lvs_proj a)) /\
           mfd_differential (open_set_atlas (:real^3)) atlas (\z. Fc(lvs_proj z)) z a dot
           (g(Fc(lvs_proj z)) ** Y(Fc(lvs_proj z))) = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `Y:A->real^3`; `s0:real`; `k:real`; `Fc:real^2->A`]
                P2BSS_E_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  ABBREV_TAC `N = lvs_set (topspace top) (p2bss_h atlas f (Y:A->real^3)) s0` THEN
  ABBREV_TAC `atlasN = lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) (topspace top)
                                 (p2bss_h atlas f (Y:A->real^3)) s0` THEN
  ABBREV_TAC `gN = lvs_metric top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)
                              (topspace top) (p2bss_h atlas f (Y:A->real^3)) s0` THEN
  ABBREV_TAC `w = lvs_proj(z:real^3)` THEN ABBREV_TAC `v = lvs_proj(a:real^3)` THEN
  ABBREV_TAC `x = (Fc:real^2->A) w` THEN
  ABBREV_TAC `D = mfd_differential (open_set_atlas (:real^2))
                    (atlasN:((A->bool)#(A->real^2))->bool) (Fc:real^2->A) w` THEN
  SUBGOAL_THEN `lvs_regular (atlas:((A->bool)#(A->real^3))->bool) (topspace top)
                            (p2bss_h atlas f (Y:A->real^3)) s0` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BSS_H_REGULAR THEN EXISTS_TAC `g:A->real^3^3` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (subtopology top N)
                  (atlasN:((A->bool)#(A->real^2))->bool) /\
                riemannian_metric (atlasN:((A->bool)#(A->real^2))->bool) (gN:A->real^2^2)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["N"; "atlasN"; "gN"] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LVS_MANIFOLD; MATCH_MP_TAC LVS_RIEMANNIAN] THEN
    ASM_REWRITE_TAC[OPEN_IN_TOPSPACE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN N` ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `topspace top:A->bool`;
                 `p2bss_h atlas f (Y:A->real^3)`; `s0:real`; `x:A`] LVS_JAC_FACTS) THEN
  ASM_REWRITE_TAC[OPEN_IN_TOPSPACE] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC P2BSS_JAC_TANGENT THEN ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`euclidean:(real^2)topology`; `open_set_atlas (:real^2)`; `p2bss_gs`;
                 `subtopology top (N:A->bool)`; `atlasN:((A->bool)#(A->real^2))->bool`;
                 `\x:A. k %% (gN:A->real^2^2) x`; `(:real^2)`; `Fc:real^2->A`; `w:real^2`]
                GEOH_LISOM_DIFF) THEN
  ASM_SIMP_TAC[P2BSS_GS_FACTS; RIEMANNIAN_METRIC_CMUL; IN_UNIV] THEN DISCH_TAC THEN
  SUBGOAL_THEN `linear(D:real^2->real^2)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC GEOI_DIFF_LINEAR THEN
    MAP_EVERY EXISTS_TAC [`euclidean:(real^2)topology`; `subtopology top (N:A->bool)`;
                          `(:real^2)`] THEN
    ASM_REWRITE_TAC[P2BSS_GS_FACTS; IN_UNIV] THEN
    ASM_MESON_TAC[mfd_local_isometry];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM MATRIX_WORKS] THEN
  REWRITE_TAC[P2BSS_CONG_DOT] THEN
  SUBGOAL_THEN `transp(matrix(lvs_jac top (atlas:((A->bool)#(A->real^3))->bool) (topspace top)
                                   (p2bss_h atlas f (Y:A->real^3)) s0 x)) **
                (g:A->real^3^3) x **
                matrix(lvs_jac top atlas (topspace top) (p2bss_h atlas f Y) s0 x) =
                (gN:A->real^2^2) x` SUBST1_TAC THENL
   [EXPAND_TAC "gN" THEN REWRITE_TAC[lvs_metric]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC; MATRIX_MUL_LMUL; MATRIX_MUL_RMUL] THEN
  REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL] THEN
  REWRITE_TAC[MATRIX_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_MUL_LID]);;

let P2BSS_PSI_LISOM = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f (Y:A->real^3) s0 k
    (Fc:real^2->A).
     hausdorff_space top /\ p2b_shrinker (top,atlas) g f /\ mfd_complete (top,atlas) g /\
     p2b_parallel_on atlas g (topspace top) Y /\
     (!x. x IN topspace top ==> Y x dot (g x ** Y x) = &1) /\ &0 < k /\
     mfd_local_isometry (euclidean,open_set_atlas (:real^2)) p2bss_gs
       (subtopology top (lvs_set (topspace top) (p2bss_h atlas f Y) s0),
        lvs_atlas top atlas (topspace top) (p2bss_h atlas f Y) s0)
       (\x. k %% lvs_metric top atlas g (topspace top) (p2bss_h atlas f Y) s0 x) (:real^2) Fc
     ==> mfd_local_isometry (euclidean,open_set_atlas (:real^3)) (p2bss_bc (inv k)) (top,atlas) g
           (:real^3) (\z. mfd_geo (top,atlas) g (Fc(lvs_proj z)) (Y(Fc(lvs_proj z))) (z$3))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `Y:A->real^3`; `s0:real`; `k:real`; `Fc:real^2->A`]
                P2BSS_E_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dE"))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `Y:A->real^3`; `s0:real`; `k:real`; `Fc:real^2->A`]
                P2BSS_E_GRAM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "egram") THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `Y:A->real^3`; `\z:real^3. (Fc:real^2->A)(lvs_proj z)`] P2BSS_PSI_FACTS) THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "d3") (LABEL_TAC "dh")))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `Y:A->real^3`; `\z:real^3. (Fc:real^2->A)(lvs_proj z)`] P2BSS_PSI_METRIC) THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "gram") THEN
  MATCH_MP_TAC GEOI_LISOM_FROM_DIFF THEN
  ASM_SIMP_TAC[GEOI_EUCLIDEAN_ATLAS; SUBTOPOLOGY_UNIV; IN_UNIV; P2BSS_BC_METRIC; REAL_LT_INV] THEN
  CONJ_TAC THENL [REWRITE_TAC[GSYM OPEN_IN; OPEN_UNIV]; ALL_TAC] THEN
  X_GEN_TAC `z:real^3` THEN
  ABBREV_TAC `M = mfd_differential (open_set_atlas (:real^3)) (atlas:((A->bool)#(A->real^3))->bool)
                    (\z. mfd_geo (top,atlas) (g:A->real^3^3) ((Fc:real^2->A)(lvs_proj z))
                                 ((Y:A->real^3)(Fc(lvs_proj z))) (z$3)) z` THEN
  ABBREV_TAC `G = (g:A->real^3^3)(mfd_geo (top,atlas) g ((Fc:real^2->A)(lvs_proj z))
                                   ((Y:A->real^3)(Fc(lvs_proj z))) (z$3))` THEN
  SUBGOAL_THEN `linear(M:real^3->real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN MATCH_MP_TAC GEOI_DIFF_LINEAR THEN
    MAP_EVERY EXISTS_TAC [`euclidean:(real^3)topology`; `top:A topology`; `(:real^3)`] THEN
    ASM_REWRITE_TAC[GEOI_EUCLIDEAN_ATLAS; SUBTOPOLOGY_UNIV; IN_UNIV] THEN
    REWRITE_TAC[GSYM OPEN_IN; OPEN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `transp(G:real^3^3) = G` ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`;
      `mfd_geo (top,atlas) (g:A->real^3^3) ((Fc:real^2->A)(lvs_proj z))
               ((Y:A->real^3)(Fc(lvs_proj z))) (z$3)`] P2BSS_G_AT) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `continuous_map (euclidean,top)
                   (\z. mfd_geo (top,atlas) (g:A->real^3^3) ((Fc:real^2->A)(lvs_proj z))
                                ((Y:A->real^3)(Fc(lvs_proj z))) (z$3))` THEN
    REWRITE_TAC[continuous_map; TOPSPACE_EUCLIDEAN; IN_UNIV] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(M:real^3->real^3) (basis 3) =
                (Y:A->real^3)(mfd_geo (top,atlas) (g:A->real^3^3) ((Fc:real^2->A)(lvs_proj z))
                                      (Y(Fc(lvs_proj z))) (z$3))` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN USE_THEN "d3" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC GEOI_QUAD_EQ THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[GSYM P2BSS_CONG_DOT] THEN
    MATCH_MP_TAC P2BKF_SYM_DOT THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN REWRITE_TAC[P2BSS_BC_DOT] THEN
    SUBGOAL_THEN `lvs_proj (v:real^3) dot lvs_proj (u:real^3) = lvs_proj u dot lvs_proj v`
    SUBST1_TAC THENL [MATCH_ACCEPT_TAC DOT_SYM; REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `u:real^3` THEN REWRITE_TAC[GSYM P2BSS_CONG_DOT] THEN
  ASM_SIMP_TAC[MATRIX_WORKS] THEN
  SUBGOAL_THEN `u = lvs_iota(lvs_proj u) + (u:real^3)$3 % basis 3` SUBST1_TAC THENL
   [REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_3; ARITH;
             LVS_IOTA_COMPONENT; LVS_PROJ_COMPONENT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `uh = lvs_iota(lvs_proj(u:real^3))` THEN
  SUBGOAL_THEN `(uh:real^3)$3 = &0 /\ lvs_proj uh = lvs_proj(u:real^3)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "uh" THEN REWRITE_TAC[LVS_IOTA_COMPONENT; LVS_PROJ_IOTA]; ALL_TAC] THEN
  USE_THEN "gram" (MP_TAC o SPECL [`z:real^3`; `uh:real^3`; `uh:real^3`]) THEN
  REWRITE_TAC[ASSUME `(uh:real^3)$3 = &0`] THEN
  USE_THEN "egram" (MP_TAC o SPECL [`z:real^3`; `uh:real^3`]) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(Y:A->real^3)(mfd_geo (top,atlas) (g:A->real^3^3) ((Fc:real^2->A)(lvs_proj z))
                         (Y(Fc(lvs_proj z))) (z$3)) dot (G ** (M:real^3->real^3) uh) = &0`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`G:real^3^3`;
                   `(Y:A->real^3)(mfd_geo (top,atlas) (g:A->real^3^3) ((Fc:real^2->A)(lvs_proj z))
                                         (Y(Fc(lvs_proj z))) (z$3))`;
                   `(M:real^3->real^3) uh`] P2BKF_SYM_DOT) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lvs_proj(basis 3:real^3) = vec 0` ASSUME_TAC THENL
   [REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; LVS_PROJ_COMPONENT; VEC_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL; MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL;
               DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL] THEN
  REWRITE_TAC[P2BSS_BC_DOT] THEN
  ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL; LVS_PROJ_LINEAR; DOT_LZERO; DOT_RZERO; VECTOR_MUL_RZERO;
               VECTOR_ADD_RID; BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
  REWRITE_TAC[p2bss_gs; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID; DOT_RMUL] THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Local isometries out of open subsets of real^N (open_set_atlas) do not    *)
(* depend on the ambient open set; the rotation qinv y = (-y3,y2,y1) is an   *)
(* isometry of G0 from Ze1 (off the closed e1 ray) onto Zn (off the closed   *)
(* north ray).                                                               *)
(* ========================================================================= *)

let P2BSS_LISOM_OPEN_SET = prove
 (`!U W (G:real^N->real^N^N) top' (atlas':((B->bool)#(B->real^N))->bool) g' (f:real^N->B).
     open U /\ W SUBSET U
     ==> (mfd_local_isometry (subtopology euclidean U,open_set_atlas U) G (top',atlas') g' W f <=>
          open W /\ continuous_map (subtopology euclidean W,top') f /\
          (!c'. c' IN atlas' ==> smooth_map_on {x | x IN W /\ f x IN FST c'} (SND c' o f)) /\
          (!c' y. c' IN atlas' /\ y IN W /\ f y IN FST c'
                  ==> G y = mpullback (SND c' o f) (metric_local atlas' c' g') y))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mfd_local_isometry; mfd_smooth_map; RFB_OPEN_SET_ATLAS_CASES] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[FST; SND; IMAGE_ID] THEN
  ASM_SIMP_TAC[OPEN_IN_OPEN_EQ; SUBTOPOLOGY_SUBTOPOLOGY] THEN
  SUBGOAL_THEN `(U:real^N->bool) INTER W = W` SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!c':(B->bool)#(B->real^N).
                  {x | x IN U INTER W /\ (f:real^N->B) x IN FST c'} = {x | x IN W /\ f x IN FST c'}`
  (fun th -> REWRITE_TAC[th]) THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `open(W:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC(TAUT `(a <=> a') /\ (b <=> b') ==> (a /\ b <=> a' /\ b')`) THEN CONJ_TAC THENL
   [AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN EQ_TAC THEN
    MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ] SMOOTH_MAP_ON_EQ) THEN
    SIMP_TAC[IN_ELIM_THM; o_THM] THEN X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN U` (fun th -> SIMP_TAC[th; MFDM_CHART_INV_ID]) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM; RIGHT_IMP_FORALL_THM; IMP_IMP; GSYM CONJ_ASSOC] THEN
  SUBGOAL_THEN
   `!c' y. y IN W
           ==> metric_local (open_set_atlas U) (U,(\x. x)) G y = (G:real^N->real^N^N) y /\
               mpullback (SND (c':(B->bool)#(B->real^N)) o (f:real^N->B) o chart_inv (U,(\x. x)))
                         (metric_local atlas' c' g') y =
               mpullback (SND c' o f) (metric_local atlas' c' g') y`
  (fun th -> SIMP_TAC[th]) THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN U` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[RFB_OPEN_SET_METRIC_LOCAL] THEN
  REWRITE_TAC[mpullback; o_THM] THEN ASM_SIMP_TAC[MFDM_CHART_INV_ID] THEN
  SUBGOAL_THEN
   `frechet_derivative (SND (c':(B->bool)#(B->real^N)) o (f:real^N->B) o chart_inv (U,(\x. x)))
                       (at y) =
    frechet_derivative (SND c' o f) (at y)`
  (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_SIMP_TAC[o_THM; MFDM_CHART_INV_ID]);;

let p2bss_qinv = new_definition
 `p2bss_qinv (y:real^3) = vector[--(y$3); y$2; y$1]:real^3`;;

let p2bss_qrot = new_definition
 `p2bss_qrot (y:real^3) = vector[y$3; y$2; --(y$1)]:real^3`;;

let P2BSS_QINV_FACTS = prove
 (`(!y. p2bss_qrot(p2bss_qinv y) = y) /\ (!y. p2bss_qinv(p2bss_qrot y) = y) /\
   linear p2bss_qinv /\ linear p2bss_qrot /\
   (!y. norm(p2bss_qinv y) = norm y) /\ (!y. norm(p2bss_qrot y) = norm y) /\
   (!y. p2bss_qinv y$1 = --(y$3) /\ p2bss_qinv y$2 = y$2 /\ p2bss_qinv y$3 = y$1) /\
   transp(matrix p2bss_qinv) ** matrix p2bss_qinv = mat 1`,
  SUBGOAL_THEN `(!y. p2bss_qinv y$1 = --(y$3) /\ p2bss_qinv y$2 = y$2 /\ p2bss_qinv y$3 = y$1) /\
                (!y. p2bss_qrot y$1 = y$3 /\ p2bss_qrot y$2 = y$2 /\ p2bss_qrot y$3 = --(y$1))`
  STRIP_ASSUME_TAC THENL [REWRITE_TAC[p2bss_qinv; p2bss_qrot; VECTOR_3]; ALL_TAC] THEN
  SUBGOAL_THEN `(!y. norm(p2bss_qinv y) = norm y) /\ (!y. norm(p2bss_qrot y) = norm y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN GEN_TAC THEN REWRITE_TAC[vector_norm] THEN AP_TERM_TAC THEN
    ASM_REWRITE_TAC[DOT_3] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `linear p2bss_qinv /\ linear p2bss_qrot` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[linear; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT] THEN
    ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3] THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    GEN_TAC THEN REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3] THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    SUBGOAL_THEN `orthogonal_transformation p2bss_qinv` MP_TAC THENL
     [ASM_REWRITE_TAC[ORTHOGONAL_TRANSFORMATION]; ALL_TAC] THEN
    SIMP_TAC[ORTHOGONAL_TRANSFORMATION_MATRIX; orthogonal_matrix]]);;

let P2BSS_QINV_ZN = prove
 (`!y:real^3. ~(norm y = y$1) <=> ~(norm(p2bss_qinv y) = p2bss_qinv y$3)`,
  REWRITE_TAC[P2BSS_QINV_FACTS]);;

let P2BSS_ZE1_OPEN = prove
 (`open {y:real^3 | ~(norm y = y$1)} /\
   (!y:real^3. y IN {y | ~(norm y = y$3)} ==> ~(y = vec 0)) /\
   (!y:real^3. y IN {y | ~(norm y = y$1)} ==> ~(y = vec 0))`,
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `{y:real^3 | ~(norm y = y$1)} = {y | p2bss_qinv y IN {z | ~(norm z = z$3)}}`
    SUBST1_TAC THENL [REWRITE_TAC[IN_ELIM_THM; P2BSS_QINV_ZN]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
    REWRITE_TAC[P2BPC_OFF_RAY_OPEN] THEN GEN_TAC THEN
    MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN REWRITE_TAC[P2BSS_QINV_FACTS];
    GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM; CONTRAPOS_THM] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[NORM_0; VEC_COMPONENT];
    GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM; CONTRAPOS_THM] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[NORM_0; VEC_COMPONENT]]);;

let P2BSS_G0_RIEMANNIAN = prove
 (`!q S. &0 < q /\ open S /\ (!y:real^3. y IN S ==> ~(y = vec 0))
         ==> smooth_manifold_atlas (subtopology euclidean S) (open_set_atlas S) /\
             riemannian_metric (open_set_atlas S) (p2bss_g0 q)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[OPEN_SET_ATLAS] THEN
  MATCH_MP_TAC RFB_OPEN_SET_RIEMANNIAN THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `{y:real^3 | ~(y = vec 0)}` THEN
  ASM_SIMP_TAC[P2BSS_G0_METRIC] THEN ASM SET_TAC[]);;

let P2BSS_QINV_LISOM = prove
 (`!q. &0 < q
       ==> mfd_local_isometry
             (subtopology euclidean {y:real^3 | ~(norm y = y$1)},
              open_set_atlas {y:real^3 | ~(norm y = y$1)}) (p2bss_g0 q)
             (subtopology euclidean {y:real^3 | ~(norm y = y$3)},
              open_set_atlas {y:real^3 | ~(norm y = y$3)}) (p2bss_g0 q)
             {y:real^3 | ~(norm y = y$1)} p2bss_qinv`,
  GEN_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `Ze1 = {y:real^3 | ~(norm y = y$1)}` THEN
  ABBREV_TAC `Zn = {y:real^3 | ~(norm y = y$3)}` THEN
  MP_TAC P2BSS_ZE1_OPEN THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(Zn:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Zn" THEN REWRITE_TAC[P2BPC_OFF_RAY_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN Ze1 ==> p2bss_qinv y IN Zn` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Ze1"; "Zn"] THEN REWRITE_TAC[IN_ELIM_THM; P2BSS_QINV_ZN];
    ALL_TAC] THEN
  MATCH_MP_TAC GEOI_LISOM_FROM_DIFF THEN
  ASM_SIMP_TAC[P2BSS_G0_RIEMANNIAN; OPEN_SET_ATLAS] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN; SUBSET_UNIV];
    REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY; INTER_IDEMPOT; CONTINUOUS_MAP_EUCLIDEAN2] THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; P2BSS_QINV_FACTS] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[MFD_SMOOTH_MAP_OPEN_SET_ATLAS] THEN
    MATCH_MP_TAC P2BPC_SMOOTH_LINEAR THEN REWRITE_TAC[P2BSS_QINV_FACTS] THEN
    SUBGOAL_THEN `{x:real^3 | x IN Ze1 INTER Ze1 /\ p2bss_qinv x IN Zn} = Ze1` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; INTER_IDEMPOT] THEN ASM_MESON_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[CMPW_PM_DIFF; MFDD_OPEN_SET_CHART_AT; ETA_AX] THEN
  SUBGOAL_THEN `frechet_derivative p2bss_qinv (at y) = p2bss_qinv` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[P2BSS_QINV_FACTS];
    ALL_TAC] THEN
  REWRITE_TAC[p2bss_g0; P2BSS_QINV_FACTS; MATRIX_MUL_LMUL; MATRIX_MUL_RMUL; MATRIX_MUL_RID;
              MATRIX_MUL_LID]);;

(* ========================================================================= *)
(* The chart maps Psi_F o theta (off the north ray) and Psi_FN o theta o     *)
(* qinv (off the e1 ray) are local isometries from G0 to g; they agree where *)
(* both are defined (mu o sig = sig o qinv), so the glued map p2bss_p is a   *)
(* local isometry from (real^3 - 0, G0) to (M, g).                           *)
(* ========================================================================= *)

let p2bss_psi = new_definition
 `p2bss_psi (top:A topology,atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)
            (Y:A->real^3) (Fc:real^2->A) (z:real^3) =
    mfd_geo (top,atlas) g (Fc(lvs_proj z)) (Y(Fc(lvs_proj z))) (z$3)`;;

let p2bss_p = new_definition
 `p2bss_p (top:A topology,atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)
          (Y:A->real^3) (FS:real^2->A) (FN:real^2->A) (c:real) (y:real^3) =
    if norm y = y$3 then p2bss_psi (top,atlas) g Y FN (p2bss_theta c (p2bss_qinv y))
    else p2bss_psi (top,atlas) g Y FS (p2bss_theta c y)`;;

let P2BSS_THETA_COMPONENTS = prove
 (`!c y:real^3. lvs_proj(p2bss_theta c y) = vector[y$1 / (norm y - y$3); y$2 / (norm y - y$3)] /\
                p2bss_theta c y$3 = c * log(norm y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bss_theta; lvs_proj; VECTOR_3] THEN
  SIMP_TAC[p2bpc_ann_n_inv; LAMBDA_BETA; DIMINDEX_3; ARITH]);;

let P2BSS_MOB_SIG = prove
 (`!y:real^3.
     ~(norm y = y$3) /\ ~(norm y = y$1)
     ==> ~(vector[y$1 / (norm y - y$3); y$2 / (norm y - y$3)]:real^2 = Cx(&1)) /\
         p2bss_mob (vector[y$1 / (norm y - y$3); y$2 / (norm y - y$3)]) =
         vector[--(y$3) / (norm y - y$1); y$2 / (norm y - y$1)]`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `norm(y:real^3) pow 2 = y$1 pow 2 + y$2 pow 2 + y$3 pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_POW_2; DOT_3] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(norm(y:real^3) - y$3 = &0) /\ ~(norm y - y$1 = &0)` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM complex; p2bss_mob] THEN
  SUBGOAL_THEN `~(complex((y:real^3)$1 / (norm y - y$3),y$2 / (norm y - y$3)) = Cx(&1))` ASSUME_TAC THENL
   [REWRITE_TAC[COMPLEX_EQ; RE; IM; RE_CX; IM_CX] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^3)$1 = norm y - y$3 /\ y$2 = &0` STRIP_ASSUME_TAC THENL
     [REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^3)$1 * y$3 = &0` MP_TAC THENL
     [UNDISCH_TAC `norm(y:real^3) pow 2 = y$1 pow 2 + y$2 pow 2 + y$3 pow 2` THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ENTIRE] THEN STRIP_TAC THEN
    UNDISCH_TAC `(y:real^3)$1 = norm y - y$3` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `z = complex((y:real^3)$1 / (norm y - y$3),y$2 / (norm y - y$3))` THEN
  ABBREV_TAC `w = complex(--((y:real^3)$3) / (norm y - y$1),y$2 / (norm y - y$1))` THEN
  SUBGOAL_THEN `w * (Cx(&1) - z) = Cx(&1) + z` MP_TAC THENL
   [MAP_EVERY EXPAND_TAC ["w"; "z"] THEN
    REWRITE_TAC[COMPLEX_EQ; complex_mul; RE; IM; RE_ADD; IM_ADD; RE_SUB; IM_SUB; RE_CX; IM_CX] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  UNDISCH_TAC `~(z = Cx(&1))` THEN CONV_TAC COMPLEX_FIELD);;

let P2BSS_GLUE = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) (Y:A->real^3) FS FN c y.
     (!z. ~(z = Cx(&1)) ==> FN(p2bss_mob z) = FS z) /\
     ~(norm y = y$3) /\ ~(norm y = y$1)
     ==> p2bss_psi (top,atlas) g Y FN (p2bss_theta c (p2bss_qinv y)) =
         p2bss_psi (top,atlas) g Y FS (p2bss_theta c y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[p2bss_psi; P2BSS_THETA_COMPONENTS; P2BSS_QINV_FACTS] THEN
  MP_TAC(SPEC `y:real^3` P2BSS_MOB_SIG) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  ASM_SIMP_TAC[]);;

let P2BSS_PSI_ETA = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) (Y:A->real^3) (Fc:real^2->A).
     p2bss_psi (top,atlas) g Y Fc =
     (\z. mfd_geo (top,atlas) g (Fc(lvs_proj z)) (Y(Fc(lvs_proj z))) (z$3))`,
  REWRITE_TAC[FUN_EQ_THM; p2bss_psi]);;

let P2BSS_PCHART_LISOM = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f (Y:A->real^3) s0 k
    (Fc:real^2->A).
     hausdorff_space top /\ p2b_shrinker (top,atlas) g f /\ mfd_complete (top,atlas) g /\
     p2b_parallel_on atlas g (topspace top) Y /\
     (!x. x IN topspace top ==> Y x dot (g x ** Y x) = &1) /\ &0 < k /\
     mfd_local_isometry (euclidean,open_set_atlas (:real^2)) p2bss_gs
       (subtopology top (lvs_set (topspace top) (p2bss_h atlas f Y) s0),
        lvs_atlas top atlas (topspace top) (p2bss_h atlas f Y) s0)
       (\x. k %% lvs_metric top atlas g (topspace top) (p2bss_h atlas f Y) s0 x) (:real^2) Fc
     ==> mfd_local_isometry
           (subtopology euclidean {y:real^3 | ~(norm y = y$3)},
            open_set_atlas {y:real^3 | ~(norm y = y$3)}) (p2bss_g0 (sqrt(inv k) pow 2))
           (top,atlas) g {y:real^3 | ~(norm y = y$3)}
           (p2bss_psi (top,atlas) g Y Fc o p2bss_theta (sqrt(inv k)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  SUBGOAL_THEN `&0 < sqrt(inv k) /\ sqrt(inv k) pow 2 = inv k` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; REAL_LT_INV; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  MP_TAC(SPEC `sqrt(inv k)` P2BSS_THETA_LISOM) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `Y:A->real^3`; `s0:real`; `k:real`; `Fc:real^2->A`]
                P2BSS_PSI_LISOM) THEN
  ASM_REWRITE_TAC[GSYM P2BSS_PSI_ETA] THEN DISCH_TAC THEN
  MATCH_MP_TAC P2BSS_LISOM_COMPOSE THEN
  MAP_EVERY EXISTS_TAC [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                        `p2bss_bc (inv k)`; `(:real^3)`] THEN
  ASM_REWRITE_TAC[IN_UNIV; GEOI_EUCLIDEAN_ATLAS] THEN
  ASM_SIMP_TAC[P2BSS_BC_METRIC; REAL_LT_INV] THEN
  MATCH_MP_TAC P2BSS_G0_RIEMANNIAN THEN
  REWRITE_TAC[P2BPC_OFF_RAY_OPEN; P2BSS_ZE1_OPEN] THEN
  ASM_SIMP_TAC[REAL_LT_INV]);;

let P2BSS_LISOM_OPEN_SET_MONO = prove
 (`!U V W (G:real^N->real^N^N) top' (atlas':((B->bool)#(B->real^N))->bool) g' (f:real^N->B).
     open U /\ open V /\ W SUBSET U /\ W SUBSET V
     ==> (mfd_local_isometry (subtopology euclidean U,open_set_atlas U) G (top',atlas') g' W f <=>
          mfd_local_isometry (subtopology euclidean V,open_set_atlas V) G (top',atlas') g' W f)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[P2BSS_LISOM_OPEN_SET]);;

let P2BSS_ZSETS = prove
 (`open {y:real^3 | ~(y = vec 0)} /\ open {y:real^3 | ~(norm y = y$3)} /\
   open {y:real^3 | ~(norm y = y$1)} /\
   {y:real^3 | ~(norm y = y$3)} SUBSET {y:real^3 | ~(y = vec 0)} /\
   {y:real^3 | ~(norm y = y$1)} SUBSET {y:real^3 | ~(y = vec 0)} /\
   (!y:real^3. ~(y = vec 0) ==> ~(norm y = y$3) \/ ~(norm y = y$1))`,
  REPEAT CONJ_TAC THENL
   [MP_TAC(SPEC `&1` P2BSS_G0_METRIC) THEN REWRITE_TAC[REAL_LT_01] THEN SIMP_TAC[];
    REWRITE_TAC[P2BPC_OFF_RAY_OPEN];
    REWRITE_TAC[P2BSS_ZE1_OPEN];
    MP_TAC P2BSS_ZE1_OPEN THEN SIMP_TAC[SUBSET; IN_ELIM_THM];
    MP_TAC P2BSS_ZE1_OPEN THEN SIMP_TAC[SUBSET; IN_ELIM_THM];
    ALL_TAC] THEN
  GEN_TAC THEN REWRITE_TAC[GSYM DE_MORGAN_THM; CONTRAPOS_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `norm(y:real^3) pow 2 + y$2 pow 2 = &0` MP_TAC THENL
   [REPEAT(POP_ASSUM MP_TAC) THEN MP_TAC(ISPEC `y:real^3` NORM_POW_2) THEN
    REWRITE_TAC[DOT_3] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  MP_TAC(SPEC `(y:real^3)$2` REAL_LE_POW_2) THEN MP_TAC(SPEC `norm(y:real^3)` REAL_LE_POW_2) THEN
  REWRITE_TAC[IMP_IMP] THEN STRIP_TAC THEN
  SUBGOAL_THEN `norm(y:real^3) pow 2 = &0` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; SIMP_TAC[REAL_POW_EQ_0; NORM_EQ_0; ARITH]]);;

let P2BSS_P_LISOM = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f (Y:A->real^3) s0 k FS FN.
     hausdorff_space top /\ p2b_shrinker (top,atlas) g f /\ mfd_complete (top,atlas) g /\
     p2b_parallel_on atlas g (topspace top) Y /\
     (!x. x IN topspace top ==> Y x dot (g x ** Y x) = &1) /\ &0 < k /\
     mfd_local_isometry (euclidean,open_set_atlas (:real^2)) p2bss_gs
       (subtopology top (lvs_set (topspace top) (p2bss_h atlas f Y) s0),
        lvs_atlas top atlas (topspace top) (p2bss_h atlas f Y) s0)
       (\x. k %% lvs_metric top atlas g (topspace top) (p2bss_h atlas f Y) s0 x) (:real^2) FS /\
     mfd_local_isometry (euclidean,open_set_atlas (:real^2)) p2bss_gs
       (subtopology top (lvs_set (topspace top) (p2bss_h atlas f Y) s0),
        lvs_atlas top atlas (topspace top) (p2bss_h atlas f Y) s0)
       (\x. k %% lvs_metric top atlas g (topspace top) (p2bss_h atlas f Y) s0 x) (:real^2) FN /\
     (!z. ~(z = Cx(&1)) ==> FN(p2bss_mob z) = FS z)
     ==> mfd_local_isometry
           (subtopology euclidean {y:real^3 | ~(y = vec 0)},
            open_set_atlas {y:real^3 | ~(y = vec 0)}) (p2bss_g0 (sqrt(inv k) pow 2))
           (top,atlas) g {y:real^3 | ~(y = vec 0)}
           (p2bss_p (top,atlas) g Y FS FN (sqrt(inv k)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  ABBREV_TAC `c = sqrt(inv k)` THEN
  SUBGOAL_THEN `&0 < c pow 2` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; REAL_LT_INV]; ALL_TAC] THEN
  ABBREV_TAC `Z = {y:real^3 | ~(y = vec 0)}` THEN
  ABBREV_TAC `Zn = {y:real^3 | ~(norm y = y$3)}` THEN
  ABBREV_TAC `Ze1 = {y:real^3 | ~(norm y = y$1)}` THEN
  MP_TAC P2BSS_ZSETS THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y:real^3. y IN Z ==> y IN Zn \/ y IN Ze1` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Z"; "Zn"; "Ze1"] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN Z ==> ~(y = vec 0)` ASSUME_TAC THENL
   [EXPAND_TAC "Z" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!Fc. mfd_local_isometry (euclidean,open_set_atlas (:real^2)) p2bss_gs
           (subtopology top (lvs_set (topspace top) (p2bss_h atlas f (Y:A->real^3)) s0),
            lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) (topspace top) (p2bss_h atlas f Y) s0)
           (\x. k %% lvs_metric top atlas (g:A->real^3^3) (topspace top) (p2bss_h atlas f Y) s0 x)
           (:real^2) Fc
         ==> mfd_local_isometry (subtopology euclidean Zn,open_set_atlas Zn) (p2bss_g0 (c pow 2))
               (top,atlas) g Zn (p2bss_psi (top,atlas) g Y Fc o p2bss_theta c)`
  (LABEL_TAC "chart") THENL
   [GEN_TAC THEN DISCH_TAC THEN MAP_EVERY EXPAND_TAC ["Zn"; "c"] THEN
    MATCH_MP_TAC P2BSS_PCHART_LISOM THEN
    MAP_EVERY EXISTS_TAC [`f:A->real`; `s0:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_local_isometry (subtopology euclidean Ze1,open_set_atlas Ze1) (p2bss_g0 (c pow 2))
      (top,atlas) (g:A->real^3^3) Ze1
      ((p2bss_psi (top,atlas) g (Y:A->real^3) FN o p2bss_theta c) o p2bss_qinv)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BSS_LISOM_COMPOSE THEN
    MAP_EVERY EXISTS_TAC [`subtopology euclidean (Zn:real^3->bool)`; `open_set_atlas (Zn:real^3->bool)`;
                          `p2bss_g0 (c pow 2)`; `Zn:real^3->bool`] THEN
    ASM_SIMP_TAC[] THEN
    MP_TAC(SPEC `c pow 2` P2BSS_QINV_LISOM) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `!S. open S /\ S SUBSET (Z:real^3->bool)
                      ==> smooth_manifold_atlas (subtopology euclidean S) (open_set_atlas S) /\
                          riemannian_metric (open_set_atlas S) (p2bss_g0 (c pow 2))`
    ASSUME_TAC THENL
     [GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC P2BSS_G0_RIEMANNIAN THEN ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["Ze1"; "Zn"] THEN REWRITE_TAC[IN_ELIM_THM; P2BSS_QINV_ZN];
    ALL_TAC] THEN
  MATCH_MP_TAC GEOH_LISOM_LOCAL THEN ASM_SIMP_TAC[OPEN_SET_ATLAS] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[OPEN_IN_OPEN_EQ; SUBSET_REFL]; ALL_TAC] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(y:real^3) IN Zn` THENL
   [MAP_EVERY EXISTS_TAC [`Zn:real^3->bool`;
                          `p2bss_psi (top,atlas) (g:A->real^3^3) (Y:A->real^3) FS o p2bss_theta c`] THEN
    ASM_SIMP_TAC[OPEN_IN_OPEN_EQ] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`Zn:real^3->bool`; `Z:real^3->bool`; `Zn:real^3->bool`; `p2bss_g0 (c pow 2)`;
                     `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `p2bss_psi (top,atlas) (g:A->real^3^3) (Y:A->real^3) FS o p2bss_theta c`]
                    P2BSS_LISOM_OPEN_SET_MONO) THEN
      ASM_REWRITE_TAC[SUBSET_REFL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      USE_THEN "chart" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[p2bss_p; o_THM] THEN X_GEN_TAC `w:real^3` THEN
      EXPAND_TAC "Zn" THEN SIMP_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN Ze1` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`Ze1:real^3->bool`;
                        `(p2bss_psi (top,atlas) (g:A->real^3^3) (Y:A->real^3) FN o p2bss_theta c) o
                         p2bss_qinv`] THEN
  ASM_SIMP_TAC[OPEN_IN_OPEN_EQ] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`Ze1:real^3->bool`; `Z:real^3->bool`; `Ze1:real^3->bool`; `p2bss_g0 (c pow 2)`;
                   `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `(p2bss_psi (top,atlas) (g:A->real^3^3) (Y:A->real^3) FN o p2bss_theta c) o
                    p2bss_qinv`] P2BSS_LISOM_OPEN_SET_MONO) THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p2bss_p; o_THM] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2BSS_GLUE THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(w:real^3) IN Ze1` THEN EXPAND_TAC "Ze1" THEN SIMP_TAC[IN_ELIM_THM]);;

(* ========================================================================= *)
(* Consequences for the glued model map p: the pullback clause (rfs_pullback *)
(* = G0 = lam cylinder_flow(0), lam = c^2/2), h along p (h(p y) = s0 + c     *)
(* log|y|), and p maps real^3 - 0 onto M.                                    *)
(* ========================================================================= *)

let P2BSS_LISOM_RFS = prove
 (`!U (G:real^N->real^N^N) top (atlas:((A->bool)#(A->real^N))->bool) g W (e:real^N->A) y.
     open U /\ W SUBSET U /\ smooth_manifold_atlas top atlas /\
     mfd_local_isometry (subtopology euclidean U,open_set_atlas U) G (top,atlas) g W e /\
     y IN W
     ==> rfs_pullback atlas e g y = G y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `mfd_local_isometry (subtopology euclidean U,open_set_atlas U) (G:real^N->real^N^N)
                 (top,atlas) (g:A->real^N^N) W (e:real^N->A)` THEN
  ASM_SIMP_TAC[P2BSS_LISOM_OPEN_SET] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(e:real^N->A) y IN topspace top` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `(e:real^N->A) y`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[rfs_pullback] THEN CONV_TAC SYM_CONV THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let P2BSS_G0_CYL = prove
 (`!c y. p2bss_g0 (c pow 2) y = (c pow 2 / &2) %% cylinder_flow (&0) y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bss_g0; cylinder_flow] THEN
  REWRITE_TAC[REAL_SUB_RZERO; real_div; REAL_MUL_LZERO; MATRIX_CMUL_LZERO; MATRIX_ADD_RID;
              MATRIX_CMUL_LID; MATRIX_CMUL_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC REAL_FIELD);;

let P2BSS_PSI_PHI = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) (Y:A->real^3) Fc z.
     p2bss_psi (top,atlas) g Y Fc z = p2bkf_phi (top,atlas) g Y (z$3) (Fc(lvs_proj z))`,
  REWRITE_TAC[p2bss_psi; p2bkf_phi]);;

let P2BSS_H_PSI = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f (Y:A->real^3) s0 Fc z.
     hausdorff_space top /\ p2b_shrinker (top,atlas) g f /\ mfd_complete (top,atlas) g /\
     p2b_parallel_on atlas g (topspace top) Y /\
     (!x. x IN topspace top ==> Y x dot (g x ** Y x) = &1) /\
     (!w. Fc w IN lvs_set (topspace top) (p2bss_h atlas f Y) s0)
     ==> p2bss_psi (top,atlas) g Y Fc z IN topspace top /\
         p2bss_h atlas f Y (p2bss_psi (top,atlas) g Y Fc z) = s0 + z$3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `lvs_proj(z:real^3)`) THEN
  REWRITE_TAC[lvs_set; IN_ELIM_THM] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[P2BSS_PSI_PHI] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `Y:A->real^3`; `(z:real^3)$3`; `(Fc:real^2->A)(lvs_proj z)`]
                  P2BKF_PHI_INVERSE) THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[p2bss_psi] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `f:A->real`; `Y:A->real^3`; `(Fc:real^2->A)(lvs_proj z)`; `(z:real^3)$3`]
                  P2BSS_H_ORBIT) THEN
    ASM_SIMP_TAC[]]);;

let P2BSS_H_P = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f (Y:A->real^3) s0 FS FN c y.
     hausdorff_space top /\ p2b_shrinker (top,atlas) g f /\ mfd_complete (top,atlas) g /\
     p2b_parallel_on atlas g (topspace top) Y /\
     (!x. x IN topspace top ==> Y x dot (g x ** Y x) = &1) /\
     (!w. FS w IN lvs_set (topspace top) (p2bss_h atlas f Y) s0) /\
     (!w. FN w IN lvs_set (topspace top) (p2bss_h atlas f Y) s0)
     ==> p2bss_p (top,atlas) g Y FS FN c y IN topspace top /\
         p2bss_h atlas f Y (p2bss_p (top,atlas) g Y FS FN c y) = s0 + c * log(norm y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[p2bss_p] THEN
  COND_CASES_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `f:A->real`; `Y:A->real^3`; `s0:real`; `FN:real^2->A`;
                   `p2bss_theta c (p2bss_qinv y)`] P2BSS_H_PSI);
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `f:A->real`; `Y:A->real^3`; `s0:real`; `FS:real^2->A`;
                   `p2bss_theta c y`] P2BSS_H_PSI)] THEN
  ASM_REWRITE_TAC[P2BSS_THETA_COMPONENTS; P2BSS_QINV_FACTS]);;

let P2BSS_PROJ3 = prove
 (`!w:real^2 t. lvs_proj(vector[w$1; w$2; t]:real^3) = w /\ (vector[w$1; w$2; t]:real^3)$3 = t`,
  REWRITE_TAC[lvs_proj; VECTOR_3; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2]);;

let P2BSS_P_ONTO = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f (Y:A->real^3) s0 FS FN c.
     hausdorff_space top /\ p2b_shrinker (top,atlas) g f /\ mfd_complete (top,atlas) g /\
     p2b_parallel_on atlas g (topspace top) Y /\
     (!x. x IN topspace top ==> Y x dot (g x ** Y x) = &1) /\ ~(c = &0) /\
     (!w. FS w IN lvs_set (topspace top) (p2bss_h atlas f Y) s0) /\
     (!w. FN w IN lvs_set (topspace top) (p2bss_h atlas f Y) s0) /\
     IMAGE FS (:real^2) UNION IMAGE FN (:real^2) = lvs_set (topspace top) (p2bss_h atlas f Y) s0 /\
     (!z. ~(z = Cx(&1)) ==> FN(p2bss_mob z) = FS z)
     ==> IMAGE (p2bss_p (top,atlas) g Y FS FN c) {y:real^3 | ~(y = vec 0)} = topspace top`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `f:A->real`; `Y:A->real^3`; `s0:real`; `FS:real^2->A`; `FN:real^2->A`;
                   `c:real`; `x:real^3`] P2BSS_H_P) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `Y:A->real^3`; `s0:real`; `x:A`] P2BSS_PROJ_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `x0 = p2bss_proj (top,atlas) (g:A->real^3^3) f (Y:A->real^3) s0 x` THEN
  ABBREV_TAC `t = p2bss_h atlas f (Y:A->real^3) x - s0` THEN
  UNDISCH_TAC `(x0:A) IN lvs_set (topspace top) (p2bss_h atlas f (Y:A->real^3)) s0` THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
  REWRITE_TAC[IN_UNION; IN_IMAGE; IN_UNIV] THEN
  DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `w:real^2` (ASSUME_TAC o SYM))) THENL
   [EXISTS_TAC `p2bss_xi c (vector[(w:real^2)$1; w$2; t])` THEN CONJ_TAC THENL
     [REWRITE_TAC[p2bss_p] THEN ASM_SIMP_TAC[P2BSS_XI_ZN; P2BSS_THETA_XI] THEN
      REWRITE_TAC[P2BSS_PSI_PHI; P2BSS_PROJ3] THEN ASM_REWRITE_TAC[];
      MP_TAC(SPECL [`c:real`; `vector[(w:real^2)$1; w$2; t]:real^3`] P2BSS_XI_ZN) THEN
      ASM_REWRITE_TAC[CONTRAPOS_THM] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[NORM_0; VEC_COMPONENT]];
    ALL_TAC] THEN
  EXISTS_TAC `p2bss_qrot (p2bss_xi c (vector[(w:real^2)$1; w$2; t]))` THEN
  SUBGOAL_THEN `~(norm(p2bss_xi c (vector[(w:real^2)$1; w$2; t])) =
                  p2bss_xi c (vector[w$1; w$2; t])$3)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[P2BSS_XI_ZN]; ALL_TAC] THEN
  ABBREV_TAC `u = p2bss_xi c (vector[(w:real^2)$1; w$2; t])` THEN
  SUBGOAL_THEN `p2bss_qinv(p2bss_qrot u) = u /\ norm(p2bss_qrot u) = norm u /\
                ~(norm(p2bss_qrot u) = p2bss_qrot u$1)` STRIP_ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[P2BSS_QINV_ZN] THEN
    REWRITE_TAC[CONJUNCT1(CONJUNCT2 P2BSS_QINV_FACTS)] THEN
    ASM_REWRITE_TAC[P2BSS_QINV_FACTS];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    UNDISCH_TAC `~(norm(p2bss_qrot u) = p2bss_qrot u$1)` THEN
    REWRITE_TAC[CONTRAPOS_THM] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[NORM_0; VEC_COMPONENT]] THEN
  SUBGOAL_THEN `p2bss_psi (top,atlas) (g:A->real^3^3) (Y:A->real^3) FN
                  (p2bss_theta c (p2bss_qinv (p2bss_qrot u))) = x` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBST1_TAC(SYM(ASSUME `p2bss_xi c (vector[(w:real^2)$1; w$2; t]) = u`)) THEN
    ASM_SIMP_TAC[P2BSS_THETA_XI] THEN
    REWRITE_TAC[P2BSS_PSI_PHI; P2BSS_PROJ3] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p2bss_p] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC P2BSS_GLUE THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The Y clause.  d theta_y (y / c) = e3 (theta inverts Xi and d Xi(e3) = Xi *)
(* / c), d Psi(e3) = Y, hence dp_y(y / c) = Y(p y).                          *)
(* ========================================================================= *)

let P2BSS_DTHETA_RADIAL = prove
 (`!c y. &0 < c /\ ~(norm y = y$3)
         ==> frechet_derivative (p2bss_theta c) (at y) (inv c % y) = basis 3`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(c = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `D = frechet_derivative (p2bss_theta c) (at (y:real^3))` THEN
  ABBREV_TAC `X = frechet_derivative (p2bss_xi c) (at (p2bss_theta c y))` THEN
  SUBGOAL_THEN `linear(D:real^3->real^3) /\ linear(X:real^3->real^3)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["D"; "X"] THEN CONJ_TAC THEN
    MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN REWRITE_TAC[differentiable] THEN
    ASM_MESON_TAC[P2BSS_THETA_HAS_DERIV; P2BSS_XI_HAS_DERIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `(D:real^3->real^3) o X = I` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`X:real^3->real^3`; `D:real^3->real^3`] LINEAR_INVERSE_LEFT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MAP_EVERY EXPAND_TAC ["D"; "X"] THEN ASM_SIMP_TAC[P2BSS_XI_THETA_DERIV; I_DEF];
    ALL_TAC] THEN
  SUBGOAL_THEN `(X:real^3->real^3) (basis 3) = inv c % y` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN SIMP_TAC[P2BSS_XI_FDERIV; ASSUME `~(c = &0)`] THEN
    SUBGOAL_THEN `lvs_proj(basis 3:real^3) = vec 0` SUBST1_TAC THENL
     [REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; LVS_PROJ_COMPONENT; VEC_COMPONENT] THEN
      SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH];
      ALL_TAC] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
    REWRITE_TAC[DOT_RZERO; REAL_MUL_RZERO; real_div; REAL_MUL_LZERO; VECTOR_MUL_LZERO] THEN
    SUBGOAL_THEN `lvs_iota(vec 0) = vec 0` SUBST1_TAC THENL
     [REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; LVS_IOTA_COMPONENT; VEC_COMPONENT]; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID; VECTOR_MUL_RZERO] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM(MATCH_MP P2BSS_XI_THETA
      (CONJ (ASSUME `~(c = &0)`) (ASSUME `~(norm(y:real^3) = y$3)`)))] THEN
    REWRITE_TAC[p2bss_xi; VECTOR_MUL_ASSOC; REAL_MUL_RID] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[real_div; REAL_MUL_RID; REAL_MUL_AC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o C AP_THM `basis 3:real^3`) THEN REWRITE_TAC[o_THM; I_THM]);;

let P2BSS_PSI_T_Y = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f (Y:A->real^3) s0 k
    (Fc:real^2->A) Z' (Tc:real^3->real^3) y v.
     hausdorff_space top /\ p2b_shrinker (top,atlas) g f /\ mfd_complete (top,atlas) g /\
     p2b_parallel_on atlas g (topspace top) Y /\
     (!x. x IN topspace top ==> Y x dot (g x ** Y x) = &1) /\ &0 < k /\
     mfd_local_isometry (euclidean,open_set_atlas (:real^2)) p2bss_gs
       (subtopology top (lvs_set (topspace top) (p2bss_h atlas f Y) s0),
        lvs_atlas top atlas (topspace top) (p2bss_h atlas f Y) s0)
       (\x. k %% lvs_metric top atlas g (topspace top) (p2bss_h atlas f Y) s0 x) (:real^2) Fc /\
     open Z' /\ y IN Z' /\
     continuous_map (subtopology euclidean Z',euclidean) Tc /\
     mfd_smooth_map (open_set_atlas Z') (open_set_atlas (:real^3)) Z' Tc /\
     frechet_derivative Tc (at y) v = basis 3
     ==> mfd_differential (open_set_atlas Z') atlas (p2bss_psi (top,atlas) g Y Fc o Tc) y v =
         Y(p2bss_psi (top,atlas) g Y Fc (Tc y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `Y:A->real^3`; `s0:real`; `k:real`; `Fc:real^2->A`]
                P2BSS_PSI_LISOM) THEN
  ASM_REWRITE_TAC[GSYM P2BSS_PSI_ETA; mfd_local_isometry; SUBTOPOLOGY_UNIV] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `Y:A->real^3`; `s0:real`; `k:real`; `Fc:real^2->A`]
                P2BSS_E_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `Y:A->real^3`; `\z:real^3. (Fc:real^2->A)(lvs_proj z)`] P2BSS_PSI_FACTS) THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[GSYM P2BSS_PSI_ETA] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology euclidean (Z':real^3->bool)`; `open_set_atlas (Z':real^3->bool)`;
                 `euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `Z':real^3->bool`; `(:real^3)`; `Tc:real^3->real^3`;
                 `p2bss_psi (top,atlas) (g:A->real^3^3) (Y:A->real^3) Fc`; `y:real^3`]
                GEOI_DIFF_COMPOSE) THEN
  ASM_SIMP_TAC[OPEN_SET_ATLAS; GEOI_EUCLIDEAN_ATLAS; SUBTOPOLOGY_UNIV; IN_UNIV;
               SUBTOPOLOGY_SUBTOPOLOGY; INTER_IDEMPOT; OPEN_IN_OPEN_EQ; SUBSET_REFL] THEN
  DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[o_THM] THEN
  ASM_SIMP_TAC[CMPW_PM_DIFF; MFDD_OPEN_SET_CHART_AT; IN_UNIV; ETA_AX] THEN
  REWRITE_TAC[p2bss_psi]);;

let P2BSS_MDIFF_LOCAL = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) Z U (p:real^N->A) h y.
     open Z /\ open U /\ U SUBSET Z /\ y IN U /\ (!w. w IN U ==> p w = h w)
     ==> mfd_differential (open_set_atlas Z) atlas p y =
         mfd_differential (open_set_atlas U) atlas h y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN Z` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[CMPW_PM_DIFF] THEN
  SUBGOAL_THEN `(p:real^N->A) y = h y` SUBST1_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_SIMP_TAC[]);;

let P2BSS_THETA_QINV_DERIV = prove
 (`!c y. &0 < c /\ ~(norm y = y$1)
         ==> (p2bss_theta c o p2bss_qinv has_derivative
              frechet_derivative (p2bss_theta c) (at (p2bss_qinv y)) o p2bss_qinv) (at y) /\
             (frechet_derivative (p2bss_theta c) (at (p2bss_qinv y)) o p2bss_qinv)
               (inv c % y) = basis 3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(norm(p2bss_qinv y) = p2bss_qinv y$3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[P2BSS_QINV_ZN]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_SIMP_TAC[P2BSS_THETA_HAS_DERIV] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[P2BSS_QINV_FACTS];
    REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `p2bss_qinv(inv c % y) = inv c % p2bss_qinv y` SUBST1_TAC THENL
     [MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2 P2BSS_QINV_FACTS))) THEN SIMP_TAC[LINEAR_CMUL];
      ASM_SIMP_TAC[P2BSS_DTHETA_RADIAL]]]);;

let P2BSS_P_Y = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f (Y:A->real^3) s0 k FS FN.
     hausdorff_space top /\ p2b_shrinker (top,atlas) g f /\ mfd_complete (top,atlas) g /\
     p2b_parallel_on atlas g (topspace top) Y /\
     (!x. x IN topspace top ==> Y x dot (g x ** Y x) = &1) /\ &0 < k /\
     mfd_local_isometry (euclidean,open_set_atlas (:real^2)) p2bss_gs
       (subtopology top (lvs_set (topspace top) (p2bss_h atlas f Y) s0),
        lvs_atlas top atlas (topspace top) (p2bss_h atlas f Y) s0)
       (\x. k %% lvs_metric top atlas g (topspace top) (p2bss_h atlas f Y) s0 x) (:real^2) FS /\
     mfd_local_isometry (euclidean,open_set_atlas (:real^2)) p2bss_gs
       (subtopology top (lvs_set (topspace top) (p2bss_h atlas f Y) s0),
        lvs_atlas top atlas (topspace top) (p2bss_h atlas f Y) s0)
       (\x. k %% lvs_metric top atlas g (topspace top) (p2bss_h atlas f Y) s0 x) (:real^2) FN /\
     (!z. ~(z = Cx(&1)) ==> FN(p2bss_mob z) = FS z)
     ==> !y. ~(y = vec 0)
             ==> mfd_differential (open_set_atlas {y:real^3 | ~(y = vec 0)}) atlas
                   (p2bss_p (top,atlas) g Y FS FN (sqrt(inv k))) y (inv(sqrt(inv k)) % y) =
                 Y(p2bss_p (top,atlas) g Y FS FN (sqrt(inv k)) y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  ABBREV_TAC `c = sqrt(inv k)` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN ASM_SIMP_TAC[SQRT_POS_LT; REAL_LT_INV]; ALL_TAC] THEN
  MP_TAC P2BSS_ZSETS THEN STRIP_TAC THEN
  MP_TAC(SPEC `c:real` P2BSS_THETA_LISOM) THEN
  ASM_REWRITE_TAC[mfd_local_isometry; SUBTOPOLOGY_SUBTOPOLOGY; INTER_IDEMPOT] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < c pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  MP_TAC(SPEC `c pow 2` P2BSS_QINV_LISOM) THEN
  ASM_REWRITE_TAC[mfd_local_isometry; SUBTOPOLOGY_SUBTOPOLOGY; INTER_IDEMPOT] THEN STRIP_TAC THEN
  ASM_CASES_TAC `~(norm(y:real^3) = y$3)` THENL
   [MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^3))->bool`; `{y:real^3 | ~(y = vec 0)}`;
                   `{y:real^3 | ~(norm y = y$3)}`;
                   `p2bss_p (top,atlas) (g:A->real^3^3) (Y:A->real^3) FS FN c`;
                   `p2bss_psi (top,atlas) (g:A->real^3^3) (Y:A->real^3) FS o p2bss_theta c`;
                   `y:real^3`] P2BSS_MDIFF_LOCAL) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL
     [SIMP_TAC[p2bss_p; o_THM]; DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `(Y:A->real^3)(p2bss_psi (top,atlas) (g:A->real^3^3) Y FS (p2bss_theta c y))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2BSS_PSI_T_Y THEN
      MAP_EVERY EXISTS_TAC [`f:A->real`; `s0:real`; `k:real`] THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN EXPAND_TAC "c" THEN
      MATCH_MP_TAC P2BSS_DTHETA_RADIAL THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "c" THEN ASM_SIMP_TAC[SQRT_POS_LT; REAL_LT_INV];
      ASM_REWRITE_TAC[p2bss_p]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(norm(y:real^3) = y$1)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^3. w IN {y:real^3 | ~(norm y = y$1)}
                ==> p2bss_p (top,atlas) (g:A->real^3^3) (Y:A->real^3) FS FN c w =
                    (p2bss_psi (top,atlas) g Y FN o (p2bss_theta c o p2bss_qinv)) w`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; o_THM; p2bss_p] THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC P2BSS_GLUE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^3))->bool`; `{y:real^3 | ~(y = vec 0)}`;
                 `{y:real^3 | ~(norm y = y$1)}`;
                 `p2bss_p (top,atlas) (g:A->real^3^3) (Y:A->real^3) FS FN c`;
                 `p2bss_psi (top,atlas) (g:A->real^3^3) (Y:A->real^3) FN o
                  (p2bss_theta c o p2bss_qinv)`;
                 `y:real^3`] P2BSS_MDIFF_LOCAL) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`c:real`; `y:real^3`] P2BSS_THETA_QINV_DERIV) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(SUBST_ALL_TAC o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  SUBGOAL_THEN
   `continuous_map (subtopology euclidean {y:real^3 | ~(norm y = y$1)},euclidean)
                   (p2bss_theta c o p2bss_qinv) /\
    mfd_smooth_map (open_set_atlas {y:real^3 | ~(norm y = y$1)}) (open_set_atlas (:real^3))
                   {y:real^3 | ~(norm y = y$1)} (p2bss_theta c o p2bss_qinv)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `subtopology euclidean {y:real^3 | ~(norm y = y$3)}` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(ISPECL [`subtopology euclidean {y:real^3 | ~(norm y = y$1)}`;
                           `open_set_atlas {y:real^3 | ~(norm y = y$1)}`;
                           `subtopology euclidean {y:real^3 | ~(norm y = y$3)}`;
                           `open_set_atlas {y:real^3 | ~(norm y = y$3)}`;
                           `euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                           `{y:real^3 | ~(norm y = y$1)}`; `{y:real^3 | ~(norm y = y$3)}`;
                           `p2bss_qinv`; `p2bss_theta c`] MFD_SMOOTH_MAP_COMPOSE) THEN
      ASM_SIMP_TAC[OPEN_SET_ATLAS; GEOI_EUCLIDEAN_ATLAS; OPEN_IN_OPEN_EQ; SUBSET_REFL;
                   SUBTOPOLOGY_SUBTOPOLOGY; INTER_IDEMPOT] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; P2BSS_QINV_ZN]];
    ALL_TAC] THEN
  MP_TAC(REWRITE_RULE[o_THM]
   (ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
            `f:A->real`; `Y:A->real^3`; `s0:real`; `k:real`; `FN:real^2->A`;
            `{y:real^3 | ~(norm y = y$1)}`; `p2bss_theta c o p2bss_qinv`; `y:real^3`;
            `inv c % (y:real^3)`] P2BSS_PSI_T_Y)) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; o_THM] THEN EXPAND_TAC "c" THEN SIMP_TAC[]);;

(* ========================================================================= *)
(* Linear algebra for the fibres of p.  A rotation of real^3 has an axis; an *)
(* orthogonal map without fixed vectors reverses some vector; an involution  *)
(* without fixed vectors is -I.                                              *)
(* ========================================================================= *)

let P2BSS_ROT3_AXIS = prove
 (`!Qm:real^3^3. orthogonal_matrix Qm /\ det Qm = &1 ==> ?v. ~(v = vec 0) /\ Qm ** v = v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `det(Qm - mat 1:real^3^3) = &0` MP_TAC THENL
   [SUBGOAL_THEN `det(Qm - mat 1:real^3^3) = --det(Qm - mat 1)` MP_TAC THENL
     [ALL_TAC; REAL_ARITH_TAC] THEN
    SUBGOAL_THEN `Qm - mat 1:real^3^3 = Qm ** (mat 1 - transp Qm)`
     (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
     [REWRITE_TAC[MATRIX_SUB_LDISTRIB; MATRIX_MUL_RID] THEN
      UNDISCH_TAC `orthogonal_matrix(Qm:real^3^3)` THEN SIMP_TAC[orthogonal_matrix];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[DET_MUL; REAL_MUL_LID] THEN
    SUBGOAL_THEN `mat 1 - transp Qm:real^3^3 = transp(--(Qm - mat 1))`
     (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
     [REWRITE_TAC[MATRIX_NEG_SUB; TRANSP_MATRIX_SUB; TRANSP_MAT]; ALL_TAC] THEN
    REWRITE_TAC[DET_TRANSP; DET_NEG; DIMINDEX_3; REAL_POW_NEG; REAL_POW_ONE; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM HOMOGENEOUS_LINEAR_EQUATIONS_DET] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB; MATRIX_VECTOR_MUL_LID; VECTOR_SUB_EQ]);;

let P2BSS_ORTHO3_ANTI = prove
 (`!Qm:real^3^3. orthogonal_matrix Qm /\ (!v. Qm ** v = v ==> v = vec 0)
                ==> ?v. ~(v = vec 0) /\ Qm ** v = --v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `det(Qm:real^3^3) = -- &1` ASSUME_TAC THENL
   [FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP DET_ORTHOGONAL_MATRIX) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `Qm:real^3^3` P2BSS_ROT3_AXIS) THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `--Qm:real^3^3` P2BSS_ROT3_AXIS) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[DET_NEG; DIMINDEX_3; REAL_POW_NEG; REAL_POW_ONE; ARITH] THEN CONJ_TAC THENL
     [UNDISCH_TAC `orthogonal_matrix(Qm:real^3^3)` THEN
      REWRITE_TAC[orthogonal_matrix; TRANSP_MATRIX_NEG; MATRIX_MUL_LNEG; MATRIX_MUL_RNEG;
                  MATRIX_NEG_NEG];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LNEG] THEN VECTOR_ARITH_TAC);;

let P2BSS_INVOL_NEG = prove
 (`!Qm:real^3^3. Qm ** Qm = mat 1 /\ (!v. Qm ** v = v ==> v = vec 0) ==> Qm = --(mat 1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MATRIX_EQ] THEN X_GEN_TAC `w:real^3` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(Qm:real^3^3) ** (w:real^3) + w`) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_ASSOC] THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LID; MATRIX_VECTOR_MUL_LNEG] THEN
  ANTS_TAC THENL [VECTOR_ARITH_TAC; VECTOR_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Orthogonal maps as isometries of (real^3 - 0, G0) and the chain rule.     *)
(* ------------------------------------------------------------------------- *)

let P2BSS_ORTHO_MDIFF = prove
 (`!(Qm:real^3^3) y.
     orthogonal_matrix Qm /\ ~(y = vec 0)
     ==> ~(Qm ** y = vec 0) /\
         mfd_differential (open_set_atlas {y:real^3 | ~(y = vec 0)})
                          (open_set_atlas {y:real^3 | ~(y = vec 0)}) (\y. Qm ** y) y =
         (\h. Qm ** h)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((Qm:real^3^3) ** y = vec 0)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM NORM_EQ_0] THEN ASM_SIMP_TAC[ORTHOGONAL_MATRIX_NORM] THEN
    ASM_REWRITE_TAC[NORM_EQ_0];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(CONJUNCT1 P2BSS_ZSETS) THEN DISCH_TAC THEN
  ASM_SIMP_TAC[CMPW_PM_DIFF; IN_ELIM_THM; MFDD_OPEN_SET_CHART_AT] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR]);;

let P2BSS_ORTHO_LISOM = prove
 (`!q (Qm:real^3^3).
     &0 < q /\ orthogonal_matrix Qm
     ==> mfd_local_isometry
           (subtopology euclidean {y:real^3 | ~(y = vec 0)},open_set_atlas {y:real^3 | ~(y = vec 0)})
           (p2bss_g0 q)
           (subtopology euclidean {y:real^3 | ~(y = vec 0)},open_set_atlas {y:real^3 | ~(y = vec 0)})
           (p2bss_g0 q) {y:real^3 | ~(y = vec 0)} (\y. Qm ** y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC P2BSS_ZSETS THEN STRIP_TAC THEN
  MATCH_MP_TAC GEOI_LISOM_FROM_DIFF THEN
  SUBGOAL_THEN `!y:real^3. y IN {y:real^3 | ~(y = vec 0)} ==> ~(y = vec 0)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  ASM_SIMP_TAC[P2BSS_G0_RIEMANNIAN; OPEN_SET_ATLAS] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[OPEN_IN_OPEN_EQ; SUBSET_REFL];
    REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY; INTER_IDEMPOT; CONTINUOUS_MAP_EUCLIDEAN2] THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; MATRIX_VECTOR_MUL_LINEAR] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN
    DISCH_TAC THEN MP_TAC(SPECL [`Qm:real^3^3`; `x:real^3`] P2BSS_ORTHO_MDIFF) THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[MFD_SMOOTH_MAP_OPEN_SET_ATLAS] THEN
    MATCH_MP_TAC P2BPC_SMOOTH_LINEAR THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN
    SUBGOAL_THEN `{x:real^3 | x IN {y:real^3 | ~(y = vec 0)} INTER {y:real^3 | ~(y = vec 0)} /\
                               (Qm:real^3^3) ** x IN {y:real^3 | ~(y = vec 0)}} =
                  {y:real^3 | ~(y = vec 0)}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN X_GEN_TAC `x:real^3` THEN
      ASM_CASES_TAC `x:real^3 = vec 0` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`Qm:real^3^3`; `x:real^3`] P2BSS_ORTHO_MDIFF) THEN ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[P2BSS_ORTHO_MDIFF; MATRIX_OF_MATRIX_VECTOR_MUL] THEN
  ASM_SIMP_TAC[p2bss_g0; ORTHOGONAL_MATRIX_NORM; MATRIX_MUL_LMUL; MATRIX_MUL_RMUL;
               MATRIX_MUL_LID] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ORTHOGONAL_MATRIX]) THEN ASM_REWRITE_TAC[]);;

let P2BSS_P_ORTHO_DIFF = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) q (Qm:real^3^3) (p:real^3->A) y.
     smooth_manifold_atlas top atlas /\ &0 < q /\ orthogonal_matrix Qm /\
     mfd_local_isometry
       (subtopology euclidean {y:real^3 | ~(y = vec 0)},open_set_atlas {y:real^3 | ~(y = vec 0)})
       (p2bss_g0 q) (top,atlas) g {y:real^3 | ~(y = vec 0)} p /\
     ~(y = vec 0)
     ==> mfd_differential (open_set_atlas {y:real^3 | ~(y = vec 0)}) atlas (p o (\y. Qm ** y)) y =
         (\h. mfd_differential (open_set_atlas {y:real^3 | ~(y = vec 0)}) atlas p (Qm ** y)
                (Qm ** h))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`q:real`; `Qm:real^3^3`] P2BSS_ORTHO_LISOM) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[mfd_local_isometry]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[mfd_local_isometry] o
    check (fun th -> can (find_term ((=) `p:real^3->A`)) (concl th))) THEN
  MP_TAC(CONJUNCT1 P2BSS_ZSETS) THEN DISCH_TAC THEN
  MP_TAC(SPECL [`Qm:real^3^3`; `y:real^3`] P2BSS_ORTHO_MDIFF) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology euclidean {y:real^3 | ~(y = vec 0)}`;
                 `open_set_atlas {y:real^3 | ~(y = vec 0)}`;
                 `subtopology euclidean {y:real^3 | ~(y = vec 0)}`;
                 `open_set_atlas {y:real^3 | ~(y = vec 0)}`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `{y:real^3 | ~(y = vec 0)}`; `{y:real^3 | ~(y = vec 0)}`;
                 `\y:real^3. (Qm:real^3^3) ** y`; `p:real^3->A`; `y:real^3`]
                GEOI_DIFF_COMPOSE) THEN
  ASM_SIMP_TAC[OPEN_SET_ATLAS; IN_ELIM_THM] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM]);;

let P2BSS_FIX_ID = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) q (Qm:real^3^3) (p:real^3->A) v.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ &0 < q /\
     orthogonal_matrix Qm /\
     mfd_local_isometry
       (subtopology euclidean {y:real^3 | ~(y = vec 0)},open_set_atlas {y:real^3 | ~(y = vec 0)})
       (p2bss_g0 q) (top,atlas) g {y:real^3 | ~(y = vec 0)} p /\
     (!y. ~(y = vec 0) ==> p(Qm ** y) = p y) /\ ~(v = vec 0) /\ Qm ** v = v
     ==> Qm = mat 1`,
  REPEAT STRIP_TAC THEN
  MP_TAC P2BSS_ZSETS THEN STRIP_TAC THEN
  ABBREV_TAC `L = mfd_differential (open_set_atlas {y:real^3 | ~(y = vec 0)})
                    (atlas:((A->bool)#(A->real^3))->bool) (p:real^3->A) v` THEN
  SUBGOAL_THEN `linear(L:real^3->real^3) /\ ~(det(matrix L) = &0)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN CONJ_TAC THENL
     [MATCH_MP_TAC GEOI_DIFF_LINEAR THEN
      MAP_EVERY EXISTS_TAC [`subtopology euclidean {y:real^3 | ~(y = vec 0)}`; `top:A topology`;
                            `{y:real^3 | ~(y = vec 0)}`] THEN
      ASM_SIMP_TAC[OPEN_SET_ATLAS; IN_ELIM_THM] THEN ASM_MESON_TAC[mfd_local_isometry];
      MATCH_MP_TAC GEOH_LISOM_DET THEN
      MAP_EVERY EXISTS_TAC [`subtopology euclidean {y:real^3 | ~(y = vec 0)}`; `p2bss_g0 q`;
                            `top:A topology`; `g:A->real^3^3`; `{y:real^3 | ~(y = vec 0)}`] THEN
      ASM_SIMP_TAC[P2BSS_G0_RIEMANNIAN; OPEN_SET_ATLAS; IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!h:real^3. (L:real^3->real^3) ((Qm:real^3^3) ** h) = L h` ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `q:real`; `Qm:real^3^3`; `p:real^3->A`; `v:real^3`] P2BSS_P_ORTHO_DIFF) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^3))->bool`; `{y:real^3 | ~(y = vec 0)}`;
                   `{y:real^3 | ~(y = vec 0)}`; `(p:real^3->A) o (\y. (Qm:real^3^3) ** y)`;
                   `p:real^3->A`; `v:real^3`] P2BSS_MDIFF_LOCAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[SUBSET_REFL; IN_ELIM_THM; o_THM] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN DISCH_THEN(MP_TAC o C AP_THM `h:real^3`) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_EQ; MATRIX_VECTOR_MUL_LID] THEN X_GEN_TAC `h:real^3` THEN
  MP_TAC(ISPEC `matrix(L:real^3->real^3)` HOMOGENEOUS_LINEAR_EQUATIONS_DET) THEN
  ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `(Qm:real^3^3) ** (h:real^3) - h`) THEN
  ASM_SIMP_TAC[MATRIX_WORKS; LINEAR_SUB; VECTOR_SUB_REFL; VECTOR_SUB_EQ]);;

(* ------------------------------------------------------------------------- *)
(* The fibres of the model map.                                              *)
(* ------------------------------------------------------------------------- *)

let P2BSS_FIBRE_ORTHO = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) (Y:A->real^3) q c
    (p:real^3->A) y1 y2.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ &0 < q /\ ~(c = &0) /\
     mfd_local_isometry
       (subtopology euclidean {y:real^3 | ~(y = vec 0)},open_set_atlas {y:real^3 | ~(y = vec 0)})
       (p2bss_g0 q) (top,atlas) g {y:real^3 | ~(y = vec 0)} p /\
     (!y. ~(y = vec 0)
          ==> mfd_differential (open_set_atlas {y:real^3 | ~(y = vec 0)}) atlas p y (inv c % y) =
              Y(p y)) /\
     ~(y1 = vec 0) /\ ~(y2 = vec 0) /\ p y1 = p y2 /\ norm y1 = norm y2
     ==> ?Qm:real^3^3.
           orthogonal_matrix Qm /\ Qm ** y1 = y2 /\
           !h. mfd_differential (open_set_atlas {y:real^3 | ~(y = vec 0)}) atlas p y2 (Qm ** h) =
               mfd_differential (open_set_atlas {y:real^3 | ~(y = vec 0)}) atlas p y1 h`,
  REPEAT STRIP_TAC THEN
  MP_TAC P2BSS_ZSETS THEN STRIP_TAC THEN
  ABBREV_TAC `L1 = mfd_differential (open_set_atlas {y:real^3 | ~(y = vec 0)})
                     (atlas:((A->bool)#(A->real^3))->bool) (p:real^3->A) y1` THEN
  ABBREV_TAC `L2 = mfd_differential (open_set_atlas {y:real^3 | ~(y = vec 0)})
                     (atlas:((A->bool)#(A->real^3))->bool) (p:real^3->A) y2` THEN
  SUBGOAL_THEN
   `!y. ~(y = vec 0)
        ==> linear(mfd_differential (open_set_atlas {y:real^3 | ~(y = vec 0)})
                     (atlas:((A->bool)#(A->real^3))->bool) (p:real^3->A) y) /\
            invertible(matrix(mfd_differential (open_set_atlas {y:real^3 | ~(y = vec 0)})
                                atlas p y)) /\
            p2bss_g0 q y =
            transp(matrix(mfd_differential (open_set_atlas {y:real^3 | ~(y = vec 0)}) atlas p y)) **
            (g:A->real^3^3)(p y) **
            matrix(mfd_differential (open_set_atlas {y:real^3 | ~(y = vec 0)}) atlas p y)`
  (LABEL_TAC "Lf") THENL
   [GEN_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC GEOI_DIFF_LINEAR THEN
      MAP_EVERY EXISTS_TAC [`subtopology euclidean {y:real^3 | ~(y = vec 0)}`; `top:A topology`;
                            `{y:real^3 | ~(y = vec 0)}`] THEN
      ASM_SIMP_TAC[OPEN_SET_ATLAS; IN_ELIM_THM] THEN ASM_MESON_TAC[mfd_local_isometry];
      REWRITE_TAC[INVERTIBLE_DET_NZ] THEN MATCH_MP_TAC GEOH_LISOM_DET THEN
      MAP_EVERY EXISTS_TAC [`subtopology euclidean {y:real^3 | ~(y = vec 0)}`; `p2bss_g0 q`;
                            `top:A topology`; `g:A->real^3^3`; `{y:real^3 | ~(y = vec 0)}`] THEN
      ASM_SIMP_TAC[P2BSS_G0_RIEMANNIAN; OPEN_SET_ATLAS; IN_ELIM_THM];
      MATCH_MP_TAC(ISPECL [`subtopology euclidean {y:real^3 | ~(y = vec 0)}`;
                           `open_set_atlas {y:real^3 | ~(y = vec 0)}`; `p2bss_g0 q`;
                           `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                           `g:A->real^3^3`; `{y:real^3 | ~(y = vec 0)}`; `p:real^3->A`;
                           `y:real^3`] GEOH_LISOM_DIFF) THEN
      ASM_SIMP_TAC[P2BSS_G0_RIEMANNIAN; OPEN_SET_ATLAS; IN_ELIM_THM]];
    ALL_TAC] THEN
  REMOVE_THEN "Lf" (fun th ->
    MP_TAC(MP (SPEC `y1:real^3` th) (ASSUME `~(y1:real^3 = vec 0)`)) THEN
    MP_TAC(MP (SPEC `y2:real^3` th) (ASSUME `~(y2:real^3 = vec 0)`))) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC `E = matrix_inv(matrix(L2:real^3->real^3))` THEN
  SUBGOAL_THEN `matrix(L2:real^3->real^3) ** (E:real^3^3) = mat 1 /\ E ** matrix L2 = mat 1`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN SIMP_TAC[MATRIX_INV; ASSUME `invertible(matrix(L2:real^3->real^3))`];
    ALL_TAC] THEN
  ABBREV_TAC `s = q / norm(y1:real^3) pow 2` THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[NORM_POS_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2bss_g0 q y1 = s %% mat 1 /\ p2bss_g0 q y2 = s %% mat 1` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[p2bss_g0] THEN EXPAND_TAC "s" THEN
    REWRITE_TAC[ASSUME `norm(y1:real^3) = norm(y2:real^3)`];
    ALL_TAC] THEN
  ABBREV_TAC `G = (g:A->real^3^3)(p(y1:real^3))` THEN
  SUBGOAL_THEN `(g:A->real^3^3)(p(y2:real^3)) = G` ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN REWRITE_TAC[ASSUME `(p:real^3->A) y1 = p y2`]; ALL_TAC] THEN
  SUBGOAL_THEN `transp(E:real^3^3) ** (s %% mat 1) ** E = (G:real^3^3)` ASSUME_TAC THENL
   [UNDISCH_TAC `p2bss_g0 q y2 = transp(matrix(L2:real^3->real^3)) ** (g:A->real^3^3)((p:real^3->A) y2) **
                                 matrix L2` THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[MATRIX_MUL_ASSOC; GSYM MATRIX_TRANSP_MUL] THEN ASM_REWRITE_TAC[TRANSP_MAT] THEN
    REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN ASM_REWRITE_TAC[MATRIX_MUL_LID; MATRIX_MUL_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(G:real^3^3) = s %% (transp(E:real^3^3) ** E)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[MATRIX_MUL_LMUL; MATRIX_MUL_RMUL; MATRIX_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^3. matrix(L1:real^3->real^3) ** v = L1 v /\
                           matrix(L2:real^3->real^3) ** v = L2 v` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MATRIX_WORKS]; ALL_TAC] THEN
  EXISTS_TAC `(E:real^3^3) ** matrix(L1:real^3->real^3)` THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[ORTHOGONAL_MATRIX] THEN
    SUBGOAL_THEN `s %% (transp((E:real^3^3) ** matrix(L1:real^3->real^3)) ** (E ** matrix L1)) = s %% mat 1`
    MP_TAC THENL
     [UNDISCH_TAC `p2bss_g0 q y1 = transp(matrix(L1:real^3->real^3)) **
                                   (g:A->real^3^3)((p:real^3->A) y2) ** matrix L1` THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[MATRIX_TRANSP_MUL; MATRIX_MUL_LMUL; MATRIX_MUL_RMUL; MATRIX_MUL_ASSOC];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `(%%) (inv s):real^3^3->real^3^3`) THEN
    REWRITE_TAC[MATRIX_CMUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; MATRIX_CMUL_LID];
    SUBGOAL_THEN `matrix(L1:real^3->real^3) ** y1 = matrix(L2:real^3->real^3) ** y2` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `!y:real^3 L:real^3->real^3. linear L ==> L y = c % L(inv c % y)`
      ASSUME_TAC THENL
       [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LINEAR_CMUL; VECTOR_MUL_ASSOC; REAL_MUL_RINV;
                                          VECTOR_MUL_LID];
        ALL_TAC] THEN
      FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[MP (SPECL [`y1:real^3`; `L1:real^3->real^3`] th)
                                               (ASSUME `linear(L1:real^3->real^3)`)]) THEN
      FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[MP (SPECL [`y2:real^3`; `L2:real^3->real^3`] th)
                                               (ASSUME `linear(L2:real^3->real^3)`)]) THEN
      MAP_EVERY EXPAND_TAC ["L1"; "L2"] THEN
      FIRST_ASSUM((fun th -> REWRITE_TAC[MP (SPEC `y1:real^3` th) (ASSUME `~(y1:real^3 = vec 0)`);
                                         MP (SPEC `y2:real^3` th) (ASSUME `~(y2:real^3 = vec 0)`)]) o
        check (fun th -> can (find_term ((=) `inv c % y:real^3`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
    REWRITE_TAC[ASSUME `matrix(L1:real^3->real^3) ** y1 = matrix(L2:real^3->real^3) ** y2`] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
    REWRITE_TAC[ASSUME `(E:real^3^3) ** matrix(L2:real^3->real^3) = mat 1`;
                MATRIX_VECTOR_MUL_LID];
    GEN_TAC THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(CONJUNCT2(SPEC `((E:real^3^3) ** matrix(L1:real^3->real^3)) ** (h:real^3)` th))]) THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_MUL_ASSOC] THEN
    ASM_REWRITE_TAC[MATRIX_MUL_LID]]);;

let P2BSS_FIBRE = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) (Y:A->real^3) q c (p:real^3->A).
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     &0 < q /\ ~(c = &0) /\
     mfd_local_isometry
       (subtopology euclidean {y:real^3 | ~(y = vec 0)},open_set_atlas {y:real^3 | ~(y = vec 0)})
       (p2bss_g0 q) (top,atlas) g {y:real^3 | ~(y = vec 0)} p /\
     (!y. ~(y = vec 0)
          ==> mfd_differential (open_set_atlas {y:real^3 | ~(y = vec 0)}) atlas p y (inv c % y) =
              Y(p y)) /\
     (!y1 y2. ~(y1 = vec 0) /\ ~(y2 = vec 0) /\ p y1 = p y2 ==> norm y1 = norm y2)
     ==> !y1 y2. ~(y1 = vec 0) /\ ~(y2 = vec 0) /\ p y1 = p y2
                 ==> y2 = y1 \/ (!y. ~(y = vec 0) ==> p(--y) = p y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `norm(y1:real^3) = norm(y2:real^3)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `Y:A->real^3`; `q:real`; `c:real`; `p:real^3->A`; `y1:real^3`; `y2:real^3`]
                P2BSS_FIBRE_ORTHO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Qm:real^3^3` STRIP_ASSUME_TAC) THEN
  MP_TAC P2BSS_ZSETS THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (subtopology euclidean {y:real^3 | ~(y = vec 0)})
                          (open_set_atlas {y:real^3 | ~(y = vec 0)}) /\
    riemannian_metric (open_set_atlas {y:real^3 | ~(y = vec 0)}) (p2bss_g0 q) /\
    hausdorff_space (subtopology euclidean {y:real^3 | ~(y = vec 0)}) /\
    connected_in (subtopology euclidean {y:real^3 | ~(y = vec 0)}) {y:real^3 | ~(y = vec 0)}`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[P2BSS_G0_RIEMANNIAN; OPEN_SET_ATLAS; IN_ELIM_THM; HAUSDORFF_SPACE_SUBTOPOLOGY;
                 HAUSDORFF_SPACE_EUCLIDEAN; CONNECTED_IN_SUBTOPOLOGY; SUBSET_REFL;
                 CONNECTED_IN_EUCLIDEAN] THEN
    REWRITE_TAC[SET_RULE `{y:real^3 | ~(y = vec 0)} = (:real^3) DIFF {vec 0}`] THEN
    MATCH_MP_TAC CONNECTED_PUNCTURED_UNIVERSE THEN REWRITE_TAC[DIMINDEX_3] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. ~(y = vec 0) ==> (p:real^3->A)((Qm:real^3^3) ** y) = p y`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`subtopology euclidean {y:real^3 | ~(y = vec 0)}`;
                   `open_set_atlas {y:real^3 | ~(y = vec 0)}`; `p2bss_g0 q`;
                   `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `{y:real^3 | ~(y = vec 0)}`; `(p:real^3->A) o (\y. (Qm:real^3^3) ** y)`;
                   `p:real^3->A`; `y1:real^3`] MFD_LOCAL_ISOMETRY_RIGID) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; o_THM] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC P2BSS_LISOM_COMPOSE THEN
        MAP_EVERY EXISTS_TAC [`subtopology euclidean {y:real^3 | ~(y = vec 0)}`;
                              `open_set_atlas {y:real^3 | ~(y = vec 0)}`; `p2bss_g0 q`;
                              `{y:real^3 | ~(y = vec 0)}`] THEN
        ASM_SIMP_TAC[P2BSS_ORTHO_LISOM; IN_ELIM_THM] THEN
        REPEAT STRIP_TAC THEN ASM_MESON_TAC[P2BSS_ORTHO_MDIFF];
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                       `q:real`; `Qm:real^3^3`; `p:real^3->A`; `y1:real^3`] P2BSS_P_ORTHO_DIFF) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[ETA_AX]];
      REWRITE_TAC[o_THM]];
    ALL_TAC] THEN
  ASM_CASES_TAC `?v:real^3. ~(v = vec 0) /\ (Qm:real^3^3) ** v = v` THENL
   [DISJ1_TAC THEN FIRST_X_ASSUM(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `Qm:real^3^3 = mat 1` (fun th -> UNDISCH_TAC `(Qm:real^3^3) ** y1 = y2` THEN
      REWRITE_TAC[th; MATRIX_VECTOR_MUL_LID] THEN MESON_TAC[]) THEN
    MATCH_MP_TAC P2BSS_FIX_ID THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:A->real^3^3`; `q:real`; `p:real^3->A`; `v:real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISJ2_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM]) THEN DISCH_TAC THEN
  SUBGOAL_THEN `!v:real^3. (Qm:real^3^3) ** v = v ==> v = vec 0` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(SPEC `Qm:real^3^3` P2BSS_ORTHO3_ANTI) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(Qm:real^3^3) ** Qm = mat 1` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BSS_FIX_ID THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:A->real^3^3`; `q:real`; `p:real^3->A`; `v:real^3`] THEN
    ASM_SIMP_TAC[ORTHOGONAL_MATRIX_MUL; GSYM MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_RNEG;
                 VECTOR_NEG_NEG] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`Qm:real^3^3`; `y:real^3`] P2BSS_ORTHO_MDIFF) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `Qm:real^3^3` P2BSS_INVOL_NEG) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `--(y:real^3) = (Qm:real^3^3) ** y` SUBST1_TAC THENL
     [REWRITE_TAC[th; MATRIX_VECTOR_MUL_LNEG; MATRIX_VECTOR_MUL_LID]; ASM_SIMP_TAC[]]));;

(* ========================================================================= *)
(* Orientation.  A smooth map p from an open connected set S of real^N with  *)
(* nonsingular differential, invariant under y |-> -y (N odd), cannot land   *)
(* in an open set W with an orientation: the sign of det D(phi o p) for      *)
(* oriented charts phi is locally constant and chart independent, but flips  *)
(* under -I.  Generic in the point type and in N.                            *)
(* ========================================================================= *)

let P2BSS_OR_CHARTS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) O W x.
     smooth_manifold_atlas top atlas /\ x IN topspace top /\ x IN W
     ==> (FST(chart_at atlas x) INTER W,SND(chart_at atlas x)) IN
         restrict_atlas atlas W UNION O /\
         x IN FST(chart_at atlas x) INTER W`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[IN_INTER; IN_UNION] THEN
  DISJ1_TAC THEN REWRITE_TAC[IN_RESTRICT_ATLAS] THEN
  EXISTS_TAC `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) x)` THEN
  ASM_REWRITE_TAC[PAIR]);;

let P2BSS_OR_SET_OPEN = prove
 (`!top (O:((A->bool)#(A->real^N))->bool) W S (p:real^N->A) c.
     open_in top W /\ smooth_manifold_atlas (subtopology top W) O /\ c IN O /\
     open S /\ continuous_map (subtopology euclidean S,top) p
     ==> open {y | y IN S /\ p y IN FST c}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[OPEN_IN] THEN
  MATCH_MP_TAC MFDM_OPEN_IN_PREIMAGE THEN EXISTS_TAC `top:A topology` THEN
  ASM_REWRITE_TAC[GSYM OPEN_IN] THEN
  MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `W:A->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`subtopology top (W:A->bool)`; `O:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
                SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_SIMP_TAC[PAIR]);;

(* Local representation: near y, SND c o p = chart_trans r c o (SND a o p)   *)
(* with a the preferred chart at p y and r its restriction to W.            *)

let P2BSS_OR_LOCAL_REP = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) O W S (p:real^N->A) c y.
     smooth_manifold_atlas top atlas /\ open_in top W /\
     smooth_manifold_atlas (subtopology top W) (restrict_atlas atlas W UNION O) /\
     open S /\ continuous_map (subtopology euclidean S,top) p /\ IMAGE p S SUBSET W /\
     c IN O /\ y IN S /\ p y IN FST c
     ==> open {z | z IN S /\ p z IN FST(chart_at atlas (p y)) INTER FST c} /\
         y IN {z | z IN S /\ p z IN FST(chart_at atlas (p y)) INTER FST c} /\
         (!z. z IN {z | z IN S /\ p z IN FST(chart_at atlas (p y)) INTER FST c}
              ==> SND c (p z) =
                  chart_trans (FST(chart_at atlas (p y)) INTER W,SND(chart_at atlas (p y))) c
                              (SND(chart_at atlas (p y)) (p z)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(p:real^N->A) y IN topspace top /\ p y IN W` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
      REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN ASM SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `O:((A->bool)#(A->real^N))->bool`; `W:A->bool`; `(p:real^N->A) y`]
                P2BSS_OR_CHARTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `(p:real^N->A) y`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `a = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((p:real^N->A) y)` THEN
  SUBGOAL_THEN `(c:(A->bool)#(A->real^N)) IN restrict_atlas atlas W UNION O` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_UNION]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[OPEN_IN] THEN MATCH_MP_TAC MFDM_OPEN_IN_PREIMAGE THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[GSYM OPEN_IN] THEN
    MATCH_MP_TAC OPEN_IN_INTER THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST(a:(A->bool)#(A->real^N))`; `SND(a:(A->bool)#(A->real^N))`]
                    SMOOTH_MANIFOLD_ATLAS_CHART) THEN
      ASM_SIMP_TAC[PAIR];
      MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `W:A->bool` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`subtopology top (W:A->bool)`;
                     `restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) W UNION O`;
                     `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
                    SMOOTH_MANIFOLD_ATLAS_CHART) THEN
      ASM_SIMP_TAC[PAIR]];
    ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^N` THEN REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN STRIP_TAC THEN
  REWRITE_TAC[chart_trans] THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`subtopology top (W:A->bool)`;
                 `restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) W UNION O`;
                 `FST(a:(A->bool)#(A->real^N)) INTER W`; `SND(a:(A->bool)#(A->real^N))`]
                CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> CONV_TAC SYM_CONV THEN MATCH_MP_TAC(CONJUNCT1 th)) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN ASM SET_TAC[]);;

let P2BSS_OR_PREF_SMOOTH = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) S (p:real^N->A) a.
     open S /\ mfd_smooth_map (open_set_atlas S) atlas S p /\ a IN atlas
     ==> smooth_map_on {x | x IN S /\ p x IN FST a} (SND a o p)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`(S:real^N->bool,(\x:real^N. x))`; `a:(A->bool)#(A->real^N)`] o
    REWRITE_RULE[mfd_smooth_map]) THEN
  ASM_REWRITE_TAC[open_set_atlas; IN_SING; FST; SND; IMAGE_ID; INTER_IDEMPOT] THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ] SMOOTH_MAP_ON_EQ) THEN
  SIMP_TAC[IN_ELIM_THM; o_THM; MFDM_CHART_INV_ID]);;

let P2BSS_OR_SMOOTH = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) O W S (p:real^N->A) c.
     smooth_manifold_atlas top atlas /\ open_in top W /\
     smooth_manifold_atlas (subtopology top W) (restrict_atlas atlas W UNION O) /\
     open S /\ continuous_map (subtopology euclidean S,top) p /\ IMAGE p S SUBSET W /\
     mfd_smooth_map (open_set_atlas S) atlas S p /\ c IN O
     ==> smooth_map_on {y | y IN S /\ p y IN FST c} (SND c o p)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2BSS_OR_SET_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) W UNION O`;
                          `W:A->bool`] THEN
    ASM_REWRITE_TAC[IN_UNION];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `O:((A->bool)#(A->real^N))->bool`; `W:A->bool`; `S:real^N->bool`;
                 `p:real^N->A`; `c:(A->bool)#(A->real^N)`; `y:real^N`] P2BSS_OR_LOCAL_REP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `{z | z IN S /\ (p:real^N->A) z IN
                   FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (p y)) INTER
                   FST(c:(A->bool)#(A->real^N))}` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(p:real^N->A) y IN topspace top /\ p y IN W` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
      REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN ASM SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `O:((A->bool)#(A->real^N))->bool`; `W:A->bool`; `(p:real^N->A) y`]
                P2BSS_OR_CHARTS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `(p:real^N->A) y`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `a = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((p:real^N->A) y)` THEN
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `t = {z | z IN S /\ (p:real^N->A) z IN FST(a:(A->bool)#(A->real^N)) INTER
                       FST(c:(A->bool)#(A->real^N))}` THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `chart_trans (FST(a:(A->bool)#(A->real^N)) INTER W,SND a) c o (SND a o (p:real^N->A))` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `IMAGE (SND(a:(A->bool)#(A->real^N))) ((FST a INTER W) INTER FST(c:(A->bool)#(A->real^N)))` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(c:(A->bool)#(A->real^N)) IN restrict_atlas atlas W UNION O` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_UNION]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`subtopology top (W:A->bool)`;
                   `restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) W UNION O`;
                   `FST(a:(A->bool)#(A->real^N)) INTER W`; `SND(a:(A->bool)#(A->real^N))`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
                  CHART_OVERLAP_IMAGE_OPEN) THEN
    ASM_REWRITE_TAC[PAIR];
    EXPAND_TAC "t" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; o_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `{x | x IN S /\ (p:real^N->A) x IN FST(a:(A->bool)#(A->real^N))}` THEN
    CONJ_TAC THENL
     [EXPAND_TAC "t" THEN SET_TAC[];
      MATCH_MP_TAC P2BSS_OR_PREF_SMOOTH THEN
      EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[]];
    MP_TAC(ISPECL [`subtopology top (W:A->bool)`;
                   `restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) W UNION O`;
                   `FST(a:(A->bool)#(A->real^N)) INTER W`; `SND(a:(A->bool)#(A->real^N))`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
                  CHART_TRANS_SMOOTH) THEN
    ASM_REWRITE_TAC[PAIR]]);;

let P2BSS_OR_DERIV = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) O W S (p:real^N->A) c y.
     smooth_manifold_atlas top atlas /\ open_in top W /\
     smooth_manifold_atlas (subtopology top W) (restrict_atlas atlas W UNION O) /\
     open S /\ continuous_map (subtopology euclidean S,top) p /\ IMAGE p S SUBSET W /\
     mfd_smooth_map (open_set_atlas S) atlas S p /\ c IN O /\ y IN S /\ p y IN FST c
     ==> (SND c o p has_derivative
          (chart_jac (FST(chart_at atlas (p y)) INTER W,SND(chart_at atlas (p y))) c (p y) o
           mfd_differential (open_set_atlas S) atlas p y)) (at y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `O:((A->bool)#(A->real^N))->bool`; `W:A->bool`; `S:real^N->bool`;
                 `p:real^N->A`; `c:(A->bool)#(A->real^N)`; `y:real^N`] P2BSS_OR_LOCAL_REP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(p:real^N->A) y IN topspace top /\ p y IN W` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
      REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN ASM SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `O:((A->bool)#(A->real^N))->bool`; `W:A->bool`; `(p:real^N->A) y`]
                P2BSS_OR_CHARTS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `(p:real^N->A) y`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `a = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((p:real^N->A) y)` THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(c:(A->bool)#(A->real^N)) IN restrict_atlas atlas W UNION O` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_UNION]; ALL_TAC] THEN
  SUBGOAL_THEN `open {x | x IN S /\ (p:real^N->A) x IN FST(a:(A->bool)#(A->real^N))}`
  ASSUME_TAC THENL
   [REWRITE_TAC[OPEN_IN] THEN MATCH_MP_TAC MFDM_OPEN_IN_PREIMAGE THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[GSYM OPEN_IN] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(a:(A->bool)#(A->real^N))`; `SND(a:(A->bool)#(A->real^N))`]
                  SMOOTH_MANIFOLD_ATLAS_CHART) THEN
    ASM_SIMP_TAC[PAIR];
    ALL_TAC] THEN
  SUBGOAL_THEN `(SND(a:(A->bool)#(A->real^N)) o (p:real^N->A) has_derivative
                 mfd_differential (open_set_atlas S) atlas p y) (at y)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CMPW_PM_DIFF] THEN
    SUBGOAL_THEN `(\z. SND(a:(A->bool)#(A->real^N)) ((p:real^N->A) z)) = SND a o p`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    EXISTS_TAC `{x | x IN S /\ (p:real^N->A) x IN FST(a:(A->bool)#(A->real^N))}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC P2BSS_OR_PREF_SMOOTH THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `chart_trans (FST(a:(A->bool)#(A->real^N)) INTER W,SND a) c o
              (SND a o (p:real^N->A))` THEN
  UNDISCH_TAC `open {z | z IN S /\ (p:real^N->A) z IN FST(a:(A->bool)#(A->real^N)) INTER
                         FST(c:(A->bool)#(A->real^N))}` THEN
  REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN EXISTS_TAC `d:real` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_BALL] THEN ASM_MESON_TAC[DIST_SYM];
    MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[o_THM] THEN
    MP_TAC(ISPECL [`subtopology top (W:A->bool)`;
                   `restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) W UNION O`;
                   `FST(a:(A->bool)#(A->real^N)) INTER W`; `SND(a:(A->bool)#(A->real^N))`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `(p:real^N->A) y`] CHART_TRANS_HAS_DERIVATIVE) THEN
    ASM_REWRITE_TAC[PAIR; IN_INTER]]);;

let P2BSS_CHART_JAC_FACTS = prove
 (`!top (U:((A->bool)#(A->real^N))->bool) c c' x.
     smooth_manifold_atlas top U /\ c IN U /\ c' IN U /\ x IN FST c /\ x IN FST c'
     ==> linear(chart_jac c c' x) /\ ~(det(matrix(chart_jac c c' x)) = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!d d':(A->bool)#(A->real^N).
                  d IN U /\ d' IN U /\ x IN FST d /\ x IN FST d' ==> linear(chart_jac d d' x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `U:((A->bool)#(A->real^N))->bool`;
                   `FST(d:(A->bool)#(A->real^N))`; `SND(d:(A->bool)#(A->real^N))`;
                   `FST(d':(A->bool)#(A->real^N))`; `SND(d':(A->bool)#(A->real^N))`; `x:A`]
                  CHART_TRANS_HAS_DERIVATIVE) THEN
    ASM_REWRITE_TAC[PAIR; IN_INTER] THEN SIMP_TAC[has_derivative];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `U:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `FST(c':(A->bool)#(A->real^N))`; `SND(c':(A->bool)#(A->real^N))`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`; `x:A`]
                CHART_JAC_CHAIN) THEN
  MP_TAC(ISPECL [`top:A topology`; `U:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`; `x:A`]
                CHART_JAC_SELF) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER] THEN DISCH_THEN SUBST1_TAC THEN
  DISCH_THEN(MP_TAC o AP_TERM `\f:real^N->real^N. det(matrix f)`) THEN
  ASM_SIMP_TAC[MATRIX_COMPOSE; DET_MUL; MATRIX_ID; DET_I] THEN
  SPEC_TAC(`det(matrix(chart_jac (c:(A->bool)#(A->real^N)) c' (x:A)))`,`u:real`) THEN
  SPEC_TAC(`det(matrix(chart_jac (c':(A->bool)#(A->real^N)) c (x:A)))`,`v:real`) THEN
  REPEAT GEN_TAC THEN CONV_TAC REAL_RING);;

let P2BSS_OR_DC = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) O W S (p:real^N->A) c y.
     smooth_manifold_atlas top atlas /\ open_in top W /\
     smooth_manifold_atlas (subtopology top W) (restrict_atlas atlas W UNION O) /\
     open S /\ continuous_map (subtopology euclidean S,top) p /\ IMAGE p S SUBSET W /\
     mfd_smooth_map (open_set_atlas S) atlas S p /\ c IN O /\ y IN S /\ p y IN FST c
     ==> frechet_derivative (SND c o p) (at y) =
         chart_jac (FST(chart_at atlas (p y)) INTER W,SND(chart_at atlas (p y))) c (p y) o
         mfd_differential (open_set_atlas S) atlas p y`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MATCH_MP_TAC P2BSS_OR_DERIV THEN EXISTS_TAC `top:A topology` THEN
  EXISTS_TAC `O:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[]);;

let P2BSS_OR_SIGN_INDEP = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) O W S (p:real^N->A) c1 c2 y.
     smooth_manifold_atlas top atlas /\ open_in top W /\
     smooth_manifold_atlas (subtopology top W) (restrict_atlas atlas W UNION O) /\
     mfd_oriented_atlas O /\
     open S /\ continuous_map (subtopology euclidean S,top) p /\ IMAGE p S SUBSET W /\
     mfd_smooth_map (open_set_atlas S) atlas S p /\
     c1 IN O /\ c2 IN O /\ y IN S /\ p y IN FST c1 /\ p y IN FST c2 /\
     ~(det(matrix(mfd_differential (open_set_atlas S) atlas p y)) = &0)
     ==> ~(det(matrix(frechet_derivative (SND c1 o p) (at y))) = &0) /\
         (&0 < det(matrix(frechet_derivative (SND c2 o p) (at y))) <=>
          &0 < det(matrix(frechet_derivative (SND c1 o p) (at y))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(p:real^N->A) y IN topspace top /\ p y IN W` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
      REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN ASM SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `O:((A->bool)#(A->real^N))->bool`; `W:A->bool`; `(p:real^N->A) y`]
                P2BSS_OR_CHARTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `O:((A->bool)#(A->real^N))->bool`; `W:A->bool`; `S:real^N->bool`;
                 `p:real^N->A`; `c1:(A->bool)#(A->real^N)`; `y:real^N`] P2BSS_OR_DC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `O:((A->bool)#(A->real^N))->bool`; `W:A->bool`; `S:real^N->bool`;
                 `p:real^N->A`; `c2:(A->bool)#(A->real^N)`; `y:real^N`] P2BSS_OR_DC) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `r = (FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((p:real^N->A) y)) INTER W,
                   SND(chart_at atlas (p y)))` THEN
  ABBREV_TAC `M = mfd_differential (open_set_atlas S) (atlas:((A->bool)#(A->real^N))->bool)
                                   (p:real^N->A) y` THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `linear(M:real^N->real^N)` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN MATCH_MP_TAC GEOI_DIFF_LINEAR THEN
    MAP_EVERY EXISTS_TAC [`subtopology euclidean (S:real^N->bool)`; `top:A topology`;
                          `S:real^N->bool`] THEN
    ASM_SIMP_TAC[OPEN_SET_ATLAS; OPEN_IN_OPEN_EQ; SUBSET_REFL; SUBTOPOLOGY_SUBTOPOLOGY;
                 INTER_IDEMPOT];
    ALL_TAC] THEN
  ABBREV_TAC `U = restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) W UNION O` THEN
  SUBGOAL_THEN `(c1:(A->bool)#(A->real^N)) IN U /\ (c2:(A->bool)#(A->real^N)) IN U`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "U" THEN ASM_REWRITE_TAC[IN_UNION]; ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^N->A) y IN FST(r:(A->bool)#(A->real^N))` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology top (W:A->bool)`; `U:((A->bool)#(A->real^N))->bool`;
                 `r:(A->bool)#(A->real^N)`; `c1:(A->bool)#(A->real^N)`; `(p:real^N->A) y`]
                P2BSS_CHART_JAC_FACTS) THEN
  MP_TAC(ISPECL [`subtopology top (W:A->bool)`; `U:((A->bool)#(A->real^N))->bool`;
                 `c1:(A->bool)#(A->real^N)`; `c2:(A->bool)#(A->real^N)`; `(p:real^N->A) y`]
                P2BSS_CHART_JAC_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(STRIP_ASSUME_TAC) THEN DISCH_THEN(STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`subtopology top (W:A->bool)`; `U:((A->bool)#(A->real^N))->bool`;
                 `FST(r:(A->bool)#(A->real^N))`; `SND(r:(A->bool)#(A->real^N))`;
                 `FST(c1:(A->bool)#(A->real^N))`; `SND(c1:(A->bool)#(A->real^N))`;
                 `FST(c2:(A->bool)#(A->real^N))`; `SND(c2:(A->bool)#(A->real^N))`;
                 `(p:real^N->A) y`] CHART_JAC_CHAIN) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `&0 < det(matrix(chart_jac (c1:(A->bool)#(A->real^N)) c2 ((p:real^N->A) y)))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_oriented_atlas (O:((A->bool)#(A->real^N))->bool)` THEN
    REWRITE_TAC[mfd_oriented_atlas] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_COMPOSE; LINEAR_COMPOSE; DET_MUL; o_ASSOC] THEN
  ASM_SIMP_TAC[REAL_ENTIRE; GSYM REAL_MUL_ASSOC; REAL_LT_MUL_EQ]);;

let P2BSS_OR_DET_CONT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) O W S (p:real^N->A) c.
     smooth_manifold_atlas top atlas /\ open_in top W /\
     smooth_manifold_atlas (subtopology top W) (restrict_atlas atlas W UNION O) /\
     open S /\ continuous_map (subtopology euclidean S,top) p /\ IMAGE p S SUBSET W /\
     mfd_smooth_map (open_set_atlas S) atlas S p /\ c IN O
     ==> open {y | y IN S /\ p y IN FST c} /\
         (\y. lift(det(matrix(frechet_derivative (SND c o p) (at y)))))
         continuous_on {y | y IN S /\ p y IN FST c}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open {y | y IN S /\ (p:real^N->A) y IN FST(c:(A->bool)#(A->real^N))}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BSS_OR_SET_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) W UNION O`;
                          `W:A->bool`] THEN
    ASM_REWRITE_TAC[IN_UNION];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_DET THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MATRIX_COMPONENT] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2BSS_OR_SMOOTH THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                        `O:((A->bool)#(A->real^N))->bool`; `W:A->bool`] THEN
  ASM_REWRITE_TAC[]);;

let P2BSS_OR_FLIP = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) O W S (p:real^N->A) c y.
     smooth_manifold_atlas top atlas /\ open_in top W /\ ODD(dimindex(:N)) /\
     smooth_manifold_atlas (subtopology top W) (restrict_atlas atlas W UNION O) /\
     open S /\ continuous_map (subtopology euclidean S,top) p /\ IMAGE p S SUBSET W /\
     mfd_smooth_map (open_set_atlas S) atlas S p /\
     (!y. y IN S ==> --y IN S /\ p(--y) = p y) /\
     c IN O /\ y IN S /\ p y IN FST c
     ==> --y IN S /\ p(--y) IN FST c /\
         det(matrix(frechet_derivative (SND c o p) (at (--y)))) =
         --det(matrix(frechet_derivative (SND c o p) (at y)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `--(y:real^N) IN S /\ (p:real^N->A)(--y) IN FST(c:(A->bool)#(A->real^N))`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `O:((A->bool)#(A->real^N))->bool`; `W:A->bool`; `S:real^N->bool`;
                 `p:real^N->A`; `c:(A->bool)#(A->real^N)`] P2BSS_OR_DET_CONT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on {y | y IN S /\ (p:real^N->A) y IN FST(c:(A->bool)#(A->real^N))}
                              (SND c o p)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BSS_OR_SMOOTH THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `O:((A->bool)#(A->real^N))->bool`; `W:A->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Sc = {y | y IN S /\ (p:real^N->A) y IN FST(c:(A->bool)#(A->real^N))}` THEN
  SUBGOAL_THEN `(y:real^N) IN Sc /\ --y IN Sc` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Sc" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^N. z IN Sc
               ==> (SND(c:(A->bool)#(A->real^N)) o (p:real^N->A) has_derivative
                    frechet_derivative (SND c o p) (at z)) (at z)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    EXISTS_TAC `Sc:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `ng = \x:real^N. (--(mat 1):real^N^N) ** x` THEN
  SUBGOAL_THEN `!x:real^N. ng x = --x` ASSUME_TAC THENL
   [EXPAND_TAC "ng" THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LNEG; MATRIX_VECTOR_MUL_LID]; ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (SND(c:(A->bool)#(A->real^N)) o (p:real^N->A)) (at y) =
    frechet_derivative (SND c o p) (at (--y)) o (ng:real^N->real^N)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_AT THEN
    EXISTS_TAC `SND(c:(A->bool)#(A->real^N)) o (p:real^N->A)` THEN EXISTS_TAC `y:real^N` THEN
    ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `(SND(c:(A->bool)#(A->real^N)) o (p:real^N->A)) o (ng:real^N->real^N)` THEN
    UNDISCH_TAC `open(Sc:real^N->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN EXISTS_TAC `d:real` THEN
    ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL
     [X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(w:real^N) IN S` (fun th -> ASM_MESON_TAC[th]) THEN
      SUBGOAL_THEN `(w:real^N) IN Sc` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[DIST_SYM]; ALL_TAC] THEN
      EXPAND_TAC "Sc" THEN SIMP_TAC[IN_ELIM_THM];
      MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_SIMP_TAC[] THEN
      EXPAND_TAC "ng" THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
      REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `linear(frechet_derivative (SND(c:(A->bool)#(A->real^N)) o (p:real^N->A))
                                          (at (--y)))` ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN REWRITE_TAC[differentiable] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(ng:real^N->real^N)` ASSUME_TAC THENL
   [EXPAND_TAC "ng" THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR]; ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_COMPOSE; DET_MUL] THEN
  EXPAND_TAC "ng" THEN REWRITE_TAC[MATRIX_OF_MATRIX_VECTOR_MUL; DET_NEG; DET_I] THEN
  ASM_REWRITE_TAC[REAL_POW_NEG; GSYM NOT_ODD; REAL_POW_ONE] THEN REAL_ARITH_TAC);;

(* The orientation obstruction (generic). *)

let P2BSS_OR_SIGN_OPEN = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) O W S (p:real^N->A) c.
     smooth_manifold_atlas top atlas /\ open_in top W /\
     smooth_manifold_atlas (subtopology top W) (restrict_atlas atlas W UNION O) /\
     open S /\ continuous_map (subtopology euclidean S,top) p /\ IMAGE p S SUBSET W /\
     mfd_smooth_map (open_set_atlas S) atlas S p /\ c IN O
     ==> open {y | y IN S /\ p y IN FST c /\
                   &0 < det(matrix(frechet_derivative (SND c o p) (at y)))} /\
         open {y | y IN S /\ p y IN FST c /\
                   det(matrix(frechet_derivative (SND c o p) (at y))) < &0}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `O:((A->bool)#(A->real^N))->bool`; `W:A->bool`; `S:real^N->bool`;
                 `p:real^N->A`; `c:(A->bool)#(A->real^N)`] P2BSS_OR_DET_CONT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`\y. lift(det(matrix(frechet_derivative
                       (SND(c:(A->bool)#(A->real^N)) o (p:real^N->A)) (at y))))`;
                   `{y | y IN S /\ (p:real^N->A) y IN FST(c:(A->bool)#(A->real^N))}`;
                   `{z:real^1 | z$1 > &0}`] CONTINUOUS_OPEN_PREIMAGE);
    MP_TAC(ISPECL [`\y. lift(det(matrix(frechet_derivative
                       (SND(c:(A->bool)#(A->real^N)) o (p:real^N->A)) (at y))))`;
                   `{y | y IN S /\ (p:real^N->A) y IN FST(c:(A->bool)#(A->real^N))}`;
                   `{z:real^1 | z$1 < &0}`] CONTINUOUS_OPEN_PREIMAGE)] THEN
  ASM_REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT; OPEN_HALFSPACE_COMPONENT_LT] THEN
  MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; LIFT_COMPONENT; real_gt; CONJ_ASSOC]);;

let P2BSS_ANTIPODAL_ORIENT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (p:real^N->A) S W.
     smooth_manifold_atlas top atlas /\ ODD(dimindex(:N)) /\
     open S /\ connected S /\ ~(S = {}) /\
     (!y. y IN S ==> --y IN S /\ p(--y) = p y) /\
     continuous_map (subtopology euclidean S,top) p /\
     mfd_smooth_map (open_set_atlas S) atlas S p /\
     (!y. y IN S ==> ~(det(matrix(mfd_differential (open_set_atlas S) atlas p y)) = &0)) /\
     open_in top W /\ IMAGE p S SUBSET W /\
     mfd_orientable (subtopology top W) (restrict_atlas atlas W)
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `O:((A->bool)#(A->real^N))->bool` STRIP_ASSUME_TAC o
    REWRITE_RULE[mfd_orientable]) THEN
  SUBGOAL_THEN
   `!y. y IN S
        ==> ?c. c IN (O:((A->bool)#(A->real^N))->bool) /\ (p:real^N->A) y IN FST c`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    EXISTS_TAC `chart_at (O:((A->bool)#(A->real^N))->bool) ((p:real^N->A) y)` THEN
    MATCH_MP_TAC CHART_AT THEN EXISTS_TAC `subtopology top (W:A->bool)` THEN
    ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
      REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN ASM SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC
   `e1 = {y | y IN S /\ ?c. c IN (O:((A->bool)#(A->real^N))->bool) /\ (p:real^N->A) y IN FST c /\
                         &0 < det(matrix(frechet_derivative (SND c o p) (at y)))}` THEN
  ABBREV_TAC
   `e2 = {y | y IN S /\ ?c. c IN (O:((A->bool)#(A->real^N))->bool) /\ (p:real^N->A) y IN FST c /\
                         det(matrix(frechet_derivative (SND c o p) (at y))) < &0}` THEN
  SUBGOAL_THEN
   `!c1 c2 y. c1 IN (O:((A->bool)#(A->real^N))->bool) /\ c2 IN O /\ y IN S /\
              (p:real^N->A) y IN FST c1 /\ p y IN FST c2
              ==> ~(det(matrix(frechet_derivative (SND c1 o p) (at y))) = &0) /\
                  (&0 < det(matrix(frechet_derivative (SND c2 o p) (at y))) <=>
                   &0 < det(matrix(frechet_derivative (SND c1 o p) (at y))))`
  (LABEL_TAC "ind") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC P2BSS_OR_SIGN_INDEP THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `O:((A->bool)#(A->real^N))->bool`; `W:A->bool`; `S:real^N->bool`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(e1:real^N->bool)` ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [OPEN_SUBOPEN] THEN X_GEN_TAC `y:real^N` THEN EXPAND_TAC "e1" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `c:(A->bool)#(A->real^N)` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `{y | y IN S /\ (p:real^N->A) y IN FST(c:(A->bool)#(A->real^N)) /\
                     &0 < det(matrix(frechet_derivative (SND c o p) (at y)))}` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `O:((A->bool)#(A->real^N))->bool`; `W:A->bool`; `S:real^N->bool`;
                   `p:real^N->A`; `c:(A->bool)#(A->real^N)`] P2BSS_OR_SIGN_OPEN) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM; SUBSET] THEN
    X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN EXPAND_TAC "e1" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `c:(A->bool)#(A->real^N)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(e2:real^N->bool)` ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [OPEN_SUBOPEN] THEN X_GEN_TAC `y:real^N` THEN EXPAND_TAC "e2" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `c:(A->bool)#(A->real^N)` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `{y | y IN S /\ (p:real^N->A) y IN FST(c:(A->bool)#(A->real^N)) /\
                     det(matrix(frechet_derivative (SND c o p) (at y))) < &0}` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `O:((A->bool)#(A->real^N))->bool`; `W:A->bool`; `S:real^N->bool`;
                   `p:real^N->A`; `c:(A->bool)#(A->real^N)`] P2BSS_OR_SIGN_OPEN) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM; SUBSET] THEN
    X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN EXPAND_TAC "e2" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `c:(A->bool)#(A->real^N)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(S:real^N->bool) SUBSET e1 UNION e2` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_UNION] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    MAP_EVERY EXPAND_TAC ["e1"; "e2"] THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(X_CHOOSE_THEN `c:(A->bool)#(A->real^N)` STRIP_ASSUME_TAC o C MATCH_MP
      (ASSUME `(y:real^N) IN S`)) THEN
    USE_THEN "ind" (MP_TAC o SPECL [`c:(A->bool)#(A->real^N)`; `c:(A->bool)#(A->real^N)`;
                                    `y:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
    ASM_CASES_TAC `&0 < det(matrix(frechet_derivative
                     (SND(c:(A->bool)#(A->real^N)) o (p:real^N->A)) (at y)))` THENL
     [DISJ1_TAC THEN EXISTS_TAC `c:(A->bool)#(A->real^N)` THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN EXISTS_TAC `c:(A->bool)#(A->real^N)` THEN ASM_REWRITE_TAC[] THEN
      REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e1:real^N->bool) INTER e2 INTER S = {}` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `y:real^N` THEN
    MAP_EVERY EXPAND_TAC ["e1"; "e2"] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `c1:(A->bool)#(A->real^N)` STRIP_ASSUME_TAC))
      (CONJUNCTS_THEN2
        (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `c2:(A->bool)#(A->real^N)` STRIP_ASSUME_TAC))
        ASSUME_TAC)) THEN
    USE_THEN "ind" (MP_TAC o SPECL [`c1:(A->bool)#(A->real^N)`; `c2:(A->bool)#(A->real^N)`;
                                    `y:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `&0 < det(matrix(frechet_derivative
                   (SND(c1:(A->bool)#(A->real^N)) o (p:real^N->A)) (at y)))` THEN
    UNDISCH_TAC `det(matrix(frechet_derivative
                   (SND(c2:(A->bool)#(A->real^N)) o (p:real^N->A)) (at y))) < &0` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~((e1:real^N->bool) INTER S = {}) /\ ~((e2:real^N->bool) INTER S = {})`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_TAC `y0:real^N` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY] o
      check (fun th -> concl th = `~(S:real^N->bool = {})`)) THEN
    FIRST_ASSUM(X_CHOOSE_THEN `c:(A->bool)#(A->real^N)` STRIP_ASSUME_TAC o C MATCH_MP
      (ASSUME `(y0:real^N) IN S`)) THEN
    USE_THEN "ind" (MP_TAC o SPECL [`c:(A->bool)#(A->real^N)`; `c:(A->bool)#(A->real^N)`;
                                    `y0:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `O:((A->bool)#(A->real^N))->bool`; `W:A->bool`; `S:real^N->bool`;
                   `p:real^N->A`; `c:(A->bool)#(A->real^N)`; `y0:real^N`] P2BSS_OR_FLIP) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXPAND_TAC ["e1"; "e2"] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM] THEN
    ASM_CASES_TAC `&0 < det(matrix(frechet_derivative
                     (SND(c:(A->bool)#(A->real^N)) o (p:real^N->A)) (at y0)))` THENL
     [CONJ_TAC THENL
       [EXISTS_TAC `y0:real^N` THEN ASM_REWRITE_TAC[] THEN
        EXISTS_TAC `c:(A->bool)#(A->real^N)` THEN ASM_REWRITE_TAC[];
        EXISTS_TAC `--y0:real^N` THEN ASM_REWRITE_TAC[] THEN
        EXISTS_TAC `c:(A->bool)#(A->real^N)` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `&0 < det(matrix(frechet_derivative
                       (SND(c:(A->bool)#(A->real^N)) o (p:real^N->A)) (at y0)))` THEN
        REAL_ARITH_TAC];
      CONJ_TAC THENL
       [EXISTS_TAC `--y0:real^N` THEN ASM_REWRITE_TAC[] THEN
        EXISTS_TAC `c:(A->bool)#(A->real^N)` THEN ASM_REWRITE_TAC[] THEN
        REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;
        EXISTS_TAC `y0:real^N` THEN ASM_REWRITE_TAC[] THEN
        EXISTS_TAC `c:(A->bool)#(A->real^N)` THEN ASM_REWRITE_TAC[] THEN
        REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  UNDISCH_TAC `connected(S:real^N->bool)` THEN
  REWRITE_TAC[connected; NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`e1:real^N->bool`; `e2:real^N->bool`]) THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The orientation excludes the antipodal case (via the annulus 1 < |y| < 2, *)
(* whose image is open with compact closure); p is injective; p is a         *)
(* parametrization on balls ball(y,|y|/2).                                   *)
(* ========================================================================= *)

let P2BSS_LISOM_SUB = prove
 (`!(G:real^N->real^N^N) top (atlas:((A->bool)#(A->real^N))->bool) g Z S (p:real^N->A).
     open Z /\ open S /\ S SUBSET Z /\
     mfd_local_isometry (subtopology euclidean Z,open_set_atlas Z) G (top,atlas) g Z p
     ==> mfd_local_isometry (subtopology euclidean S,open_set_atlas S) G (top,atlas) g S p`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `mfd_local_isometry (subtopology euclidean Z,open_set_atlas Z)
                  (G:real^N->real^N^N) (top,atlas) (g:A->real^N^N) S (p:real^N->A)` MP_TAC THENL
   [MATCH_MP_TAC GEOH_LISOM_SUBSET THEN EXISTS_TAC `Z:real^N->bool` THEN
    ASM_SIMP_TAC[OPEN_IN_OPEN_EQ];
    MP_TAC(ISPECL [`Z:real^N->bool`; `S:real^N->bool`; `S:real^N->bool`; `G:real^N->real^N^N`;
                   `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `p:real^N->A`] P2BSS_LISOM_OPEN_SET_MONO) THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]]);;

let P2BSS_ANNULUS_FACTS = prove
 (`open {y:real^3 | &1 < norm y /\ norm y < &2} /\
   connected {y:real^3 | &1 < norm y /\ norm y < &2} /\
   ~({y:real^3 | &1 < norm y /\ norm y < &2} = {}) /\
   compact {y:real^3 | &1 <= norm y /\ norm y <= &2} /\
   {y:real^3 | &1 < norm y /\ norm y < &2} SUBSET {y:real^3 | &1 <= norm y /\ norm y <= &2} /\
   {y:real^3 | &1 <= norm y /\ norm y <= &2} SUBSET {y:real^3 | ~(y = vec 0)} /\
   (!y:real^3. y IN {y:real^3 | &1 < norm y /\ norm y < &2}
               ==> --y IN {y:real^3 | &1 < norm y /\ norm y < &2})`,
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `{y:real^3 | &1 < norm y /\ norm y < &2} = ball(vec 0,&2) DIFF cball(vec 0,&1)`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_BALL_0; IN_CBALL_0] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC OPEN_DIFF THEN REWRITE_TAC[OPEN_BALL; CLOSED_CBALL]];
    MP_TAC(ISPECL [`vec 0:real^3`; `&1`; `&2`] (CONJUNCT1 CONNECTED_ANNULUS)) THEN
    REWRITE_TAC[VECTOR_SUB_RZERO; DIMINDEX_3] THEN ARITH_TAC;
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    EXISTS_TAC `(&3 / &2) % basis 1:real^3` THEN
    SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `{y:real^3 | &1 <= norm y /\ norm y <= &2} = cball(vec 0,&2) DIFF ball(vec 0,&1)`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_BALL_0; IN_CBALL_0] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC COMPACT_DIFF THEN REWRITE_TAC[COMPACT_CBALL; OPEN_BALL]];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN GEN_TAC THEN
    ASM_CASES_TAC `x:real^3 = vec 0` THEN ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
    REWRITE_TAC[IN_ELIM_THM; NORM_NEG]]);;

let P2BSS_NOT_ANTIPODAL = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) q (p:real^3->A).
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     p2b_lorient top atlas /\ &0 < q /\
     mfd_local_isometry
       (subtopology euclidean {y:real^3 | ~(y = vec 0)},open_set_atlas {y:real^3 | ~(y = vec 0)})
       (p2bss_g0 q) (top,atlas) g {y:real^3 | ~(y = vec 0)} p /\
     (!y. ~(y = vec 0) ==> p(--y) = p y)
     ==> F`,
  REPEAT STRIP_TAC THEN
  MP_TAC P2BSS_ANNULUS_FACTS THEN
  ABBREV_TAC `An = {y:real^3 | &1 < norm y /\ norm y < &2}` THEN
  ABBREV_TAC `K = {y:real^3 | &1 <= norm y /\ norm y <= &2}` THEN
  STRIP_TAC THEN
  MP_TAC P2BSS_ZSETS THEN STRIP_TAC THEN
  SUBGOAL_THEN `(An:real^3->bool) SUBSET {y:real^3 | ~(y = vec 0)}` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_local_isometry (subtopology euclidean An,open_set_atlas An) (p2bss_g0 q) (top,atlas)
                       (g:A->real^3^3) An (p:real^3->A)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BSS_LISOM_SUB THEN EXISTS_TAC `{y:real^3 | ~(y = vec 0)}` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ASSUME `mfd_local_isometry (subtopology euclidean An,open_set_atlas An) (p2bss_g0 q)
                   (top,atlas) (g:A->real^3^3) An (p:real^3->A)`) THEN
  REWRITE_TAC[mfd_local_isometry; SUBTOPOLOGY_SUBTOPOLOGY; INTER_IDEMPOT] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y:real^3. y IN An ==> ~(y = vec 0)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (IMAGE (p:real^3->A) An)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(An:real^3->bool) = topspace(subtopology euclidean An)` SUBST1_TAC THENL
     [REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]; ALL_TAC] THEN
    MATCH_MP_TAC(ISPECL [`subtopology euclidean (An:real^3->bool)`; `open_set_atlas (An:real^3->bool)`;
                         `p2bss_g0 q`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                         `g:A->real^3^3`] P2BSS_LISOM_IMAGE_OPEN) THEN
    ASM_SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY; HAUSDORFF_SPACE_EUCLIDEAN; OPEN_SET_ATLAS;
                 P2BSS_G0_RIEMANNIAN; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in top (top closure_of (IMAGE (p:real^3->A) An))` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_COMPACT_IN THEN EXISTS_TAC `IMAGE (p:real^3->A) K` THEN
    REWRITE_TAC[CLOSED_IN_CLOSURE_OF] THEN
    SUBGOAL_THEN `compact_in top (IMAGE (p:real^3->A) K)` ASSUME_TAC THENL
     [MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `subtopology euclidean (K:real^3->bool)` THEN
      ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN; SUBSET_REFL] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
      EXISTS_TAC `{y:real^3 | ~(y = vec 0)}` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `mfd_local_isometry
         (subtopology euclidean {y:real^3 | ~(y = vec 0)},open_set_atlas {y:real^3 | ~(y = vec 0)})
         (p2bss_g0 q) (top,atlas) (g:A->real^3^3) {y:real^3 | ~(y = vec 0)} (p:real^3->A)` THEN
      SIMP_TAC[mfd_local_isometry; SUBTOPOLOGY_SUBTOPOLOGY; INTER_IDEMPOT];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN
    ASM_SIMP_TAC[COMPACT_IN_IMP_CLOSED_IN; IMAGE_SUBSET];
    ALL_TAC] THEN
  MP_TAC(SPEC `IMAGE (p:real^3->A) An`
    (REWRITE_RULE[p2b_lorient] (ASSUME `p2b_lorient top (atlas:((A->bool)#(A->real^3))->bool)`))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `p:real^3->A`; `An:real^3->bool`; `IMAGE (p:real^3->A) An`]
                      P2BSS_ANTIPODAL_ORIENT) THEN
  ASM_REWRITE_TAC[DIMINDEX_3; SUBSET_REFL] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ODD_CONV) THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN ASM_SIMP_TAC[];
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC GEOH_LISOM_DET THEN
    MAP_EVERY EXISTS_TAC [`subtopology euclidean (An:real^3->bool)`; `p2bss_g0 q`;
                          `top:A topology`; `g:A->real^3^3`; `An:real^3->bool`] THEN
    ASM_SIMP_TAC[OPEN_SET_ATLAS; P2BSS_G0_RIEMANNIAN]]);;

let P2BSS_P_INJ = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) (Y:A->real^3) q c (p:real^3->A).
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     p2b_lorient top atlas /\ &0 < q /\ ~(c = &0) /\
     mfd_local_isometry
       (subtopology euclidean {y:real^3 | ~(y = vec 0)},open_set_atlas {y:real^3 | ~(y = vec 0)})
       (p2bss_g0 q) (top,atlas) g {y:real^3 | ~(y = vec 0)} p /\
     (!y. ~(y = vec 0)
          ==> mfd_differential (open_set_atlas {y:real^3 | ~(y = vec 0)}) atlas p y (inv c % y) =
              Y(p y)) /\
     (!y1 y2. ~(y1 = vec 0) /\ ~(y2 = vec 0) /\ p y1 = p y2 ==> norm y1 = norm y2)
     ==> !y z. ~(y = vec 0) /\ ~(z = vec 0) ==> (p y = p z <=> z = y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  EQ_TAC THENL [ALL_TAC; DISCH_THEN SUBST1_TAC THEN REFL_TAC] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `Y:A->real^3`; `q:real`; `c:real`; `p:real^3->A`] P2BSS_FIBRE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`y:real^3`; `z:real^3`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN MATCH_MP_TAC P2BSS_NOT_ANTIPODAL THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                        `g:A->real^3^3`; `q:real`; `p:real^3->A`] THEN
  ASM_REWRITE_TAC[]);;

let P2BSS_P_PARAM = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) q (p:real^3->A).
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     &0 < q /\
     mfd_local_isometry
       (subtopology euclidean {y:real^3 | ~(y = vec 0)},open_set_atlas {y:real^3 | ~(y = vec 0)})
       (p2bss_g0 q) (top,atlas) g {y:real^3 | ~(y = vec 0)} p /\
     (!y z. ~(y = vec 0) /\ ~(z = vec 0) ==> (p y = p z <=> z = y))
     ==> !y. ~(y = vec 0)
             ==> ?r. &0 < r /\ r < norm y /\ mfd_param top atlas (ball(y,r)) p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  EXISTS_TAC `norm(y:real^3) / &2` THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC P2BSS_ZSETS THEN STRIP_TAC THEN
  ABBREV_TAC `B = ball(y:real^3,norm y / &2)` THEN
  SUBGOAL_THEN `open(B:real^3->bool) /\ B SUBSET {y:real^3 | ~(y = vec 0)}` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN REWRITE_TAC[OPEN_BALL; SUBSET; IN_BALL; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[DIST_0]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_local_isometry (subtopology euclidean B,open_set_atlas B) (p2bss_g0 q)
                       (top,atlas) (g:A->real^3^3) B (p:real^3->A)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BSS_LISOM_SUB THEN EXISTS_TAC `{y:real^3 | ~(y = vec 0)}` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_local_isometry (subtopology euclidean (:real^3),open_set_atlas (:real^3)) (p2bss_g0 q)
                       (top,atlas) (g:A->real^3^3) B (p:real^3->A)` MP_TAC THENL
   [MP_TAC(ISPECL [`B:real^3->bool`; `(:real^3)`; `B:real^3->bool`; `p2bss_g0 q`;
                   `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `p:real^3->A`] P2BSS_LISOM_OPEN_SET_MONO) THEN
    ASM_REWRITE_TAC[SUBSET_REFL; SUBSET_UNIV; OPEN_UNIV] THEN
    DISCH_THEN(fun th -> ASM_REWRITE_TAC[GSYM th]);
    ALL_TAC] THEN
  REWRITE_TAC[mfd_local_isometry; SUBTOPOLOGY_UNIV] THEN STRIP_TAC THEN
  MATCH_MP_TAC GEOS_INJECTIVE_PARAM THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`v:real^3`; `w:real^3`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`v:real^3`; `w:real^3`] o
      check (fun th -> can (find_term ((=) `(p:real^3->A) y`)) (concl th) && is_forall(concl th))) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`v:real^3`; `h:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((v:real^3) = vec 0)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_differential (open_set_atlas (:real^3)) (atlas:((A->bool)#(A->real^3))->bool)
                     (p:real^3->A) v =
    mfd_differential (open_set_atlas {y:real^3 | ~(y = vec 0)}) atlas p v`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[MFD_DIFFERENTIAL_OPEN_SET_ATLAS; CMPW_PM_DIFF; IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `linear(mfd_differential (open_set_atlas {y:real^3 | ~(y = vec 0)})
             (atlas:((A->bool)#(A->real^3))->bool) (p:real^3->A) v) /\
    ~(det(matrix(mfd_differential (open_set_atlas {y:real^3 | ~(y = vec 0)}) atlas p v)) = &0)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC GEOI_DIFF_LINEAR THEN
      MAP_EVERY EXISTS_TAC [`subtopology euclidean {y:real^3 | ~(y = vec 0)}`; `top:A topology`;
                            `{y:real^3 | ~(y = vec 0)}`] THEN
      ASM_SIMP_TAC[OPEN_SET_ATLAS; IN_ELIM_THM] THEN ASM_MESON_TAC[mfd_local_isometry];
      MATCH_MP_TAC GEOH_LISOM_DET THEN
      MAP_EVERY EXISTS_TAC [`subtopology euclidean {y:real^3 | ~(y = vec 0)}`; `p2bss_g0 q`;
                            `top:A topology`; `g:A->real^3^3`; `{y:real^3 | ~(y = vec 0)}`] THEN
      ASM_SIMP_TAC[OPEN_SET_ATLAS; P2BSS_G0_RIEMANNIAN; IN_ELIM_THM]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `matrix(mfd_differential (open_set_atlas {y:real^3 | ~(y = vec 0)})
                         (atlas:((A->bool)#(A->real^3))->bool) (p:real^3->A) v)`
               HOMOGENEOUS_LINEAR_EQUATIONS_DET) THEN
  ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_THEN(MP_TAC o SPEC `h:real^3`) THEN
  ASM_SIMP_TAC[MATRIX_WORKS] THEN
  UNDISCH_TAC `mfd_differential (open_set_atlas (:real^3)) (atlas:((A->bool)#(A->real^3))->bool)
                                (p:real^3->A) v h = vec 0` THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* ========================================================================= *)
(* The main theorem.  With the leaf N through a point of positive scalar     *)
(* curvature (curvature k > 0), c = sqrt(1/k), lam = c^2/2 = 1/(2k), the     *)
(* glued model map p2bss_p is the one-to-one round cylinder model.           *)
(* ========================================================================= *)

let P2B_SHRINKER_SPLIT_CYL = prove
 (`!w:B->bool. P2B_SHRINKER_SPLIT_CYL_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2B_SHRINKER_SPLIT_CYL_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:B->real^3^3`; `f:B->real`; `Y:B->real^3`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_TAC `K0:real`)
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `x0:B` STRIP_ASSUME_TAC)
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `f:B->real`; `Y:B->real^3`; `x0:B`; `K0:real`] P2BSS_LEAF_PAIR) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `s0 = p2bss_h atlas f (Y:B->real^3) x0` THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` (X_CHOOSE_THEN `FS:real^2->B`
    (X_CHOOSE_THEN `FN:real^2->B` STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `c = sqrt(inv k)` THEN
  SUBGOAL_THEN `&0 < c /\ c pow 2 = inv k` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN ASM_SIMP_TAC[SQRT_POS_LT; REAL_LT_INV; SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(c = &0) /\ &0 < c pow 2` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_NZ; REAL_POW_LT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `f:B->real`; `Y:B->real^3`; `s0:real`; `k:real`; `FS:real^2->B`; `FN:real^2->B`]
                P2BSS_P_LISOM) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `f:B->real`; `Y:B->real^3`; `s0:real`; `k:real`; `FS:real^2->B`; `FN:real^2->B`]
                P2BSS_P_Y) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `p = p2bss_p (top,atlas) (g:B->real^3^3) (Y:B->real^3) FS FN c` THEN
  SUBGOAL_THEN `(!w. (FS:real^2->B) w IN lvs_set (topspace top) (p2bss_h atlas f (Y:B->real^3)) s0) /\
                (!w. (FN:real^2->B) w IN lvs_set (topspace top) (p2bss_h atlas f Y) s0)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                     `f:B->real`; `Y:B->real^3`; `s0:real`; `k:real`; `FS:real^2->B`]
                    P2BSS_E_FACTS);
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                     `f:B->real`; `Y:B->real^3`; `s0:real`; `k:real`; `FN:real^2->B`]
                    P2BSS_E_FACTS)] THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. ~(y = vec 0)
        ==> (p:real^3->B) y IN topspace top /\
            p2bss_h atlas f (Y:B->real^3) (p y) = s0 + c * log(norm y)`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "p" THEN MATCH_MP_TAC P2BSS_H_P THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y z. ~(y = vec 0) /\ ~(z = vec 0) ==> ((p:real^3->B) y = p z <=> z = y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BSS_P_INJ THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                          `g:B->real^3^3`; `Y:B->real^3`; `c pow 2`; `c:real`] THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`y1:real^3`; `y2:real^3`] THEN STRIP_TAC THEN
    FIRST_ASSUM((fun th ->
      MP_TAC(CONJUNCT2(MP (SPEC `y1:real^3` th) (ASSUME `~(y1:real^3 = vec 0)`))) THEN
      MP_TAC(CONJUNCT2(MP (SPEC `y2:real^3` th) (ASSUME `~(y2:real^3 = vec 0)`)))) o
      check (fun th -> can (find_term ((=) `log`)) (concl th))) THEN
    REWRITE_TAC[ASSUME `(p:real^3->B) y1 = p y2`] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_EQ_ADD_LCANCEL] THEN
    ASM_SIMP_TAC[REAL_EQ_MUL_LCANCEL; LOG_INJ; NORM_POS_LT] THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`p:real^3->B`; `c pow 2 / &2`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH];
    EXPAND_TAC "p" THEN MATCH_MP_TAC P2BSS_P_ONTO THEN
    MAP_EVERY EXISTS_TAC [`f:B->real`; `s0:real`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2BSS_P_PARAM THEN
    MAP_EVERY EXISTS_TAC [`g:B->real^3^3`; `c pow 2`] THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN REWRITE_TAC[GSYM P2BSS_G0_CYL] THEN
    MATCH_MP_TAC P2BSS_LISOM_RFS THEN
    MAP_EVERY EXISTS_TAC [`{y:real^3 | ~(y = vec 0)}`; `top:B topology`;
                          `{y:real^3 | ~(y = vec 0)}`] THEN
    REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[IN_ELIM_THM; SUBSET_REFL; P2BSS_ZSETS];
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `sqrt(&2 * c pow 2 / &2) = c` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_ARITH `&2 * x / &2 = x`] THEN ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;


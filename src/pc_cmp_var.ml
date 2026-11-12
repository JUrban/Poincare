(* ========================================================================= *)
(* Unit pc_cmp_var (comparison-geometry layer CMP): the second variation of *)
(* energy for one smooth piece.  For a smooth two-parameter family f(s,t)   *)
(* whose s-curves are geodesics, e = |d_t f|^2 has                           *)
(* d_s e = 2 <D_t V, T> and d_s^2 e = 2 (<R(V,T)V, T> + |D_t V|^2)           *)
(* (V = d_s f, T = d_t f), by the symmetry lemma, metric compatibility and  *)
(* the curvature commutator; differentiation under the integral gives the   *)
(* first and second derivatives of the energy on [a,b].  For a smooth field *)
(* X along a geodesic the variation exp(s X(t)) is such a family, and the   *)
(* second derivative at s = 0 is the integral of 2 (|D_t X|^2 -             *)
(* <X, R(X,T)T>) (CMPV_PIECE_VARIATION).  The index inequality, Jacobi's    *)
(* theorem and MT Claim 3.24 follow in pc_cmp_index.                         *)
(* ========================================================================= *)

needs "src/pc_cmp_jcomp.ml";;
needs "src/pc_cmp_comm.ml";;
needs "src/pc_geo_gauss.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Smooth two-parameter families and fields along them.                      *)
(* ========================================================================= *)

(* A two-parameter family on S0 x J, smooth in every chart (the hypotheses  *)
(* of MFD_COVD_SYMMETRY and MFD_COVD_COMMUTATOR).                            *)

let cmp_family = new_definition
 `cmp_family (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
             (f:real->real->A) (S0:real->bool) (J:real->bool) <=>
    real_open S0 /\ is_realinterval S0 /\ real_open J /\ is_realinterval J /\
    continuous_map
      (subtopology euclidean {pastecart (lift s) (lift t) | s IN S0 /\ t IN J},top)
      (\z. f (drop(fstcart z)) (drop(sndcart z))) /\
    (!c. c IN atlas
         ==> smooth_map_on
               {pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\ f s t IN FST c}
               (\z. SND c (f (drop(fstcart z)) (drop(sndcart z)))))`;;

(* A vector field along the family, smooth in every chart. *)

let cmp_ffield = new_definition
 `cmp_ffield (atlas:((A->bool)#(A->real^N))->bool) (f:real->real->A)
             (S0:real->bool) (J:real->bool) (Z:real->real->real^N) <=>
    !c. c IN atlas
        ==> smooth_map_on
              {pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\ f s t IN FST c}
              (\z. chart_jac (chart_at atlas (f (drop(fstcart z)) (drop(sndcart z))))
                             c (f (drop(fstcart z)) (drop(sndcart z)))
                             (Z (drop(fstcart z)) (drop(sndcart z))))`;;

let CMPV_FAMILY_CHART_OPEN = prove
 (`!top atlas (f:real->real->A) S0 J c.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        cmp_family (top,atlas) f S0 J /\ c IN atlas
        ==> open {pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\ f s t IN FST c}`,
  REWRITE_TAC[cmp_family] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC GEOC_PAIR_CHART_OPEN THEN EXISTS_TAC `top:A topology` THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MFDM_CHART]);;

(* The two velocity fields of a family are smooth fields along it. *)

let CMPV_VEL_FIELDS = prove
 (`!top atlas (f:real->real->A) S0 J.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        cmp_family (top,atlas) f S0 J
        ==> cmp_ffield atlas f S0 J (\s t. mfd_vel atlas (\s'. f s' t) s) /\
            cmp_ffield atlas f S0 J (\s t. mfd_vel atlas (f s) t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[cmp_ffield] THEN
  CONJ_TAC THEN X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:real->real->A`; `S0:real->bool`; `J:real->bool`;
                 `c:(A->bool)#(A->real^N)`] CMPV_FAMILY_CHART_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `cmp_family (top,atlas:((A->bool)#(A->real^N))->bool) (f:real->real->A) S0 J` THEN
  REWRITE_TAC[cmp_family] THEN STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THENL
   [EXISTS_TAC `\z. frechet_derivative
                     (\z. SND (c:(A->bool)#(A->real^N))
                            ((f:real->real->A) (drop(fstcart z)) (drop(sndcart z))))
                     (at z) (pastecart (vec 1) (vec 0))`;
    EXISTS_TAC `\z. frechet_derivative
                     (\z. SND (c:(A->bool)#(A->real^N))
                            ((f:real->real->A) (drop(fstcart z)) (drop(sndcart z))))
                     (at z) (pastecart (vec 0) (vec 1))`] THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE] THEN
  REWRITE_TAC[FORALL_IN_GSPEC; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:real->real->A`; `S0:real->bool`; `J:real->bool`;
                 `c:(A->bool)#(A->real^N)`; `s:real`; `t:real`] GEOC_VEL_CHART2) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* Christoffel symbols at a moving point applied to moving vectors. *)

let CMPV_CHRISTOFFEL_MOVING = prove
 (`!U (G:real^N->real^N^N) s (y:real^M->real^N) (u:real^M->real^N) v.
        metric_field U G /\ open s /\ smooth_map_on s y /\ smooth_map_on s u /\
        smooth_map_on s v /\ (!x. x IN s ==> y x IN U)
        ==> smooth_map_on s (\x. christoffel G (y x) (u x) (v x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC
   `\x. vsum(1..dimindex(:N))
          (\i. vsum(1..dimindex(:N))
                 (\j. drop(lift(((u:real^M->real^N) x)$i * ((v:real^M->real^N) x)$j)) %
                      christoffel (G:real^N->real^N^N) ((y:real^M->real^N) x)
                                  (basis i) (basis j)))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
    CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC(ISPEC `christoffel (G:real^N->real^N^N) ((y:real^M->real^N) x)`
                   CMPC_BILINEAR_EXPAND) THEN
    MATCH_MP_TAC CHRISTOFFEL_BILINEAR THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`s:real^M->bool`; `\x. lift(((u:real^M->real^N) x)$i)`;
                   `\x. lift(((v:real^M->real^N) x)$j)`] SMOOTH_MAP_ON_LIFT_MUL) THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_LIFT_COMPONENT; LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. christoffel (G:real^N->real^N^N) ((y:real^M->real^N) x) (basis i) (basis j)) =
    (\z. christoffel G z (basis i) (basis j)) o y`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_SIMP_TAC[LRG_CHRISTOFFEL_SMOOTH] THEN ASM SET_TAC[]);;

(* D_t Z and D_s Z of a smooth field along the family are smooth fields. *)

let CMPV_COVD_T_FIELD = prove
 (`!top atlas (g:A->real^N^N) (f:real->real->A) S0 J (Z:real->real->real^N).
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        cmp_family (top,atlas) f S0 J /\ cmp_ffield atlas f S0 J Z
        ==> cmp_ffield atlas f S0 J (\s t. mfd_covd atlas g (f s) (Z s) t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[cmp_ffield] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:real->real->A`; `S0:real->bool`; `J:real->bool`;
                 `c:(A->bool)#(A->real^N)`] CMPV_FAMILY_CHART_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `cmp_family (top,atlas:((A->bool)#(A->real^N))->bool) (f:real->real->A) S0 J` THEN
  REWRITE_TAC[cmp_family] THEN STRIP_TAC THEN
  UNDISCH_TAC `cmp_ffield atlas (f:real->real->A) S0 J (Z:real->real->real^N)` THEN
  REWRITE_TAC[cmp_ffield] THEN DISCH_TAC THEN
  ABBREV_TAC `D = {pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\
                   (f:real->real->A) s t IN FST (c:(A->bool)#(A->real^N))}` THEN
  ABBREV_TAC `fc = \z. SND (c:(A->bool)#(A->real^N))
                         ((f:real->real->A) (drop(fstcart z)) (drop(sndcart z)))` THEN
  ABBREV_TAC `Zc = \z. chart_jac (chart_at atlas ((f:real->real->A) (drop(fstcart z))
                                                       (drop(sndcart z))))
                         (c:(A->bool)#(A->real^N)) (f (drop(fstcart z)) (drop(sndcart z)))
                         ((Z:real->real->real^N) (drop(fstcart z)) (drop(sndcart z)))` THEN
  SUBGOAL_THEN `smooth_map_on D (fc:real^(1,1)finite_sum->real^N) /\
                smooth_map_on D (Zc:real^(1,1)finite_sum->real^N)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["D"; "fc"; "Zc"] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND c) (FST c))
                 (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))`
  ASSUME_TAC THENL [ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN D ==> (fc:real^(1,1)finite_sum->real^N) z IN
                               IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["D"; "fc"] THEN
    REWRITE_TAC[FORALL_IN_GSPEC; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `\z. frechet_derivative (Zc:real^(1,1)finite_sum->real^N) (at z)
                    (pastecart (vec 0) (vec 1)) +
                  christoffel (metric_local atlas (c:(A->bool)#(A->real^N))
                                               (g:A->real^N^N))
                    ((fc:real^(1,1)finite_sum->real^N) z)
                    (frechet_derivative fc (at z) (pastecart (vec 0) (vec 1)))
                    (Zc z)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE] THEN
    MATCH_MP_TAC CMPV_CHRISTOFFEL_MOVING THEN
    EXISTS_TAC `IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE]] THEN
  EXPAND_TAC "D" THEN
  REWRITE_TAC[FORALL_IN_GSPEC; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  REPEAT STRIP_TAC THEN MAP_EVERY EXPAND_TAC ["fc"; "Zc"] THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `f:real->real->A`; `Z:real->real->real^N`;
                 `S0:real->bool`; `J:real->bool`; `c:(A->bool)#(A->real^N)`;
                 `s:real`; `t:real`] CMPC_COVD_REP_T) THEN
  ASM_REWRITE_TAC[mfd_field_rep] THEN DISCH_THEN(ACCEPT_TAC o SYM));;

let CMPV_COVD_S_FIELD = prove
 (`!top atlas (g:A->real^N^N) (f:real->real->A) S0 J (Z:real->real->real^N).
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        cmp_family (top,atlas) f S0 J /\ cmp_ffield atlas f S0 J Z
        ==> cmp_ffield atlas f S0 J 
              (\s t. mfd_covd atlas g (\s'. f s' t) (\s'. Z s' t) s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[cmp_ffield] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:real->real->A`; `S0:real->bool`; `J:real->bool`;
                 `c:(A->bool)#(A->real^N)`] CMPV_FAMILY_CHART_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `cmp_family (top,atlas:((A->bool)#(A->real^N))->bool) (f:real->real->A) S0 J` THEN
  REWRITE_TAC[cmp_family] THEN STRIP_TAC THEN
  UNDISCH_TAC `cmp_ffield atlas (f:real->real->A) S0 J (Z:real->real->real^N)` THEN
  REWRITE_TAC[cmp_ffield] THEN DISCH_TAC THEN
  ABBREV_TAC `D = {pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\
                   (f:real->real->A) s t IN FST (c:(A->bool)#(A->real^N))}` THEN
  ABBREV_TAC `fc = \z. SND (c:(A->bool)#(A->real^N))
                         ((f:real->real->A) (drop(fstcart z)) (drop(sndcart z)))` THEN
  ABBREV_TAC `Zc = \z. chart_jac (chart_at atlas ((f:real->real->A) (drop(fstcart z))
                                                       (drop(sndcart z))))
                         (c:(A->bool)#(A->real^N)) (f (drop(fstcart z)) (drop(sndcart z)))
                         ((Z:real->real->real^N) (drop(fstcart z)) (drop(sndcart z)))` THEN
  SUBGOAL_THEN `smooth_map_on D (fc:real^(1,1)finite_sum->real^N) /\
                smooth_map_on D (Zc:real^(1,1)finite_sum->real^N)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["D"; "fc"; "Zc"] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND c) (FST c))
                 (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))`
  ASSUME_TAC THENL [ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN D ==> (fc:real^(1,1)finite_sum->real^N) z IN
                               IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["D"; "fc"] THEN
    REWRITE_TAC[FORALL_IN_GSPEC; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `\z. frechet_derivative (Zc:real^(1,1)finite_sum->real^N) (at z)
                    (pastecart (vec 1) (vec 0)) +
                  christoffel (metric_local atlas (c:(A->bool)#(A->real^N))
                                               (g:A->real^N^N))
                    ((fc:real^(1,1)finite_sum->real^N) z)
                    (frechet_derivative fc (at z) (pastecart (vec 1) (vec 0)))
                    (Zc z)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE] THEN
    MATCH_MP_TAC CMPV_CHRISTOFFEL_MOVING THEN
    EXISTS_TAC `IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE]] THEN
  EXPAND_TAC "D" THEN
  REWRITE_TAC[FORALL_IN_GSPEC; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  REPEAT STRIP_TAC THEN MAP_EVERY EXPAND_TAC ["fc"; "Zc"] THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `f:real->real->A`; `Z:real->real->real^N`;
                 `S0:real->bool`; `J:real->bool`; `c:(A->bool)#(A->real^N)`;
                 `s:real`; `t:real`] CMPC_COVD_REP_S) THEN
  ASM_REWRITE_TAC[mfd_field_rep] THEN DISCH_THEN(ACCEPT_TAC o SYM));;


(* ========================================================================= *)
(* The pointwise first and second s-derivatives of the energy                *)
(* density e = <T, T> of a family with geodesic s-curves.                    *)
(* ========================================================================= *)

(* Lines of a family are C1 and smooth fields are differentiable along them. *)

let CMPV_FAMILY_LINES = prove
 (`!top atlas (f:real->real->A) S0 J (Z:real->real->real^N).
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        cmp_family (top,atlas) f S0 J /\ cmp_ffield atlas f S0 J Z
        ==> (!r. r IN S0
                 ==> (!a b. a <= b /\ real_interval[a,b] SUBSET J
                            ==> mfd_c1_curve (top,atlas) (f r) a b) /\
                     mfd_field_diff atlas (f r) (Z r) J) /\
            (!r. r IN J
                 ==> (!a b. a <= b /\ real_interval[a,b] SUBSET S0
                            ==> mfd_c1_curve (top,atlas) (\s. f s r) a b) /\
                     mfd_field_diff atlas (\s. f s r) (\s. Z s r) S0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmp_family; cmp_ffield] THEN STRIP_TAC THEN
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC CMPC_LINE_T_C1 THEN
    MAP_EVERY EXISTS_TAC [`S0:real->bool`; `J:real->bool`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CMPC_LINE_T_FIELD_DIFF THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `S0:real->bool`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CMPC_LINE_S_C1 THEN
    MAP_EVERY EXISTS_TAC [`S0:real->bool`; `J:real->bool`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CMPC_LINE_S_FIELD_DIFF THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `J:real->bool`] THEN ASM_REWRITE_TAC[]]);;

(* d_s <T,T> = 2 <D_t V, T>. *)

let CMPV_DE = prove
 (`!top atlas (g:A->real^N^N) (f:real->real->A) S0 J s t.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        cmp_family (top,atlas) f S0 J /\ s IN S0 /\ t IN J
        ==> ((\r. mfd_vel atlas (f r) t dot (g(f r t) ** mfd_vel atlas (f r) t))
             has_real_derivative
             (&2 * (mfd_covd atlas g (f s) (\t'. mfd_vel atlas (\s'. f s' t') s) t dot
                    (g(f s t) ** mfd_vel atlas (f s) t)))) (atreal s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:real->real->A`; `S0:real->bool`; `J:real->bool`] CMPV_VEL_FIELDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:real->real->A`; `S0:real->bool`; `J:real->bool`;
                 `\s t. mfd_vel (atlas:((A->bool)#(A->real^N))->bool) ((f:real->real->A) s) t`] CMPV_FAMILY_LINES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `cmp_family (top,atlas:((A->bool)#(A->real^N))->bool) (f:real->real->A) S0 J` THEN
  REWRITE_TAC[cmp_family] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `\s'. (f:real->real->A) s' t`; `S0:real->bool`;
                 `\s'. mfd_vel (atlas:((A->bool)#(A->real^N))->bool) ((f:real->real->A) s') t`;
                 `\s'. mfd_vel (atlas:((A->bool)#(A->real^N))->bool) ((f:real->real->A) s') t`; `s:real`]
    MFD_COVD_METRIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MATCH_MP_TAC CMPJ_LIFT_DERIV THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `f:real->real->A`; `S0:real->bool`; `J:real->bool`;
                 `s:real`; `t:real`] MFD_COVD_SYMMETRY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `((f:real->real->A) s t) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[CMPC_PAIR_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(f:real->real->A) s t`] GEOG_G_SYM_POS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `&2 * (mfd_covd atlas (g:A->real^N^N) ((f:real->real->A) s)
            (\t'. mfd_vel atlas (\s'. f s' t') s) t dot
          (g(f s t) ** mfd_vel atlas (f s) t)) =
    mfd_covd atlas g (\s'. f s' t) (\s'. mfd_vel atlas (f s') t) s dot
    (g(f s t) ** mfd_vel atlas (f s) t) +
    mfd_vel atlas (f s) t dot
    (g(f s t) ** mfd_covd atlas g (\s'. f s' t) (\s'. mfd_vel atlas (f s') t) s)`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`mfd_vel (atlas:((A->bool)#(A->real^N))->bool) ((f:real->real->A) s) t`;
      `mfd_covd atlas (g:A->real^N^N) ((f:real->real->A) s)
         (\t'. mfd_vel atlas (\s'. f s' t') s) t`]) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;

(* D_t of a field that vanishes on the open interval J vanishes. *)

let CMPV_COVD_VANISHING = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (X:real->real^N) (Y:real->real^N) t.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        real_open J /\
        (!a b. a <= b /\ real_interval[a,b] SUBSET J
               ==> mfd_c1_curve (top,atlas) gamma a b) /\
        mfd_field_diff atlas gamma Y J /\
        (!s. s IN J ==> X s = vec 0) /\ t IN J
        ==> mfd_covd atlas g gamma X t = vec 0`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `t:real` o GEN_REWRITE_RULE I [real_open]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `mfd_covd atlas (g:A->real^N^N) (gamma:real->A) (X:real->real^N) t =
    mfd_covd atlas g gamma (\s. (\s:real. &0) s % (Y:real->real^N) s) t`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CMPG_COVD_LOCAL THEN EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN REWRITE_TAC[VECTOR_MUL_LZERO] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `Y:real->real^N`;
                 `\s:real. &0`; `&0`; `t:real`] CMPG_COVD_SCALAR) THEN
  ASM_REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID]);;

(* d_s <D_t V, T> = <R(V,T)V, T> + |D_t V|^2 when the s-curves are geodesics. *)

let CMPV_DDE = prove
 (`!top atlas (g:A->real^N^N) (f:real->real->A) S0 J s t.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        cmp_family (top,atlas) f S0 J /\
        (!t. t IN J ==> mfd_geodesic (top,atlas) g (\s'. f s' t) S0) /\
        s IN S0 /\ t IN J
        ==> ((\r. mfd_covd atlas g (f r) (\t'. mfd_vel atlas (\s'. f s' t') r) t dot
                  (g(f r t) ** mfd_vel atlas (f r) t))
             has_real_derivative
             (mfd_riemann atlas g (f s t) (mfd_vel atlas (\s'. f s' t) s)
                          (mfd_vel atlas (f s) t) (mfd_vel atlas (\s'. f s' t) s) dot
              (g(f s t) ** mfd_vel atlas (f s) t) +
              mfd_covd atlas g (f s) (\t'. mfd_vel atlas (\s'. f s' t') s) t dot
              (g(f s t) **
               mfd_covd atlas g (f s) (\t'. mfd_vel atlas (\s'. f s' t') s) t)))
            (atreal s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:real->real->A`; `S0:real->bool`; `J:real->bool`] CMPV_VEL_FIELDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `f:real->real->A`; `S0:real->bool`; `J:real->bool`;
                 `\s t'. mfd_vel (atlas:((A->bool)#(A->real^N))->bool)
                           (\s'. (f:real->real->A) s' t') s`] CMPV_COVD_T_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `cmp_family (top,atlas:((A->bool)#(A->real^N))->bool) (f:real->real->A) S0 J` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(GEN_REWRITE_RULE I [cmp_family] th)) THEN
  (* lines and field differentiability *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:real->real->A`; `S0:real->bool`; `J:real->bool`;
                 `\s t. mfd_covd atlas (g:A->real^N^N) ((f:real->real->A) s)
                          (\t'. mfd_vel atlas (\s'. f s' t') s) t`] CMPV_FAMILY_LINES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:real->real->A`; `S0:real->bool`; `J:real->bool`;
                 `\s t. mfd_vel (atlas:((A->bool)#(A->real^N))->bool)
                          ((f:real->real->A) s) t`] CMPV_FAMILY_LINES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `\s'. (f:real->real->A) s' t`; `S0:real->bool`;
                 `\s'. mfd_covd atlas (g:A->real^N^N) ((f:real->real->A) s')
                         (\t'. mfd_vel atlas (\s'. f s' t') s') t`;
                 `\s'. mfd_vel (atlas:((A->bool)#(A->real^N))->bool)
                         ((f:real->real->A) s') t`; `s:real`]
    MFD_COVD_METRIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "met") THEN MATCH_MP_TAC CMPJ_LIFT_DERIV THEN
  (* D_s T = D_t V *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `f:real->real->A`; `S0:real->bool`; `J:real->bool`;
                 `s:real`; `t:real`] MFD_COVD_SYMMETRY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* the commutator for Z = V *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `f:real->real->A`;
                 `\s t'. mfd_vel (atlas:((A->bool)#(A->real^N))->bool)
                           (\s'. (f:real->real->A) s' t') s`;
                 `S0:real->bool`; `J:real->bool`; `s:real`; `t:real`]
    MFD_COVD_COMMUTATOR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `cmp_ffield (atlas:((A->bool)#(A->real^N))->bool) (f:real->real->A) S0 J
                   (\s t. mfd_vel atlas (\s'. f s' t) s)` THEN
    REWRITE_TAC[cmp_ffield] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `mfd_covd atlas (g:A->real^N^N) ((f:real->real->A) s)
      (\t'. mfd_covd atlas g (\s'. f s' t') (\s'. mfd_vel atlas (\s'. f s' t') s') s) t =
    vec 0`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CMPV_COVD_VANISHING THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `J:real->bool`;
                          `mfd_vel (atlas:((A->bool)#(A->real^N))->bool)
                             ((f:real->real->A) s)`] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `f:real->real->A`; `S0:real->bool`; `J:real->bool`;
                   `\s t. mfd_vel (atlas:((A->bool)#(A->real^N))->bool)
                            ((f:real->real->A) s) t`] CMPV_FAMILY_LINES) THEN
    ASM_REWRITE_TAC[ETA_AX] THEN DISCH_THEN(MP_TAC o SPEC `s:real` o CONJUNCT1) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `r:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `\s'. (f:real->real->A) s' r`; `S0:real->bool`]
      MFD_GEODESIC_VEL_PARALLEL) THEN
    ASM_SIMP_TAC[mfd_parallel];
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_SUB_RZERO] THEN DISCH_TAC THEN
  REMOVE_THEN "met" MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Differentiation under the integral sign.  The three lemmas below are from *)
(* the Navier_Stokes development (github.com/hol-light-family/Navier_Stokes, *)
(* ns_heat_factor.ml: NS_REALLIM_WITHINREAL_SEQUENTIALLY,                    *)
(* NS_IS_REALINTERVAL_BETWEEN, NS_HAS_REAL_DERIVATIVE_INTEGRAL_DOMINATED),   *)
(* here named with CMPV_ in place of NS_; that file is not part of this      *)
(* repository.                                                               *)
(* ========================================================================= *)

let CMPV_REALLIM_WITHINREAL_SEQUENTIALLY = prove
 (`!f:real->real l a s.
        (f ---> l) (atreal a within s) <=>
        !x. (!n. x n IN s DELETE a) /\ (x ---> a) sequentially
            ==> ((f o x) ---> l) sequentially`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REALLIM_WITHINREAL_WITHIN; TENDSTO_REAL; LIM_WITHIN_SEQUENTIALLY] THEN
  GEN_REWRITE_TAC LAND_CONV [FORALL_LIFT_FUN] THEN
  REWRITE_TAC[o_DEF; LIFT_DROP; IN_DELETE; IN_IMAGE_LIFT_DROP; LIFT_EQ]);;

let CMPV_IS_REALINTERVAL_BETWEEN = prove
 (`!s x y d. is_realinterval s /\ x IN s /\ y IN s /\ &0 <= d /\ d <= &1
             ==> x + (y - x) * d IN s`,
  REWRITE_TAC[is_realinterval] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  DISJ_CASES_TAC (REAL_ARITH `x <= y \/ y <= x`) THENL
   [SUBGOAL_THEN `&0 <= (y - x) * d /\ (y - x) * d <= (y - x) * &1`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_LMUL] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`x:real`; `y:real`];
    SUBGOAL_THEN `&0 <= (x - y) * d /\ (x - y) * d <= (x - y) * &1`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_LMUL] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`y:real`; `x:real`]] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Differentiation under the integral sign, general form.  The integrable  *)
(* majorant g bounds the parameter derivative uniformly; s is a real       *)
(* interval with at least two points.                                       *)

let CMPV_HAS_REAL_DERIVATIVE_INTEGRAL_DOMINATED = prove
 (`!f:real->real->real f' g s t.
        is_realinterval s /\
        (!x. x IN s ==> f x real_integrable_on t) /\
        g real_integrable_on t /\
        (!x v. x IN s /\ v IN t
               ==> ((\x. f x v) has_real_derivative f' x v)
                   (atreal x within s)) /\
        (!x v. x IN s /\ v IN t ==> abs(f' x v) <= g v)
        ==> !x. x IN s /\ (?y. y IN s /\ ~(y = x))
                ==> f' x real_integrable_on t /\
                    ((\x. real_integral t (f x)) has_real_derivative
                     real_integral t (f' x)) (atreal x within s)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ivl") (CONJUNCTS_THEN2
    (LABEL_TAC "fint") (CONJUNCTS_THEN2 (LABEL_TAC "gint")
    (CONJUNCTS_THEN2 (LABEL_TAC "der") (LABEL_TAC "bd"))))) THEN
  X_GEN_TAC `x:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `y0:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `!y v. y IN s /\ v IN t
          ==> abs((f:real->real->real) y v - f x v) <= g v * abs(y - x)`
  (LABEL_TAC "lip") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(BETA_RULE(ISPECL
      [`\z. (f:real->real->real) z v`; `\z. (f':real->real->real) z v`;
       `s:real->bool`; `(g:real->real) v`] REAL_DIFFERENTIABLE_BOUND)) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[];
      DISCH_THEN(MP_TAC o SPECL [`y:real`; `x:real`]) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:num->real.
        (!n. y n IN s DELETE x) /\ (y ---> x) sequentially
        ==> (f':real->real->real) x real_integrable_on t /\
            ((\n. (real_integral t ((f:real->real->real) (y n)) -
                   real_integral t (f x)) / (y n - x)) --->
             real_integral t (f' x)) sequentially`
  (LABEL_TAC "seq") THENL
   [X_GEN_TAC `y:num->real` THEN REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!n. (real_integral t ((f:real->real->real) ((y:num->real) n)) -
           real_integral t (f x)) / (y n - x) =
          real_integral t (\v. (f (y n) v - f x v) / (y n - x))`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN REWRITE_TAC[real_div] THEN
      ASM_SIMP_TAC[REAL_INTEGRAL_RMUL; REAL_INTEGRABLE_SUB; REAL_INTEGRAL_SUB;
                   ETA_AX];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`\n v. ((f:real->real->real) ((y:num->real) n) v - f x v) / (y n - x)`;
      `(f':real->real->real) x`; `g:real->real`; `t:real->bool`]
     REAL_DOMINATED_CONVERGENCE) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN REWRITE_TAC[real_div] THEN
      MATCH_MP_TAC REAL_INTEGRABLE_RMUL THEN
      MATCH_MP_TAC REAL_INTEGRABLE_SUB THEN ASM_SIMP_TAC[ETA_AX];
      MAP_EVERY X_GEN_TAC [`n:num`; `v:real`] THEN DISCH_TAC THEN
      REWRITE_TAC[REAL_ABS_DIV] THEN
      SUBGOAL_THEN `&0 < abs(y(n:num) - x)` ASSUME_TAC THENL
       [ASM_MESON_TAC[REAL_ABS_NZ; REAL_SUB_0]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ];
      X_GEN_TAC `v:real` THEN DISCH_TAC THEN
      USE_THEN "der" (MP_TAC o SPECL [`x:real`; `v:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[HAS_REAL_DERIVATIVE_WITHINREAL;
                  CMPV_REALLIM_WITHINREAL_SEQUENTIALLY] THEN
      DISCH_THEN(MP_TAC o SPEC `y:num->real`) THEN
      ASM_REWRITE_TAC[IN_DELETE; o_DEF]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REMOVE_THEN "seq" (MP_TAC o SPEC `\n:num. x + (y0 - x) * inv(&n + &1)`) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    SUBGOAL_THEN `!n. &0 < inv(&n + &1) /\ inv(&n + &1) <= &1`
    ASSUME_TAC THENL
     [GEN_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV; MATCH_MP_TAC REAL_INV_LE_1] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN REWRITE_TAC[IN_DELETE] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CMPV_IS_REALINTERVAL_BETWEEN THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE];
        REWRITE_TAC[REAL_ARITH `x + a = x <=> a = &0`; REAL_ENTIRE] THEN
        ASM_SIMP_TAC[REAL_SUB_0; REAL_LT_IMP_NZ]];
      SUBGOAL_THEN
       `((\n. x + (y0 - x) * inv(&n + &1)) ---> x + &0) sequentially`
      MP_TAC THENL
       [MATCH_MP_TAC REALLIM_ADD THEN REWRITE_TAC[REALLIM_CONST] THEN
        MATCH_MP_TAC REALLIM_NULL_LMUL THEN
        REWRITE_TAC[REALLIM_1_OVER_N_OFFSET];
        REWRITE_TAC[REAL_ADD_RID]]];
    REWRITE_TAC[HAS_REAL_DERIVATIVE_WITHINREAL;
                CMPV_REALLIM_WITHINREAL_SEQUENTIALLY] THEN
    X_GEN_TAC `y:num->real` THEN DISCH_TAC THEN
    REMOVE_THEN "seq" (MP_TAC o SPEC `y:num->real`) THEN
    ASM_REWRITE_TAC[o_DEF] THEN SIMP_TAC[]]);;

(* s-derivatives along lines of a smooth map of (s,t). *)

let CMPV_LINE_DERIV = prove
 (`!O (E:real^(1,1)finite_sum->real^1) s t.
        open O /\ smooth_map_on O E /\ pastecart (lift s) (lift t) IN O
        ==> ((\r. drop(E(pastecart (lift r) (lift t)))) has_real_derivative
             drop(frechet_derivative E (at (pastecart (lift s) (lift t)))
                    (pastecart (vec 1) (vec 0)))) (atreal s)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF; LIFT_DROP; has_vector_derivative] THEN
  ABBREV_TAC `z = pastecart (lift s) (lift t):real^(1,1)finite_sum` THEN
  SUBGOAL_THEN `((E:real^(1,1)finite_sum->real^1) has_derivative frechet_derivative E (at z)) (at (z:real^(1,1)finite_sum))` ASSUME_TAC THENL
   [ASM_MESON_TAC[SMOOTH_MAP_ON_HAS_DERIVATIVE]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [has_derivative]) THEN
  SUBGOAL_THEN
   `(\x:real^1. (E:real^(1,1)finite_sum->real^1) (pastecart x (lift t))) =
    E o (\x. pastecart x (lift t))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\h:real^1. drop h % frechet_derivative (E:real^(1,1)finite_sum->real^1) (at z)
                         (pastecart (vec 1) (vec 0))) =
    frechet_derivative E (at z) o (\h. pastecart h (vec 0))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `h:real^1` THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP LINEAR_CMUL th)]) THEN
    AP_TERM_TAC THEN
    REWRITE_TAC[GSYM PASTECART_CMUL; VECTOR_MUL_RZERO] THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; DROP_VEC; REAL_MUL_RID];
    ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_PASTECART THEN
  REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST]);;

(* Parameter integrals of smooth functions: the s-derivative may be taken  *)
(* under the integral sign.                                                 *)

let CMPV_PARAM_DERIV = prove
 (`!O (E:real^(1,1)finite_sum->real^1) S a b.
        open O /\ smooth_map_on O E /\ real_open S /\ a <= b /\
        (!s t. s IN S /\ t IN real_interval[a,b] ==> pastecart (lift s) (lift t) IN O)
        ==> !s. s IN S
                ==> ((\r. real_integral (real_interval[a,b])
                            (\t. drop(E(pastecart (lift r) (lift t)))))
                     has_real_derivative
                     real_integral (real_interval[a,b])
                       (\t. drop(frechet_derivative E (at (pastecart (lift s) (lift t)))
                                   (pastecart (vec 1) (vec 0))))) (atreal s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `s:real` o GEN_REWRITE_RULE I [real_open]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `d = e / &2` THEN
  SUBGOAL_THEN `&0 < d /\ d < e` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `K = interval[lift(s - d),lift(s + d)] PCROSS interval[lift a,lift b]` THEN
  SUBGOAL_THEN `compact (K:real^(1,1)finite_sum->bool) /\ K SUBSET O` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN SIMP_TAC[COMPACT_PCROSS; COMPACT_INTERVAL] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_PCROSS; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `D1 = \z. frechet_derivative (E:real^(1,1)finite_sum->real^1) (at z)
                         (pastecart (vec 1) (vec 0))` THEN
  SUBGOAL_THEN `smooth_map_on O (D1:real^(1,1)finite_sum->real^1)` ASSUME_TAC THENL
   [EXPAND_TAC "D1" THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE]; ALL_TAC] THEN
  SUBGOAL_THEN `?M. &0 < M /\ !z. z IN K ==> norm((D1:real^(1,1)finite_sum->real^1) z) <= M`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `bounded(IMAGE (D1:real^(1,1)finite_sum->real^1) K)` MP_TAC THENL
     [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `O:real^(1,1)finite_sum->bool` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
      REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\x v. drop((E:real^(1,1)finite_sum->real^1) (pastecart (lift x) (lift v)))`;
    `\x v. drop((D1:real^(1,1)finite_sum->real^1) (pastecart (lift x) (lift v)))`;
    `\v:real. M:real`; `real_interval(s - d,s + d)`; `real_interval[a,b]`]
    CMPV_HAS_REAL_DERIVATIVE_INTEGRAL_DOMINATED) THEN
  REWRITE_TAC[IS_REALINTERVAL_INTERVAL; REAL_INTEGRABLE_CONST] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON; IMAGE_LIFT_REAL_INTERVAL; o_DEF; LIFT_DROP] THEN
      SUBGOAL_THEN
       `(\y:real^1. (E:real^(1,1)finite_sum->real^1) (pastecart (lift x) y)) =
        E o (\y. pastecart (lift x) y)`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
        REWRITE_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `O:real^(1,1)finite_sum->bool` THEN
        ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      MAP_EVERY X_GEN_TAC [`x:real`; `v:real`] THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      EXPAND_TAC "D1" THEN MATCH_MP_TAC CMPV_LINE_DERIV THEN
      EXISTS_TAC `O:real^(1,1)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`x:real`; `v:real`] THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm((D1:real^(1,1)finite_sum->real^1) (pastecart (lift x) (lift v)))` THEN
      REWRITE_TAC[GSYM NORM_1; REAL_LE_REFL] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN EXPAND_TAC "K" THEN
      REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; EXISTS_TAC `s + d / &2` THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  SIMP_TAC[HAS_REAL_DERIVATIVE_WITHIN_REAL_OPEN; REAL_OPEN_REAL_INTERVAL;
           IN_REAL_INTERVAL; REAL_ARITH `&0 < d ==> s - d < s /\ s < s + d`;
           ASSUME `&0 < d`] THEN
  EXPAND_TAC "D1" THEN REWRITE_TAC[ETA_AX]);;

(* ========================================================================= *)
(* The energy of one piece.  The energy density of a family is               *)
(* smooth, so the energy may be differentiated twice under the integral     *)
(* sign; with geodesic s-curves its second s-derivative is                   *)
(* int 2 (<R(V,T)V, T> + |D_t V|^2).                                         *)
(* ========================================================================= *)

let CMPV_ENERGY_SMOOTH = prove
 (`!top atlas (g:A->real^N^N) (f:real->real->A) S0 J.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        cmp_family (top,atlas) f S0 J
        ==> smooth_map_on {pastecart (lift s) (lift t) | s IN S0 /\ t IN J}
              (\z. lift(mfd_vel atlas (f (drop(fstcart z))) (drop(sndcart z)) dot
                        (g(f (drop(fstcart z)) (drop(sndcart z))) **
                         mfd_vel atlas (f (drop(fstcart z))) (drop(sndcart z)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(GEN_REWRITE_RULE I [cmp_family] th)) THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_SIMP_TAC[GEOC_PAIR_DOMAIN_OPEN] THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN MAP_EVERY X_GEN_TAC [`s:real`; `t:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(f:real->real->A) s t IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[CMPC_PAIR_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(f:real->real->A) s t`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((f:real->real->A) s t)` THEN
  STRIP_TAC THEN
  ABBREV_TAC `D = {pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\
                   (f:real->real->A) s t IN FST (c:(A->bool)#(A->real^N))}` THEN
  EXISTS_TAC `D:real^(1,1)finite_sum->bool` THEN
  SUBGOAL_THEN `open (D:real^(1,1)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC CMPV_FAMILY_CHART_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[GEOC_IN_PAIR_SET] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `fc = \z. SND (c:(A->bool)#(A->real^N))
                         ((f:real->real->A) (drop(fstcart z)) (drop(sndcart z)))` THEN
  SUBGOAL_THEN `smooth_map_on D (fc:real^(1,1)finite_sum->real^N)` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["D"; "fc"] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND c) (FST c))
                 (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))`
  ASSUME_TAC THENL [ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC
   `\z. lift(frechet_derivative (fc:real^(1,1)finite_sum->real^N) (at z)
               (pastecart (vec 0) (vec 1)) dot
             (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N) (fc z) **
              frechet_derivative fc (at z) (pastecart (vec 0) (vec 1))))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [EXPAND_TAC "D" THEN
    REWRITE_TAC[FORALL_IN_GSPEC; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    MAP_EVERY X_GEN_TAC [`s':real`; `t':real`] THEN STRIP_TAC THEN
    EXPAND_TAC "fc" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    AP_TERM_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `f:real->real->A`; `S0:real->bool`; `J:real->bool`;
                   `c:(A->bool)#(A->real^N)`; `s':real`; `t':real`] GEOC_VEL_CHART2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
    MATCH_MP_TAC GEOC_BILIN_CHART THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[CMPC_PAIR_IN_TOPSPACE];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE] THEN
  MATCH_MP_TAC LRG_SMOOTH_MATVEC THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE] THEN
  SUBGOAL_THEN
   `(vectorize o (\z. metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)
                        ((fc:real^(1,1)finite_sum->real^N) z))) =
    (vectorize o metric_local atlas c g) o fc`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))` THEN
  UNDISCH_TAC `metric_field (IMAGE (SND c) (FST c))
                 (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))` THEN
  REWRITE_TAC[metric_field] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXPAND_TAC ["D"; "fc"] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC; FSTCART_PASTECART;
              SNDCART_PASTECART; LIFT_DROP] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]);;

(* The variation field V = d_s f and D_t V. *)

let cmp_vfield = new_definition
 `cmp_vfield (atlas:((A->bool)#(A->real^N))->bool) (f:real->real->A) s t =
    mfd_vel atlas (\s'. f s' t) s`;;

let cmp_dtvfield = new_definition
 `cmp_dtvfield (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
               (f:real->real->A) s t =
    mfd_covd atlas g (f s) (\t'. mfd_vel atlas (\s'. f s' t') s) t`;;

(* First and second s-derivatives of the energy of the piece [a,b]. *)

let CMPV_ENERGY_VARIATION = prove
 (`!top atlas (g:A->real^N^N) (f:real->real->A) S0 J a b.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        cmp_family (top,atlas) f S0 J /\
        (!t. t IN J ==> mfd_geodesic (top,atlas) g (\s'. f s' t) S0) /\
        a <= b /\ real_interval[a,b] SUBSET J
        ==> !s. s IN S0
                ==> ((\r. real_integral (real_interval[a,b])
                            (\t. mfd_vel atlas (f r) t dot
                                 (g(f r t) ** mfd_vel atlas (f r) t)))
                     has_real_derivative
                     real_integral (real_interval[a,b])
                       (\t. &2 * (cmp_dtvfield atlas g f s t dot
                                  (g(f s t) ** mfd_vel atlas (f s) t)))) (atreal s) /\
                    ((\r. real_integral (real_interval[a,b])
                            (\t. &2 * (cmp_dtvfield atlas g f r t dot
                                       (g(f r t) ** mfd_vel atlas (f r) t))))
                     has_real_derivative
                     real_integral (real_interval[a,b])
                       (\t. &2 * (mfd_riemann atlas g (f s t) (cmp_vfield atlas f s t)
                                    (mfd_vel atlas (f s) t) (cmp_vfield atlas f s t) dot
                                  (g(f s t) ** mfd_vel atlas (f s) t) +
                                  cmp_dtvfield atlas g f s t dot
                                  (g(f s t) ** cmp_dtvfield atlas g f s t))))
                    (atreal s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(GEN_REWRITE_RULE I [cmp_family] th)) THEN
  REWRITE_TAC[cmp_vfield; cmp_dtvfield] THEN
  ABBREV_TAC `O = {pastecart (lift s) (lift t) | s IN S0 /\ t IN J}` THEN
  ABBREV_TAC
   `E = \z. lift(mfd_vel atlas ((f:real->real->A) (drop(fstcart z))) (drop(sndcart z)) dot
                 ((g:A->real^N^N)(f (drop(fstcart z)) (drop(sndcart z))) **
                  mfd_vel atlas (f (drop(fstcart z))) (drop(sndcart z))))` THEN
  SUBGOAL_THEN `open (O:real^(1,1)finite_sum->bool) /\
                smooth_map_on O (E:real^(1,1)finite_sum->real^1)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "O" THEN MATCH_MP_TAC GEOC_PAIR_DOMAIN_OPEN THEN ASM_REWRITE_TAC[];
      MAP_EVERY EXPAND_TAC ["O"; "E"] THEN MATCH_MP_TAC CMPV_ENERGY_SMOOTH THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s t. s IN S0 /\ t IN J ==> pastecart (lift s) (lift t) IN O`
  ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!r t. drop((E:real^(1,1)finite_sum->real^1) (pastecart (lift r) (lift t))) =
                      mfd_vel atlas ((f:real->real->A) r) t dot
                      ((g:A->real^N^N)(f r t) ** mfd_vel atlas (f r) t)`
  ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
    ALL_TAC] THEN
  (* the first partial *)
  ABBREV_TAC `E2 = \z. frechet_derivative (E:real^(1,1)finite_sum->real^1) (at z)
                         (pastecart (vec 1) (vec 0))` THEN
  SUBGOAL_THEN `smooth_map_on O (E2:real^(1,1)finite_sum->real^1)` ASSUME_TAC THENL
   [EXPAND_TAC "E2" THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s t. s IN S0 /\ t IN J
          ==> drop((E2:real^(1,1)finite_sum->real^1) (pastecart (lift s) (lift t))) =
              &2 * (mfd_covd atlas (g:A->real^N^N) ((f:real->real->A) s)
                      (\t'. mfd_vel atlas (\s'. f s' t') s) t dot
                    (g(f s t) ** mfd_vel atlas (f s) t))`
  (LABEL_TAC "e1") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
    EXISTS_TAC `\r. drop((E:real^(1,1)finite_sum->real^1) (pastecart (lift r) (lift t)))` THEN
    EXISTS_TAC `s:real` THEN CONJ_TAC THENL
     [EXPAND_TAC "E2" THEN MATCH_MP_TAC CMPV_LINE_DERIV THEN
      EXISTS_TAC `O:real^(1,1)finite_sum->bool` THEN ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CMPV_DE THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `S0:real->bool`; `J:real->bool`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the second partial *)
  SUBGOAL_THEN
   `!s t. s IN S0 /\ t IN J
          ==> drop(frechet_derivative (E2:real^(1,1)finite_sum->real^1)
                     (at (pastecart (lift s) (lift t))) (pastecart (vec 1) (vec 0))) =
              &2 * (mfd_riemann atlas (g:A->real^N^N) ((f:real->real->A) s t)
                      (mfd_vel atlas (\s'. f s' t) s) (mfd_vel atlas (f s) t)
                      (mfd_vel atlas (\s'. f s' t) s) dot
                    (g(f s t) ** mfd_vel atlas (f s) t) +
                    mfd_covd atlas g (f s) (\t'. mfd_vel atlas (\s'. f s' t') s) t dot
                    (g(f s t) **
                     mfd_covd atlas g (f s) (\t'. mfd_vel atlas (\s'. f s' t') s) t))`
  (LABEL_TAC "e2") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
    EXISTS_TAC `\r. drop((E2:real^(1,1)finite_sum->real^1) (pastecart (lift r) (lift t)))` THEN
    EXISTS_TAC `s:real` THEN CONJ_TAC THENL
     [MATCH_MP_TAC CMPV_LINE_DERIV THEN EXISTS_TAC `O:real^(1,1)finite_sum->bool` THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `real_open (S0:real->bool)` THEN REWRITE_TAC[real_open] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    EXISTS_TAC `\r. &2 * (mfd_covd atlas (g:A->real^N^N) ((f:real->real->A) r)
                            (\t'. mfd_vel atlas (\s'. f s' t') r) t dot
                          (g(f r t) ** mfd_vel atlas (f r) t))` THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `r:real` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN REWRITE_TAC[] THEN
      USE_THEN "e1" MATCH_MP_TAC THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
      MATCH_MP_TAC CMPV_DDE THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `S0:real->bool`; `J:real->bool`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `!t. t IN real_interval[a,b] ==> (t:real) IN J` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`O:real^(1,1)finite_sum->bool`; `E:real^(1,1)finite_sum->real^1`;
                 `S0:real->bool`; `a:real`; `b:real`] CMPV_PARAM_DERIV) THEN
  MP_TAC(ISPECL [`O:real^(1,1)finite_sum->bool`; `E2:real^(1,1)finite_sum->real^1`;
                 `S0:real->bool`; `a:real`; `b:real`] CMPV_PARAM_DERIV) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `real_integral (real_interval[a,b])
        (\t. &2 * (mfd_covd atlas (g:A->real^N^N) ((f:real->real->A) s)
                     (\t'. mfd_vel atlas (\s'. f s' t') s) t dot
                   (g(f s t) ** mfd_vel atlas (f s) t))) =
      real_integral (real_interval[a,b])
        (\t. drop(frechet_derivative (E:real^(1,1)finite_sum->real^1)
                    (at (pastecart (lift s) (lift t))) (pastecart (vec 1) (vec 0))))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
      USE_THEN "e1" (MP_TAC o SPECL [`s:real`; `t:real`]) THEN
      EXPAND_TAC "E2" THEN ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `real_integral (real_interval[a,b])
      (\t. &2 * (mfd_riemann atlas (g:A->real^N^N) ((f:real->real->A) s t)
                   (mfd_vel atlas (\s'. f s' t) s) (mfd_vel atlas (f s) t)
                   (mfd_vel atlas (\s'. f s' t) s) dot
                 (g(f s t) ** mfd_vel atlas (f s) t) +
                 mfd_covd atlas g (f s) (\t'. mfd_vel atlas (\s'. f s' t') s) t dot
                 (g(f s t) **
                  mfd_covd atlas g (f s) (\t'. mfd_vel atlas (\s'. f s' t') s) t))) =
    real_integral (real_interval[a,b])
      (\t. drop(frechet_derivative (E2:real^(1,1)finite_sum->real^1)
                  (at (pastecart (lift s) (lift t))) (pastecart (vec 1) (vec 0))))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    USE_THEN "e2" MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `real_open (S0:real->bool)` THEN REWRITE_TAC[real_open] THEN
  DISCH_THEN(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  EXISTS_TAC `\r. real_integral (real_interval[a,b])
                    (\t. drop((E2:real^(1,1)finite_sum->real^1)
                                (pastecart (lift r) (lift t))))` THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `r:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_INTEGRAL_EQ THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN USE_THEN "e1" MATCH_MP_TAC THEN ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* The exponential variation exp_{gamma(t)}(s X(t)) of a                     *)
(* smooth field X along a geodesic.                                          *)
(* ========================================================================= *)

(* Smooth vector fields along a curve on an open interval J. *)

let cmp_sfield = new_definition
 `cmp_sfield (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) (J:real->bool)
             (X:real->real^N) <=>
    !c. c IN atlas
        ==> smooth_map_on {lift t | t IN J /\ gamma t IN FST c}
                          (\s. mfd_field_rep atlas gamma X c (drop s))`;;

(* exp in the coordinates of a chart of the tangent bundle. *)

let CMPV_EXP_CHART_EQ = prove
 (`!top atlas (g:A->real^N^N) c (p:A) (w:real^N).
        smooth_manifold_atlas top atlas /\ c IN atlas /\ p IN FST c /\
        p IN topspace top
        ==> (pastecart (SND c p) (chart_jac (chart_at atlas p) c p w) IN
             mfd_exp_chart_dom (top,atlas) g c <=>
             w IN mfd_exp_dom (top,atlas) g p) /\
            mfd_exp_chart (top,atlas) g c
              (pastecart (SND c p) (chart_jac (chart_at atlas p) c p w)) =
            mfd_exp (top,atlas) g p w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) (SND c (p:A)) = p` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
      CHART_INV) THEN
    ASM_SIMP_TAC[PAIR];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `p:A`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `chart_jac (c:(A->bool)#(A->real^N))
       (chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A)) p
       (chart_jac (chart_at atlas p) c p w) = (w:real^N)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A))`;
                   `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A))`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `p:A`] CHART_JAC_INVERSE) THEN
    ASM_REWRITE_TAC[PAIR; IN_INTER; FUN_EQ_THM; o_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[mfd_exp_chart_dom; mfd_exp_chart; IN_ELIM_THM; FSTCART_PASTECART;
                  SNDCART_PASTECART] THEN
  MATCH_MP_TAC(TAUT `a ==> (a /\ b <=> b)`) THEN
  MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]);;

(* A tube around {0} x [a,b] inside an open subset of R^2. *)

let CMPV_TUBE = prove
 (`!O a b.
        open (O:real^(1,1)finite_sum->bool) /\
        (!t. a <= t /\ t <= b ==> pastecart (lift(&0)) (lift t) IN O)
        ==> ?d. &0 < d /\
                !s t. abs s < d /\ a - d < t /\ t < b + d
                      ==> pastecart (lift s) (lift t) IN O`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `b < a` THENL
   [EXISTS_TAC `(a - b) / &2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (\t. pastecart (lift(&0)) (lift t)) (real_interval[a,b])`;
                 `(:real^(1,1)finite_sum) DIFF O`] SEPARATE_COMPACT_CLOSED) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
      SUBGOAL_THEN
       `IMAGE (\t. pastecart (lift(&0)) (lift t)) (real_interval[a,b]) =
        IMAGE (\x:real^1. pastecart (lift(&0)) x) (interval[lift a,lift b])`
      SUBST1_TAC THENL
       [REWRITE_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL; GSYM IMAGE_o; o_DEF]; ALL_TAC] THEN
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN REWRITE_TAC[COMPACT_INTERVAL] THEN
      MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
      REWRITE_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
      ASM_REWRITE_TAC[GSYM OPEN_CLOSED];
      REWRITE_TAC[EXTENSION; IN_INTER; IN_DIFF; IN_UNIV; NOT_IN_EMPTY; IN_IMAGE;
                  IN_REAL_INTERVAL] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e / &2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `t:real`] THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`pastecart (lift(&0)) (lift(max a (min b t)))`; `pastecart (lift s) (lift t)`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; IN_IMAGE; IN_REAL_INTERVAL] THEN
    EXISTS_TAC `max a (min b t)` THEN REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x < e ==> e <= x ==> F`) THEN
  REWRITE_TAC[dist; PASTECART_SUB] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `norm(lift(&0) - lift s) + norm(lift(max a (min b t)) - lift t)` THEN
  REWRITE_TAC[NORM_PASTECART_LE; GSYM LIFT_SUB; NORM_LIFT] THEN
  ASM_REAL_ARITH_TAC);;

(* GEOP_CHART_REP of pc_geo_param for maps from an open subset of any real^M. *)

let CMPV_CHART_REP = prove
 (`!top atlas (Fm:real^M->A) U (c:(A->bool)#(A->real^N)).
        smooth_manifold_atlas top atlas /\ open U /\
        continuous_map (subtopology euclidean U,top) Fm /\
        mfd_smooth_map (open_set_atlas (:real^M)) atlas U Fm /\ c IN atlas
        ==> open {u | u IN U /\ Fm u IN FST c} /\
            smooth_map_on {u | u IN U /\ Fm u IN FST c} (\u. SND c (Fm u))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas euclidean (open_set_atlas (:real^M))`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `(:real^M)` MFD_EUCLIDEAN_OPEN) THEN
    REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV; open_set_atlas] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((:real^M),(\y:real^M. y)) IN open_set_atlas (:real^M)` ASSUME_TAC THENL
   [REWRITE_TAC[open_set_atlas; IN_SING]; ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^M)topology`; `open_set_atlas (:real^M)`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `((:real^M),(\y:real^M. y))`; `c:(A->bool)#(A->real^N)`;
                 `U:real^M->bool`; `Fm:real^M->A`] MFDM_CHART_DOMAIN_OPEN) THEN
  ASM_REWRITE_TAC[GSYM OPEN_IN] THEN
  REWRITE_TAC[FST; SND; IMAGE_ID; INTER_UNIV] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`((:real^M),(\y:real^M. y))`; `c:(A->bool)#(A->real^N)`] o
    GEN_REWRITE_RULE I [mfd_smooth_map] o check (fun th -> can (term_match []
      `mfd_smooth_map (open_set_atlas (:real^M)) (atlas:((A->bool)#(A->real^N))->bool)
                      W (f:real^M->A)`) (concl th))) THEN
  ASM_REWRITE_TAC[FST; SND; IMAGE_ID; INTER_UNIV] THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ] SMOOTH_MAP_ON_EQ) THEN
  SIMP_TAC[IN_ELIM_THM; o_THM; MFDM_CHART_INV_ID; IN_UNIV]);;

(* The coordinate map of the exponential variation in a base chart c. *)

let CMPV_PHI_SMOOTH = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (X:real->real^N) c.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\ cmp_sfield atlas gamma J X /\
        c IN atlas
        ==> open {z:real^(1,1)finite_sum |
                  sndcart z IN {lift t | t IN J /\ gamma t IN FST c}} /\
            smooth_map_on
              {z:real^(1,1)finite_sum | sndcart z IN {lift t | t IN J /\ gamma t IN FST c}}
              (\z. pastecart (SND c (gamma(drop(sndcart z))))
                             (drop(fstcart z) %
                              mfd_field_rep atlas gamma X c (drop(sndcart z))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                 `c:(A->bool)#(A->real^N)`] MFD_GEODESIC_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `I1 = {lift t | t IN J /\ (gamma:real->A) t IN FST (c:(A->bool)#(A->real^N))}` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on I1 (\s. mfd_field_rep atlas (gamma:real->A) (X:real->real^N)
                                        (c:(A->bool)#(A->real^N)) (drop s))`
  ASSUME_TAC THENL
   [EXPAND_TAC "I1" THEN UNDISCH_TAC `cmp_sfield atlas (gamma:real->A) J (X:real->real^N)` THEN
    REWRITE_TAC[cmp_sfield] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open {z:real^(1,1)finite_sum | sndcart z IN I1}` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[LINEAR_CONTINUOUS_AT; LINEAR_SNDCART];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `(\z:real^(1,1)finite_sum. SND (c:(A->bool)#(A->real^N)) ((gamma:real->A) (drop(sndcart z)))) =
      (\s. SND c (gamma(drop s))) o sndcart`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC];
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC GEOF_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[ETA_AX; LINEAR_FSTCART];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\z:real^(1,1)finite_sum. mfd_field_rep atlas (gamma:real->A) (X:real->real^N)
                                  (c:(A->bool)#(A->real^N)) (drop(sndcart z))) =
      (\s. mfd_field_rep atlas gamma X c (drop s)) o sndcart`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC]] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `I1:real^1->bool` THEN
  ASM_REWRITE_TAC[] THEN
  (CONJ_TAC THENL [SET_TAC[]; ALL_TAC]) THEN
  MATCH_MP_TAC GEOF_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[ETA_AX; LINEAR_SNDCART]);;

(* exp_{gamma t}(s X t) through the coordinate map in a base chart c. *)

let CMPV_EXP_VAR_EQ = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) (X:real->real^N) c s t.
        smooth_manifold_atlas top atlas /\ c IN atlas /\ gamma t IN FST c /\
        gamma t IN topspace top
        ==> (pastecart (SND c (gamma t)) (s % mfd_field_rep atlas gamma X c t) IN
             mfd_exp_chart_dom (top,atlas) g c <=>
             s % X t IN mfd_exp_dom (top,atlas) g (gamma t)) /\
            mfd_exp_chart (top,atlas) g c
              (pastecart (SND c (gamma t)) (s % mfd_field_rep atlas gamma X c t)) =
            mfd_exp (top,atlas) g (gamma t) (s % X t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `s % mfd_field_rep atlas (gamma:real->A) (X:real->real^N) c t =
    chart_jac (chart_at atlas (gamma t)) (c:(A->bool)#(A->real^N)) (gamma t) (s % X t)`
  SUBST1_TAC THENL
   [REWRITE_TAC[mfd_field_rep] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC LINEAR_CMUL THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(gamma:real->A) t`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) t))`;
                   `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) t))`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `(gamma:real->A) t`] CHART_JAC_LINEAR) THEN
    ASM_REWRITE_TAC[PAIR; IN_INTER];
    ALL_TAC] THEN
  MATCH_MP_TAC CMPV_EXP_CHART_EQ THEN ASM_REWRITE_TAC[]);;

(* The set of (s,t) with s X(t) in the domain of exp at gamma(t) is open. *)

let CMPV_EXP_DOM_OPEN = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (X:real->real^N).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\ cmp_sfield atlas gamma J X
        ==> open {z:real^(1,1)finite_sum |
                  drop(sndcart z) IN J /\
                  drop(fstcart z) % X(drop(sndcart z)) IN
                  mfd_exp_dom (top,atlas) g (gamma(drop(sndcart z)))}`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[OPEN_SUBOPEN] THEN
  X_GEN_TAC `z0:real^(1,1)finite_sum` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  ABBREV_TAC `t0 = drop(sndcart(z0:real^(1,1)finite_sum))` THEN
  SUBGOAL_THEN `(gamma:real->A) t0 IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[GEOL_GEODESIC_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(gamma:real->A) t0`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) t0)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `X:real->real^N`;
                 `c:(A->bool)#(A->real^N)`] CMPV_PHI_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `D = {z:real^(1,1)finite_sum |
                   sndcart z IN {lift t | t IN J /\ (gamma:real->A) t IN FST (c:(A->bool)#(A->real^N))}}` THEN
  ABBREV_TAC `Phi = \z:real^(1,1)finite_sum.
                      pastecart (SND (c:(A->bool)#(A->real^N)) ((gamma:real->A) (drop(sndcart z))))
                        (drop(fstcart z) % mfd_field_rep atlas gamma (X:real->real^N) c
                                             (drop(sndcart z)))` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `c:(A->bool)#(A->real^N)`] MFD_EXP_CHART_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `{z:real^(1,1)finite_sum | z IN D /\
                (Phi:real^(1,1)finite_sum->real^(N,N)finite_sum) z IN
                mfd_exp_chart_dom (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
                  (g:A->real^N^N) (c:(A->bool)#(A->real^N))}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM; SUBSET] THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "D" THEN REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `t0:real` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "t0" THEN REWRITE_TAC[LIFT_DROP];
      EXPAND_TAC "Phi" THEN REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `gamma:real->A`; `X:real->real^N`;
                     `c:(A->bool)#(A->real^N)`; `drop(fstcart(z0:real^(1,1)finite_sum))`;
                     `t0:real`] CMPV_EXP_VAR_EQ) THEN
      ASM_SIMP_TAC[]];
    X_GEN_TAC `z:real^(1,1)finite_sum` THEN EXPAND_TAC "D" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) MP_TAC) THEN
    SUBGOAL_THEN `drop(sndcart(z:real^(1,1)finite_sum)) = t` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "Phi" THEN REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(gamma:real->A) t IN topspace top` ASSUME_TAC THENL
     [ASM_MESON_TAC[GEOL_GEODESIC_IN_TOPSPACE]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `X:real->real^N`;
                   `c:(A->bool)#(A->real^N)`; `drop(fstcart(z:real^(1,1)finite_sum))`;
                   `t:real`] CMPV_EXP_VAR_EQ) THEN
    ASM_SIMP_TAC[]]);;

(* Local representation of the exponential variation near a time t0.      *)

let CMPV_EXP_FAMILY_LOCAL = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (X:real->real^N) S0 J' t0.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\ cmp_sfield atlas gamma J X /\
        real_open S0 /\ real_open J' /\ J' SUBSET J /\
        (!s t. s IN S0 /\ t IN J' ==> s % X t IN mfd_exp_dom (top,atlas) g (gamma t)) /\
        t0 IN J'
        ==> ?W (Phi:real^(1,1)finite_sum->real^(N,N)finite_sum) c.
                c IN atlas /\ open W /\
                (!s. s IN S0 ==> pastecart (lift s) (lift t0) IN W) /\
                W SUBSET {pastecart (lift s) (lift t) | s IN S0 /\ t IN J'} /\
                smooth_map_on W Phi /\
                (!z. z IN W
                     ==> Phi z IN mfd_exp_chart_dom (top,atlas) g c /\
                         mfd_exp (top,atlas) g (gamma(drop(sndcart z)))
                           (drop(fstcart z) % X(drop(sndcart z))) =
                         mfd_exp_chart (top,atlas) g c (Phi z))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(t0:real) IN J` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) t0 IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[GEOL_GEODESIC_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(gamma:real->A) t0`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) t0)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `X:real->real^N`;
                 `c:(A->bool)#(A->real^N)`] CMPV_PHI_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`{pastecart (lift s) (lift t) | s IN S0 /\ t IN J'} INTER
     {z:real^(1,1)finite_sum |
      sndcart z IN {lift t | t IN J /\ (gamma:real->A) t IN FST (c:(A->bool)#(A->real^N))}}`;
    `\z:real^(1,1)finite_sum.
       pastecart (SND (c:(A->bool)#(A->real^N)) ((gamma:real->A) (drop(sndcart z))))
         (drop(fstcart z) % mfd_field_rep atlas gamma (X:real->real^N) c (drop(sndcart z)))`;
    `c:(A->bool)#(A->real^N)`] THEN
  ASM_REWRITE_TAC[INTER_SUBSET] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_INTER THEN ASM_SIMP_TAC[GEOC_PAIR_DOMAIN_OPEN];
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    REWRITE_TAC[IN_INTER; GEOC_PAIR_DOMAIN_OPEN; IN_ELIM_THM; SNDCART_PASTECART] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; EXISTS_TAC `t0:real` THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `{z:real^(1,1)finite_sum |
                 sndcart z IN {lift t | t IN J /\ (gamma:real->A) t IN
                                        FST (c:(A->bool)#(A->real^N))}}` THEN
    ASM_REWRITE_TAC[INTER_SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `z:real^(1,1)finite_sum` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real` (X_CHOOSE_THEN `t:real`
    STRIP_ASSUME_TAC)) (X_CHOOSE_THEN `t':real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `t':real = t` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `sndcart(z:real^(1,1)finite_sum) = lift t'` THEN
    ASM_REWRITE_TAC[SNDCART_PASTECART; LIFT_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  SUBGOAL_THEN `(gamma:real->A) t IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[GEOL_GEODESIC_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `X:real->real^N`;
                 `c:(A->bool)#(A->real^N)`; `s:real`; `t:real`] CMPV_EXP_VAR_EQ) THEN
  ASM_SIMP_TAC[]);;

(* An open interval containing [a,b] contains a slightly larger one. *)

let CMPV_OPEN_INTERVAL_ROOM = prove
 (`!J a b. real_open J /\ is_realinterval J /\ a <= b /\ real_interval[a,b] SUBSET J
           ==> ?d. &0 < d /\ real_interval(a - d,b + d) SUBSET J`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(a:real) IN J /\ (b:real) IN J` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `a:real` o GEN_REWRITE_RULE I [real_open]) THEN
  FIRST_ASSUM(MP_TAC o SPEC `b:real` o GEN_REWRITE_RULE I [real_open]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eb:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "eb"))) THEN
  DISCH_THEN(X_CHOOSE_THEN `ea:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ea"))) THEN
  EXISTS_TAC `min ea eb` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  ASM_CASES_TAC `x < a` THENL
   [USE_THEN "ea" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `b < x` THENL
   [USE_THEN "eb" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `real_interval[a,b] SUBSET J` THEN
  REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REAL_ARITH_TAC);;

(* Radial geodesics s |-> exp_p(s w) on (-d,d). *)

let CMPV_RADIAL_GEODESIC = prove
 (`!top atlas (g:A->real^N^N) (p:A) (w:real^N) d.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ p IN topspace top /\ &0 < d /\
        (!s. abs s < d ==> s % w IN mfd_exp_dom (top,atlas) g p)
        ==> mfd_geodesic (top,atlas) g (\s. mfd_exp (top,atlas) g p (s % w))
                         (real_interval(--d,d)) /\
            mfd_exp (top,atlas) g p (&0 % w) = p /\
            mfd_vel atlas (\s. mfd_exp (top,atlas) g p (s % w)) (&0) = w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `w:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `M = mfd_geo_maxint (top,atlas) (g:A->real^N^N) p w` THEN
  ABBREV_TAC `gam = mfd_geo (top,atlas) (g:A->real^N^N) p w` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!s. abs s < d ==> s IN M /\ mfd_exp (top,atlas) (g:A->real^N^N) p (s % w) = gam s`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`; `w:real^N`; `s:real`] MFD_EXP_RADIAL) THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_geodesic (top,atlas) (g:A->real^N^N) gam (real_interval(--d,d))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_GEODESIC_SUBINTERVAL THEN EXISTS_TAC `M:real->bool` THEN
    ASM_REWRITE_TAC[IS_REALINTERVAL_INTERVAL; REAL_OPEN_REAL_INTERVAL] THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `{real_interval(--d,d)}`;
                   `\K:real->bool. (gam:real->A)`;
                   `\s. mfd_exp (top,atlas) (g:A->real^N^N) p (s % w)`]
      GEOM_GEODESIC_GLUE) THEN
    REWRITE_TAC[UNIONS_1; IN_SING; FORALL_UNWIND_THM2] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IS_REALINTERVAL_INTERVAL] THEN
    MAP_EVERY X_GEN_TAC [`K:real->bool`; `t:real`] THEN
    DISCH_THEN(fun th -> MP_TAC(CONJUNCT2 th) THEN REWRITE_TAC[CONJUNCT1 th]) THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    FIRST_X_ASSUM(MP_TAC o SPEC `&0`) THEN ASM_REWRITE_TAC[REAL_ABS_0] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_vel atlas (\s. mfd_exp (top,atlas) (g:A->real^N^N) p (s % w)) (&0) =
    mfd_vel atlas (gam:real->A) (&0)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC GEOM_VEL_LOCAL THEN EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `r:real` THEN REWRITE_TAC[REAL_SUB_RZERO] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:real`) THEN ASM_SIMP_TAC[];
    ASM_REWRITE_TAC[]]);;

(* The exponential variation of a smooth field along a geodesic is a       *)
(* smooth family on (-d,d) x (a-d,b+d) with geodesic s-curves, starting at  *)
(* gamma with variation field X.                                             *)

let CMPV_EXP_FAMILY = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (X:real->real^N) a b.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\ cmp_sfield atlas gamma J X /\
        a <= b /\ real_interval[a,b] SUBSET J
        ==> ?d. &0 < d /\ real_interval(a - d,b + d) SUBSET J /\
                cmp_family (top,atlas) (\s t. mfd_exp (top,atlas) g (gamma t) (s % X t))
                           (real_interval(--d,d)) (real_interval(a - d,b + d)) /\
                (!t. t IN real_interval(a - d,b + d)
                     ==> mfd_geodesic (top,atlas) g
                           (\s. mfd_exp (top,atlas) g (gamma t) (s % X t))
                           (real_interval(--d,d)) /\
                         mfd_exp (top,atlas) g (gamma t) (&0 % X t) = gamma t /\
                         mfd_vel atlas (\s. mfd_exp (top,atlas) g (gamma t) (s % X t)) (&0) =
                         X t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GEOL_GEODESIC_BASIC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `X:real->real^N`]
    CMPV_EXP_DOM_OPEN) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`{z:real^(1,1)finite_sum | drop(sndcart z) IN J /\
                    drop(fstcart z) % (X:real->real^N)(drop(sndcart z)) IN
                    mfd_exp_dom (top,atlas) (g:A->real^N^N) ((gamma:real->A)(drop(sndcart z)))}`;
                 `a:real`; `b:real`] CMPV_TUBE) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP;
                  VECTOR_MUL_LZERO] THEN
  ANTS_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(t:real) IN J` ASSUME_TAC THENL
     [UNDISCH_TAC `real_interval[a,b] SUBSET J` THEN
      REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `(gamma:real->A) t`] MFD_EXP_DOM) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[GEOL_GEODESIC_IN_TOPSPACE]; SIMP_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tube")))] THEN
  MP_TAC(ISPECL [`J:real->bool`; `a:real`; `b:real`] CMPV_OPEN_INTERVAL_ROOM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `dd = min d1 d2` THEN
  SUBGOAL_THEN `&0 < dd /\ dd <= d1 /\ dd <= d2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "dd" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `dd:real` THEN
  SUBGOAL_THEN `real_interval(a - dd,b + dd) SUBSET J` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `real_interval(a - d2,b + d2)` THEN
    ASM_REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s t. s IN real_interval(--dd,dd) /\ t IN real_interval(a - dd,b + dd)
          ==> s % (X:real->real^N) t IN
              mfd_exp_dom (top,atlas) (g:A->real^N^N) ((gamma:real->A) t)`
  (LABEL_TAC "dom") THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
    USE_THEN "tube" (MP_TAC o SPECL [`s:real`; `t:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `S1 = real_interval(--dd,dd)` THEN
  ABBREV_TAC `J1 = real_interval(a - dd,b + dd)` THEN
  SUBGOAL_THEN `real_open S1 /\ is_realinterval S1 /\ real_open J1 /\ is_realinterval J1`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["S1"; "J1"] THEN
    REWRITE_TAC[REAL_OPEN_REAL_INTERVAL; IS_REALINTERVAL_INTERVAL];
    ALL_TAC] THEN
  (* the local representations *)
  SUBGOAL_THEN
   `!t0. t0 IN J1
         ==> ?W (Phi:real^(1,1)finite_sum->real^(N,N)finite_sum) c.
                c IN atlas /\ open W /\
                (!s. s IN S1 ==> pastecart (lift s) (lift t0) IN W) /\
                W SUBSET {pastecart (lift s) (lift t) | s IN S1 /\ t IN J1} /\
                smooth_map_on W Phi /\
                (!z. z IN W
                     ==> Phi z IN mfd_exp_chart_dom (top,atlas) (g:A->real^N^N) c /\
                         mfd_exp (top,atlas) g ((gamma:real->A)(drop(sndcart z)))
                           (drop(fstcart z) % (X:real->real^N)(drop(sndcart z))) =
                         mfd_exp_chart (top,atlas) g c (Phi z))`
  (LABEL_TAC "loc") THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC CMPV_EXP_FAMILY_LOCAL THEN
    EXISTS_TAC `J:real->bool` THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN USE_THEN "dom" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* continuity *)
  SUBGOAL_THEN
   `continuous_map
      (subtopology euclidean {pastecart (lift s) (lift t) | s IN S1 /\ t IN J1},top)
      (\z. mfd_exp (top,atlas) (g:A->real^N^N) ((gamma:real->A)(drop(sndcart z)))
             (drop(fstcart z) % (X:real->real^N)(drop(sndcart z))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC TOPC_CONTINUOUS_MAP_LOCAL THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`s0:real`; `t0:real`] THEN STRIP_TAC THEN
    USE_THEN "loc" (MP_TAC o C MP (ASSUME `(t0:real) IN J1`) o SPEC `t0:real`) THEN
    DISCH_THEN(X_CHOOSE_THEN `W:real^(1,1)finite_sum->bool` (X_CHOOSE_THEN
      `Phi:real^(1,1)finite_sum->real^(N,N)finite_sum` (X_CHOOSE_THEN
      `c:(A->bool)#(A->real^N)` STRIP_ASSUME_TAC))) THEN
    EXISTS_TAC `W:real^(1,1)finite_sum->bool` THEN REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `W = {pastecart (lift s) (lift t) | s IN S1 /\ t IN J1} INTER
                        (W:real^(1,1)finite_sum->bool)`
      SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
    SUBGOAL_THEN `{pastecart (lift s) (lift t) | s IN S1 /\ t IN J1} INTER W =
                  (W:real^(1,1)finite_sum->bool)` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
    EXISTS_TAC `mfd_exp_chart (top,atlas) (g:A->real^N^N) (c:(A->bool)#(A->real^N)) o
                (Phi:real^(1,1)finite_sum->real^(N,N)finite_sum)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; o_THM] THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean
                  (mfd_exp_chart_dom (top,atlas) (g:A->real^N^N) (c:(A->bool)#(A->real^N)))` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `c:(A->bool)#(A->real^N)`] MFD_EXP_CHART_SMOOTH) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2] THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[cmp_family] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `c':(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN CONJ_TAC THENL
     [MATCH_MP_TAC GEOC_PAIR_CHART_OPEN THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MFDM_CHART];
      ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN MAP_EVERY X_GEN_TAC [`s0:real`; `t0:real`] THEN
    STRIP_TAC THEN
    USE_THEN "loc" (MP_TAC o C MP (ASSUME `(t0:real) IN J1`) o SPEC `t0:real`) THEN
    DISCH_THEN(X_CHOOSE_THEN `W:real^(1,1)finite_sum->bool` (X_CHOOSE_THEN
      `Phi:real^(1,1)finite_sum->real^(N,N)finite_sum` (X_CHOOSE_THEN
      `c:(A->bool)#(A->real^N)` STRIP_ASSUME_TAC))) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `c:(A->bool)#(A->real^N)`] MFD_EXP_CHART_SMOOTH) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `mfd_exp_chart (top,atlas) (g:A->real^N^N) (c:(A->bool)#(A->real^N))`;
                   `mfd_exp_chart_dom (top,atlas) (g:A->real^N^N) (c:(A->bool)#(A->real^N))`;
                   `c':(A->bool)#(A->real^N)`] CMPV_CHART_REP) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXISTS_TAC `{z:real^(1,1)finite_sum | z IN W /\
                  (Phi:real^(1,1)finite_sum->real^(N,N)finite_sum) z IN
                  {u | u IN mfd_exp_chart_dom (top,atlas) (g:A->real^N^N)
                                                (c:(A->bool)#(A->real^N)) /\
                       mfd_exp_chart (top,atlas) g c u IN FST (c':(A->bool)#(A->real^N))}}` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
      REWRITE_TAC[IN_ELIM_THM] THEN
      SUBGOAL_THEN `pastecart (lift s0) (lift t0) IN (W:real^(1,1)finite_sum->bool)`
      ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN
      FIRST_ASSUM(MP_TAC o C MP
        (ASSUME `pastecart (lift s0) (lift t0) IN (W:real^(1,1)finite_sum->bool)`) o
        SPEC `pastecart (lift s0) (lift t0)`) THEN
      REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
      DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `(\u. SND (c':(A->bool)#(A->real^N))
                       (mfd_exp_chart (top,atlas) (g:A->real^N^N) (c:(A->bool)#(A->real^N)) u)) o
                (Phi:real^(1,1)finite_sum->real^(N,N)finite_sum)` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
      REWRITE_TAC[IN_ELIM_THM; o_THM] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
      EXISTS_TAC `{u | u IN mfd_exp_chart_dom (top,atlas) (g:A->real^N^N)
                                          (c:(A->bool)#(A->real^N)) /\
                       mfd_exp_chart (top,atlas) g c u IN FST (c':(A->bool)#(A->real^N))}` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
        ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
        SET_TAC[];
        MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
        EXISTS_TAC `W:real^(1,1)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]]];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(gamma:real->A) t`; `(X:real->real^N) t`; `dd:real`]
    CMPV_RADIAL_GEODESIC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                            `J:real->bool`] THEN ASM SET_TAC[];
      X_GEN_TAC `s:real` THEN DISCH_TAC THEN USE_THEN "dom" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "S1" THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      ASM_REAL_ARITH_TAC];
    EXPAND_TAC "S1" THEN SIMP_TAC[VECTOR_MUL_LZERO]]);;

(* ========================================================================= *)
(* The second variation of the energy of one piece in terms of               *)
(* the field X: E''(0) = 2 int (|D_t X|^2 - <X, R(X,T)T>).                   *)
(* ========================================================================= *)

(* The index density |D_t X|^2 - <X, R(X,T)T> of a field along a curve.   *)

let cmp_idens = new_definition
 `cmp_idens (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (gamma:real->A)
            (X:real->real^N) t =
    mfd_covd atlas g gamma X t dot (g(gamma t) ** mfd_covd atlas g gamma X t) -
    X t dot (g(gamma t) ** mfd_riemann atlas g (gamma t) (X t) (mfd_vel atlas gamma t)
                                       (mfd_vel atlas gamma t))`;;

(* The covariant derivative depends only on the curve near t. *)

let CMPV_COVD_CURVE_LOCAL = prove
 (`!atlas (g:A->real^N^N) (gamma1:real->A) gamma2 (Y:real->real^N) t d.
        &0 < d /\ (!s. abs(s - t) < d ==> gamma1 s = gamma2 s)
        ==> mfd_covd atlas g gamma1 Y t = mfd_covd atlas g gamma2 Y t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_covd] THEN
  SUBGOAL_THEN `(gamma1:real->A) t = gamma2 t` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gamma1:real->A) t =
                mfd_vel atlas gamma2 t`
  SUBST1_TAC THENL
   [MATCH_MP_TAC GEOM_VEL_LOCAL THEN EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC CMPG_VECTOR_DERIVATIVE_LOCAL THEN EXISTS_TAC `d:real` THEN
  ASM_REWRITE_TAC[mfd_field_rep] THEN X_GEN_TAC `y:real^1` THEN
  REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th
    (ASSUME `abs(drop y - t) < d`)]));;

(* <R(X,T)X, T> = -<X, R(X,T)T>. *)

let CMPV_RIEMANN_SWAP = prove
 (`!top atlas (g:A->real^N^N) x u v.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        riemannian_metric atlas g /\ x IN topspace top
        ==> mfd_riemann atlas g x u v u dot (g x ** v) =
            --(u dot (g x ** mfd_riemann atlas g x u v v))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] GEOG_G_SYM_POS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [CONJUNCT1 th]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] CMPG_LOCAL_METRIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[mfd_riemann] THEN MATCH_MP_TAC LRIEMANN_METRIC_ANTISYM THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                    (FST(chart_at atlas x))` THEN
  ASM_REWRITE_TAC[]);;

(* The energy of a curve on [a,b] (with the two-sided velocity). *)

let cmp_energy = new_definition
 `cmp_energy (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (c:real->A) a b =
    real_integral (real_interval[a,b])
      (\t. mfd_vel atlas c t dot (g(c t) ** mfd_vel atlas c t))`;;

(* The second variation of the energy of one piece of the exponential       *)
(* variation of X along a geodesic.                                          *)

let CMPV_PIECE_VARIATION = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (X:real->real^N) a b.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\ cmp_sfield atlas gamma J X /\
        a <= b /\ real_interval[a,b] SUBSET J
        ==> ?d E1. &0 < d /\ real_interval(a - d,b + d) SUBSET J /\
                   cmp_family (top,atlas)
                     (\s t. mfd_exp (top,atlas) g (gamma t) (s % X t))
                     (real_interval(--d,d)) (real_interval(a - d,b + d)) /\
                   (!t. t IN real_interval(a - d,b + d)
                        ==> mfd_exp (top,atlas) g (gamma t) (&0 % X t) = gamma t) /\
                   (!s. s IN real_interval(--d,d)
                        ==> ((\r. cmp_energy atlas g
                                    (\t. mfd_exp (top,atlas) g (gamma t) (r % X t)) a b)
                             has_real_derivative E1 s) (atreal s)) /\
                   (E1 has_real_derivative
                    real_integral (real_interval[a,b])
                      (\t. &2 * cmp_idens atlas g gamma X t)) (atreal (&0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `X:real->real^N`;
                 `a:real`; `b:real`] CMPV_EXP_FAMILY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!t. t IN real_interval(a - d,b + d)
                    ==> mfd_exp (top,atlas) (g:A->real^N^N) ((gamma:real->A) t)
                          (&0 % (X:real->real^N) t) = gamma t`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `f = \s t. mfd_exp (top,atlas) (g:A->real^N^N) ((gamma:real->A) t)
                          (s % (X:real->real^N) t)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `f:real->real->A`; `real_interval(--d,d)`;
                 `real_interval(a - d,b + d)`; `a:real`; `b:real`]
    CMPV_ENERGY_VARIATION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN DISCH_TAC THEN EXPAND_TAC "f" THEN
      ASM_SIMP_TAC[ETA_AX];
      REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "ev") THEN
  EXISTS_TAC `d:real` THEN
  EXISTS_TAC `\s. real_integral (real_interval[a,b])
                    (\t. &2 * (cmp_dtvfield atlas (g:A->real^N^N) (f:real->real->A) s t dot
                               (g(f s t) ** mfd_vel atlas (f s) t)))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "ev" (MP_TAC o CONJUNCT1 o C MP (ASSUME `s IN real_interval(--d,d)`) o
                   SPEC `s:real`) THEN
    REWRITE_TAC[cmp_energy] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `r:real` THEN
    EXPAND_TAC "f" THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&0:real) IN real_interval(--d,d)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "ev" (MP_TAC o CONJUNCT2 o C MP (ASSUME `(&0:real) IN real_interval(--d,d)`) o
                 SPEC `&0`) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC REAL_INTEGRAL_EQ THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `(t:real) IN real_interval(a - d,b + d)` ASSUME_TAC THENL
   [UNDISCH_TAC `(t:real) IN real_interval[a,b]` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?e. &0 < e /\ !r. abs(r - t) < e ==> r IN real_interval(a - d,b + d)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `real_interval(a - d,b + d)` real_open) THEN
    REWRITE_TAC[REAL_OPEN_REAL_INTERVAL] THEN
    DISCH_THEN(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(LABEL_TAC "near" o check (fun th ->
    try fst(dest_var(fst(dest_forall(concl th)))) = "r" with Failure _ -> false)) THEN
  SUBGOAL_THEN `!r. r IN real_interval(a - d,b + d) ==> (f:real->real->A) (&0) r = gamma r`
  (LABEL_TAC "f0") THENL
   [EXPAND_TAC "f" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real->real->A) (&0) t = gamma t` ASSUME_TAC THENL
   [USE_THEN "f0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) ((f:real->real->A) (&0)) t =
                mfd_vel atlas (gamma:real->A) t`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GEOM_VEL_LOCAL THEN EXISTS_TAC `e:real` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `r:real` THEN DISCH_TAC THEN USE_THEN "f0" MATCH_MP_TAC THEN
    USE_THEN "near" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `cmp_vfield atlas (f:real->real->A) (&0) t = (X:real->real^N) t`
  ASSUME_TAC THENL
   [REWRITE_TAC[cmp_vfield] THEN EXPAND_TAC "f" THEN ASM_SIMP_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cmp_dtvfield atlas (g:A->real^N^N) (f:real->real->A) (&0) t =
    mfd_covd atlas g (gamma:real->A) (X:real->real^N) t`
  ASSUME_TAC THENL
   [REWRITE_TAC[cmp_dtvfield] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `mfd_covd atlas (g:A->real^N^N) ((f:real->real->A) (&0)) (X:real->real^N) t` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CMPG_COVD_LOCAL THEN EXISTS_TAC `e:real` THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `r:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `(r:real) IN real_interval(a - d,b + d)` ASSUME_TAC THENL
       [USE_THEN "near" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "f" THEN ASM_SIMP_TAC[ETA_AX];
      MATCH_MP_TAC CMPV_COVD_CURVE_LOCAL THEN EXISTS_TAC `e:real` THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `r:real` THEN DISCH_TAC THEN USE_THEN "f0" MATCH_MP_TAC THEN
      USE_THEN "near" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[cmp_idens] THEN
  SUBGOAL_THEN `(gamma:real->A) t IN topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                          `J:real->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `real_interval[a,b] SUBSET J` THEN
    UNDISCH_TAC `(t:real) IN real_interval[a,b]` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(gamma:real->A) t`; `(X:real->real^N) t`;
                 `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) t`]
    CMPV_RIEMANN_SWAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;


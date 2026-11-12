(* ========================================================================= *)
(* Unit pc_p2c_flloc (Part 2C, flowlim route): rescaled pulled back view     *)
(* flows in charts.  The general single-flow setting p2cv_one: a regular     *)
(* view V smooth from its initial times, an open set Wb of a base manifold   *)
(* (top,atlas), a diffeomorphism f from Wb onto a region of the slice at t0, *)
(* and a scale q > 0, with the family P s = q (f^* g(t0 + s / q))            *)
(* (p2cv_pb).  Over a working interval [a',b] with a' <= 0 <= b on which     *)
(* IMAGE f Wb persists, the chart representatives of P are local Ricci flows *)
(* (P2CV_LFLOW) with smooth extensions past both ends (P2CV_TOP_EXT,         *)
(* P2CV_BOT_EXT, P2CV_GLUE_EXT, P2CV_EXT), their quadratic forms at two      *)
(* times are comparable under a curvature bound (P2CV_QF_COMPARE,            *)
(* P2CV_QF_ALL), and at a bottom without margin they are local flows from 0  *)
(* (P2CV_LFROM).  For the sequence of MT Prop 5.14 (p2cv_hyp, p2cv_P), each  *)
(* member is a single-flow setting (P2CV_HYP_ONE), with the time-0 clause of *)
(* p2ca_set (P2CV_TIME0) and uniform quadratic-form bounds (P2CV_QF_BOUNDS). *)
(* ========================================================================= *)

needs "src/pc_p2c_flasm.ml";;
needs "src/pc_p2c_vfrom.ml";;
needs "src/pc_p2a_par.ml";;
needs "src/pc_p2b_ltr.ml";;
needs "src/pc_apx_chain.ml";;
needs "src/pc_apx_local.ml";;
needs "src/pc_smt_glue.ml";;
needs "src/pc_rfa_shi328.ml";;
needs "src/pc_rfa_shi329.ml";;

prioritize_real();;
type_invention_error := true;;

(* Parsing abbreviation for the three-dimensional view type. *)

new_type_abbrev("p2cvv3",
  `:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`);;

(* ------------------------------------------------------------------------- *)
(* Regular views.  The standing view facts (p2a_svs), regions                *)
(* of persisting sets (p2a_region of pc_p2a_defs, as P2AB_REGION does for    *)
(* histories), smaller persistence intervals, and the identity maps between *)
(* slices as diffeomorphisms (conjunct 4 of p2c_regular_view inside, and    *)
(* p2cz_from_smooth at an initial slice in which the set is open).  The      *)
(* conjuncts are selected by their shape, not their position.               *)
(* ------------------------------------------------------------------------- *)

let P2CV_RV_SVS = prove
 (`!V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3).
     p2c_regular_view V ==> p2a_svs V`,
  GEN_TAC THEN REWRITE_TAC[p2c_regular_view; p2a_svs; P2A_VIEW_PROJ_3] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN MATCH_MP_TAC MONO_FORALL THEN
  X_GEN_TAC `t:real` THEN
  ASM_CASES_TAC
   `topspace(rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)) t) = {}` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[hausdorff_space] THEN ASM_REWRITE_TAC[NOT_IN_EMPTY]);;

let P2CV_PERSISTS_MONO = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b a' b'.
     rfs_persists V W a b /\ a <= a' /\ b' <= b ==> rfs_persists V W a' b'`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_persists] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

let P2CV_RV_REGION = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b.
     p2c_regular_view V /\ a < b /\ rfs_persists V W a b ==> p2a_region V W a b`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o REWRITE_RULE[p2c_regular_view])
                             STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[p2a_region; P2A_PERSISTS_3; P2A_VIEW_PROJ_3; P2AP_RMETRIC_VFAM;
              P2A_FLOW_UPTO_3] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`W:A->bool`; `a:real`; `b:real`; `s:real`] o
      check (fun th -> can (SPECL [`W:A->bool`; `a:real`; `b:real`; `s:real`]) th)) THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`W:A->bool`; `a:real`; `b:real`] o
      check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "p2c_vflow"
                                                 with Failure _ -> false)) (concl th))) THEN
    ASM_REWRITE_TAC[p2c_vflow] THEN SIMP_TAC[]]);;

(* Identity maps between slices. *)

let P2CV_SLICE_DIFFEO = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b u v.
     p2c_regular_view V /\ p2cz_from_smooth V /\ rfs_persists V W a b /\
     a <= u /\ u < v /\ v <= b /\ (a < u \/ open_in (rfs_vtop V u) W)
     ==> mfd_diffeo (rfs_vtop V u) (rfs_vatlas V u) W (rfs_vtop V v) (rfs_vatlas V v) W
                    (\y:A. y) (\y. y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[p2c_regular_view] o
      check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "p2c_regular_view"
                                                 with Failure _ -> false)) (concl th))) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`W:A->bool`; `a:real`; `v:real`; `u:real`] o
      check (fun th -> can (SPECL [`W:A->bool`; `a:real`; `v:real`; `u:real`]) th)) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC P2CV_PERSISTS_MONO THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    UNDISCH_TAC `p2cz_from_smooth (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                     (real->A->real^3^3))` THEN
    REWRITE_TAC[p2cz_from_smooth] THEN
    DISCH_THEN(MP_TAC o SPECL [`W:A->bool`; `u:real`; `v:real`]) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2CV_PERSISTS_MONO THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[]]);;

(* The slices inside a persistence interval. *)

let P2CV_PERSISTS_AT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b s.
     rfs_persists V W a b /\ a < s /\ s <= b
     ==> smooth_manifold_atlas (rfs_vtop V s) (rfs_vatlas V s) /\
         open_in (rfs_vtop V s) W`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_persists; rfs_vtop; rfs_vatlas] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The hypotheses of MT Prop 5.14 as a predicate (p2cv_hyp;                 *)
(* verbatim from P2C_PROP_5_14_STATEMENT with p2cz_from_smooth added) and    *)
(* the rescaled pulled back metrics p2cv_P of the sequence; the general     *)
(* single-flow setting p2cv_one (a view V, an open set Wb of a base         *)
(* manifold, a diffeomorphism f from Wb onto a region of the slice at t0,   *)
(* a scale q) with its family p2cv_pb, P s = q (f^* g(t0 + s / q)); f as a  *)
(* diffeomorphism into every slice over which IMAGE f Wb persists.          *)
(* ------------------------------------------------------------------------- *)

let p2cv_hyp = new_definition
 `p2cv_hyp (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3))
           (x:num->A) (t:num->real) (Q:num->real) (J:real->bool)
           (top:B topology,atlas:((B->bool)#(B->real^3))->bool) (g0:B->real^3^3) (xl:B)
           (W:num->B->bool) (phi:num->B->A) <=>
    is_realinterval J /\ (&0) IN J /\
    (!a0. a0 IN J /\ (!s. s IN J ==> a0 <= s) ==> a0 = &0) /\
    (!n. p2c_regular_view (V n) /\ p2cz_from_smooth (V n)) /\
    p2c_slice_limit_with V x t Q (top,atlas) g0 xl W phi /\
    (!m a b. real_interval[a,b] SUBSET J
             ==> ?CM N. !n. N <= n
                      ==> (!s. a <= s /\ s <= b
                               ==> IMAGE (phi n) (W m) SUBSET
                                   topspace(rfs_vtop (V n) (t n + s / Q n))) /\
                          rfs_persists (V n) (IMAGE (phi n) (W m))
                                       (t n + a / Q n) (t n + b / Q n) /\
                          !s y. a <= s /\ s <= b /\ y IN IMAGE (phi n) (W m)
                                ==> p3_vrm (V n) (t n + s / Q n) y <= CM * Q n)`;;

let p2cv_P = new_definition
 `p2cv_P (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                 (real->A->real^3^3))
         (t:num->real) (Q:num->real) (atlas:((B->bool)#(B->real^3))->bool)
         (phi:num->B->A) =
    \n s z. Q n %% mfd_pullback_metric atlas (rfs_vatlas (V n) (t n + s / Q n)) (phi n)
                                       (rfs_vmetric (V n) (t n + s / Q n)) z`;;

(* The components of the hypotheses. *)

let P2CV_HYP_BASIC = prove
 (`!V x t Q J (top:B topology) atlas g0 xl W (phi:num->B->A).
     p2cv_hyp V x t Q J (top,atlas) g0 xl W phi
     ==> is_realinterval J /\ (&0) IN J /\
         (!a0. a0 IN J /\ (!s. s IN J ==> a0 <= s) ==> a0 = &0) /\
         (!n. p2c_regular_view (V n) /\ p2cz_from_smooth (V n)) /\
         hausdorff_space top /\ smooth_manifold_atlas top atlas /\ xl IN topspace top /\
         riemannian_metric atlas g0 /\ (!k. &0 < Q k) /\
         (!k. open_in top (W k) /\ xl IN W k /\ compact_in top (top closure_of W k) /\
              top closure_of W k SUBSET W (SUC k)) /\
         UNIONS {W k | k IN (:num)} = topspace top /\
         (!k. phi k xl = x k) /\
         (!k. ?psi. mfd_diffeo top atlas (W k) (rfs_vtop (V k) (t k)) (rfs_vatlas (V k) (t k))
                               (IMAGE (phi k) (W k)) (phi k) psi) /\
         (!K m eta. compact_in top K /\ &0 < eta
                    ==> ?k0. !k. k0 <= k
                                 ==> K SUBSET W k /\
                                     !y. y IN K
                                         ==> lck_dist2 m
                                               (metric_local atlas (chart_at atlas y) g0)
                                               (\z. Q k %%
                                                    rfs_pullback (rfs_vatlas (V k) (t k))
                                                      (phi k o chart_inv (chart_at atlas y))
                                                      (rfs_vmetric (V k) (t k)) z)
                                               (SND(chart_at atlas y) y) < eta) /\
         (!m a b. real_interval[a,b] SUBSET J
                  ==> ?CM N. !n. N <= n
                           ==> (!s. a <= s /\ s <= b
                                    ==> IMAGE (phi n) (W m) SUBSET
                                        topspace(rfs_vtop (V n) (t n + s / Q n))) /\
                               rfs_persists (V n) (IMAGE (phi n) (W m))
                                            (t n + a / Q n) (t n + b / Q n) /\
                               !s y. a <= s /\ s <= b /\ y IN IMAGE (phi n) (W m)
                                     ==> p3_vrm (V n) (t n + s / Q n) y <= CM * Q n)`,
  REWRITE_TAC[p2cv_hyp; p2c_slice_limit_with] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[]);;

(* The exhaustion is increasing. *)

let P2CV_W_MONO = prove
 (`!top (W:num->B->bool) m n.
     (!k. open_in top (W k) /\ top closure_of W k SUBSET W (SUC k)) /\ m <= n
     ==> W m SUBSET W n`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[LE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET_REFL]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_CASES_TAC `m = SUC n` THENL
   [ASM_REWRITE_TAC[SUBSET_REFL]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(W:num->B->bool) n` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `top closure_of (W:num->B->bool) n` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_OF_SUBSET THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET]]);;

(* Order facts of the rescaled times t n + s / Q n. *)

let P2CV_DIV_LZERO = REAL_ARITH `!x. &0 / x = &0`;;

let P2CV_TT_IFF = prove
 (`!tn q. &0 < q
          ==> (!x y. tn + x / q < tn + y / q <=> x < y) /\
              (!x y. tn + x / q <= tn + y / q <=> x <= y) /\
              (!x. tn + x / q < tn <=> x < &0) /\ (!x. tn < tn + x / q <=> &0 < x) /\
              (!x. tn + x / q <= tn <=> x <= &0) /\ (!x. tn <= tn + x / q <=> &0 <= x) /\
              (!x. tn + x / q = tn <=> x = &0) /\ (!x. tn = tn + x / q <=> x = &0) /\
              (!x y. tn + x / q = tn + y / q <=> x = y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!x y. x / q < y / q <=> x < y` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV2_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `!x y. x / q <= y / q <=> x <= y` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV2_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. x / q < &0 <=> x < &0` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_MUL_LZERO]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. &0 < x / q <=> &0 < x` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_MUL_LZERO]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. x / q <= &0 <=> x <= &0` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. &0 <= x / q <=> &0 <= x` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LZERO]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. x / q = &0 <=> x = &0` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_DIV_EQ_0; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `!x y. x / q = y / q <=> x = y` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM REAL_LE_ANTISYM]; ALL_TAC] THEN
  REWRITE_TAC[REAL_LT_LADD; REAL_LE_LADD; REAL_ARITH `tn + z < tn <=> z < &0`;
              REAL_ARITH `tn < tn + z <=> &0 < z`; REAL_ARITH `tn + z <= tn <=> z <= &0`;
              REAL_ARITH `tn <= tn + z <=> &0 <= z`; REAL_ARITH `tn + z = tn <=> z = &0`;
              REAL_ARITH `tn = tn + z <=> z = &0`; REAL_EQ_ADD_LCANCEL] THEN
  ASM_REWRITE_TAC[]);;

(* Identity maps between two slices of a persisting set, either direction. *)

let P2CV_SLICE_DIFFEO2 = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b u v.
     p2c_regular_view V /\ p2cz_from_smooth V /\ rfs_persists V W a b /\
     a <= u /\ u <= b /\ a <= v /\ v <= b /\ ~(u = v) /\ open_in (rfs_vtop V u) W /\
     (v < u ==> a < v)
     ==> mfd_diffeo (rfs_vtop V u) (rfs_vatlas V u) W (rfs_vtop V v) (rfs_vatlas V v) W
                    (\y:A. y) (\y. y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `u < v \/ v < (u:real)` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC P2CV_SLICE_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MFD_DIFFEO_SYM THEN MATCH_MP_TAC P2CV_SLICE_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_SIMP_TAC[]]);;

(* The general single-flow setting and its rescaled pulled back family.   *)

let p2cv_one = new_definition
 `p2cv_one (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
           (top:B topology,atlas:((B->bool)#(B->real^3))->bool) (Wb:B->bool) (f:B->A)
           (t0:real) (q:real) <=>
    p2c_regular_view V /\ p2cz_from_smooth V /\
    hausdorff_space top /\ smooth_manifold_atlas top atlas /\
    open_in top Wb /\ ~(Wb = {}) /\ &0 < q /\
    ?psi. mfd_diffeo top atlas Wb (rfs_vtop V t0) (rfs_vatlas V t0) (IMAGE f Wb) f psi`;;

let p2cv_pb = new_definition
 `p2cv_pb (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
          (t0:real) (q:real) (atlas:((B->bool)#(B->real^3))->bool) (f:B->A) =
    \s z. q %% mfd_pullback_metric atlas (rfs_vatlas V (t0 + s / q)) f
                                   (rfs_vmetric V (t0 + s / q)) z`;;

let p2cv_ov = [`V:p2cvv3`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
               `Wb:B->bool`; `f:B->A`; `t0:real`; `q:real`];;

let P2CV_P_PB = prove
 (`!V t Q (atlas:((B->bool)#(B->real^3))->bool) (phi:num->B->A) n.
     p2cv_P V t Q atlas phi n = p2cv_pb (V n) (t n) (Q n) atlas (phi n)`,
  REWRITE_TAC[p2cv_P; p2cv_pb]);;

let P2CV_ONE_DIFFEO = prove
 (`!(V:p2cvv3) (top:B topology) atlas Wb (f:B->A) t0 q.
     p2cv_one V (top,atlas) Wb f t0 q
     ==> ?psi. mfd_diffeo top atlas Wb (rfs_vtop V t0) (rfs_vatlas V t0) (IMAGE f Wb) f psi`,
  REWRITE_TAC[p2cv_one] THEN MESON_TAC[]);;

let P2CV_ONE_BASIC = prove
 (`!(V:p2cvv3) (top:B topology) atlas Wb (f:B->A) t0 q.
     p2cv_one V (top,atlas) Wb f t0 q
     ==> p2c_regular_view V /\ p2cz_from_smooth V /\
         hausdorff_space top /\ smooth_manifold_atlas top atlas /\
         open_in top Wb /\ ~(Wb = {}) /\ &0 < q /\
         smooth_manifold_atlas (rfs_vtop V t0) (rfs_vatlas V t0) /\
         open_in (rfs_vtop V t0) (IMAGE f Wb)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `psi0:A->B` o MATCH_MP P2CV_ONE_DIFFEO) THEN
  UNDISCH_TAC `p2cv_one (V:p2cvv3) (top:B topology,atlas) Wb (f:B->A) t0 q` THEN
  REWRITE_TAC[p2cv_one] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open_in (rfs_vtop (V:p2cvv3) t0) (IMAGE (f:B->A) Wb)` ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_diffeo]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `V:p2cvv3` P2CV_RV_SVS) THEN
  ASM_REWRITE_TAC[p2a_svs; P2A_VIEW_PROJ_3] THEN
  DISCH_THEN(MP_TAC o SPEC `t0:real`) THEN
  MATCH_MP_TAC(TAUT `p ==> (q /\ (p ==> r /\ s)) ==> r`) THEN
  UNDISCH_TAC `open_in (rfs_vtop (V:p2cvv3) t0) (IMAGE (f:B->A) Wb)` THEN
  DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
  UNDISCH_TAC `~(Wb:B->bool = {})` THEN SET_TAC[]);;

(* f as a diffeomorphism into the slices over which its image persists. *)

let P2CV_PHI_DIFFEO = prove
 (`!(V:p2cvv3) (top:B topology) atlas Wb (f:B->A) t0 q a0 b0 s.
     p2cv_one V (top,atlas) Wb f t0 q /\
     rfs_persists V (IMAGE f Wb) (t0 + a0 / q) (t0 + b0 / q) /\
     a0 <= &0 /\ &0 <= b0 /\ a0 <= s /\ s <= b0 /\ (&0 <= s \/ a0 < s)
     ==> ?psi. mfd_diffeo top atlas Wb (rfs_vtop V (t0 + s / q))
                          (rfs_vatlas V (t0 + s / q)) (IMAGE f Wb) f psi`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_ONE_BASIC) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `psi0:A->B` o MATCH_MP P2CV_ONE_DIFFEO) THEN
  ABBREV_TAC `R = IMAGE (f:B->A) Wb` THEN
  ASM_CASES_TAC `s = &0` THENL
   [ASM_REWRITE_TAC[P2CV_DIV_LZERO; REAL_ADD_RID] THEN
    EXISTS_TAC `psi0:A->B` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t0:real`; `q:real`] P2CV_TT_IFF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (rfs_vtop (V:p2cvv3) (t0 + s / q)) (rfs_vatlas V (t0 + s / q))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_persists (V:p2cvv3) R (t0 + a0 / q) (t0 + b0 / q)` THEN
    SPEC_TAC(`V:p2cvv3`,`VV:p2cvv3`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; rfs_persists; rfs_vtop; rfs_vatlas] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o SPEC `t0 + s / q`) THEN
    ASM_REWRITE_TAC[] THEN TRY(ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_diffeo (rfs_vtop (V:p2cvv3) t0) (rfs_vatlas V t0) R
               (rfs_vtop V (t0 + s / q)) (rfs_vatlas V (t0 + s / q)) R (\y:A. y) (\y. y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2CV_SLICE_DIFFEO2 THEN
    MAP_EVERY EXISTS_TAC [`t0 + a0 / q`; `t0 + b0 / q`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `(psi0:A->B) o (\y:A. y)` THEN
  SUBGOAL_THEN `(f:B->A) = (\y:A. y) o f` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC(INST_TYPE [`:3`,`:N`] MFD_DIFFEO_COMPOSE) THEN
  EXISTS_TAC `rfs_vtop (V:p2cvv3) t0` THEN EXISTS_TAC `rfs_vatlas (V:p2cvv3) t0` THEN
  EXISTS_TAC `R:A->bool` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Chart representatives of p2cv_pb are the rescaled pullbacks              *)
(* rfs_pullback of the view metrics by f o chart_inv c (P2BL_PB_CHART,       *)
(* METRIC_LOCAL_CMUL); the time-0 slices of the sequence are smooth          *)
(* manifolds; each member of the sequence is a single-flow setting           *)
(* (P2CV_HYP_ONE); the time-0 clause of p2ca_set from the slice limit.       *)
(* ------------------------------------------------------------------------- *)

let P2CV_P_CHART = prove
 (`!(V:p2cvv3) (top:B topology) atlas Wb (f:B->A) t0 q s psi c z.
     p2cv_one V (top,atlas) Wb f t0 q /\
     mfd_diffeo top atlas Wb (rfs_vtop V (t0 + s / q))
                (rfs_vatlas V (t0 + s / q)) (IMAGE f Wb) f psi /\
     smooth_manifold_atlas (rfs_vtop V (t0 + s / q))
                           (rfs_vatlas V (t0 + s / q)) /\
     c IN atlas /\ z IN IMAGE (SND c) (FST c INTER Wb)
     ==> metric_local atlas c (p2cv_pb V t0 q atlas f s) z =
         q %% rfs_pullback (rfs_vatlas V (t0 + s / q)) (f o chart_inv c)
                             (rfs_vmetric V (t0 + s / q)) z`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o MATCH_MP P2CV_ONE_BASIC) STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[p2cv_pb; METRIC_LOCAL_CMUL] THEN AP_TERM_TAC THEN REWRITE_TAC[ETA_AX] THEN
  MATCH_MP_TAC P2BL_PB_CHART THEN
  MAP_EVERY EXISTS_TAC
   [`top:B topology`;
    `rfs_vtop (V:p2cvv3) (t0 + s / q)`;
    `(Wb:B->bool)`; `IMAGE (f:B->A) (Wb:B->bool)`; `psi:A->B`] THEN
  ASM_REWRITE_TAC[]);;

let P2CV_SLICE0 = prove
 (`!V x t Q J (top:B topology) atlas g0 xl W (phi:num->B->A) n.
     p2cv_hyp V x t Q J (top,atlas) g0 xl W phi
     ==> smooth_manifold_atlas (rfs_vtop (V n) (t n)) (rfs_vatlas (V n) (t n)) /\
         ?psi. mfd_diffeo top atlas (W n) (rfs_vtop (V n) (t n))
                          (rfs_vatlas (V n) (t n)) (IMAGE (phi n) (W n))
                          (phi n) psi`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP P2CV_HYP_BASIC) THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `psi0:A->B` o SPEC `n:num` o check (fun th ->
    can (find_term (fun t -> try fst(dest_const t) = "mfd_diffeo" with Failure _ -> false))
        (concl th) && is_forall (concl th))) THEN
  CONJ_TAC THENL [ALL_TAC; EXISTS_TAC `psi0:A->B` THEN ASM_REWRITE_TAC[]] THEN
  MP_TAC(SPEC `(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                       (real->A->real^3^3)) n` P2CV_RV_SVS) THEN
  ASM_REWRITE_TAC[p2a_svs; P2A_VIEW_PROJ_3] THEN
  DISCH_THEN(MP_TAC o SPEC `(t:num->real) n`) THEN
  MATCH_MP_TAC(TAUT `p ==> (q /\ (p ==> r /\ s)) ==> r`) THEN
  UNDISCH_TAC `mfd_diffeo (top:B topology) (atlas:((B->bool)#(B->real^3))->bool) ((W:num->B->bool) n)
                 (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)) n) (t n)) (rfs_vatlas (V n) (t n))
                 (IMAGE ((phi:num->B->A) n) (W n)) (phi n) (psi0:A->B)` THEN
  REWRITE_TAC[mfd_diffeo] THEN
  DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1 o CONJUNCT2) THEN
  SUBGOAL_THEN `(phi:num->B->A) n xl IN IMAGE (phi n) ((W:num->B->bool) n)` MP_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_MESON_TAC[]; SET_TAC[]]);;

(* Each member of the sequence is a single-flow setting. *)

let P2CV_HYP_ONE = prove
 (`!V x t Q J (top:B topology) atlas g0 xl W (phi:num->B->A) m n.
     p2cv_hyp V x t Q J (top,atlas) g0 xl W phi /\ m <= n
     ==> p2cv_one (V n) (top,atlas) (W m) (phi n) (t n) (Q n)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o MATCH_MP P2CV_HYP_BASIC) ASSUME_TAC) THEN
  SUBGOAL_THEN `(W:num->B->bool) m SUBSET W n` ASSUME_TAC THENL
   [MATCH_MP_TAC P2CV_W_MONO THEN EXISTS_TAC `top:B topology` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p2cv_one] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `xl:B` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `psi0:A->B` o SPEC `n:num` o check (fun th ->
    can (find_term (fun t -> try fst(dest_const t) = "mfd_diffeo" with Failure _ -> false))
        (concl th) && is_forall (concl th))) THEN
  EXISTS_TAC `psi0:A->B` THEN
  MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN
  MAP_EVERY EXISTS_TAC [`(W:num->B->bool) n`; `IMAGE ((phi:num->B->A) n) ((W:num->B->bool) n)`] THEN
  ASM_REWRITE_TAC[]);;

(* The time-0 clause of p2ca_set. *)

let P2CV_TIME0 = prove
 (`!V x t Q J (top:B topology) atlas g0 xl W (phi:num->B->A).
     p2cv_hyp V x t Q J (top,atlas) g0 xl W phi
     ==> !K m e. compact_in top K /\ &0 < e
                 ==> ?N. !n y. N <= n /\ y IN K
                             ==> lck_dist2 m (metric_local atlas (chart_at atlas y) g0)
                                   (metric_local atlas (chart_at atlas y)
                                      (p2cv_P V t Q atlas phi n (&0)))
                                   (SND(chart_at atlas y) y) < e`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_HYP_BASIC) THEN
  MAP_EVERY X_GEN_TAC [`K:B->bool`; `m:num`; `e:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`K:B->bool`; `m:num`; `e:real`] o check (fun th ->
    can (find_term (fun t -> try fst(dest_const t) = "lck_dist2" with Failure _ -> false))
        (concl th) && is_forall (concl th))) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  DISCH_THEN(LABEL_TAC "N") THEN MAP_EVERY X_GEN_TAC [`n:num`; `y:B`] THEN STRIP_TAC THEN
  USE_THEN "N" (MP_TAC o C MP (ASSUME `N <= n:num`) o SPEC `n:num`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o C MP (ASSUME `(y:B) IN K`) o SPEC `y:B`)) THEN
  MATCH_MP_TAC(REAL_ARITH `x = y ==> y < e ==> x < e`) THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`; `x:num->A`; `t:num->real`; `Q:num->real`;
                 `J:real->bool`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `n:num`]
                P2CV_SLICE0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `psi:A->B`)) THEN
  SUBGOAL_THEN `(y:B) IN topspace (top:B topology)` ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPACT_IN_SUBSET_TOPSPACE; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `y:B`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC LCK_DIST2_LOCAL THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (y:B)))
                    (FST(chart_at (atlas:((B->bool)#(B->real^3))->bool) y) INTER (W:num->B->bool) n)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2CA_CHART_IMAGE_OPEN_C THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EXISTS_TAC `y:B` THEN ASM SET_TAC[];
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN REWRITE_TAC[P2CV_P_PB] THEN
    MP_TAC(ISPECL [`(V:num->p2cvv3) n`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(W:num->B->bool) n`; `(phi:num->B->A) n`; `(t:num->real) n`;
                   `(Q:num->real) n`; `&0`; `psi:A->B`;
                   `chart_at (atlas:((B->bool)#(B->real^3))->bool) (y:B)`; `z:real^3`]
                  P2CV_P_CHART) THEN
    ASM_REWRITE_TAC[P2CV_DIV_LZERO; REAL_ADD_RID] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC P2CV_HYP_ONE THEN
    MAP_EVERY EXISTS_TAC [`x:num->A`; `J:real->bool`; `g0:B->real^3^3`; `xl:B`] THEN
    ASM_REWRITE_TAC[LE_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Parametrizations f o chart_inv c of the view slices on                    *)
(* the chart images of Wb   (MFD_PARAM_CHART_INV, MFD_PARAM_RESTRICT,         *)
(* MFD_PARAM_COMPOSE_DIFFEO), hence metric fields of the chart              *)
(* representatives of p2cv_pb (APX_RFS_PULLBACK_FIELD, LRG_METRIC_FIELD_SCALE). *)
(* ------------------------------------------------------------------------- *)

let P2CV_CHART_PARAM = prove
 (`!(top:B topology) atlas (topX:A topology) (atlasX:((A->bool)#(A->real^3))->bool)
    W W' (f:B->A) f' c.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas topX atlasX /\
     mfd_diffeo top atlas W topX atlasX W' f f' /\ c IN atlas
     ==> mfd_param topX atlasX (IMAGE (SND c) (FST c INTER W)) (f o chart_inv c)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
  MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                        `W:B->bool`; `W':A->bool`; `f':A->B`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN
    EXISTS_TAC `IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c)` THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `FST(c:(B->bool)#(B->real^3))`; `SND(c:(B->bool)#(B->real^3))`]
                    MFD_PARAM_CHART_INV) THEN
      ASM_REWRITE_TAC[PAIR];
      MATCH_MP_TAC P2CA_CHART_IMAGE_OPEN_C THEN
      MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
      ASM_MESON_TAC[mfd_diffeo];
      SET_TAC[]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN ASM_SIMP_TAC[]]);;

(* Metric fields of the chart representatives. *)

let P2CV_P_FIELD = prove
 (`!(V:p2cvv3) (top:B topology) atlas Wb (f:B->A) t0 q s psi c.
     p2cv_one V (top,atlas) Wb f t0 q /\
     mfd_diffeo top atlas Wb (rfs_vtop V (t0 + s / q))
                (rfs_vatlas V (t0 + s / q)) (IMAGE f Wb) f psi /\
     smooth_manifold_atlas (rfs_vtop V (t0 + s / q))
                           (rfs_vatlas V (t0 + s / q)) /\
     c IN atlas
     ==> metric_field (IMAGE (SND c) (FST c INTER Wb))
                      (metric_local atlas c (p2cv_pb V t0 q atlas f s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_ONE_BASIC) THEN
  MATCH_MP_TAC MFDR_METRIC_FIELD_EQ THEN
  EXISTS_TAC `\z. (q:real) %%
                  rfs_pullback (rfs_vatlas (V:p2cvv3) (t0 + s / q))
                               ((f:B->A) o chart_inv c)
                               (rfs_vmetric V (t0 + s / q)) z` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRG_METRIC_FIELD_SCALE THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN
    EXISTS_TAC `rfs_vtop (V:p2cvv3) (t0 + s / q)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(SPEC `(V:p2cvv3)` P2CV_RV_SVS) THEN
      ASM_REWRITE_TAC[p2a_svs; P2A_VIEW_PROJ_3] THEN
      DISCH_THEN(MP_TAC o SPEC `(t0:real) + s / q`) THEN
      MATCH_MP_TAC(TAUT `p ==> (q /\ (p ==> r /\ s)) ==> s`) THEN
      UNDISCH_TAC `mfd_diffeo (top:B topology) (atlas:((B->bool)#(B->real^3))->bool) (Wb:B->bool)
                     (rfs_vtop (V:p2cvv3) (t0 + s / q))
                     (rfs_vatlas V (t0 + s / q)) (IMAGE (f:B->A) (Wb))
                     f (psi:A->B)` THEN
      REWRITE_TAC[mfd_diffeo] THEN
      DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1 o CONJUNCT2) THEN
      UNDISCH_TAC `~(Wb:B->bool = {})` THEN SET_TAC[];
      MATCH_MP_TAC P2CV_CHART_PARAM THEN
      MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                            `IMAGE (f:B->A) (Wb:B->bool)`; `psi:A->B`] THEN
      ASM_REWRITE_TAC[]];
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC P2CV_P_CHART THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `Wb:B->bool`; `psi:A->B`] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The chart representatives of p2cv_P are local Ricci flows.                *)
(* Near a point, phi n o chart_inv c is the region chart parametrization    *)
(* chart_inv (U,psi) of the top slice composed with the chart representative *)
(* h of phi n (MFDR_DIFFEO_CHART_REP); the region chart representatives are *)
(* local Ricci flows (P2A_REGION_LRICCI) equal to the pullbacks by           *)
(* chart_inv (U,psi) (P2AP_VFAM_PULLBACK_LOCAL); pullback by h, union over  *)
(* points, and the affine time change s |-> t n + s / Q n with the factor   *)
(* Q n.                                                                      *)
(* ------------------------------------------------------------------------- *)

let P2CV_FD_LOCAL = prove
 (`!(f:real^N->real^M) g O z.
     open O /\ z IN O /\ (!w. w IN O ==> f w = g w)
     ==> frechet_derivative f (at z) = frechet_derivative g (at z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[frechet_derivative] THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `f':real^N->real^M` THEN
  FIRST_ASSUM(MP_TAC o SPEC `z:real^N` o GEN_REWRITE_RULE I [open_def]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EQ_TAC THEN DISCH_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THENL
   [MAP_EVERY EXISTS_TAC [`f:real^N->real^M`; `d:real`];
    MAP_EVERY EXISTS_TAC [`g:real^N->real^M`; `d:real`]] THEN
  ASM_SIMP_TAC[]);;

let P2CV_RFS_PULLBACK_LOCAL = prove
 (`!atlas (e1:real^N->A) e2 (g:A->real^N^N) O z.
     open O /\ z IN O /\ (!w. w IN O ==> e1 w = e2 w)
     ==> rfs_pullback atlas e1 g z = rfs_pullback atlas e2 g z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_pullback; mpullback] THEN
  SUBGOAL_THEN `(e1:real^N->A) z = e2 z` SUBST1_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((e2:real^N->A) z)) o
                        (e1:real^N->A)) (at z) =
    frechet_derivative (SND(chart_at atlas (e2 z)) o e2) (at z)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC P2CV_FD_LOCAL THEN EXISTS_TAC `O:real^N->bool` THEN
    ASM_SIMP_TAC[o_THM];
    ALL_TAC] THEN
  REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[]);;

(* The affine time change of a local Ricci flow. *)

let P2CV_LRICCI_FLOW_AFFINE = prove
 (`!U t0 q a b (Fm:real->real^N->real^N^N).
     lricci_flow U (t0 + a / q) (t0 + b / q) Fm /\ &0 < q
     ==> lricci_flow U a b (\s y. q %% Fm (t0 + s / q) y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `t0 + a / q`; `t0 + b / q`;
                 `Fm:real->real^N->real^N^N`; `--t0`] P2CH_LRICCI_FLOW_SHIFT) THEN
  ASM_REWRITE_TAC[REAL_ARITH `(t0 + x) + --t0 = x`; REAL_ARITH `s - --t0 = t0 + s`] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a / q`; `b / q`;
                 `\u. (Fm:real->real^N->real^N^N) (t0 + u)`; `q:real`] LRICCI_FLOW_RESCALE) THEN
  ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ]);;

(* ------------------------------------------------------------------------- *)
(* Smooth extensions of the chart representatives past the                  *)
(* ends of a working interval.  The region family at its top slice is its   *)
(* own chart representative (P2CV_VFAM_TOP); near a point the rescaled      *)
(* chart representatives agree with the pullback by the chart transition   *)
(* of the region chart representatives at all times of (a',b]               *)
(* (P2CV_LOCAL_REP); the rfs_flow_upto extension past the top slice then    *)
(* gives local extensions of the time-reversed family, globalized by        *)
(* PDM_UPTO_LOCAL (P2CV_TOP_EXT).                                            *)
(* ------------------------------------------------------------------------- *)

let P2CV_VFAM_TOP = prove
 (`!(V:p2cvv3) W b U (psi:A->real^3) z.
     smooth_manifold_atlas (rfs_vtop V b) (rfs_vatlas V b) /\ open_in (rfs_vtop V b) W /\
     (U,psi) IN rfs_vatlas V b /\ z IN IMAGE psi (U INTER W)
     ==> metric_local (restrict_atlas (rfs_vatlas V b) W) (U INTER W,psi)
                      (p2c_vfam V W b b) z =
         rfs_pullback (rfs_vatlas V b) (chart_inv (U,psi)) (rfs_vmetric V b) z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2c_vfam; ETA_AX] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:p2cvv3) b`; `rfs_vatlas (V:p2cvv3) b`; `U:A->bool`;
                 `psi:A->real^3`; `W:A->bool`; `rfs_vmetric (V:p2cvv3) b`; `z:real^3`]
                P2CF_METRIC_LOCAL_RESTRICT_ON) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CONV_TAC SYM_CONV THEN
  MP_TAC(ISPECL [`rfs_vtop (V:p2cvv3) b`; `rfs_vatlas (V:p2cvv3) b`; `U:A->bool`;
                 `psi:A->real^3`] CHART_INV) THEN
  MP_TAC(ISPECL [`rfs_vtop (V:p2cvv3) b`; `rfs_vatlas (V:p2cvv3) b`; `U:A->bool`;
                 `psi:A->real^3`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(z:real^3) IN IMAGE psi (U:A->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^3) IN IMAGE psi ((U:A->bool) INTER W)` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:p2cvv3) b`; `rfs_vatlas (V:p2cvv3) b`;
                 `rfs_vmetric (V:p2cvv3) b`; `IMAGE (psi:A->real^3) U`;
                 `chart_inv (U:A->bool,psi:A->real^3)`; `U:A->bool`; `psi:A->real^3`;
                 `z:real^3`] APX_RFS_PULLBACK_CHART) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN MATCH_MP_TAC MFD_PARAM_CHART_INV THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC P2CF_MPULLBACK_LOCAL_ID THEN EXISTS_TAC `IMAGE (psi:A->real^3) U` THEN
  ASM_SIMP_TAC[o_THM]);;

(* The region chart representatives below the top slice, given the identity *)
(* diffeomorphism to the top slice (P2BL_PB_CHART).                         *)

let P2CV_VFAM_GEN = prove
 (`!(V:p2cvv3) W b s U (psi:A->real^3) z.
     ~(s = b) /\ smooth_manifold_atlas (rfs_vtop V b) (rfs_vatlas V b) /\
     smooth_manifold_atlas (rfs_vtop V s) (rfs_vatlas V s) /\
     mfd_diffeo (rfs_vtop V s) (rfs_vatlas V s) W (rfs_vtop V b) (rfs_vatlas V b) W
                (\y:A. y) (\y. y) /\
     (U,psi) IN rfs_vatlas V b /\ z IN IMAGE psi (U INTER W)
     ==> metric_local (restrict_atlas (rfs_vatlas V b) W) (U INTER W,psi)
                      (p2c_vfam V W b s) z =
         rfs_pullback (rfs_vatlas V s) (chart_inv (U,psi)) (rfs_vmetric V s) z`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[p2c_vfam; ETA_AX] THEN
  SUBGOAL_THEN `open_in (rfs_vtop (V:p2cvv3) b) W` ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_diffeo]; ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:p2cvv3) b`; `rfs_vatlas (V:p2cvv3) b`; `U:A->bool`;
                 `psi:A->real^3`; `W:A->bool`;
                 `mfd_pullback_metric (rfs_vatlas (V:p2cvv3) b) (rfs_vatlas V s) (\y:A. y)
                                      (rfs_vmetric V s)`; `z:real^3`]
                P2CF_METRIC_LOCAL_RESTRICT_ON) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `chart_inv (U:A->bool,psi:A->real^3) = (\y:A. y) o chart_inv (U,psi)`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF; ETA_AX]; ALL_TAC] THEN
  MATCH_MP_TAC P2BL_PB_CHART THEN
  MAP_EVERY EXISTS_TAC [`rfs_vtop (V:p2cvv3) b`; `rfs_vtop (V:p2cvv3) s`;
                        `W:A->bool`; `W:A->bool`; `\y:A. y`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_DIFFEO_SYM THEN ASM_REWRITE_TAC[]);;

(* Near a point, the chart representatives of p2cv_pb at the times s in      *)
(* (a',b] and at s = 0 are the rescaled pullbacks by the chart transition   *)
(* h of the region chart representatives at the top slice.                  *)

let P2CV_LOCAL_REP = prove
 (`!(V:p2cvv3) (top:B topology) atlas Wb (f:B->A) t0 q a' b c z0.
     p2cv_one V (top,atlas) Wb f t0 q /\
     a' <= &0 /\ &0 <= b /\ a' < b /\
     rfs_persists V (IMAGE f Wb) (t0 + a' / q) (t0 + b / q) /\
     c IN atlas /\ z0 IN IMAGE (SND c) (FST c INTER Wb)
     ==> ?O O' (h:real^3->real^3) h' U (psi:A->real^3).
            open O /\ z0 IN O /\ O SUBSET IMAGE (SND c) (FST c INTER Wb) /\
            (U,psi) IN rfs_vatlas V (t0 + b / q) /\
            diffeomorphism_on O O' h h' /\ O' SUBSET IMAGE psi (U INTER IMAGE f Wb) /\
            !s y. (a' < s \/ s = &0) /\ s <= b /\ y IN O
                  ==> metric_local atlas c (p2cv_pb V t0 q atlas f s) y =
                      q %% mpullback h
                               (metric_local (restrict_atlas (rfs_vatlas V (t0 + b / q))
                                                             (IMAGE f Wb))
                                  (U INTER IMAGE f Wb,psi)
                                  (p2c_vfam V (IMAGE f Wb) (t0 + b / q)
                                            (t0 + s / q))) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_ONE_BASIC) THEN
  SUBGOAL_THEN `&0 < (q:real)` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t0:real`; `q:real`] P2CV_TT_IFF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!s. (a' < s \/ s = &0) /\ s <= b
        ==> smooth_manifold_atlas (rfs_vtop (V:p2cvv3) (t0 + s / q))
                                  (rfs_vatlas V (t0 + s / q)) /\
            ?psi. mfd_diffeo (top:B topology) (atlas:((B->bool)#(B->real^3))->bool) Wb (rfs_vtop V (t0 + s / q))
                             (rfs_vatlas V (t0 + s / q))
                             (IMAGE (f:B->A) (Wb:B->bool)) f psi`
  (LABEL_TAC "sl") THENL
   [X_GEN_TAC `s:real` THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    MATCH_MP_TAC(TAUT `b /\ (b ==> a) ==> a /\ b`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2CV_PHI_DIFFEO THEN
      MAP_EVERY EXISTS_TAC [`a':real`; `b:real`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `psis:A->B`) THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
     [MP_TAC(ISPECL [`(V:p2cvv3)`; `IMAGE (f:B->A) (Wb:B->bool)`;
                     `(t0:real) + a' / q`; `(t0:real) + b / q`;
                     `(t0:real) + s / q`] P2CV_PERSISTS_AT) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[P2CV_DIV_LZERO; REAL_ADD_RID] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. (a' < s \/ s = &0) /\ s < b
        ==> mfd_diffeo (rfs_vtop (V:p2cvv3) (t0 + s / q))
                       (rfs_vatlas V (t0 + s / q))
                       (IMAGE (f:B->A) (Wb:B->bool))
                       (rfs_vtop V (t0 + b / q)) (rfs_vatlas V (t0 + b / q))
                       (IMAGE f Wb) (\y:A. y) (\y. y)`
  (LABEL_TAC "id") THENL
   [X_GEN_TAC `s:real` THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    USE_THEN "sl" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `psis:A->B`)) THEN
    MATCH_MP_TAC P2CV_SLICE_DIFFEO2 THEN
    MAP_EVERY EXISTS_TAC [`(t0:real) + a' / q`; `(t0:real) + b / q`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(ASM_REAL_ARITH_TAC THEN NO_TAC) THEN ASM_MESON_TAC[mfd_diffeo];
    ALL_TAC] THEN
  SUBGOAL_THEN `?xb:B. xb IN FST(c:(B->bool)#(B->real^3)) /\ xb IN (Wb:B->bool) /\
                       SND c xb = z0`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(z0:real^3) IN IMAGE (SND(c:(B->bool)#(B->real^3)))
                                      (FST c INTER (Wb:B->bool))` THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "sl" (MP_TAC o SPEC `b:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `psib:A->B`)) THEN
  ABBREV_TAC `R = IMAGE (f:B->A) (Wb:B->bool)` THEN
  SUBGOAL_THEN `open_in (rfs_vtop (V:p2cvv3) (t0 + b / q)) R` ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_diffeo]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:B->A) xb IN R` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:B->A) xb IN
                topspace (rfs_vtop (V:p2cvv3) (t0 + b / q))`
  ASSUME_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:p2cvv3) (t0 + b / q)`;
                 `rfs_vatlas (V:p2cvv3) (t0 + b / q)`;
                 `(f:B->A) xb`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (rfs_vatlas (V:p2cvv3) (t0 + b / q))
                         ((f:B->A) xb)` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `psi:A->real^3`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(Wb:B->bool)`;
                 `rfs_vtop (V:p2cvv3) (t0 + b / q)`;
                 `rfs_vatlas (V:p2cvv3) (t0 + b / q)`;
                 `R:A->bool`; `(f:B->A)`; `psib:A->B`;
                 `FST(c:(B->bool)#(B->real^3))`; `SND(c:(B->bool)#(B->real^3))`;
                 `U:A->bool`; `psi:A->real^3`] MFDR_DIFFEO_CHART_REP) THEN
  ASM_REWRITE_TAC[PAIR] THEN
  ABBREV_TAC `O = IMAGE (SND(c:(B->bool)#(B->real^3)))
                        {x | x IN FST c INTER (Wb:B->bool) /\ (f:B->A) x IN U}` THEN
  ABBREV_TAC `O' = IMAGE (psi:A->real^3)
                         {y | y IN U INTER R /\ (psib:A->B) y IN FST(c:(B->bool)#(B->real^3))}` THEN
  ABBREV_TAC `h = (psi:A->real^3) o (f:B->A) o chart_inv (c:(B->bool)#(B->real^3))` THEN
  ABBREV_TAC `h' = SND(c:(B->bool)#(B->real^3)) o (psib:A->B) o chart_inv (U:A->bool,psi:A->real^3)` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(O':real^3->bool) SUBSET IMAGE (psi:A->real^3) (U INTER R)` ASSUME_TAC THENL
   [EXPAND_TAC "O'" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open (O:real^3->bool) /\ open (O':real^3->bool) /\
                IMAGE (h:real^3->real^3) O = O'`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on (O:real^3->bool) O' (h:real^3->real^3) h'` THEN
    SIMP_TAC[diffeomorphism_on];
    ALL_TAC] THEN
  SUBGOAL_THEN `(O':real^3->bool) SUBSET IMAGE (psi:A->real^3) U` ASSUME_TAC THENL
   [UNDISCH_TAC `(O':real^3->bool) SUBSET IMAGE (psi:A->real^3) (U INTER R)` THEN SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`O:real^3->bool`; `O':real^3->bool`; `h:real^3->real^3`;
                        `h':real^3->real^3`; `U:A->bool`; `psi:A->real^3`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [EXPAND_TAC "O" THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
    EXISTS_TAC `xb:B` THEN ASM_REWRITE_TAC[];
    EXPAND_TAC "O" THEN SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  USE_THEN "sl" (MP_TAC o SPEC `s:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `psis:A->B`)) THEN
  MP_TAC(ISPECL [`V:p2cvv3`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `Wb:B->bool`; `f:B->A`; `t0:real`; `q:real`; `s:real`; `psis:A->B`; `c:(B->bool)#(B->real^3)`; `y:real^3`]
                P2CV_P_CHART) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(y:real^3) IN O` THEN EXPAND_TAC "O" THEN SET_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN
   `!w. w IN O ==> ((f:B->A) o chart_inv (c:(B->bool)#(B->real^3))) w =
                   (chart_inv (U:A->bool,psi:A->real^3) o (h:real^3->real^3)) w`
  ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN EXPAND_TAC "h" THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER; o_THM] THEN
    X_GEN_TAC `xx:B` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`rfs_vtop (V:p2cvv3) (t0 + b / q)`;
                   `rfs_vatlas (V:p2cvv3) (t0 + b / q)`;
                   `U:A->bool`; `psi:A->real^3`] CHART_INV) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_param (rfs_vtop (V:p2cvv3) (t0 + s / q)) (rfs_vatlas V (t0 + s / q))
              O' (chart_inv (U:A->bool,psi:A->real^3))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `mfd_param (rfs_vtop (V:p2cvv3) (t0 + b / q))
                (rfs_vatlas V (t0 + b / q)) O' (chart_inv (U:A->bool,psi:A->real^3))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `IMAGE (psi:A->real^3) U` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_PARAM_CHART_INV THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `s:real = b` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MFD_PARAM_EQ THEN
    EXISTS_TAC `(\y:A. y) o chart_inv (U:A->bool,psi:A->real^3)` THEN
    ASM_REWRITE_TAC[o_THM] THEN
    MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`rfs_vtop (V:p2cvv3) (t0 + b / q)`;
                          `rfs_vatlas (V:p2cvv3) (t0 + b / q)`;
                          `R:A->bool`; `R:A->bool`; `\y:A. y`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_DIFFEO_SYM THEN USE_THEN "id" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `(O':real^3->bool) SUBSET IMAGE (psi:A->real^3) (U INTER R)` THEN
      MP_TAC(ISPECL [`rfs_vtop (V:p2cvv3) (t0 + b / q)`;
                     `rfs_vatlas (V:p2cvv3) (t0 + b / q)`;
                     `U:A->bool`; `psi:A->real^3`] CHART_INV) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `rfs_pullback (rfs_vatlas (V:p2cvv3) (t0 + s / q))
                (chart_inv (U:A->bool,psi:A->real^3) o (h:real^3->real^3))
                (rfs_vmetric V (t0 + s / q)) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2CV_RFS_PULLBACK_LOCAL THEN EXISTS_TAC `O:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:p2cvv3) (t0 + s / q)`;
                 `rfs_vatlas (V:p2cvv3) (t0 + s / q)`;
                 `rfs_vmetric (V:p2cvv3) (t0 + s / q)`; `O':real^3->bool`;
                 `chart_inv (U:A->bool,psi:A->real^3)`; `O:real^3->bool`;
                 `h:real^3->real^3`; `h':real^3->real^3`; `y:real^3`]
                APX_RFS_PULLBACK_PRECOMP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(h:real^3->real^3) y IN IMAGE (psi:A->real^3) (U INTER R)` ASSUME_TAC THENL
   [UNDISCH_TAC `(O':real^3->bool) SUBSET IMAGE (psi:A->real^3) (U INTER R)` THEN
    UNDISCH_TAC `IMAGE (h:real^3->real^3) O = O'` THEN
    UNDISCH_TAC `(y:real^3) IN O` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `rfs_pullback (rfs_vatlas (V:p2cvv3) (t0 + s / q))
                 (chart_inv (U:A->bool,psi:A->real^3))
                 (rfs_vmetric V (t0 + s / q)) ((h:real^3->real^3) y) =
    metric_local (restrict_atlas (rfs_vatlas V (t0 + b / q)) R) (U INTER R,psi)
                 (p2c_vfam V R (t0 + b / q) (t0 + s / q)) (h y)`
  ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN ASM_CASES_TAC `s:real = b` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC P2CV_VFAM_TOP THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2CV_VFAM_GEN THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "id" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ASM_REWRITE_TAC[mpullback]]);;

(* The chart representatives of p2cv_pb are local Ricci flows (the region    *)
(* chart representatives are, LRG_RICCI_FLOW_ON_CHART; pullback by h, the   *)
(* affine time change, and the union over points).                          *)

let P2CV_LFLOW = prove
 (`!(V:p2cvv3) (top:B topology) atlas Wb (f:B->A) t0 q a' b c.
     p2cv_one V (top,atlas) Wb f t0 q /\
     a' <= &0 /\ &0 <= b /\ a' < b /\
     rfs_persists V (IMAGE f Wb) (t0 + a' / q) (t0 + b / q) /\
     c IN atlas
     ==> lricci_flow (IMAGE (SND c) (FST c INTER Wb)) a' b
                     (\s. metric_local atlas c (p2cv_pb V t0 q atlas f s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_ONE_BASIC) THEN
  SUBGOAL_THEN `&0 < (q:real)` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t0:real`; `q:real`] P2CV_TT_IFF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC RFA_LRICCI_FLOW_UNION THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2CA_CHART_IMAGE_OPEN_C THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `z0:real^3` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`V:p2cvv3`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `Wb:B->bool`; `f:B->A`; `t0:real`; `q:real`; `a':real`; `b:real`; `c:(B->bool)#(B->real^3)`; `z0:real^3`]
                P2CV_LOCAL_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `O:real^3->bool` (X_CHOOSE_THEN `O':real^3->bool`
    (X_CHOOSE_THEN `h:real^3->real^3` (X_CHOOSE_THEN `h':real^3->real^3`
    (X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `psi:A->real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rep"))))))))))))) THEN
  EXISTS_TAC `O:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `R = IMAGE (f:B->A) (Wb:B->bool)` THEN
  SUBGOAL_THEN `p2a_region (V:p2cvv3) R (t0 + a' / q) (t0 + b / q)`
  ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN MATCH_MP_TAC P2CV_RV_REGION THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open (O':real^3->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on (O:real^3->bool) O' (h:real^3->real^3) h'` THEN
    SIMP_TAC[diffeomorphism_on];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lricci_flow (IMAGE (psi:A->real^3) (U INTER R)) (t0 + a' / q) (t0 + b / q)
      (\u. metric_local (restrict_atlas (rfs_vatlas (V:p2cvv3) (t0 + b / q)) R)
                        (U INTER R,psi) (p2c_vfam V R (t0 + b / q) u))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(V:p2cvv3)`; `R:A->bool`; `(t0:real) + a' / q`;
                   `(t0:real) + b / q`] P2AP_REGION_UPTO) THEN
    ASM_REWRITE_TAC[rfs_flow_upto] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
    MP_TAC(ISPECL [`subtopology (rfs_vtop (V:p2cvv3) (t0 + b / q)) R`;
                   `restrict_atlas (rfs_vatlas (V:p2cvv3) (t0 + b / q)) R`;
                   `(t0:real) + a' / q`; `(t0:real) + b / q`;
                   `p2c_vfam (V:p2cvv3) R (t0 + b / q)`;
                   `(U INTER R:A->bool,psi:A->real^3)`] LRG_RICCI_FLOW_ON_CHART) THEN
    ASM_REWRITE_TAC[FST; SND] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[restrict_atlas; IN_ELIM_THM; PAIR_EQ] THEN
    MAP_EVERY EXISTS_TAC [`U:A->bool`; `psi:A->real^3`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lricci_flow (O:real^3->bool) (t0 + a' / q) (t0 + b / q)
      (\u. mpullback (h:real^3->real^3)
             (metric_local (restrict_atlas (rfs_vatlas (V:p2cvv3) (t0 + b / q)) R)
                           (U INTER R,psi:A->real^3) (p2c_vfam V R (t0 + b / q) u)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LRICCI_FLOW_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`O':real^3->bool`; `h':real^3->real^3`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFA_LRICCI_FLOW_SUBSET THEN
    EXISTS_TAC `IMAGE (psi:A->real^3) (U INTER R)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`O:real^3->bool`; `(t0:real)`; `(q:real)`; `a':real`; `b:real`;
                 `\u. mpullback (h:real^3->real^3)
                        (metric_local (restrict_atlas (rfs_vatlas (V:p2cvv3)
                                                                   (t0 + b / q)) R)
                                      (U INTER R,psi:A->real^3)
                                      (p2c_vfam V R (t0 + b / q) u))`]
                P2CV_LRICCI_FLOW_AFFINE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC RFA_LRICCI_FLOW_EQ THEN
  EXISTS_TAC `\s y. (q:real) %%
                    (\u. mpullback (h:real^3->real^3)
                           (metric_local (restrict_atlas (rfs_vatlas (V:p2cvv3)
                                                                      (t0 + b / q)) R)
                                         (U INTER R,psi:A->real^3)
                                         (p2c_vfam V R (t0 + b / q) u)))
                    (t0 + s / q) y` THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  USE_THEN "rep" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Smoothness of the affine time change of space-time points. *)

let P2CV_SMOOTH_TIME_AFFINE = prove
 (`!t0 q. smooth_map_on (:real^(1,N)finite_sum)
            (\v. pastecart (lift(t0 + --(drop(fstcart v)) / q)) (sndcart v:real^N))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `(\v. pastecart (lift(t0 + --(drop(fstcart v)) / q)) (sndcart v:real^N)) =
    (\v. pastecart (lift t0) (vec 0) +
         (\w:real^(1,N)finite_sum. pastecart ((--inv q) % fstcart w) (sndcart w)) v)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; PASTECART_ADD; VECTOR_ADD_LID] THEN GEN_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM DROP_EQ; DROP_ADD; DROP_CMUL; LIFT_DROP; real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST] THEN
  SUBGOAL_THEN
   `(\w:real^(1,N)finite_sum. pastecart ((--inv q) % fstcart w) (sndcart w)) =
    (\w:real^(1,N)finite_sum. pastecart ((--inv q) % fstcart w) (sndcart w)) o (\w. w)`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF; ETA_AX]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
  REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID] THEN
  REWRITE_TAC[linear; FSTCART_ADD; SNDCART_ADD; FSTCART_CMUL; SNDCART_CMUL;
              PASTECART_ADD; GSYM PASTECART_CMUL] THEN
  REPEAT STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN VECTOR_ARITH_TAC);;

(* The time-reversed chart representatives extend smoothly past the top     *)
(* time (rfs_flow_upto of the region family, PDM_UPTO_LOCAL).               *)

let P2CV_TOP_EXT = prove
 (`!(V:p2cvv3) (top:B topology) atlas Wb (f:B->A) t0 q a' b c.
     p2cv_one V (top,atlas) Wb f t0 q /\
     a' <= &0 /\ &0 <= b /\ a' < b /\
     rfs_persists V (IMAGE f Wb) (t0 + a' / q) (t0 + b / q) /\
     c IN atlas
     ==> pde_upto (--b) (--a') (IMAGE (SND c) (FST c INTER Wb))
           (\s y. (vectorize:real^3^3->real^(3,3)finite_prod)
                    (metric_local atlas c (p2cv_pb V t0 q atlas f (--s)) y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_ONE_BASIC) THEN
  SUBGOAL_THEN `&0 < (q:real)` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t0:real`; `q:real`] P2CV_TT_IFF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC PDM_UPTO_LOCAL THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2CA_CHART_IMAGE_OPEN_C THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
    ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `z0:real^3` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`V:p2cvv3`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `Wb:B->bool`; `f:B->A`; `t0:real`; `q:real`; `a':real`; `b:real`; `c:(B->bool)#(B->real^3)`; `z0:real^3`]
                P2CV_LOCAL_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `O:real^3->bool` (X_CHOOSE_THEN `O':real^3->bool`
    (X_CHOOSE_THEN `h:real^3->real^3` (X_CHOOSE_THEN `h':real^3->real^3`
    (X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `psi:A->real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rep"))))))))))))) THEN
  EXISTS_TAC `O:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `R = IMAGE (f:B->A) (Wb:B->bool)` THEN
  MP_TAC(ISPECL [`(V:p2cvv3)`; `R:A->bool`; `(t0:real) + a' / q`;
                 `(t0:real) + b / q`; `(t0:real) + b / q`] P2CV_PERSISTS_AT) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2a_region (V:p2cvv3) R (t0 + a' / q) (t0 + b / q)`
  ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN MATCH_MP_TAC P2CV_RV_REGION THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(V:p2cvv3)`; `R:A->bool`; `(t0:real) + a' / q`;
                 `(t0:real) + b / q`] P2AP_REGION_UPTO) THEN
  ASM_REWRITE_TAC[rfs_flow_upto] THEN
  DISCH_THEN(MP_TAC o SPEC `(U INTER R:A->bool,psi:A->real^3)` o last o CONJUNCTS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[restrict_atlas; IN_ELIM_THM; PAIR_EQ] THEN
    MAP_EVERY EXISTS_TAC [`U:A->bool`; `psi:A->real^3`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FST; SND] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN
    `Fx:real^(1,3)finite_sum->real^(3,3)finite_prod`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fx"))))) THEN
  SUBGOAL_THEN `open (O:real^3->bool) /\ open (O':real^3->bool) /\
                IMAGE (h:real^3->real^3) O = O' /\ smooth_map_on O h`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on (O:real^3->bool) O' (h:real^3->real^3) h'` THEN
    SIMP_TAC[diffeomorphism_on];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (psi:A->real^3) (U INTER R))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`rfs_vtop (V:p2cvv3) (t0 + b / q)`;
                   `rfs_vatlas (V:p2cvv3) (t0 + b / q)`;
                   `U:A->bool`; `psi:A->real^3`; `U INTER R:A->bool`] CHART_IMAGE_OPEN) THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART];
    ALL_TAC] THEN
  REWRITE_TAC[pde_upto] THEN EXISTS_TAC `e * (q:real)` THEN
  EXISTS_TAC
   `\w:real^(1,3)finite_sum.
      (q:real) %
      (vectorize:real^3^3->real^(3,3)finite_prod)
        (mpullback (h:real^3->real^3)
           (\z. (matrify:real^(3,3)finite_prod->real^3^3)
                  ((Fx:real^(1,3)finite_sum->real^(3,3)finite_prod)
                     (pastecart (lift((t0:real) + --(drop(fstcart w)) / q)) z)))
           (sndcart w))` THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL];
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL]; ALL_TAC] THEN
    MP_TAC(ISPECL [`interval(lift(--b - e * (q:real)),lift(--a'))`;
                   `O:real^3->bool`; `O':real^3->bool`; `h:real^3->real^3`;
                   `(Fx:real^(1,3)finite_sum->real^(3,3)finite_prod) o
                    (\v:real^(1,3)finite_sum.
                       pastecart (lift((t0:real) + --(drop(fstcart v)) / q))
                                 (sndcart v))`] PDM_MPULLBACK_SMOOTH_ST) THEN
    REWRITE_TAC[o_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[OPEN_INTERVAL; SUBSET_REFL] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `interval(lift((t0:real) + a' / q),lift((t0 + b / q) + e)) PCROSS
                IMAGE (psi:A->real^3) (U INTER R)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; PASTECART_IN_PCROSS;
                  FSTCART_PASTECART; SNDCART_PASTECART; IN_INTERVAL_1; LIFT_DROP] THEN
      MAP_EVERY X_GEN_TAC [`u:real^1`; `y:real^3`] THEN STRIP_TAC THEN
      CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      SUBGOAL_THEN `--(drop u) / (q:real) < b / q + e /\
                    a' / q < --(drop u) / q`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ADD_RDISTRIB; REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN
          ASM_REAL_ARITH_TAC;
          ASM_SIMP_TAC[REAL_LT_DIV2_EQ] THEN ASM_REAL_ARITH_TAC];
        ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `(:real^(1,3)finite_sum)` THEN
      REWRITE_TAC[SUBSET_UNIV; P2CV_SMOOTH_TIME_AFFINE]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN STRIP_TAC THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  USE_THEN "rep" (MP_TAC o SPECL [`--s:real`; `y:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[VECTORIZE_CMUL] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[mpullback] THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `(h:real^3->real^3) y IN IMAGE (psi:A->real^3) (U INTER R)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  USE_THEN "fx" (MP_TAC o SPECL [`(t0:real) + --s / q`; `(h:real^3->real^3) y`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MATRIFY_VECTORIZE]);;

(* ------------------------------------------------------------------------- *)
(* The bottom extension at an initial slice (the region family               *)
(* is ricci_flow_from at the slice t0, by conjunct 3 of the regular views,   *)
(* since IMAGE f Wb is open there), and the gluing of a bottom and a top     *)
(* extension into one smooth extension past both ends.                       *)
(* ------------------------------------------------------------------------- *)

let P2CV_SMOOTH_TIME_AFFINE_POS = prove
 (`!t0 q. smooth_map_on (:real^(1,N)finite_sum)
            (\v. pastecart (lift(t0 + drop(fstcart v) / q)) (sndcart v:real^N))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `(\v. pastecart (lift(t0 + drop(fstcart v) / q)) (sndcart v:real^N)) =
    (\v. pastecart (lift t0) (vec 0) +
         (\w:real^(1,N)finite_sum. pastecart (inv q % fstcart w) (sndcart w)) v)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; PASTECART_ADD; VECTOR_ADD_LID] THEN GEN_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM DROP_EQ; DROP_ADD; DROP_CMUL; LIFT_DROP; real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST] THEN
  SUBGOAL_THEN
   `(\w:real^(1,N)finite_sum. pastecart (inv q % fstcart w) (sndcart w)) =
    (\w:real^(1,N)finite_sum. pastecart (inv q % fstcart w) (sndcart w)) o (\w. w)`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF; ETA_AX]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
  REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID] THEN
  REWRITE_TAC[linear; FSTCART_ADD; SNDCART_ADD; FSTCART_CMUL; SNDCART_CMUL;
              PASTECART_ADD; GSYM PASTECART_CMUL] THEN
  REPEAT STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN VECTOR_ARITH_TAC);;

(* The chart representatives extend smoothly below the time-0 slice. *)

let P2CV_BOT_EXT = prove
 (`!(V:p2cvv3) (top:B topology) atlas Wb (f:B->A) t0 q b c.
     p2cv_one V (top,atlas) Wb f t0 q /\ &0 < b /\
     rfs_persists V (IMAGE f Wb) (t0 + &0 / q) (t0 + b / q) /\
     c IN atlas
     ==> pde_upto (&0) b (IMAGE (SND c) (FST c INTER Wb))
           (\s y. (vectorize:real^3^3->real^(3,3)finite_prod)
                    (metric_local atlas c (p2cv_pb V t0 q atlas f s) y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_ONE_BASIC) THEN
  SUBGOAL_THEN `&0 < (q:real)` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t0:real`; `q:real`] P2CV_TT_IFF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC PDM_UPTO_LOCAL THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2CA_CHART_IMAGE_OPEN_C THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `z0:real^3` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`V:p2cvv3`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `Wb:B->bool`; `f:B->A`; `t0:real`; `q:real`; `&0`; `b:real`; `c:(B->bool)#(B->real^3)`; `z0:real^3`]
                P2CV_LOCAL_REP) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `O:real^3->bool` (X_CHOOSE_THEN `O':real^3->bool`
    (X_CHOOSE_THEN `h:real^3->real^3` (X_CHOOSE_THEN `h':real^3->real^3`
    (X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `psi:A->real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rep"))))))))))))) THEN
  EXISTS_TAC `O:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`V:p2cvv3`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `Wb:B->bool`; `f:B->A`; `t0:real`; `q:real`; `&0`; `b:real`; `&0`] P2CV_PHI_DIFFEO) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `psi0:A->B`) THEN
  ABBREV_TAC `R = IMAGE (f:B->A) (Wb:B->bool)` THEN
  SUBGOAL_THEN `open_in (rfs_vtop (V:p2cvv3) (t0 + &0 / q)) R` ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_diffeo]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ricci_flow_from (subtopology (rfs_vtop (V:p2cvv3) (t0 + b / q)) R,
                     restrict_atlas (rfs_vatlas V (t0 + b / q)) R)
                    (t0 + &0 / q) (t0 + b / q)
                    (p2c_vfam V R (t0 + b / q))`
  MP_TAC THENL
   [SUBGOAL_THEN `p2c_vflow_from (V:p2cvv3) R (t0 + &0 / q) (t0 + b / q)`
    MP_TAC THENL
     [UNDISCH_TAC `p2c_regular_view (V:p2cvv3)` THEN REWRITE_TAC[p2c_regular_view] THEN
      DISCH_THEN(MP_TAC o SPECL [`R:A->bool`; `(t0:real) + &0 / q`;
                                 `(t0:real) + b / q`] o
                 CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[];
      SIMP_TAC[p2c_vflow_from]];
    ALL_TAC] THEN
  REWRITE_TAC[ricci_flow_from] THEN
  DISCH_THEN(MP_TAC o SPEC `(U INTER R:A->bool,psi:A->real^3)` o last o CONJUNCTS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[restrict_atlas; IN_ELIM_THM; PAIR_EQ] THEN
    MAP_EVERY EXISTS_TAC [`U:A->bool`; `psi:A->real^3`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FST; SND] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN
    `Fx:real^(1,3)finite_sum->real^(3,3)finite_prod`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fx"))))) THEN
  SUBGOAL_THEN `open (O:real^3->bool) /\ open (O':real^3->bool) /\
                IMAGE (h:real^3->real^3) O = O' /\ smooth_map_on O h`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on (O:real^3->bool) O' (h:real^3->real^3) h'` THEN
    SIMP_TAC[diffeomorphism_on];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (psi:A->real^3) (U INTER R))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`rfs_vtop (V:p2cvv3) (t0 + b / q)`;
                   `rfs_vatlas (V:p2cvv3) (t0 + b / q)`;
                   `U:A->bool`; `psi:A->real^3`; `U INTER R:A->bool`] CHART_IMAGE_OPEN) THEN
    MP_TAC(ISPECL [`(V:p2cvv3)`; `R:A->bool`; `(t0:real) + &0 / q`;
                   `(t0:real) + b / q`; `(t0:real) + b / q`]
                  P2CV_PERSISTS_AT) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART];
    ALL_TAC] THEN
  REWRITE_TAC[pde_upto] THEN EXISTS_TAC `e * (q:real)` THEN
  EXISTS_TAC
   `\w:real^(1,3)finite_sum.
      (q:real) %
      (vectorize:real^3^3->real^(3,3)finite_prod)
        (mpullback (h:real^3->real^3)
           (\z. (matrify:real^(3,3)finite_prod->real^3^3)
                  ((Fx:real^(1,3)finite_sum->real^(3,3)finite_prod)
                     (pastecart (lift((t0:real) + drop(fstcart w) / q)) z)))
           (sndcart w))` THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL];
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL]; ALL_TAC] THEN
    MP_TAC(ISPECL [`interval(lift(&0 - e * (q:real)),lift b)`;
                   `O:real^3->bool`; `O':real^3->bool`; `h:real^3->real^3`;
                   `(Fx:real^(1,3)finite_sum->real^(3,3)finite_prod) o
                    (\v:real^(1,3)finite_sum.
                       pastecart (lift((t0:real) + drop(fstcart v) / q)) (sndcart v))`]
                  PDM_MPULLBACK_SMOOTH_ST) THEN
    REWRITE_TAC[o_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[OPEN_INTERVAL; SUBSET_REFL] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `interval(lift(((t0:real) + &0 / q) - e),lift(t0 + b / q)) PCROSS
                IMAGE (psi:A->real^3) (U INTER R)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; PASTECART_IN_PCROSS;
                  FSTCART_PASTECART; SNDCART_PASTECART; IN_INTERVAL_1; LIFT_DROP] THEN
      MAP_EVERY X_GEN_TAC [`u:real^1`; `y:real^3`] THEN STRIP_TAC THEN
      CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      SUBGOAL_THEN `--e < drop u / (q:real) /\ drop u / q < b / q`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
          ASM_SIMP_TAC[REAL_LT_DIV2_EQ] THEN ASM_REAL_ARITH_TAC];
        REWRITE_TAC[P2CV_DIV_LZERO] THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `(:real^(1,3)finite_sum)` THEN
      REWRITE_TAC[SUBSET_UNIV; P2CV_SMOOTH_TIME_AFFINE_POS]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN STRIP_TAC THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  USE_THEN "rep" (MP_TAC o SPECL [`s:real`; `y:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[VECTORIZE_CMUL] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[mpullback] THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `(h:real^3->real^3) y IN IMAGE (psi:A->real^3) (U INTER R)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  USE_THEN "fx" (MP_TAC o SPECL [`(t0:real) + s / q`; `(h:real^3->real^3) y`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MATRIFY_VECTORIZE]);;

(* Gluing a bottom and a top extension. *)

let P2CV_OPEN_TIME_GT = prove
 (`!c. open {w:real^(1,N)finite_sum | c < drop(fstcart w)}`,
  GEN_TAC THEN
  SUBGOAL_THEN `{w:real^(1,N)finite_sum | c < drop(fstcart w)} =
                {w | fstcart w IN {x:real^1 | x$1 > c}}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; drop] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
  REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT] THEN
  GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN REWRITE_TAC[LINEAR_FSTCART]);;

let P2CV_GLUE_EXT = prove
 (`!(U:real^N->bool) a b e1 e2 (F1:real^(1,N)finite_sum->real^K) F2 (u:real->real^N->real^K).
     open U /\ a < b /\ &0 < e1 /\ &0 < e2 /\
     smooth_map_on (interval(lift(a - e1),lift b) PCROSS U) F1 /\
     smooth_map_on (interval(lift a,lift(b + e2)) PCROSS U) F2 /\
     (!t y. a <= t /\ t < b /\ y IN U ==> F1(pastecart (lift t) y) = u t y) /\
     (!t y. a < t /\ t <= b /\ y IN U ==> F2(pastecart (lift t) y) = u t y)
     ==> ?e FF. &0 < e /\
                smooth_map_on (interval(lift(a - e),lift(b + e)) PCROSS U) FF /\
                !t y. a <= t /\ t <= b /\ y IN U ==> FF(pastecart (lift t) y) = u t y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "a1") (LABEL_TAC "a2")))))))) THEN
  SUBGOAL_THEN
   `!w:real^(1,N)finite_sum. a < drop(fstcart w) /\ drop(fstcart w) < b /\ sndcart w IN U
                             ==> (F1:real^(1,N)finite_sum->real^K) w = F2 w`
  (LABEL_TAC "a12") THENL
   [GEN_TAC THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN
    GEN_REWRITE_TAC (BINOP_CONV o RAND_CONV o LAND_CONV) [GSYM LIFT_DROP] THEN
    USE_THEN "a1" (fun th -> USE_THEN "a2" (fun th' ->
      ASM_SIMP_TAC[th; th'; REAL_LT_IMP_LE]));
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < min e1 e2 /\ min e1 e2 <= e1 /\ min e1 e2 <= e2` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[real_min] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `min e1 e2` THEN
  EXISTS_TAC `\w:real^(1,N)finite_sum.
                if drop(fstcart w) < (a + b) / &2 then (F1:real^(1,N)finite_sum->real^K) w
                else F2 w` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; FORALL_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    MAP_EVERY X_GEN_TAC [`u0:real^1`; `y0:real^N`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `drop u0 < b` THENL
     [EXISTS_TAC `interval(lift(a - e1),lift b) PCROSS (U:real^N->bool)` THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                   LIFT_DROP] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC TEXT_SMOOTH_MAP_ON_EQ_OPEN THEN
      EXISTS_TAC `F1:real^(1,N)finite_sum->real^K` THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; FORALL_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP;
                   FSTCART_PASTECART; SNDCART_PASTECART] THEN
      MAP_EVERY X_GEN_TAC [`u:real^1`; `y:real^N`] THEN STRIP_TAC THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      USE_THEN "a12" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN ASM_REAL_ARITH_TAC;
      EXISTS_TAC `{w:real^(1,N)finite_sum | (a + b) / &2 < drop(fstcart w)} INTER
                  (interval(lift a,lift(b + e2)) PCROSS (U:real^N->bool))` THEN
      ASM_SIMP_TAC[OPEN_INTER; OPEN_PCROSS; OPEN_INTERVAL; P2CV_OPEN_TIME_GT] THEN
      ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP;
                      FSTCART_PASTECART] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC TEXT_SMOOTH_MAP_ON_EQ_OPEN THEN
      EXISTS_TAC `F2:real^(1,N)finite_sum->real^K` THEN
      ASM_SIMP_TAC[OPEN_INTER; OPEN_PCROSS; OPEN_INTERVAL; P2CV_OPEN_TIME_GT] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
        EXISTS_TAC `interval(lift a,lift(b + e2)) PCROSS (U:real^N->bool)` THEN
        ASM_REWRITE_TAC[INTER_SUBSET];
        REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `w:real^(1,N)finite_sum` THEN
        STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]];
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
    REWRITE_TAC[FSTCART_PASTECART; LIFT_DROP] THEN COND_CASES_TAC THENL
     [USE_THEN "a1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      USE_THEN "a2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Comparison of the quadratic forms of the chart                           *)
(* representatives at two times of (a',b] under a curvature bound, from     *)
(* P2AP_METRIC_COMPARE for the region family at the top slice, read through *)
(* the time-independent chart Jacobians (P2CV_ML_QF_MONO, LRG_MPULLBACK_DOT). *)
(* ------------------------------------------------------------------------- *)

let P2CV_ML_QF_MONO = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) c (g1:A->real^N^N) g2 C z w.
     (!u. u dot (g1 (chart_inv c z) ** u) <= C * (u dot (g2 (chart_inv c z) ** u)))
     ==> w dot (metric_local atlas c g1 z ** w) <= C * (w dot (metric_local atlas c g2 z ** w))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[metric_local] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
  FIRST_X_ASSUM MATCH_ACCEPT_TAC);;

let P2CV_EXP_ARITH = prove
 (`!CM q t0 b s. ~(q = &0)
                 ==> &4 * (CM * q) * ((t0 + b / q) - (t0 + s / q)) = &4 * CM * (b - s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ARITH `(t0 + x) - (t0 + y) = x - y`] THEN
  REWRITE_TAC[real_div; GSYM REAL_SUB_RDISTRIB] THEN
  REWRITE_TAC[REAL_ARITH `&4 * (CM * q) * x * y = (&4 * CM * x) * (q * y)`] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_MUL_RID]);;

(* A bound at the rescaled times s gives the bound at the view times. *)

let P2CV_CURV_VIEW = prove
 (`!(f:real->A->real) tn q a b K (R:A->bool).
     &0 < q /\ (!s z. a <= s /\ s <= b /\ z IN R ==> f (tn + s / q) z <= K)
     ==> !tt z. tn + a / q < tt /\ tt <= tn + b / q /\ z IN R ==> f tt z <= K`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`(tt - tn) * q`; `z:A`]) THEN
  SUBGOAL_THEN `tn + ((tt - tn) * q) / q = tt` SUBST1_TAC THENL
   [ASM_SIMP_TAC[REAL_FIELD `~(q = &0) ==> tn + ((tt - tn) * q) / q = tt`; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `tn + a / q < tt` THEN UNDISCH_TAC `tt <= tn + b / q` THEN
  REWRITE_TAC[REAL_ARITH `tt <= tn + x <=> tt - tn <= x`;
              REAL_ARITH `tn + x < tt <=> x < tt - tn`] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_LDIV_EQ] THEN REAL_ARITH_TAC);;

let P2CV_QF_COMPARE = prove
 (`!(V:p2cvv3) (top:B topology) atlas Wb (f:B->A) t0 q a' b c CM y v s1 s2.
     p2cv_one V (top,atlas) Wb f t0 q /\
     a' <= &0 /\ &0 <= b /\ a' < b /\ &0 <= CM /\
     rfs_persists V (IMAGE f Wb) (t0 + a' / q) (t0 + b / q) /\
     (!s z. a' <= s /\ s <= b /\ z IN IMAGE f Wb
            ==> p3_vrm V (t0 + s / q) z <= CM * q) /\
     c IN atlas /\ y IN IMAGE (SND c) (FST c INTER Wb) /\
     a' < s1 /\ s1 <= b /\ a' < s2 /\ s2 <= b
     ==> v dot (metric_local atlas c (p2cv_pb V t0 q atlas f s1) y ** v) <=
         exp(&8 * CM * (b - a')) *
         (v dot (metric_local atlas c (p2cv_pb V t0 q atlas f s2) y ** v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_ONE_BASIC) THEN
  SUBGOAL_THEN `&0 < (q:real)` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t0:real`; `q:real`] P2CV_TT_IFF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2cvv3`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `Wb:B->bool`; `f:B->A`; `t0:real`; `q:real`; `a':real`; `b:real`; `c:(B->bool)#(B->real^3)`; `y:real^3`]
                P2CV_LOCAL_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `O:real^3->bool` (X_CHOOSE_THEN `O':real^3->bool`
    (X_CHOOSE_THEN `h:real^3->real^3` (X_CHOOSE_THEN `h':real^3->real^3`
    (X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `psi:A->real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rep"))))))))))))) THEN
  ABBREV_TAC `R = IMAGE (f:B->A) (Wb:B->bool)` THEN
  SUBGOAL_THEN `p2a_region (V:p2cvv3) R (t0 + a' / q) (t0 + b / q)`
  ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN MATCH_MP_TAC P2CV_RV_REGION THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `p2a_svs (V:p2cvv3)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2CV_RV_SVS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open (O:real^3->bool) /\ IMAGE (h:real^3->real^3) O = O' /\
                smooth_map_on O h`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on (O:real^3->bool) O' (h:real^3->real^3) h'` THEN
    SIMP_TAC[diffeomorphism_on];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(frechet_derivative (h:real^3->real^3) (at y))` ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `O:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^3->real^3) y IN IMAGE (psi:A->real^3) (U INTER R)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `chart_inv (U INTER R:A->bool,psi:A->real^3) ((h:real^3->real^3) y) IN U INTER R`
  ASSUME_TAC THENL
   [REWRITE_TAC[chart_inv; FST; SND] THEN
    SUBGOAL_THEN `?x:A. x IN U INTER R /\ psi x = (h:real^3->real^3) y` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SELECT_RULE) THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `w = frechet_derivative (h:real^3->real^3) (at y) v` THEN
  ABBREV_TAC `L = \s. metric_local (restrict_atlas (rfs_vatlas (V:p2cvv3)
                                                    (t0 + b / q)) R)
                                   (U INTER R,psi:A->real^3)
                                   (p2c_vfam (V:p2cvv3) R (t0 + b / q) (t0 + s / q))` THEN
  SUBGOAL_THEN
   `!s. a' < s /\ s <= b
        ==> v dot (metric_local (atlas:((B->bool)#(B->real^3))->bool) (c:(B->bool)#(B->real^3)) (p2cv_pb (V:p2cvv3) t0 q (atlas:((B->bool)#(B->real^3))->bool) (f:B->A) s) y ** v) =
            (q:real) * (w dot ((L:real->real^3->real^3^3) s ((h:real^3->real^3) y) ** w))`
  (LABEL_TAC "qf") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "rep" (MP_TAC o SPECL [`s:real`; `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL] THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`h:real^3->real^3`;
                   `(L:real->real^3->real^3^3) s`; `y:real^3`; `v:real^3`; `v:real^3`]
                  LRG_MPULLBACK_DOT) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "L" THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\tt (z:A). p3_vrm (V:p2cvv3) tt z`; `(t0:real)`;
                 `(q:real)`; `a':real`; `b:real`; `CM * (q:real)`; `R:A->bool`]
                P2CV_CURV_VIEW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[] THEN DISCH_TAC] THEN
  SUBGOAL_THEN
   `!s. a' < s /\ s <= b
        ==> w dot ((L:real->real^3->real^3^3) s ((h:real^3->real^3) y) ** w) <=
            exp(&4 * CM * (b - s)) * (w dot (L b (h y) ** w)) /\
            w dot (L b (h y) ** w) <= exp(&4 * CM * (b - s)) * (w dot (L s (h y) ** w))`
  (LABEL_TAC "cmp") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN EXPAND_TAC "L" THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`(V:p2cvv3)`; `R:A->bool`; `(t0:real) + a' / q`;
                   `(t0:real) + b / q`; `CM * (q:real)`;
                   `(t0:real) + s / q`;
                   `chart_inv (U INTER R:A->bool,psi:A->real^3) ((h:real^3->real^3) y)`]
                  P2AP_METRIC_COMPARE) THEN
    REWRITE_TAC[P2AP_RMETRIC_VFAM; GSYM RIGHT_IMP_FORALL_THM] THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> CONJ_TAC THEN MATCH_MP_TAC P2CV_ML_QF_MONO THEN
      X_GEN_TAC `u:real^3` THEN MP_TAC(SPEC `u:real^3` th) THEN
      ASM_SIMP_TAC[P2CV_EXP_ARITH; REAL_LT_IMP_NZ] THEN SIMP_TAC[]);
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= w dot ((L:real->real^3->real^3^3) s2 ((h:real^3->real^3) y) ** w)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(V:p2cvv3)`; `R:A->bool`; `(t0:real) + a' / q`;
                   `(t0:real) + b / q`] P2AP_REGION_UPTO) THEN
    ASM_REWRITE_TAC[rfs_flow_upto; ricci_flow_on] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `riemannian_metric (restrict_atlas (rfs_vatlas (V:p2cvv3) (t0 + b / q)) R)
                        (p2c_vfam (V:p2cvv3) R (t0 + b / q) (t0 + s2 / q))`
    MP_TAC THENL
     [ASM_CASES_TAC `s2:real = b` THENL
       [ASM_REWRITE_TAC[]; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[riemannian_metric] THEN
    DISCH_THEN(MP_TAC o SPEC `(U INTER R:A->bool,psi:A->real^3)`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[restrict_atlas; IN_ELIM_THM; PAIR_EQ] THEN
      MAP_EVERY EXISTS_TAC [`U:A->bool`; `psi:A->real^3`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[metric_field; FST; SND] THEN
    DISCH_THEN(MP_TAC o SPEC `(h:real^3->real^3) y` o last o CONJUNCTS) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "L" THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_CASES_TAC `w:real^3 = vec 0` THENL
     [ASM_REWRITE_TAC[DOT_LZERO; REAL_LE_REFL]; ASM_MESON_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  USE_THEN "qf" (fun th -> ASM_SIMP_TAC[th]) THEN
  USE_THEN "cmp" (MP_TAC o C MP (CONJ (ASSUME `a' < s1`) (ASSUME `s1 <= b`)) o
    SPEC `s1:real`) THEN
  USE_THEN "cmp" (MP_TAC o C MP (CONJ (ASSUME `a' < s2`) (ASSUME `s2 <= b`)) o
    SPEC `s2:real`) THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_ARITH `(e * q) * x = q * (e * x)`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp(&4 * CM * (b - s1)) *
              (w dot ((L:real->real^3->real^3^3) b ((h:real^3->real^3) y) ** w))` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp(&4 * CM * (b - s1)) * exp(&4 * CM * (b - s2)) *
              (w dot ((L:real->real^3->real^3^3) s2 ((h:real^3->real^3) y) ** w))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE]; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_EXP_ADD] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_EXP_MONO_LE] THEN
  SUBGOAL_THEN `CM * (b - s1) <= CM * (b - a') /\ CM * (b - s2) <= CM * (b - a')`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Extensions of the chart representatives beyond both ends of               *)
(* a compact interval [a,b] around 0: below a from the local flow on a       *)
(* working interval [a',b'] with a' < a or, at a = 0, from the bottom        *)
(* extension; above b from the local flow with b < b' or, at b = b', from    *)
(* the top extension, time reversed; glued with P2CV_GLUE_EXT.               *)
(* ------------------------------------------------------------------------- *)

let p2cv_hv = [`V:num->p2cvv3`; `x:num->A`; `t:num->real`; `Q:num->real`;
               `J:real->bool`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
               `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`];;

(* Time reversal of an extension beyond the top. *)

let P2CV_UPTO_REVERSE = prove
 (`!a b (U:real^N->bool) (u:real->real^N->real^K).
     open U /\ pde_upto (--b) (--a) U (\s y. u (--s) y)
     ==> ?e F. &0 < e /\ smooth_map_on (interval(lift a,lift(b + e)) PCROSS U) F /\
               !s y. a < s /\ s <= b /\ y IN U ==> F(pastecart (lift s) y) = u s y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_upto] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `F0:real^(1,N)finite_sum->real^K`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ag")))))) THEN
  EXISTS_TAC `e:real` THEN
  EXISTS_TAC `(F0:real^(1,N)finite_sum->real^K) o
              (\v:real^(1,N)finite_sum. pastecart (lift(--(drop(fstcart v)))) (sndcart v))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `interval(lift(--b - e),lift(--a)) PCROSS (U:real^N->bool)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; PASTECART_IN_PCROSS;
                  FSTCART_PASTECART; SNDCART_PASTECART; IN_INTERVAL_1; LIFT_DROP] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^(1,N)finite_sum)` THEN
      REWRITE_TAC[SUBSET_UNIV] THEN
      MP_TAC(ISPECL [`&0`; `&1`] P2CV_SMOOTH_TIME_AFFINE) THEN
      REWRITE_TAC[REAL_DIV_1; REAL_ADD_LID]];
    MAP_EVERY X_GEN_TAC [`s:real`; `y:real^N`] THEN STRIP_TAC THEN
    REWRITE_TAC[o_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    USE_THEN "ag" (MP_TAC o SPECL [`--s:real`; `y:real^N`]) THEN
    REWRITE_TAC[REAL_NEG_NEG] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* The extension clause of p2ca_seqhyp for one n. *)

let P2CV_EXT = prove
 (`!(V:p2cvv3) (top:B topology) atlas Wb (f:B->A) t0 q a b a' b' c.
     p2cv_one V (top,atlas) Wb f t0 q /\
     a <= &0 /\ &0 <= b /\ a < b /\ a' <= a /\ b <= b' /\
     (a' < a \/ a = &0) /\ (b < b' \/ b' = b) /\
     rfs_persists V (IMAGE f Wb) (t0 + a' / q) (t0 + b' / q) /\
     c IN atlas
     ==> ?e (FF:real^(1,3)finite_sum->real^(3,3)finite_prod).
           &0 < e /\
           smooth_map_on (interval(lift(a - e),lift(b + e)) PCROSS
                          IMAGE (SND c) (FST c INTER Wb)) FF /\
           (!s y. a <= s /\ s <= b /\ y IN IMAGE (SND c) (FST c INTER Wb)
                  ==> FF(pastecart (lift s) y) =
                      vectorize(metric_local atlas c (p2cv_pb V t0 q atlas f s) y))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_ONE_BASIC) THEN
  SUBGOAL_THEN `&0 < (q:real)` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t0:real`; `q:real`] P2CV_TT_IFF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open (IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (Wb:B->bool)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2CA_CHART_IMAGE_OPEN_C THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL (p2cv_ov @ [`a':real`; `b':real`;
                            `c:(B->bool)#(B->real^3)`]) P2CV_LFLOW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[lricci_flow] THEN STRIP_TAC THEN
  (* below a *)
  SUBGOAL_THEN
   `?e1 (F1:real^(1,3)finite_sum->real^(3,3)finite_prod).
      &0 < e1 /\
      smooth_map_on (interval(lift(a - e1),lift b) PCROSS
                     IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (Wb:B->bool))) F1 /\
      (!s y. a <= s /\ s < b /\ y IN IMAGE (SND c) (FST c INTER Wb)
             ==> F1(pastecart (lift s) y) =
                 vectorize(metric_local atlas c (p2cv_pb V t0 q atlas (f:B->A) s) y))`
  (X_CHOOSE_THEN `e1:real` (X_CHOOSE_THEN `F1:real^(1,3)finite_sum->real^(3,3)finite_prod`
     STRIP_ASSUME_TAC)) THENL
   [ASM_CASES_TAC `a' < a` THENL
     [EXISTS_TAC `a - a'` THEN
      EXISTS_TAC `\z. (vectorize:real^3^3->real^(3,3)finite_prod)
                        (metric_local atlas c
                           (p2cv_pb V t0 q atlas (f:B->A) (drop(fstcart z)))
                           (sndcart z))` THEN
      REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `interval(lift a',lift b') PCROSS
                  IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (Wb:B->bool))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL] THEN
      REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `a = &0 /\ a' = &0` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `a' < a \/ a = &0` THEN UNDISCH_TAC `~(a' < a)` THEN
      UNDISCH_TAC `a' <= a` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `a' = &0` THEN UNDISCH_TAC `a = &0` THEN
    DISCH_THEN SUBST_ALL_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(ISPECL (p2cv_ov @ [`b:real`; `c:(B->bool)#(B->real^3)`])
                  P2CV_BOT_EXT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC P2CV_PERSISTS_MONO THEN
      MAP_EVERY EXISTS_TAC [`(t0:real) + &0 / q`; `(t0:real) + b' / q`] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL];
      ALL_TAC] THEN
    DISCH_THEN(ACCEPT_TAC o REWRITE_RULE[pde_upto]);
    ALL_TAC] THEN
  (* above b *)
  SUBGOAL_THEN
   `?e2 (F2:real^(1,3)finite_sum->real^(3,3)finite_prod).
      &0 < e2 /\
      smooth_map_on (interval(lift a,lift(b + e2)) PCROSS
                     IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (Wb:B->bool))) F2 /\
      (!s y. a < s /\ s <= b /\ y IN IMAGE (SND c) (FST c INTER Wb)
             ==> F2(pastecart (lift s) y) =
                 vectorize(metric_local atlas c (p2cv_pb V t0 q atlas (f:B->A) s) y))`
  (X_CHOOSE_THEN `e2:real` (X_CHOOSE_THEN `F2:real^(1,3)finite_sum->real^(3,3)finite_prod`
     STRIP_ASSUME_TAC)) THENL
   [ASM_CASES_TAC `b < b'` THENL
     [EXISTS_TAC `b' - b` THEN
      EXISTS_TAC `\z. (vectorize:real^3^3->real^(3,3)finite_prod)
                        (metric_local atlas c
                           (p2cv_pb V t0 q atlas (f:B->A) (drop(fstcart z)))
                           (sndcart z))` THEN
      REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `interval(lift a',lift b') PCROSS
                  IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (Wb:B->bool))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL] THEN
      REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `b':real = b` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `b < b' \/ b' = b:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`a':real`; `b:real`;
                   `IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (Wb:B->bool))`;
                   `\s y. (vectorize:real^3^3->real^(3,3)finite_prod)
                            (metric_local atlas c (p2cv_pb V t0 q atlas (f:B->A) s) y)`]
                  P2CV_UPTO_REVERSE) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL (p2cv_ov @ [`a':real`; `b:real`;
                                `c:(B->bool)#(B->real^3)`]) P2CV_TOP_EXT) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN ACCEPT_TAC];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN
      `F0:real^(1,3)finite_sum->real^(3,3)finite_prod` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `e:real` THEN EXISTS_TAC `F0:real^(1,3)finite_sum->real^(3,3)finite_prod` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `interval(lift a',lift(b + e)) PCROSS
                  IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (Wb:B->bool))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL] THEN
      REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (Wb:B->bool))`;
                 `a:real`; `b:real`; `e1:real`; `e2:real`;
                 `F1:real^(1,3)finite_sum->real^(3,3)finite_prod`;
                 `F2:real^(1,3)finite_sum->real^(3,3)finite_prod`;
                 `\s y. (vectorize:real^3^3->real^(3,3)finite_prod)
                          (metric_local atlas c (p2cv_pb V t0 q atlas (f:B->A) s) y)`]
                P2CV_GLUE_EXT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Bounds on the quadratic forms of the chart representatives.               *)
(* At time 0 the time-0 closeness puts P within a factor 1/2 of g0 on a      *)
(* compact set (P2CV_QF_TIME0).  The comparison of two times extends to      *)
(* s = 0 at a bottom without margin, by continuity from the right            *)
(* (P2CV_LFROM, P2CV_RCONT_BOUNDS, P2CV_QF_ALL).  With the bounds of g0 on   *)
(* compact sets of a chart (GRGD_METRIC_BOUNDS) this gives uniform two-sided *)
(* bounds and entry bounds (P2CV_QF_BOUNDS, P2CV_ENTRY_BOUNDS).              *)
(* ------------------------------------------------------------------------- *)

let P2CV_MF_QF_NONNEG = prove
 (`!U (G:real^N->real^N^N) y v. metric_field U G /\ y IN U ==> &0 <= v dot (G y ** v)`,
  REWRITE_TAC[metric_field] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `v:real^N = vec 0` THENL
   [ASM_REWRITE_TAC[DOT_LZERO; REAL_LE_REFL];
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_MESON_TAC[]]);;

let P2CV_EXP_GE1 = prove
 (`!x. &0 <= x ==> &1 <= exp x`,
  GEN_TAC THEN MP_TAC(SPEC `x:real` REAL_EXP_LE_X) THEN REAL_ARITH_TAC);;

let P2CV_LE_EMUL = prove
 (`!e x. &1 <= e /\ &0 <= x ==> x <= e * x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= (e - &1) * x ==> x <= e * x`) THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC);;

(* Bounds at 0 from bounds on (0,b] for a function continuous on [0,b]. *)

let P2CV_RCONT_BOUNDS = prove
 (`!ff b c. &0 < b /\ ff real_continuous_on real_interval[&0,b]
            ==> ((!s. &0 < s /\ s <= b ==> c <= ff s) ==> c <= ff(&0)) /\
                ((!s. &0 < s /\ s <= b ==> ff s <= c) ==> ff(&0) <= c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 IN real_interval[&0,b]` ASSUME_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(ff ---> ff(&0)) (atreal (&0) within real_interval[&0,b]) /\
                ~trivial_limit(atreal (&0) within real_interval[&0,b])`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_CONTINUOUS_WITHINREAL] THEN
      ASM_MESON_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN];
      ASM_SIMP_TAC[TRIVIAL_LIMIT_WITHIN_REALINTERVAL; IS_REALINTERVAL_INTERVAL] THEN
      REWRITE_TAC[EXTENSION; IN_REAL_INTERVAL; IN_SING] THEN
      DISCH_THEN(MP_TAC o SPEC `b:real`) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!P. (!s. &0 < s /\ s <= b ==> P s)
                    ==> eventually P (atreal (&0) within real_interval[&0,b])`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[EVENTUALLY_WITHINREAL] THEN
    EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THEN DISCH_TAC THENL
   [MATCH_MP_TAC(ISPEC `atreal (&0) within real_interval[&0,b]` REALLIM_LBOUND);
    MATCH_MP_TAC(ISPEC `atreal (&0) within real_interval[&0,b]` REALLIM_UBOUND)] THEN
  EXISTS_TAC `ff:real->real` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* Metric fields at the times of a working interval. *)

let P2CV_P_FIELD_AT = prove
 (`!(V:p2cvv3) (top:B topology) atlas Wb (f:B->A) t0 q a' b s c.
     p2cv_one V (top,atlas) Wb f t0 q /\
     a' <= &0 /\ &0 <= b /\
     rfs_persists V (IMAGE f Wb) (t0 + a' / q) (t0 + b / q) /\
     (a' < s \/ s = &0) /\ s <= b /\ c IN atlas
     ==> metric_field (IMAGE (SND c) (FST c INTER Wb))
                      (metric_local atlas c (p2cv_pb V t0 q atlas f s))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_ONE_BASIC) THEN
  SUBGOAL_THEN `&0 < (q:real)` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t0:real`; `q:real`] P2CV_TT_IFF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL (p2cv_ov @ [`a':real`; `b:real`; `s:real`])
                P2CV_PHI_DIFFEO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `psi:A->B`) THEN
  SUBGOAL_THEN `smooth_manifold_atlas (rfs_vtop (V:p2cvv3) (t0 + s / q))
                                      (rfs_vatlas V (t0 + s / q))`
  ASSUME_TAC THENL
   [ASM_CASES_TAC `a' < s` THENL
     [MP_TAC(ISPECL [`(V:p2cvv3)`; `IMAGE (f:B->A) (Wb:B->bool)`;
                     `(t0:real) + a' / q`; `(t0:real) + b / q`;
                     `(t0:real) + s / q`] P2CV_PERSISTS_AT) THEN
      ASM_SIMP_TAC[];
      SUBGOAL_THEN `s = &0` SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[P2CV_DIV_LZERO; REAL_ADD_RID]];
    ALL_TAC] THEN
  MP_TAC(ISPECL (p2cv_ov @ [`s:real`; `psi:A->B`;
                            `c:(B->bool)#(B->real^3)`]) P2CV_P_FIELD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC]);;

(* At a bottom without margin the chart representatives are local flows     *)
(* from 0 in the sense of rfa_lfrom.                                         *)

let P2CV_LFROM = prove
 (`!(V:p2cvv3) (top:B topology) atlas Wb (f:B->A) t0 q b c.
     p2cv_one V (top,atlas) Wb f t0 q /\ &0 < b /\
     rfs_persists V (IMAGE f Wb) (t0 + &0 / q) (t0 + b / q) /\
     c IN atlas
     ==> rfa_lfrom (IMAGE (SND c) (FST c INTER Wb)) (&0) b
                   (\s. metric_local atlas c (p2cv_pb V t0 q atlas f s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_ONE_BASIC) THEN
  REWRITE_TAC[rfa_lfrom] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL (p2cv_ov @ [`&0`; `b:real`;
                             `c:(B->bool)#(B->real^3)`]) P2CV_LFLOW) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; DISCH_THEN ACCEPT_TAC];
    MP_TAC(ISPECL (p2cv_ov @ [`&0`; `b:real`; `&0`;
                             `c:(B->bool)#(B->real^3)`]) P2CV_P_FIELD_AT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; DISCH_THEN ACCEPT_TAC];
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL (p2cv_ov @ [`b:real`; `c:(B->bool)#(B->real^3)`])
                  P2CV_BOT_EXT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[pde_upto]] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN
      `FF:real^(1,3)finite_sum->real^(3,3)finite_prod` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC
     [`IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (Wb:B->bool))`;
      `e:real`; `FF:real^(1,3)finite_sum->real^(3,3)finite_prod`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN
    MATCH_MP_TAC P2CA_CHART_IMAGE_OPEN_C THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
    ASM_REWRITE_TAC[]]);;

(* The comparison of two times, including s = 0 when the working interval  *)
(* starts at 0.                                                             *)

let P2CV_QF_ALL = prove
 (`!(V:p2cvv3) (top:B topology) atlas Wb (f:B->A) t0 q a' b c CM y v s1 s2.
     p2cv_one V (top,atlas) Wb f t0 q /\
     a' <= &0 /\ &0 <= b /\ a' < b /\ &0 <= CM /\
     rfs_persists V (IMAGE f Wb) (t0 + a' / q) (t0 + b / q) /\
     (!s z. a' <= s /\ s <= b /\ z IN IMAGE f Wb
            ==> p3_vrm V (t0 + s / q) z <= CM * q) /\
     c IN atlas /\ y IN IMAGE (SND c) (FST c INTER Wb) /\
     (a' < s1 \/ s1 = &0) /\ s1 <= b /\ (a' < s2 \/ s2 = &0) /\ s2 <= b
     ==> v dot (metric_local atlas c (p2cv_pb V t0 q atlas f s1) y ** v) <=
         exp(&8 * CM * (b - a')) *
         (v dot (metric_local atlas c (p2cv_pb V t0 q atlas f s2) y ** v))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `a' < s1 /\ a' < s2` THENL
   [MP_TAC(ISPECL (p2cv_ov @ [`a':real`; `b:real`;
                             `c:(B->bool)#(B->real^3)`; `CM:real`; `y:real^3`; `v:real^3`;
                             `s1:real`; `s2:real`]) P2CV_QF_COMPARE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `a' = &0` SUBST_ALL_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`~(a' < s1 /\ a' < s2)`; `a' < s1 \/ s1 = &0`;
                           `a' < s2 \/ s2 = &0`; `a' <= &0`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\s. v dot (metric_local atlas c (p2cv_pb V t0 q atlas (f:B->A) s)
                  (y:real^3) ** v))
    real_continuous_on real_interval[&0,b / &2]`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (Wb:B->bool))`;
                   `&0`; `b:real`;
                   `\s. metric_local atlas (c:(B->bool)#(B->real^3))
                          (p2cv_pb V t0 q atlas (f:B->A) s)`;
                   `y:real^3`; `b / &2`; `v:real^3`] RFA_LFROM_QFORM_CONT) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL (p2cv_ov @ [`b:real`; `c:(B->bool)#(B->real^3)`])
                    P2CV_LFROM) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `s1 = &0` THEN ASM_CASES_TAC `s2 = &0` THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2CV_LE_EMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2CV_EXP_GE1 THEN MATCH_MP_TAC REAL_LE_MUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC P2CV_MF_QF_NONNEG THEN
      EXISTS_TAC `IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (Wb:B->bool))` THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL (p2cv_ov @ [`&0`; `b:real`; `&0`;
                               `c:(B->bool)#(B->real^3)`]) P2CV_P_FIELD_AT) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC]];
    MP_TAC(ISPECL
     [`\s. v dot (metric_local atlas c (p2cv_pb V t0 q atlas (f:B->A) s)
                    (y:real^3) ** v)`;
      `b / &2`;
      `exp(&8 * CM * (b - &0)) *
       (v dot (metric_local atlas c (p2cv_pb V t0 q atlas (f:B->A) s2)
                 (y:real^3) ** v))`] P2CV_RCONT_BOUNDS) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL (p2cv_ov @ [`&0`; `b:real`;
                             `c:(B->bool)#(B->real^3)`; `CM:real`; `y:real^3`; `v:real^3`;
                             `s:real`; `s2:real`]) P2CV_QF_COMPARE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN ACCEPT_TAC];
    MP_TAC(ISPECL
     [`\s. exp(&8 * CM * (b - &0)) *
           (v dot (metric_local atlas c (p2cv_pb V t0 q atlas (f:B->A) s)
                     (y:real^3) ** v))`;
      `b / &2`;
      `v dot (metric_local atlas c (p2cv_pb V t0 q atlas (f:B->A) s1)
                (y:real^3) ** v)`] P2CV_RCONT_BOUNDS) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL (p2cv_ov @ [`&0`; `b:real`;
                             `c:(B->bool)#(B->real^3)`; `CM:real`; `y:real^3`; `v:real^3`;
                             `s1:real`; `s:real`]) P2CV_QF_COMPARE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN ACCEPT_TAC];
    ASM_REAL_ARITH_TAC]);;

(* Time 0: P within a factor 1/2 of g0 on a compact set, eventually. *)

let P2CV_QF_TIME0 = prove
 (`!V x t Q J (top:B topology) atlas g0 xl W (phi:num->B->A) K.
     p2cv_hyp V x t Q J (top,atlas) g0 xl W phi /\ compact_in top K
     ==> ?N. !n y u. N <= n /\ y IN K
                     ==> K SUBSET W n /\
                         abs(u dot (p2cv_P V t Q atlas phi n (&0) y ** u) -
                             u dot (g0 y ** u)) <= inv(&2) * (u dot (g0 y ** u))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_HYP_BASIC) THEN
  FIRST_ASSUM(MP_TAC o C MP (CONJ (ASSUME `compact_in top (K:B->bool)`) REAL_LT_01) o
    SPECL [`K:B->bool`; `0`; `&1`] o check (fun th ->
    can (find_term (fun t -> try fst(dest_const t) = "lck_dist2" with Failure _ -> false))
        (concl th) && is_forall (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "k0")) THEN
  MP_TAC(ISPECL p2cv_hv P2CV_TIME0) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`K:B->bool`; `0`; `inv(&2) pow 2`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1")) THEN
  EXISTS_TAC `k0 + N1:num` THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `y:B`; `u:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(K:B->bool) SUBSET (W:num->B->bool) n` ASSUME_TAC THENL
   [USE_THEN "k0" (MP_TAC o SPEC `n:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(ACCEPT_TAC o CONJUNCT1)];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "N1" (MP_TAC o SPECL [`n:num`; `y:B`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `(y:B) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPACT_IN_SUBSET_TOPSPACE; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `y:B`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL (p2cv_hv @ [`n:num`]) P2CV_SLICE0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `psi:A->B`)) THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (y:B)))
                        (FST(chart_at atlas y) INTER (W:num->B->bool) n))
                 (metric_local atlas (chart_at atlas y) (g0:B->real^3^3)) /\
    metric_field (IMAGE (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (y:B)))
                        (FST(chart_at atlas y) INTER (W:num->B->bool) n))
                 (metric_local atlas (chart_at atlas y)
                    (p2cv_P V t Q atlas (phi:num->B->A) n (&0))) /\
    SND(chart_at atlas y) y IN IMAGE (SND(chart_at atlas y)) (FST(chart_at atlas y) INTER W n)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
      EXISTS_TAC `IMAGE (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (y:B)))
                        (FST(chart_at atlas y))` THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `riemannian_metric (atlas:((B->bool)#(B->real^3))->bool) (g0:B->real^3^3)` THEN
        REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        CONJ_TAC THENL
         [MATCH_MP_TAC P2CA_CHART_IMAGE_OPEN_C THEN
          MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
          ASM_REWRITE_TAC[];
          SET_TAC[]]];
      REWRITE_TAC[P2CV_P_PB] THEN
      MP_TAC(ISPECL [`(V:num->p2cvv3) n`; `top:B topology`;
                     `atlas:((B->bool)#(B->real^3))->bool`; `(W:num->B->bool) n`;
                     `(phi:num->B->A) n`; `(t:num->real) n`; `(Q:num->real) n`; `&0`;
                     `psi:A->B`; `chart_at (atlas:((B->bool)#(B->real^3))->bool) (y:B)`]
                    P2CV_P_FIELD) THEN
      ASM_REWRITE_TAC[P2CV_DIV_LZERO; REAL_ADD_RID] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC P2CV_HYP_ONE THEN
      MAP_EVERY EXISTS_TAC [`x:num->A`; `J:real->bool`; `g0:B->real^3^3`; `xl:B`] THEN
      ASM_REWRITE_TAC[LE_REFL];
      REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EXISTS_TAC `y:B` THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `p2cv_P V t Q atlas (phi:num->B->A) n (&0)`; `y:B`] METRIC_LOCAL_AT) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g0:B->real^3^3`; `y:B`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sqrt(lck_dist2 0 (metric_local atlas (chart_at atlas y) (g0:B->real^3^3))
                     (metric_local atlas (chart_at atlas y)
                        (p2cv_P V t Q atlas (phi:num->B->A) n (&0)))
                     (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (y:B)) y)) *
    (u dot (metric_local atlas (chart_at atlas y) g0 (SND(chart_at atlas y) y) ** u))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LCK_DIST_C0 THEN
    EXISTS_TAC `IMAGE (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (y:B)))
                      (FST(chart_at atlas y) INTER (W:num->B->bool) n)` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      MATCH_MP_TAC P2CV_MF_QF_NONNEG THEN
      EXISTS_TAC `IMAGE (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (y:B)))
                        (FST(chart_at atlas y) INTER (W:num->B->bool) n)` THEN
      ASM_REWRITE_TAC[]]]);;

(* The arithmetic of the two-sided bounds. *)

let P2CV_QF_ARITH = prove
 (`!pp p0 gg nv c0 C0 E.
     &0 < c0 /\ &0 <= C0 /\ &1 <= E /\ &0 <= nv /\ &0 <= pp /\
     c0 * nv <= gg /\ gg <= C0 * nv /\ pp <= E * p0 /\ p0 <= E * pp /\
     p0 <= &3 / &2 * gg /\ gg <= &2 * p0
     ==> nv <= (&2 * E * (inv c0 + C0)) * pp /\ pp <= (&2 * E * (inv c0 + C0)) * nv`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < inv c0` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `nv <= inv c0 * gg` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv c0 * c0 * nv` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_MUL_LID; REAL_LE_REFL];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv c0 * gg <= inv c0 * (&2 * p0)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `inv c0 * (&2 * p0) <= inv c0 * (&2 * (E * pp))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `E * p0 <= E * (&3 / &2 * gg)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `E * gg <= E * (C0 * nv)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= E * C0 * pp /\ &0 <= E * inv c0 * nv /\ &0 <= E * C0 * nv`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THEN ASM_REAL_ARITH_TAC);;

(* Uniform two-sided bounds of the chart representatives on a compact set  *)
(* of a chart, for all large n and all times of [a,b].                     *)

let P2CV_QF_BOUNDS = prove
 (`!V x t Q J (top:B topology) atlas g0 xl W (phi:num->B->A) m a b a' b' CM N c K.
     p2cv_hyp V x t Q J (top,atlas) g0 xl W phi /\
     a' <= a /\ a <= &0 /\ &0 <= b /\ a < b /\ b <= b' /\ (a' < a \/ a = &0) /\
     &0 <= CM /\ m <= N /\
     (!n. N <= n
          ==> rfs_persists (V n) (IMAGE (phi n) (W m)) (t n + a' / Q n) (t n + b' / Q n) /\
              (!s z. a' <= s /\ s <= b' /\ z IN IMAGE (phi n) (W m)
                     ==> p3_vrm (V n) (t n + s / Q n) z <= CM * Q n)) /\
     (!n y u. N <= n /\ y IN W m
              ==> abs(u dot (p2cv_P V t Q atlas phi n (&0) y ** u) - u dot (g0 y ** u))
                  <= inv(&2) * (u dot (g0 y ** u))) /\
     c IN atlas /\ compact K /\ K SUBSET IMAGE (SND c) (FST c INTER W m)
     ==> ?Lm. &0 <= Lm /\
              !n s y v. N <= n /\ a <= s /\ s <= b /\ y IN K
                        ==> norm v pow 2 <=
                            Lm * (v dot (metric_local atlas c (p2cv_P V t Q atlas phi n s) y ** v)) /\
                            v dot (metric_local atlas c (p2cv_P V t Q atlas phi n s) y ** v) <=
                            Lm * norm v pow 2`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_HYP_BASIC) THEN
  MP_TAC(ISPECL [`atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
                 `FST(c:(B->bool)#(B->real^3))`; `SND(c:(B->bool)#(B->real^3))`;
                 `K:real^3->bool`] GRGD_METRIC_BOUNDS) THEN
  ASM_REWRITE_TAC[PAIR] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c0:real` (X_CHOOSE_THEN `C0:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "g0b"))))) THEN
  ABBREV_TAC `E = exp(&8 * CM * (b' - a'))` THEN
  SUBGOAL_THEN `&1 <= E` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN MATCH_MP_TAC P2CV_EXP_GE1 THEN MATCH_MP_TAC REAL_LE_MUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv c0` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV_EQ]; ALL_TAC] THEN
  EXISTS_TAC `&2 * E * (inv c0 + C0)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `s:real`; `y:real^3`; `v:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (W:num->B->bool) m)`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `m:num <= n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `p2cv_one ((V:num->p2cvv3) n) (top,atlas) ((W:num->B->bool) m)
                         ((phi:num->B->A) n) (t n) (Q n)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2CV_HYP_ONE THEN
    MAP_EVERY EXISTS_TAC [`x:num->A`; `J:real->bool`; `g0:B->real^3^3`; `xl:B`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MP (ASSUME `N <= n:num`) o SPEC `n:num`) THEN
  SUBGOAL_THEN `a' < s \/ s = &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the two comparisons with time 0 *)
  SUBGOAL_THEN
   `v dot (metric_local atlas c (p2cv_P V t Q atlas (phi:num->B->A) n s) y ** v) <=
    E * (v dot (metric_local atlas c (p2cv_P V t Q atlas phi n (&0)) y ** v)) /\
    v dot (metric_local atlas c (p2cv_P V t Q atlas phi n (&0)) y ** v) <=
    E * (v dot (metric_local atlas c (p2cv_P V t Q atlas phi n s) y ** v))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN REWRITE_TAC[P2CV_P_PB] THEN CONJ_TAC THEN
    MATCH_MP_TAC P2CV_QF_ALL THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `(W:num->B->bool) m`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* time 0 against g0 in the chart *)
  SUBGOAL_THEN `chart_inv (c:(B->bool)#(B->real^3)) y IN (W:num->B->bool) m` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `(y:real^3) IN IMAGE (SND(c:(B->bool)#(B->real^3)))
                                    (FST c INTER (W:num->B->bool) m)` THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `v dot (metric_local atlas c (p2cv_P V t Q atlas (phi:num->B->A) n (&0)) y ** v) <=
    &3 / &2 * (v dot (metric_local atlas c (g0:B->real^3^3) y ** v)) /\
    v dot (metric_local atlas c g0 y ** v) <=
    &2 * (v dot (metric_local atlas c (p2cv_P V t Q atlas phi n (&0)) y ** v))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC P2CV_ML_QF_MONO THEN X_GEN_TAC `u:real^3` THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `chart_inv (c:(B->bool)#(B->real^3)) y`;
                                  `u:real^3`] o check (fun th ->
      can (find_term ((=) `inv(&2)`)) (concl th) && is_forall (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "g0b" (STRIP_ASSUME_TAC o C MP (ASSUME `(y:real^3) IN K`) o
                  SPECL [`y:real^3`; `v:real^3`]) THEN
  SUBGOAL_THEN
   `&0 <= v dot (metric_local atlas c (p2cv_P V t Q atlas (phi:num->B->A) n s) y ** v)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2CV_MF_QF_NONNEG THEN
    EXISTS_TAC `IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (W:num->B->bool) m)` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[P2CV_P_PB] THEN MATCH_MP_TAC P2CV_P_FIELD_AT THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `a':real`; `b':real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= C0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC P2CV_QF_ARITH THEN
  EXISTS_TAC `v dot (metric_local atlas c (p2cv_P V t Q atlas (phi:num->B->A) n (&0)) y ** v)` THEN
  EXISTS_TAC `v dot (metric_local atlas c (g0:B->real^3^3) y ** v)` THEN
  ASM_REWRITE_TAC[REAL_LE_POW_2]);;

(* Entry bounds from the two-sided bounds. *)

let P2CV_ENTRY_BOUNDS = prove
 (`!U (G:real^N->real^N^N) y Lm p q.
     metric_field U G /\ y IN U /\ (!v. v dot (G y ** v) <= Lm * norm v pow 2) /\
     1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
     ==> abs(G y$p$q) <= Lm`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_QFORM_ENTRY_BOUND THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `metric_field U (G:real^N->real^N^N)` THEN REWRITE_TAC[metric_field] THEN
    ASM_SIMP_TAC[];
    GEN_TAC THEN MATCH_MP_TAC P2CV_MF_QF_NONNEG THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[]]);;


(* ========================================================================= *)
(* Unit pc_p2c_blowup3 (Part 2C): MT Thm 11.8 part 2 and the main theorem in *)
(* view form.  For the backward hypothesis at every Tb: RBU(T) for every T   *)
(* along one subsequence (nested subsequences and the diagonal), the flow    *)
(* limit on (-inf,0] and one subsequence for every Tl, and the limit is a    *)
(* kappa-solution: non-flat (P2B_REQ_FLAT_FORWARD with the left limit of R   *)
(* at time 0) and kappa-noncollapsed on every scale (the local form of L4 of *)
(* the limit-geometry layer, unit pc_lim_knc_local).                         *)
(* ========================================================================= *)

needs "src/pc_p2c_blowup2.ml";;
needs "src/pc_lim_knc_local.ml";;
needs "src/pc_rfa_splitend.ml";;
needs "src/pc_p2c_c1116u.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Tools for part 2.  The left limit of R at the final time                 *)
(* (P2BU_UPTO_SCALAR_LE_LEFT), non-flatness of the slices (P2BU_NONFLAT),   *)
(* the time-0 data along subsequences, RBU(T) for every T along one         *)
(* subsequence (P2BU_RBU_ALL), the flow limit on (-inf,0]                    *)
(* (P2BU_FLOW_FROM_RBU_ALL), and the local noncollapsing hypothesis          *)
(* (P2BU_KNC_HYP).                                                            *)
(* ========================================================================= *)

(* An upper bound of R on [t1,b) passes to the final time b of a flow       *)
(* smooth up to b.  Mirrors P2AL65_UPTO_SCALAR_LEFT (pc_p2a_l965, the lower  *)
(* bound), by RFA_UPTO_BOX and RFA_LEFT_LIMIT_NONNEG.                        *)

let P2BU_UPTO_SCALAR_LE_LEFT = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:real->A->real^3^3) a b x t1 c0.
     rfs_flow_upto (top,atlas) a b g /\ x IN topspace top /\ t1 < b /\
     (!t. t1 <= t /\ t < b ==> mfd_scalar atlas (g t) x <= c0)
     ==> mfd_scalar atlas (g b) x <= c0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^3))->bool)`
  ASSUME_TAC THENL [ASM_MESON_TAC[rfs_flow_upto; ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `c:(A->bool)#(A->real^3)`;
                 `SND (c:(A->bool)#(A->real^3)) x`] RFA_UPTO_BOX) THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `Gb:real->real^3->real^3^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`\p. c0 - lscalar ((Gb:real->real^3->real^3^3) (drop(fstcart p))) (sndcart p)`;
                 `interval(lift(b - d),lift(b + d)) PCROSS ball(SND (c:(A->bool)#(A->real^3)) x,d)`;
                 `max t1 (b - d / &2)`; `b:real`; `SND (c:(A->bool)#(A->real^3)) x`]
                RFA_LEFT_LIMIT_NONNEG) THEN
  BETA_TAC THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [CONV_TAC(RATOR_CONV(RAND_CONV(REWRITE_CONV[o_DEF] THENC DEPTH_CONV BETA_CONV THENC
                                    REWRITE_CONV[LIFT_SUB]))) THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS THEN MATCH_MP_TAC LRG_LSMOOTH_LSCALAR THEN
      ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; CENTRE_IN_BALL] THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(Gb:real->real^3->real^3^3) t = metric_local atlas c ((g:real->A->real^3^3) t)`
      SUBST1_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= c0 ==> &0 <= c0 - x`) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
        can (term_match [] `!t. t1 <= t /\ t < b
                                ==> mfd_scalar atlas ((g:real->A->real^3^3) t) (x:A) <= c0`)
            (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      EXPAND_TAC "c" THEN REWRITE_TAC[mfd_scalar]];
    SUBGOAL_THEN `(Gb:real->real^3->real^3^3) b = metric_local atlas c ((g:real->A->real^3^3) b)`
    SUBST1_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "c" THEN REWRITE_TAC[GSYM mfd_scalar] THEN REAL_ARITH_TAC]);;

(* Non-flatness of the slices (MT p. 279): a flat slice at time             *)
(* s0 < 0 stays flat up to time 0 (P2B_REQ_FLAT_FORWARD), and R(xl,0) > 0    *)
(* is the limit from the left (P2BU_UPTO_SCALAR_LE_LEFT).                   *)

let P2BU_NONFLAT = prove
 (`!(w:B->bool) (top:B topology) atlas (g:real->B->real^3^3) xl.
     P2B_REQ_FLAT_FORWARD_STATEMENT w /\ hausdorff_space top /\
     smooth_manifold_atlas top atlas /\
     (!a b. a < b /\ b <= &0 ==> ricci_flow_on (top,atlas) a b g) /\
     (!a. a < &0 ==> rfs_flow_upto (top,atlas) a (&0) g) /\
     (!s. s <= &0
          ==> riemannian_metric atlas (g s) /\ mfd_complete (top,atlas) (g s) /\
              (!y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
                       ==> &0 <= mfd_sectional atlas (g s) y u v)) /\
     (!a. a <= &0
          ==> ?K. !s y. a <= s /\ s <= &0 /\ y IN topspace top
                        ==> mfd_rm_norm atlas (g s) y <= K) /\
     xl IN topspace top /\ &0 < mfd_scalar atlas (g (&0)) xl
     ==> !s. s <= &0 ==> ?y. y IN topspace top /\ &0 < mfd_rm_norm atlas (g s) y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ff") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "rf")
    (CONJUNCTS_THEN2 (LABEL_TAC "upto") (CONJUNCTS_THEN2 (LABEL_TAC "Jp")
    (CONJUNCTS_THEN2 (LABEL_TAC "rmb") STRIP_ASSUME_TAC))))))) THEN
  X_GEN_TAC `s0:real` THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(LABEL_TAC "flat" o
    REWRITE_RULE[NOT_EXISTS_THM; TAUT `~(p /\ q) <=> p ==> ~q`; REAL_NOT_LT]) THEN
  (* R vanishes on the slice s0 *)
  SUBGOAL_THEN `!y. y IN topspace top ==> mfd_scalar atlas ((g:real->B->real^3^3) s0) y = &0`
  (LABEL_TAC "R0") THENL
   [X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    USE_THEN "Jp" (MP_TAC o C MP (ASSUME `s0 <= &0`) o SPEC `s0:real`) THEN STRIP_TAC THEN
    SUBGOAL_THEN `!u v. ~collinear {vec 0,u,v}
                        ==> mfd_sectional atlas ((g:real->B->real^3^3) s0) y u v = &0`
    ASSUME_TAC THENL
     [MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `(g:real->B->real^3^3) s0`; `y:B`; `u:real^3`; `v:real^3`]
                    MFD_SECTIONAL_LE_RM_NORM) THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "flat" (MP_TAC o C MP (ASSUME `(y:B) IN topspace top`) o SPEC `y:B`) THEN
      SUBGOAL_THEN `&0 <= mfd_sectional atlas ((g:real->B->real^3^3) s0) y u v` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_sectional"))
              (concl th))) THEN ASM_REWRITE_TAC[];
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) s0`; `y:B`; `&0`] P2BS_MFD_SCALAR_SECT) THEN
    ASM_SIMP_TAC[REAL_LE_REFL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `s0 = &0` THENL
   [UNDISCH_TAC `&0 < mfd_scalar atlas ((g:real->B->real^3^3) (&0)) xl` THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s0 = &0`)) THEN
    USE_THEN "R0" (fun th -> ASM_SIMP_TAC[th]) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `s0 < &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "rmb" (X_CHOOSE_TAC `K:real` o C MP (ASSUME `s0 <= &0`) o SPEC `s0:real`) THEN
  (* flat forward from s0 *)
  UNDISCH_TAC `P2B_REQ_FLAT_FORWARD_STATEMENT (w:B->bool)` THEN
  REWRITE_TAC[P2B_REQ_FLAT_FORWARD_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `s0 - &1`; `&0`; `g:real->B->real^3^3`; `s0:real`; `K:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "rf" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC;
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      USE_THEN "Jp" (MP_TAC o SPEC `t:real`) THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      MAP_EVERY X_GEN_TAC [`t:real`; `y:B`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`t:real`; `y:B`; `v1:real^3`; `v2:real^3`] THEN STRIP_TAC THEN
      USE_THEN "Jp" (MP_TAC o SPEC `t:real`) THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2) THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(LABEL_TAC "ffw")] THEN
  (* R(xl,0) <= 0 *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `g:real->B->real^3^3`; `s0 - &1`; `&0`; `xl:B`; `s0:real`; `&0`]
    P2BU_UPTO_SCALAR_LE_LEFT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "upto" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      USE_THEN "ffw" (MP_TAC o C MP (CONJ (ASSUME `s0 <= t`) (CONJ (ASSUME `t < &0`)
        (ASSUME `(xl:B) IN topspace top`))) o SPECL [`t:real`; `xl:B`]) THEN
      REAL_ARITH_TAC];
    ASM_REAL_ARITH_TAC]);;

(* The time-0 data pass to subsequences.                                    *)

let P2BU_GOOD_SUBSEQ = prove
 (`!C eps kappa r0 mu (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x t T0 (top0:B topology) atlas0 g0 xl0 W0 (phi0:num->B->A) d.
     p2bu_good (C,eps,kappa,r0,mu) V x t T0 (top0,atlas0) g0 xl0 W0 phi0 /\ p3_subseq d
     ==> p2bu_good (C,eps,kappa,r0,mu) (\n. V (d n)) (\n. x (d n)) (\n. t (d n)) T0
           (top0,atlas0) g0 xl0 (\n. W0 (d n)) (\n. phi0 (d n))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bu_good] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (LABEL_TAC "bseq")
    (CONJUNCTS_THEN2 (LABEL_TAC "sep") (CONJUNCTS_THEN2 (LABEL_TAC "cc")
    (CONJUNCTS_THEN2 (LABEL_TAC "back") (CONJUNCTS_THEN2 (LABEL_TAC "sl")
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))))) ASSUME_TAC) THEN
  SUBGOAL_THEN `!n:num. n <= d n` (LABEL_TAC "ge") THENL
   [GEN_TAC THEN MATCH_MP_TAC P2BU_SUBSEQ_GE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  FIRST
   [MP_TAC(ISPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
      `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
      `x:num->A`; `t:num->real`; `d:num->num`] P2BU_VBLOWUP_SUBSEQ) THEN
    ASM_REWRITE_TAC[o_DEF] THEN NO_TAC;
    REPEAT GEN_TAC THEN USE_THEN "sep" (fun th -> REWRITE_TAC[th]) THEN NO_TAC;
    X_GEN_TAC `A:real` THEN USE_THEN "cc" (X_CHOOSE_TAC `N:num` o SPEC `A:real`) THEN
    EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN
    ASM_REWRITE_TAC[] THEN NO_TAC;
    X_GEN_TAC `Tb:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`kappa:real`; `r0:real`;
      `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
      `x:num->A`; `t:num->real`; `Tb:real`; `d:num->num`] P2BU_BACK_SUBSEQ) THEN
    ASM_SIMP_TAC[o_DEF] THEN NO_TAC;
    MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
      `x:num->A`; `t:num->real`;
      `\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) ((t:num->real) n) ((x:num->A) n)`;
      `top0:B topology`; `atlas0:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl0:B`;
      `W0:num->B->bool`; `phi0:num->B->A`; `d:num->num`] P2BU_SLICE_LIMIT_SUBSEQ) THEN
    ASM_REWRITE_TAC[o_DEF] THEN NO_TAC]);;

(* RBU(T) for every T along one subsequence: RBU(n + 1) along nested        *)
(* subsequences (P2BU_RBU_FULL below every subsequence) and the diagonal.    *)

let P2BU_RBU_ALL = prove
 (`!(u:A->bool) (w:B->bool).
     P2C_REQ_THM_10_2_VIEW_STATEMENT u /\ P2C_LEMMA_11_2_DB_STATEMENT u /\
     P2C_CANON_DERIV_STATEMENT u /\ P2C_CG_COMPACT_STATEMENT u w /\
     P2C_THM_5_33_STATEMENT u w /\ P2C_REQ_SLICE_FIX_STATEMENT u w /\
     P2C_REQ_NONNEG_BOUNDED_SLICE_STATEMENT w /\ P2C_COR_11_16_FLOW_STATEMENT w
     ==> ?eps0. &0 < eps0 /\
           !C eps kappa r0 mu V x t (top0:B topology) atlas0 g0 xl0 W0 (phi0:num->B->A).
              &1 < C /\ &0 < eps /\ eps <= eps0 /\
              (!T0. &0 < T0
                    ==> p2bu_good (C,eps,kappa,r0,mu) (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x t T0 (top0,atlas0) g0 xl0
                          W0 phi0)
              ==> ?d. p3_subseq d /\ !Tr. &0 < Tr ==> p2bu_rbus V x t d Tr`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP P2BU_RBU_FULL) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `eps0:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "full")) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `top0:B topology`;
    `atlas0:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl0:B`;
    `W0:num->B->bool`; `phi0:num->B->A`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "good")))) THEN
  (* below every subsequence r, RBU(T0) along a further subsequence *)
  SUBGOAL_THEN `!r T0. p3_subseq r /\ &0 < T0
                       ==> ?e. p3_subseq e /\ p2bu_rbus (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x t (r o e) T0`
  (LABEL_TAC "step") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "full" (MP_TAC o SPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
      `\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((r:num->num) n)`; `\n. (x:num->A) ((r:num->num) n)`;
      `\n. (t:num->real) ((r:num->num) n)`; `T0:real`; `top0:B topology`;
      `atlas0:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl0:B`;
      `\n. (W0:num->B->bool) ((r:num->num) n)`; `\n. (phi0:num->B->A) ((r:num->num) n)`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BU_GOOD_SUBSEQ THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "good" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:num->num` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[p2bu_rbus; o_DEF] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  (* the nested sequence *)
  MP_TAC(ISPECL
   [`\n:num r:num->num. p3_subseq r /\ p2bu_rbus (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (x:num->A) (t:num->real) r (&n + &1)`;
    `\n:num r:num->num r':num->num. ?e. p3_subseq e /\ r' = r o e`] DEPENDENT_CHOICE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "step" (MP_TAC o SPECL [`\n:num. n`; `&0 + &1`]) THEN
      ANTS_TAC THENL [REWRITE_TAC[p3_subseq] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `e:num->num` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `(\n:num. n) o (e:num->num)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC P2BU_SUBSEQ_O THEN ASM_REWRITE_TAC[p3_subseq];
      MAP_EVERY X_GEN_TAC [`n:num`; `r:num->num`] THEN STRIP_TAC THEN
      USE_THEN "step" (MP_TAC o SPECL [`r:num->num`; `&(SUC n) + &1`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `e:num->num` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `(r:num->num) o (e:num->num)` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC P2BU_SUBSEQ_O THEN ASM_REWRITE_TAC[];
        EXISTS_TAC `e:num->num` THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->num->num` (CONJUNCTS_THEN2 (LABEL_TAC "Pf")
    (LABEL_TAC "Rf"))) THEN
  MP_TAC(ISPEC `f:num->num->num` P2BU_DIAG_NESTED) THEN ANTS_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `j:num` THENL
     [USE_THEN "Pf" (MP_TAC o SPEC `j:num`) THEN SIMP_TAC[];
      USE_THEN "Rf" (MP_TAC o SPEC `j:num`) THEN SIMP_TAC[]];
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dev"))] THEN
  EXISTS_TAC `\n. (f:num->num->num) n n` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `Tr:real` THEN DISCH_TAC THEN
  MP_TAC(SPEC `Tr:real` REAL_ARCH_SIMPLE) THEN DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN
  SUBGOAL_THEN `p2bu_rbus (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (x:num->A) (t:num->real) (\n. (f:num->num->num) n n)
                  (&m + &1)` MP_TAC THENL
   [MATCH_MP_TAC P2BU_RBUS_EVSUB THEN EXISTS_TAC `(f:num->num->num) m` THEN
    USE_THEN "dev" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "Pf" (MP_TAC o SPEC `m:num`) THEN SIMP_TAC[];
    REWRITE_TAC[p2bu_rbus] THEN
    DISCH_THEN(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ] P2BU_RBU_MONO)) THEN
    ASM_REAL_ARITH_TAC]);;

(* RBU(T) for every T gives the region hypotheses of P2BU_FROM_SLICE_UPTO on *)
(* (-inf,0] and, for each a <= 0, a bound on [a,0] uniform in A.              *)

let P2BU_RBU_ALL_TO_J = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x t Q.
     (!n. &0 < Q n) /\ (!Tr. &0 < Tr ==> p2bu_rbu V x t Q Tr)
     ==> (!A a b. &0 < A /\ real_interval[a,b] SUBSET {s | s <= &0}
                  ==> ?CA N. !n. N <= n
                         ==> (!s. a <= s /\ s <= b
                                  ==> rfs_vball (V n) (t n) (x n) (A * inv(sqrt(Q n))) SUBSET
                                      topspace(rfs_vtop (V n) (t n + s / Q n))) /\
                             rfs_persists (V n)
                               (rfs_vball (V n) (t n) (x n) (A * inv(sqrt(Q n))))
                               (t n + a / Q n) (t n + b / Q n) /\
                             !s y. a <= s /\ s <= b /\
                                   y IN rfs_vball (V n) (t n) (x n) (A * inv(sqrt(Q n)))
                                   ==> p3_vrm (V n) (t n + s / Q n) y <= CA * Q n) /\
         (!a. a <= &0
              ==> ?K. !A. &0 < A
                     ==> ?N. !n s y. N <= n /\ a <= s /\ s <= &0 /\
                                     y IN rfs_vball (V n) (t n) (x n) (A * inv(sqrt(Q n)))
                                     ==> p3_vrm (V n) (t n + s / Q n) y <= K * Q n)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "Qpos") (LABEL_TAC "rbu")) THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`A:real`; `a:real`; `b:real`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                   `x:num->A`; `t:num->real`; `Q:num->real`; `abs a + &1`] P2BU_RBU_TO_J) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "rbu" MATCH_MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `real_interval[a,b] SUBSET {s:real | s <= &0}` THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN
    DISCH_THEN(fun th -> X_GEN_TAC `s:real` THEN DISCH_TAC THEN MP_TAC(SPEC `s:real` th)) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `a:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                   `x:num->A`; `t:num->real`; `Q:num->real`; `abs a + &1`] P2BU_RBU_TO_J) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "rbu" MATCH_MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REAL_ARITH_TAC]);;

(* The flow limit on (-inf,0] from RBU(T) for every T (P2BU_FLOW_FROM_RBU    *)
(* with J = (-inf,0]).                                                         *)

let P2BU_FLOW_FROM_RBU_ALL = prove
 (`!(u:A->bool) (w:B->bool).
     P2C_THM_5_33_STATEMENT u w
     ==> !V x t Q (top:B topology) atlas g0 xl W (phi:num->B->A).
           (!n. p2c_regular_view (V n:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                      (real->A->real^3^3)) /\
                rfs_pinched (V n) /\ (!s. s < &0 ==> rfs_vtop (V n) s = discrete_topology {})) /\
           (!B. ?N. !n. N <= n ==> B < Q n) /\
           p2c_slice_limit_with V x t Q (top,atlas) g0 xl W phi /\
           mfd_complete (top,atlas) g0 /\ (!Tr. &0 < Tr ==> p2bu_rbu V x t Q Tr)
           ==> ?sub (top':B topology) atlas' g.
                  p3_subseq sub /\
                  p3_flow_limit_on (\n. V (sub n)) (x o sub) (t o sub) (Q o sub)
                    {s | s <= &0} (top',atlas') g xl /\
                  connected_space top' /\
                  (!s. s <= &0
                       ==> riemannian_metric atlas' (g s) /\ mfd_complete (top',atlas') (g s) /\
                           (!y u v. y IN topspace top' /\ ~collinear {vec 0,u,v}
                                    ==> &0 <= mfd_sectional atlas' (g s) y u v)) /\
                  (!a b. a < b /\ b <= &0 ==> ricci_flow_on (top',atlas') a b g) /\
                  (!a. a < &0 ==> rfs_flow_upto (top',atlas') a (&0) g) /\
                  (!a. a <= &0
                       ==> ?K. !s y. a <= s /\ s <= &0 /\ y IN topspace top'
                                     ==> mfd_rm_norm atlas' (g s) y <= K) /\
                  (!y. y IN topspace top' ==> mfd_joinable (top',atlas') xl y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "views") (CONJUNCTS_THEN2 (LABEL_TAC "Qinf")
    (CONJUNCTS_THEN2 (LABEL_TAC "sl") (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rbu"))))) THEN
  SUBGOAL_THEN `!n. &0 < (Q:num->real) n` (LABEL_TAC "Qpos") THENL
   [USE_THEN "sl" (MP_TAC o REWRITE_RULE[p2c_slice_limit_with]) THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `Q:num->real`]
                P2BU_RBU_ALL_TO_J) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rj1") (LABEL_TAC "rj2")) THEN
  SUBGOAL_THEN `is_realinterval {s:real | s <= &0} /\
                (&0) IN {s:real | s <= &0} /\
                (!a0. a0 IN {s:real | s <= &0} /\
                      (!s. s IN {s:real | s <= &0} ==> a0 <= s) ==> a0 = &0)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[is_realinterval; IN_ELIM_THM; REAL_LE_REFL] THEN CONJ_TAC THENL
     [REAL_ARITH_TAC;
      X_GEN_TAC `a0:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `a0 - &1`) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `Q:num->real`;
                 `{s:real | s <= &0}`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`] P2BU_FROM_SLICE_UPTO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    FIRST [USE_THEN "views" (fun th -> MESON_TAC[th]) THEN NO_TAC;
           GEN_TAC THEN MATCH_MP_TAC P2BU_SLICE_BASE_IN THEN
           MAP_EVERY EXISTS_TAC [`Q:num->real`; `top:B topology`;
             `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl:B`;
             `W:num->B->bool`; `phi:num->B->A`] THEN
           ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub2:num->num` (X_CHOOSE_THEN `top':B topology`
    (X_CHOOSE_THEN `atlas':((B->bool)#(B->real^3))->bool` (X_CHOOSE_THEN `g:real->B->real^3^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "fl")
    (CONJUNCTS_THEN2 (LABEL_TAC "riem") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "rf") (CONJUNCTS_THEN2 (LABEL_TAC "compl")
    (CONJUNCTS_THEN2 (LABEL_TAC "upto") (LABEL_TAC "join")))))))))))) THEN
  SUBGOAL_THEN `!n:num. n <= sub2 n` (LABEL_TAC "ge") THENL
   [MP_TAC(ISPEC `sub2:num->num` MONOTONE_BIGGER) THEN REWRITE_TAC[GSYM p3_subseq] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top':B topology) (atlas':((B->bool)#(B->real^3))->bool)`
  ASSUME_TAC THENL
   [USE_THEN "fl" (MP_TAC o REWRITE_RULE[p3_flow_limit_on]) THEN SIMP_TAC[]; ALL_TAC] THEN
  (* completeness on J *)
  SUBGOAL_THEN `!s. s <= &0 ==> mfd_complete (top',atlas') ((g:real->B->real^3^3) s)`
  (LABEL_TAC "cs") THENL
   [X_GEN_TAC `s0:real` THEN STRIP_TAC THEN
    USE_THEN "rj2" (MP_TAC o C MP (ASSUME `s0 <= &0`) o SPEC `s0:real`) THEN
    DISCH_THEN(X_CHOOSE_THEN `K:real` (LABEL_TAC "K")) THEN
    USE_THEN "compl" (MP_TAC o SPECL [`s0:real`; `&0`; `K:real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL] THEN REPEAT CONJ_TAC THEN
      FIRST [REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
             X_GEN_TAC `A:real` THEN DISCH_TAC THEN USE_THEN "K" MATCH_MP_TAC THEN
             ASM_REWRITE_TAC[]];
      DISCH_THEN(MP_TAC o SPEC `s0:real`) THEN ASM_REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  (* sec >= 0 on J (Thm 5.33) *)
  SUBGOAL_THEN `!s y u v. s IN {s:real | s <= &0} /\ y IN topspace top' /\
                          ~collinear {vec 0,u,v}
                          ==> &0 <= mfd_sectional atlas' ((g:real->B->real^3^3) s) y u v`
  (LABEL_TAC "sec") THENL
   [UNDISCH_TAC `P2C_THM_5_33_STATEMENT (u:A->bool) (w:B->bool)` THEN
    REWRITE_TAC[P2C_THM_5_33_STATEMENT] THEN
    DISCH_THEN(MP_TAC o ISPECL
     [`\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub2:num->num) n)`;
      `(x:num->A) o (sub2:num->num)`; `(t:num->real) o (sub2:num->num)`;
      `(Q:num->real) o (sub2:num->num)`;
      `{s:real | s <= &0}`; `top':B topology`;
      `atlas':((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`]) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    REWRITE_TAC[o_THM] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`Q:num->real`; `sub2:num->num`] P2BU_QINF_SUBSEQ) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* |Rm| bounded on each [a,0] *)
  SUBGOAL_THEN `!a. a <= &0
                    ==> ?K. !s y. a <= s /\ s <= &0 /\ y IN topspace top'
                                  ==> mfd_rm_norm atlas' ((g:real->B->real^3^3) s) y <= K`
  (LABEL_TAC "rmb") THENL
   [X_GEN_TAC `a:real` THEN DISCH_TAC THEN
    USE_THEN "rj2" (MP_TAC o C MP (ASSUME `a <= &0`) o SPEC `a:real`) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `K:real` THEN DISCH_THEN(LABEL_TAC "K") THEN
    MAP_EVERY X_GEN_TAC [`s0:real`; `y0:B`] THEN STRIP_TAC THEN
    USE_THEN "fl" (MP_TAC o REWRITE_RULE[P2C_FLOW_LIMIT_ON_WITH]) THEN
    DISCH_THEN(X_CHOOSE_THEN `W':num->B->bool` (X_CHOOSE_THEN `phi':num->B->A` ASSUME_TAC)) THEN
    MP_TAC(ISPECL
     [`\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub2:num->num) n)`;
      `(x:num->A) o (sub2:num->num)`; `(t:num->real) o (sub2:num->num)`;
      `(Q:num->real) o (sub2:num->num)`;
      `{s:real | s <= &0}`; `top':B topology`;
      `atlas':((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
      `W':num->B->bool`; `phi':num->B->A`; `s0:real`; `y0:B`; `K:real`] P2BU_RM_TRANSFER) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[o_THM] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      USE_THEN "join" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `A:real` THEN DISCH_TAC THEN
      USE_THEN "K" (MP_TAC o C MP (ASSUME `&0 < A`) o SPEC `A:real`) THEN
      DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN EXISTS_TAC `N:num` THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `y:A`] THEN STRIP_TAC THEN
      USE_THEN "N" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* connectedness *)
  SUBGOAL_THEN `connected_space (top':B topology)` ASSUME_TAC THENL
   [REWRITE_TAC[CONNECTED_SPACE_IFF_CONNECTED_COMPONENT] THEN
    MAP_EVERY X_GEN_TAC [`y1:B`; `y2:B`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `y1:B`; `y2:B`]
      MFD_JOINABLE_CONNECTED_COMPONENT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `xl:B` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `xl:B`; `y1:B`]
        MFD_JOINABLE_SYM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      USE_THEN "join" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "join" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`sub2:num->num`; `top':B topology`;
                        `atlas':((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [USE_THEN "riem" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM];
      USE_THEN "cs" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM]];
    REPEAT STRIP_TAC THEN USE_THEN "rf" MATCH_MP_TAC THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN USE_THEN "upto" MATCH_MP_TAC THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC]);;

(* R / sqrt q <= r0 once q > (R / r0)^2.                                     *)

let P2BU_SCALE_SMALL = prove
 (`!R r0 q. &0 < r0 /\ (R / r0) pow 2 < q ==> R * inv(sqrt q) <= r0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(R / r0) pow 2` THEN
    ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt q` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `R / r0 < sqrt q` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_RSQRT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

(* The local noncollapsing hypothesis of P2BU_KNC_LOCAL for a blow-up       *)
(* limit on (-inf,0]: the image of a limit point lies, eventually, in the   *)
(* rescaled ball about x k at t k (LIM_BALL_OUT at time 0), where the        *)
(* backward hypothesis gives noncollapsing on scales <= r0 at every time of *)
(* (t k - Tb / Q k, t k], and R / sqrt(Q k) <= r0 eventually.                *)

let P2BU_KNC_HYP = prove
 (`!kappa r0 (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x t (top:B topology) atlas g xl W (phi:num->B->A) R.
     (!n. p2c_regular_view (V n)) /\
     (!B. ?N. !n. N <= n ==> B < rfs_vscalar (V n) (t n) (x n)) /\
     &0 < r0 /\ (!Tb. &0 < Tb ==> p2c_vblowup_back (kappa,r0) V x t Tb) /\
     p2c_flow_limit_with V x t (\n. rfs_vscalar (V n) (t n) (x n)) {s | s <= &0}
       (top,atlas) g xl W phi /\
     riemannian_metric atlas (g (&0)) /\ mfd_complete (top,atlas) (g (&0)) /\
     (!y. y IN topspace top ==> mfd_joinable (top,atlas) xl y)
     ==> !tt xx. tt IN {s | s <= &0} /\ xx IN topspace top
                 ==> ?k1. !k. k1 <= k
                              ==> p3_noncoll_at (V k) kappa
                                    (R * inv(sqrt(rfs_vscalar (V k) (t k) (x k))))
                                    (phi k xx) (t k + tt / rfs_vscalar (V k) (t k) (x k))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "views") (CONJUNCTS_THEN2 (LABEL_TAC "Qinf")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "back")
    (CONJUNCTS_THEN2 (LABEL_TAC "fl") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "join")))))))) THEN
  MAP_EVERY X_GEN_TAC [`tt:real`; `xx:B`] THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  USE_THEN "fl" (STRIP_ASSUME_TAC o REWRITE_RULE[] o GEN_REWRITE_RULE I [p2c_flow_limit_with]) THEN
  SUBGOAL_THEN `!n. &0 < rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) ((t:num->real) n) ((x:num->A) n)`
  (LABEL_TAC "Qpos") THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `D = abs(mfd_dist (top,atlas) ((g:real->B->real^3^3) (&0)) xl xx) + &1` THEN
  SUBGOAL_THEN `&0 < D /\ (xx:B) IN mfd_ball (top,atlas) ((g:real->B->real^3^3) (&0)) xl D`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [USE_THEN "join" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the image of xx in the rescaled ball at t k *)
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`;
    `\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) ((t:num->real) n) ((x:num->A) n)`;
    `{s:real | s <= &0}`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `g:real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `&0`; `xl:B`;
    `D:real`; `D + &1`] LIM_BALL_OUT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM; REAL_LE_REFL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2CO_REGULAR_SLICES THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "out")) THEN
  (* noncollapsing at earlier times on that ball *)
  USE_THEN "back" (MP_TAC o SPEC `&1 - tt`) THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[p2c_vblowup_back] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "nc") o SPEC `D + &1`) THEN
  USE_THEN "Qinf" (X_CHOOSE_THEN `N2:num` (LABEL_TAC "big") o SPEC `(R / r0) pow 2`) THEN
  EXISTS_TAC `k0 + N1 + N2:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC P2BU_NONCOLL_AT_MONO THEN EXISTS_TAC `r0:real` THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC P2BU_SCALE_SMALL THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "big" MATCH_MP_TAC THEN UNDISCH_TAC `k0 + N1 + N2 <= k:num` THEN ARITH_TAC] THEN
  USE_THEN "nc" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL
   [UNDISCH_TAC `k0 + N1 + N2 <= k:num` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
  USE_THEN "Qpos" (ASSUME_TAC o SPEC `k:num`) THEN
  SUBGOAL_THEN `&0 < inv(rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) ((t:num->real) k) ((x:num->A) k))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_ARITH `t + a <= t <=> a <= &0`] THEN
    MATCH_MP_TAC(REAL_ARITH `!tt i. &0 <= --tt * i ==> tt * i <= &0`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    USE_THEN "out" (MP_TAC o SPECL [`k:num`; `xx:B`]) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `k0 + N1 + N2 <= k:num` THEN ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[P2CO_VBALL]]);;

(* ========================================================================= *)
(* MT Thm 11.8 part 2, both parts together, and the main theorem.           *)
(* ========================================================================= *)

(* MT Thm 11.8, the second part (the backward hypothesis for every Tb) in   *)
(* view form: one subsequence along which the flows converge on (-T,0] for *)
(* every T (RBU(T) for every T, the flow limit on (-inf,0], times k + 1),   *)
(* and the limit is a kappa-solution (non-flat by P2BU_NONFLAT,             *)
(* kappa-noncollapsed on all scales by P2BU_KNC_LOCAL and P2BU_KNC_HYP).     *)

let P2BU_THM_11_8_PART2 = prove
 (`!(u:A->bool) (w:B->bool).
     P2C_REQ_THM_10_2_VIEW_STATEMENT u /\ P2C_LEMMA_11_2_DB_STATEMENT u /\
     P2C_CANON_DERIV_STATEMENT u /\ P2C_CG_COMPACT_STATEMENT u w /\
     P2C_THM_5_33_STATEMENT u w /\ P2C_REQ_SLICE_FIX_STATEMENT u w /\
     P2C_REQ_NONNEG_BOUNDED_SLICE_STATEMENT w /\ P2C_COR_11_16_FLOW_STATEMENT w /\
     P2B_REQ_FLAT_FORWARD_STATEMENT w
     ==> ?eps0. &0 < eps0 /\
           !C eps kappa r0 mu V x t.
              &1 < C /\ &0 < eps /\ eps <= eps0 /\
              p2c_vblowup_seq (C,eps,kappa,r0,mu) (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x t /\
              (!n s. apx_sphere_sep (rfs_vtop (V n) s) (rfs_vatlas (V n) s)) /\
              (!A. ?N. !n. N <= n
                           ==> compact_in (rfs_vtop (V n) (t n))
                                 (rfs_vtop (V n) (t n) closure_of
                                  rfs_vball (V n) (t n) (x n)
                                    (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n))))))
              ==> (!Tb. &0 < Tb ==> p2c_vblowup_back (kappa,r0) V x t Tb)
                  ==> ?sub (top:B topology) atlas g xl.
                         p3_subseq sub /\
                         (!Tl. &0 < Tl
                               ==> p3_flow_limit (\n. V (sub n)) (x o sub) (t o sub)
                                     (\n. rfs_vscalar (V (sub n)) (t (sub n)) (x (sub n)))
                                     (top,atlas) g xl Tl) /\
                         p2b_kappa_solution kappa (top,atlas) g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`u:A->bool`; `w:B->bool`] P2BU_GOOD_START) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gs"))) THEN
  MP_TAC(SPECL [`u:A->bool`; `w:B->bool`] P2BU_RBU_ALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "all"))) THEN
  EXISTS_TAC `min e1 e2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN DISCH_THEN(LABEL_TAC "back") THEN
  SUBGOAL_THEN `&0 < kappa /\ &0 < r0` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[p2c_vblowup_seq] o check (fun th ->
      can (find_term (fun u -> try fst(dest_const u) = "p2c_vblowup_seq" with _ -> false))
          (concl th))) THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the connected time-0 limit, good for every T0 *)
  USE_THEN "gs" (MP_TAC o SPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `&1`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "back" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub1:num->num` (X_CHOOSE_THEN `top0:B topology`
    (X_CHOOSE_THEN `atlas0:((B->bool)#(B->real^3))->bool` (X_CHOOSE_THEN `g0:B->real^3^3`
    (X_CHOOSE_THEN `xl0:B` (X_CHOOSE_THEN `W0:num->B->bool` (X_CHOOSE_THEN `phi0:num->B->A`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "good1"))))))))) THEN
  SUBGOAL_THEN
   `!T0. &0 < T0
         ==> p2bu_good (C,eps,kappa,r0,mu) (\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub1:num->num) n))
               (\n. (x:num->A) (sub1 n)) (\n. (t:num->real) (sub1 n)) T0
               (top0:B topology,atlas0:((B->bool)#(B->real^3))->bool) (g0:B->real^3^3)
               (xl0:B) (W0:num->B->bool) (phi0:num->B->A)`
  (LABEL_TAC "goodall") THENL
   [X_GEN_TAC `T0:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `!Tb. &0 < Tb /\ Tb < T0
           ==> p2c_vblowup_back (kappa,r0) (\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub1:num->num) n))
                 (\n. (x:num->A) (sub1 n)) (\n. (t:num->real) (sub1 n)) Tb`
    ASSUME_TAC THENL
     [X_GEN_TAC `Tb:real` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`kappa:real`; `r0:real`; `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `Tb:real`;
                     `sub1:num->num`] P2BU_BACK_SUBSEQ) THEN
      REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "back" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "good1" (MP_TAC o REWRITE_RULE[p2bu_good]) THEN
    ASM_REWRITE_TAC[p2bu_good] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* RBU(T) for every T along a further subsequence d *)
  USE_THEN "all" (MP_TAC o SPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub1:num->num) n)`; `\n. (x:num->A) ((sub1:num->num) n)`;
    `\n. (t:num->real) ((sub1:num->num) n)`; `top0:B topology`;
    `atlas0:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl0:B`;
    `W0:num->B->bool`; `phi0:num->B->A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num->num` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rbs"))) THEN
  USE_THEN "goodall" (MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(MP_TAC o C CONJ (ASSUME `p3_subseq (d:num->num)`)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP P2BU_GOOD_SUBSEQ) THEN REWRITE_TAC[p2bu_good] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "bs2") (CONJUNCTS_THEN2 (LABEL_TAC "sep2")
    (CONJUNCTS_THEN2 (LABEL_TAC "cc2") (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "sl2") (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))))) THEN
  USE_THEN "bs2" (MP_TAC o REWRITE_RULE[p2c_vblowup_seq]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "views2")
    (CONJUNCTS_THEN2 (LABEL_TAC "Qinf2") (K ALL_TAC)))))) THEN
  (* the flow limit on (-inf,0] *)
  MP_TAC(SPECL [`u:A->bool`; `w:B->bool`] P2BU_FLOW_FROM_RBU_ALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub1:num->num) ((d:num->num) n))`;
    `\n. (x:num->A) ((sub1:num->num) ((d:num->num) n))`;
    `\n. (t:num->real) ((sub1:num->num) ((d:num->num) n))`;
    `\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub1:num->num) ((d:num->num) n)))
                     ((t:num->real) (sub1 (d n))) ((x:num->A) (sub1 (d n)))`;
    `top0:B topology`; `atlas0:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl0:B`;
    `\n. (W0:num->B->bool) ((d:num->num) n)`; `\n. (phi0:num->B->A) ((d:num->num) n)`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    FIRST
     [USE_THEN "views2" (fun th -> MESON_TAC[th]) THEN NO_TAC;
      USE_THEN "Qinf2" ACCEPT_TAC;
      X_GEN_TAC `Tr:real` THEN DISCH_TAC THEN
      USE_THEN "rbs" (MP_TAC o C MP (ASSUME `&0 < Tr`) o SPEC `Tr:real`) THEN
      REWRITE_TAC[p2bu_rbus] THEN NO_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub3:num->num` (X_CHOOSE_THEN `top:B topology`
    (X_CHOOSE_THEN `atlas:((B->bool)#(B->real^3))->bool` (X_CHOOSE_THEN `g:real->B->real^3^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "fl")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "Jp")
    (CONJUNCTS_THEN2 (LABEL_TAC "rf") (CONJUNCTS_THEN2 (LABEL_TAC "upto")
    (CONJUNCTS_THEN2 (LABEL_TAC "rmb") (LABEL_TAC "join")))))))))))) THEN
  USE_THEN "fl" (LABEL_TAC "fl3" o REWRITE_RULE[o_DEF]) THEN
  SUBGOAL_THEN `hausdorff_space (top:B topology) /\
                smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool) /\
                xl0 IN topspace top` STRIP_ASSUME_TAC THENL
   [USE_THEN "fl" (MP_TAC o REWRITE_RULE[p3_flow_limit_on]) THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!n:num. p2c_regular_view ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub1:num->num) ((d:num->num) ((sub3:num->num) n))))`
  ASSUME_TAC THENL
   [GEN_TAC THEN USE_THEN "views2" (MP_TAC o SPEC `(sub3:num->num) n`) THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the flow limit with W and phi *)
  USE_THEN "fl3" (MP_TAC o REWRITE_RULE[P2C_FLOW_LIMIT_ON_WITH]) THEN
  DISCH_THEN(X_CHOOSE_THEN `W:num->B->bool` (X_CHOOSE_THEN `phi:num->B->A` (LABEL_TAC "flw"))) THEN
  (* times k + 1 *)
  MP_TAC(ISPECL [`\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub1:num->num) ((d:num->num) ((sub3:num->num) n)))`;
    `\n. (x:num->A) ((sub1:num->num) ((d:num->num) ((sub3:num->num) n)))`;
    `\n. (t:num->real) ((sub1:num->num) ((d:num->num) ((sub3:num->num) n)))`;
    `\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub1:num->num) ((d:num->num) ((sub3:num->num) n))))
                     ((t:num->real) (sub1 (d (sub3 n)))) ((x:num->A) (sub1 (d (sub3 n))))`;
    `{s:real | s <= &0}`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl0:B`;
    `\k:num. &k + &1`] P2BU_FLOW_LIMIT_OF_ON) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "fl3" ACCEPT_TAC;
      X_GEN_TAC `k:num` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_SUC; SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN
      MP_TAC(SPEC `k:num` REAL_POS) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub4:num->num` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fls"))) THEN
  MAP_EVERY EXISTS_TAC
   [`(sub1:num->num) o (d:num->num) o (sub3:num->num) o (sub4:num->num)`;
    `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`;
    `xl0:B`] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC P2BU_SUBSEQ_O THEN CONJ_TAC) THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `Tl:real` THEN DISCH_TAC THEN
    USE_THEN "fls" (MP_TAC o SPEC `Tl:real`) THEN ANTS_TAC THENL
     [REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        X_GEN_TAC `a:real` THEN DISCH_TAC THEN
        MP_TAC(SPEC `a:real` REAL_ARCH_SIMPLE) THEN MATCH_MP_TAC MONO_EXISTS THEN
        REAL_ARITH_TAC;
        X_GEN_TAC `a:real` THEN STRIP_TAC THEN USE_THEN "upto" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN(ACCEPT_TAC o REWRITE_RULE[o_DEF]);
    ALL_TAC] THEN
  (* the kappa-solution *)
  REWRITE_TAC[p2b_kappa_solution; p2c_kappa_sol] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  FIRST
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `xl0:B` THEN ASM_REWRITE_TAC[] THEN
    NO_TAC;
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "Jp" (MP_TAC o C MP (ASSUME `s <= &0`) o SPEC `s:real`) THEN SIMP_TAC[] THEN
    NO_TAC;
    MAP_EVERY X_GEN_TAC [`s:real`; `y:B`; `v1:real^3`; `v2:real^3`] THEN STRIP_TAC THEN
    USE_THEN "Jp" (MP_TAC o C MP (ASSUME `s <= &0`) o SPEC `s:real`) THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN NO_TAC;
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "rmb" (X_CHOOSE_TAC `K:real` o C MP (ASSUME `s <= &0`) o SPEC `s:real`) THEN
    EXISTS_TAC `K:real` THEN X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN NO_TAC;
    (* non-flat *)
    MATCH_MP_TAC P2BU_NONFLAT THEN EXISTS_TAC `w:B->bool` THEN EXISTS_TAC `xl0:B` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    FIRST
     [USE_THEN "rf" ACCEPT_TAC;
      USE_THEN "Jp" ACCEPT_TAC;
      USE_THEN "rmb" ACCEPT_TAC;
      USE_THEN "upto" ACCEPT_TAC;
      MATCH_MP_TAC(REAL_ARITH `x = &1 ==> &0 < x`) THEN
      MATCH_MP_TAC P2BU_BASE_SCALAR_ONE THEN
      MAP_EVERY EXISTS_TAC
       [`\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub1:num->num) ((d:num->num) ((sub3:num->num) n)))`;
        `\n. (x:num->A) ((sub1:num->num) ((d:num->num) ((sub3:num->num) n)))`;
        `\n. (t:num->real) ((sub1:num->num) ((d:num->num) ((sub3:num->num) n)))`;
        `{s:real | s <= &0}`; `top:B topology`; `W:num->B->bool`; `phi:num->B->A`] THEN
      REWRITE_TAC[] THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THEN
      FIRST
       [USE_THEN "flw" ACCEPT_TAC;
        X_GEN_TAC `s:real` THEN DISCH_TAC THEN
        USE_THEN "Jp" (MP_TAC o C MP (ASSUME `s <= &0`) o SPEC `s:real`) THEN SIMP_TAC[]]] THEN
    NO_TAC;
    (* kappa-noncollapsed on all scales *)
    X_GEN_TAC `R:real` THEN
    MATCH_MP_TAC P2BU_KNC_LOCAL THEN
    MAP_EVERY EXISTS_TAC
     [`\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub1:num->num) ((d:num->num) ((sub3:num->num) n)))`;
      `\n. (x:num->A) ((sub1:num->num) ((d:num->num) ((sub3:num->num) n)))`;
      `\n. (t:num->real) ((sub1:num->num) ((d:num->num) ((sub3:num->num) n)))`;
      `\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub1:num->num) ((d:num->num) ((sub3:num->num) n))))
                       ((t:num->real) (sub1 (d (sub3 n)))) ((x:num->A) (sub1 (d (sub3 n))))`;
      `xl0:B`; `W:num->B->bool`; `phi:num->B->A`] THEN
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    FIRST
     [USE_THEN "flw" ACCEPT_TAC;
      MATCH_MP_TAC P2CO_REGULAR_SLICES THEN ASM_REWRITE_TAC[] THEN NO_TAC;
      MAP_EVERY X_GEN_TAC [`k:num`; `tau:real`] THEN
      MP_TAC(MATCH_MP P2CV_RV_SVS (SPEC `k:num`
        (ASSUME `!n:num. p2c_regular_view ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub1:num->num) ((d:num->num) ((sub3:num->num) n))))`))) THEN
      REWRITE_TAC[p2a_svs; P2A_VIEW_PROJ_3] THEN SIMP_TAC[] THEN NO_TAC;
      X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
      USE_THEN "Jp" (MP_TAC o C MP (ASSUME `s <= &0`) o SPEC `s:real`) THEN SIMP_TAC[] THEN
      NO_TAC;
      MP_TAC(ISPECL [`kappa:real`; `r0:real`;
        `\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub1:num->num) ((d:num->num) ((sub3:num->num) n)))`;
        `\n. (x:num->A) ((sub1:num->num) ((d:num->num) ((sub3:num->num) n)))`;
        `\n. (t:num->real) ((sub1:num->num) ((d:num->num) ((sub3:num->num) n)))`;
        `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`;
        `xl0:B`; `W:num->B->bool`; `phi:num->B->A`; `R:real`] P2BU_KNC_HYP) THEN
      REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
      FIRST
       [X_GEN_TAC `B:real` THEN USE_THEN "Qinf2" (X_CHOOSE_TAC `N:num` o SPEC `B:real`) THEN
        EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BU_SUBSEQ_GE THEN ASM_REWRITE_TAC[] THEN NO_TAC;
        X_GEN_TAC `Tb:real` THEN DISCH_TAC THEN
        MP_TAC(ISPECL [`kappa:real`; `r0:real`; `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `Tb:real`;
                       `(sub1:num->num) o (d:num->num) o (sub3:num->num)`] P2BU_BACK_SUBSEQ) THEN
        REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
         [USE_THEN "back" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[GSYM o_DEF] THEN
          REPEAT(MATCH_MP_TAC P2BU_SUBSEQ_O THEN CONJ_TAC) THEN ASM_REWRITE_TAC[]] THEN NO_TAC;
        USE_THEN "flw" ACCEPT_TAC;
        USE_THEN "Jp" (MP_TAC o SPEC `&0`) THEN REWRITE_TAC[REAL_LE_REFL] THEN SIMP_TAC[]]] THEN
    NO_TAC;
    (* bounds on [a,0] *)
    X_GEN_TAC `a:real` THEN DISCH_TAC THEN
    USE_THEN "rmb" (MP_TAC o C MP (ASSUME `a <= &0`) o SPEC `a:real`) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `K:real` THEN
    DISCH_THEN(fun th -> MAP_EVERY X_GEN_TAC [`s:real`; `y:B`] THEN STRIP_TAC THEN
      MATCH_MP_TAC th THEN ASM_REWRITE_TAC[])]);;

(* MT Thm 11.8 in view form from the route hypotheses: both parts.           *)

let P2BU_THM_11_8_CORE = prove
 (`!(u:A->bool) (w:B->bool).
     P2C_REQ_THM_10_2_VIEW_STATEMENT u /\ P2C_LEMMA_11_2_DB_STATEMENT u /\
     P2C_CANON_DERIV_STATEMENT u /\ P2C_CG_COMPACT_STATEMENT u w /\
     P2C_THM_5_33_STATEMENT u w /\ P2C_REQ_SLICE_FIX_STATEMENT u w /\
     P2C_REQ_NONNEG_BOUNDED_SLICE_STATEMENT w /\ P2C_COR_11_16_FLOW_STATEMENT w /\
     P2B_REQ_FLAT_FORWARD_STATEMENT w
     ==> P2C_THM_11_8_VIEW_STATEMENT u w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`u:A->bool`; `w:B->bool`] P2BU_THM_11_8_PART1) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "p1"))) THEN
  MP_TAC(SPECL [`u:A->bool`; `w:B->bool`] P2BU_THM_11_8_PART2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "p2"))) THEN
  REWRITE_TAC[P2C_THM_11_8_VIEW_STATEMENT] THEN EXISTS_TAC `min e1 e2` THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `T0:real` THEN STRIP_TAC THEN
    USE_THEN "p1" (MP_TAC o SPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
      `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
      `x:num->A`; `t:num->real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `T0:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN SIMP_TAC[];
    USE_THEN "p2" (MP_TAC o SPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
      `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
      `x:num->A`; `t:num->real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]]);;

(* Headline: MT Thm 11.8 in view form along its route (CG_COMPACT at real^3 *)
(* is P2CK_CG_COMPACT; Cor 11.16 in flow form is P2C_COR_11_16_FLOW).        *)

let P2BU_THM_11_8_VIEW_ROUTE = prove
 (`!u:A->bool. P2C_THM_11_8_VIEW_ROUTE_STATEMENT u (:real^3)`,
  GEN_TAC THEN REWRITE_TAC[P2C_THM_11_8_VIEW_ROUTE_STATEMENT] THEN STRIP_TAC THEN
  MATCH_MP_TAC P2BU_THM_11_8_CORE THEN
  ASM_REWRITE_TAC[P2CK_CG_COMPACT; P2C_COR_11_16_FLOW]);;


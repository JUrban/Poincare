(* ========================================================================= *)
(* Unit pc_p2c_lcgc (Part 2C, the general form G of local compactness): the  *)
(* exhaustion of the glued limit for the general levels of pc_p2c_lcgb,      *)
(* without completeness.  A point of the chart b at level j lies in a        *)
(* level-(j+1) chart ball of radius rho(j+1)/8 (the level-up lemma: the      *)
(* shift clause, pigeonhole and the D-limit, as in P2CC_NET_COVER and        *)
(* P2CC_DELTA_CHART); the exhaustion is W j = the level-(j+1) pieces of      *)
(* radius rho(j+1)/5, with compact closures and closure of W j inside W      *)
(* (j+1); the closure of W j is covered by the level-(j+2) pieces of radius  *)
(* 2 rho/15 (what the embeddings of cgemb need).  The levels of              *)
(* pc_p2c_cgglue are general levels (the ball instance).                     *)
(* ========================================================================= *)

needs "src/pc_p2c_lcgb.ml";;
needs "src/pc_p2c_cgcomp.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The level-up lemma.                                                        *)
(* ------------------------------------------------------------------------- *)

let P2GC_NET_COVER = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc s D b z.
     p2gb_seq top atlas h x /\ p2gb_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_dsys top atlas h yc rho s D /\ z IN cball(vec 0,rho(NUMFST b) / &2)
     ==> ?i. i < P (SUC (NUMFST b)) /\
             p2cg_dv D (NUMPAIR (SUC (NUMFST b)) i) (vec 0) b z <= rho (SUC (NUMFST b)) / &8`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `j = NUMFST b` THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [p2cg_dsys]) THEN
  FIRST_ASSUM(LABEL_TAC "big" o MATCH_MP MONOTONE_BIGGER) THEN
  SUBGOAL_THEN `&0 < (rho:num->real) j /\ rho j < &1 /\ &0 < rho (SUC j) /\ rho (SUC j) < &1`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL (p2cg_std @ [`j:num`]) P2GB_RHO_POS) THEN
    MP_TAC(ISPECL (p2cg_std @ [`SUC j`]) P2GB_RHO_POS) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(z:real^3) < (rho:num->real) j` ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^3) IN cball(vec 0,(rho:num->real) j / &2)` THEN
    REWRITE_TAC[IN_CBALL_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. p2cg_nv (N0:num->num) (Nn:num->num) b + N0 (SUC j) + Nn (SUC j) <= n
        ==> ?i. i < (P:num->num) (SUC j) /\
                p2cg_dk (top:num->A topology) (atlas:num->((A->bool)#(A->real^3))->bool) (h:num->A->real^3^3)
                  (yc:num->num->num->A) ((s:num->num) n) (NUMPAIR (SUC j) i) (vec 0) b z <
                (rho:num->real) (SUC j) / &8`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    ABBREV_TAC `k = (s:num->num) n` THEN
    SUBGOAL_THEN `p2cg_nv (N0:num->num) (Nn:num->num) b <= k /\ N0 (SUC j) + Nn (SUC j) <= k`
    STRIP_ASSUME_TAC THENL
     [USE_THEN "big" (MP_TAC o SPEC `n:num`) THEN ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num` o GEN_REWRITE_RULE I [p2gb_seq]) THEN
    MP_TAC(ISPECL (p2cg_std @ [`b:num`; `k:num`]) P2GB_NCH_BASIC) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "c0") (LABEL_TAC "nb")) THEN
    USE_THEN "nb" (MP_TAC o SPEC `z:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "nb" (MP_TAC o SPEC `vec 0:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[NORM_0]; ALL_TAC] THEN
    USE_THEN "c0" (fun th -> REWRITE_TAC[th]) THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `p2cg_nch (top:num->A topology) atlas (h:num->A->real^3^3) (yc:num->num->num->A) k b z IN
      mfd_ball ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k)
               ((h:num->A->real^3^3) k) ((yc:num->num->num->A) j k (NUMSND b)) ((rho:num->real) j)`
    ASSUME_TAC THENL
     [REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
      SUBGOAL_THEN `p2cg_ctr (yc:num->num->num->A) k b = yc j k (NUMSND b)` (SUBST1_TAC o SYM) THENL
       [ASM_REWRITE_TAC[p2cg_ctr]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MFD_JOINABLE_SYM; MFD_JOINABLE_TRANS];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`j:num`; `k:num`; `NUMSND b`] o last o CONJUNCTS o
                GEN_REWRITE_RULE I [p2gb_levels]) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `p2cg_nv (N0:num->num) (Nn:num->num) b <= k` THEN
      ASM_REWRITE_TAC[p2cg_nv] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `p2cg_nch (top:num->A topology) (atlas:num->((A->bool)#(A->real^3))->bool) (h:num->A->real^3^3)
                                (yc:num->num->num->A) k b z`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `i:num` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL (p2cg_std @ [`NUMPAIR (SUC j) i`; `k:num`]) P2GB_NCH_BASIC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[p2cg_nv; NUMPAIR_DEST] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
    ASM_REWRITE_TAC[p2cg_dk] THEN
    UNDISCH_TAC `p2cg_nch (top:num->A topology) atlas (h:num->A->real^3^3)
                   (yc:num->num->num->A) k b z IN
                 mfd_ball ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k)
                          ((h:num->A->real^3^3) k) (yc (SUC j) k i) ((rho:num->real) (SUC j) / &8)` THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM; p2cg_ctr; NUMPAIR_DEST] THEN SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP P2CC_PIGEONHOLE) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `i:num` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "freq")) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                 `h:num->A->real^3^3`; `yc:num->num->num->A`; `rho:num->real`;
                 `s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`; `NUMPAIR (SUC j) i`; `b:num`;
                 `vec 0:real^3`; `z:real^3`] P2CG_D_SEQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[NUMPAIR_DEST; CENTRE_IN_CBALL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `p2cg_dv (D:num#num->real^(3,3)finite_sum->real^1) (NUMPAIR (SUC j) i) (vec 0) b z - (rho:num->real) (SUC j) / &8`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "n2")) THEN
  USE_THEN "freq" (MP_TAC o SPEC `N2:num`) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  USE_THEN "n2" (MP_TAC o C MP (ASSUME `N2 <= n:num`) o SPEC `n:num`) THEN
  UNDISCH_TAC `p2cg_dk (top:num->A topology) (atlas:num->((A->bool)#(A->real^3))->bool) (h:num->A->real^3^3)
                 (yc:num->num->num->A) ((s:num->num) n) (NUMPAIR (SUC j) i) (vec 0) b z <
               (rho:num->real) (SUC j) / &8` THEN
  REAL_ARITH_TAC);;

(* A point of a chart at level j is a point of a level-(j+1) chart near its *)
(* centre.                                                                    *)

let P2GC_LEVEL_UP = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc s D (kp:num->real^3->real^3) b z.
     p2gb_seq top atlas h x /\ p2gb_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_dsys top atlas h yc rho s D /\
     p2cl_glue (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D) kp /\
     z IN p2cg_dm rho b
     ==> ?i w. i < P (SUC (NUMFST b)) /\ norm w <= rho (SUC (NUMFST b)) / &8 /\
               kp b z = kp (NUMPAIR (SUC (NUMFST b)) i) w`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CG_BALL4_CBALL o REWRITE_RULE[p2cg_dm] o
              check (fun th -> concl th = `(z:real^3) IN p2cg_dm (rho:num->real) b`)) THEN
  MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `b:num`; `z:real^3`]) P2GC_NET_COVER) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `j = SUC(NUMFST b)` THEN
  MP_TAC(ISPECL (p2cg_std @ [`NUMPAIR j i`]) P2GB_CENTRE_CBALL) THEN
  ASM_REWRITE_TAC[NUMPAIR_DEST] THEN STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `NUMPAIR j i`; `vec 0:real^3`; `b:num`; `z:real^3`]) P2GB_DV_SYM) THEN
  ASM_REWRITE_TAC[NUMPAIR_DEST] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:real^3) IN p2cg_om (rho:num->real) (D:num#num->real^(3,3)finite_sum->real^1) b (NUMPAIR j i)` ASSUME_TAC THENL
   [REWRITE_TAC[P2CG_IN_OM; NUMPAIR_DEST; IN_BALL_0] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `b:num`; `NUMPAIR j i`; `z:real^3`]) P2GB_TR_PROPS) THEN
  ASM_REWRITE_TAC[NUMPAIR_DEST] THEN STRIP_TAC THEN
  EXISTS_TAC `p2cg_tr (rho:num->real) (D:num#num->real^(3,3)finite_sum->real^1) b (NUMPAIR j i) z` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `p2cg_dv (D:num#num->real^(3,3)finite_sum->real^1) b z (NUMPAIR j i) (vec 0)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC P2GB_DV_ZERO_NORM THEN
    MAP_EVERY EXISTS_TAC (p2cg_std @ [`s:num->num`]) THEN
    ASM_REWRITE_TAC[NUMPAIR_DEST] THEN
    UNDISCH_TAC `p2cg_tr (rho:num->real) (D:num#num->real^(3,3)finite_sum->real^1) b (NUMPAIR j i) z IN ball(vec 0,rho j / &4)` THEN
    REWRITE_TAC[IN_BALL_0; IN_CBALL_0] THEN ASM_REAL_ARITH_TAC;
    FIRST_ASSUM(MP_TAC o SPECL [`b:num`; `NUMPAIR j i`; `z:real^3`;
                                `p2cg_tr (rho:num->real) (D:num#num->real^(3,3)finite_sum->real^1) b (NUMPAIR j i) z`] o
                GEN_REWRITE_RULE I [p2cl_glue]) THEN
    ASM_REWRITE_TAC[p2cg_dm; NUMPAIR_DEST]]);;

(* ------------------------------------------------------------------------- *)
(* The base charts (level J, net index 0, centred at x k) all               *)
(* glue the centre to the base point p2cc_xl kp; the glued manifold facts;  *)
(* each level above 0 has at least one net point (P (SUC j) > 0).           *)
(* ------------------------------------------------------------------------- *)

let P2GC_A0_CTR = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc k J.
     p2gb_levels top atlas h x rho K N0 B NB P Nn yc /\ Nn J <= k
     ==> p2cg_ctr yc k (NUMPAIR J 0) = x k`,
  REWRITE_TAC[p2gb_levels; p2cg_ctr; NUMPAIR_DEST] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`J:num`; `k:num`] o
                check (fun th -> can (find_term ((=) `yc:num->num->num->A`)) (concl th) &&
                                 can (find_term ((=) `x:num->A`)) (concl th))) THEN
  ASM_SIMP_TAC[]);;

let P2GC_XL_CHART = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl (kp:num->real^3->real^3) J.
     p2gb_seq top atlas h x /\ p2gb_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_limit top atlas h yc rho sq D Gl /\
     p2cl_glue (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D) kp
     ==> kp (NUMPAIR J 0) (vec 0) = p2cc_xl kp`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cg_limit]) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [p2cg_dsys]) THEN
  MP_TAC(ISPECL (p2cg_std @ [`J:num`]) P2GB_RHO_POS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`0`]) P2GB_RHO_POS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2cg_dv (D:num#num->real^(3,3)finite_sum->real^1) (NUMPAIR J 0) (vec 0) p2cc_a0 (vec 0) = &0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                   `h:num->A->real^3^3`; `yc:num->num->num->A`; `rho:num->real`;
                   `sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                   `NUMPAIR J 0`; `p2cc_a0`; `vec 0:real^3`; `vec 0:real^3`] P2CG_D_SEQ) THEN
    ASM_REWRITE_TAC[CENTRE_IN_CBALL; NUMPAIR_DEST; P2CC_A0] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
    MATCH_MP_TAC(MESON[REAL_LT_REFL; REAL_ARITH `~(x = &0) ==> &0 < abs x`]
                   `!x. (!e. &0 < e ==> abs x < e) ==> x = &0`) THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
    ABBREV_TAC `n = N1 + p2cg_nv (N0:num->num) (Nn:num->num) (NUMPAIR J 0) + p2cg_nv N0 Nn p2cc_a0 +
                    Nn J + Nn 0` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    ANTS_TAC THENL [EXPAND_TAC "n" THEN ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `y = &0 ==> abs(y - x) < e ==> abs x < e`) THEN
    FIRST_ASSUM(LABEL_TAC "big" o MATCH_MP MONOTONE_BIGGER) THEN
    SUBGOAL_THEN `p2cg_nv (N0:num->num) (Nn:num->num) (NUMPAIR J 0) <= (sq:num->num) n /\
                  p2cg_nv N0 Nn p2cc_a0 <= sq n /\ Nn J <= sq n /\ Nn 0 <= sq n`
    STRIP_ASSUME_TAC THENL
     [USE_THEN "big" (MP_TAC o SPEC `n:num`) THEN EXPAND_TAC "n" THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[p2cg_dk] THEN
    MP_TAC(ISPECL (p2cg_std @ [`NUMPAIR J 0`; `(sq:num->num) n`]) P2GB_NCH_BASIC) THEN
    MP_TAC(ISPECL (p2cg_std @ [`p2cc_a0`; `(sq:num->num) n`]) P2GB_NCH_BASIC) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    REWRITE_TAC[p2cc_a0] THEN
    MP_TAC(ISPECL (p2cg_std @ [`(sq:num->num)(n:num):num`; `J:num`]) P2GC_A0_CTR) THEN
    MP_TAC(ISPECL (p2cg_std @ [`(sq:num->num)(n:num):num`; `0`]) P2GC_A0_CTR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC MFD_DIST_REFL THEN
    UNDISCH_TAC `p2gb_seq (top:num->A topology) (atlas:num->((A->bool)#(A->real^3))->bool) (h:num->A->real^3^3) (x:num->A)` THEN
    REWRITE_TAC[p2gb_seq] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p2cc_xl] THEN
  UNDISCH_TAC `p2cl_glue (p2cg_dm (rho:num->real)) (p2cg_om rho (D:num#num->real^(3,3)finite_sum->real^1)) (p2cg_tr rho D)
                         (kp:num->real^3->real^3)` THEN
  REWRITE_TAC[p2cl_glue] THEN
  DISCH_THEN(MP_TAC o SPECL [`NUMPAIR J 0`; `p2cc_a0`; `vec 0:real^3`; `vec 0:real^3`]) THEN
  REWRITE_TAC[p2cg_dm; CENTRE_IN_BALL; NUMPAIR_DEST; P2CC_A0] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[P2CG_IN_OM; CENTRE_IN_BALL; NUMPAIR_DEST; P2CC_A0] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `NUMPAIR J 0`; `p2cc_a0`; `vec 0:real^3`]) P2GB_TR_PROPS) THEN
  ASM_REWRITE_TAC[P2CG_IN_OM; CENTRE_IN_BALL; NUMPAIR_DEST; P2CC_A0] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[CENTRE_IN_CBALL] THEN ASM_REAL_ARITH_TAC);;

let P2GC_MANIFOLD = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl (kp:num->real^3->real^3).
     p2gb_seq top atlas h x /\ p2gb_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_limit top atlas h yc rho sq D Gl /\
     p2cl_glue (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D) kp
     ==> hausdorff_space (p2cl_top (p2cg_dm rho) kp) /\
         smooth_manifold_atlas (p2cl_top (p2cg_dm rho) kp) (p2cl_atlas (p2cg_dm rho) kp) /\
         riemannian_metric (p2cl_atlas (p2cg_dm rho) kp) (p2cl_metric (p2cg_dm rho) kp Gl) /\
         topspace (p2cl_top (p2cg_dm rho) kp) =
         UNIONS {IMAGE (kp i) (p2cg_dm rho i) | i IN (:num)} /\
         (!i. p2cl_chart (p2cg_dm rho) kp i IN p2cl_atlas (p2cg_dm rho) kp /\
              FST(p2cl_chart (p2cg_dm rho) kp i) = IMAGE (kp i) (p2cg_dm rho i) /\
              !z. z IN p2cg_dm rho i ==> SND(p2cl_chart (p2cg_dm rho) kp i) (kp i z) = z) /\
         (!i y. y IN p2cg_dm rho i
                ==> metric_local (p2cl_atlas (p2cg_dm rho) kp) (p2cl_chart (p2cg_dm rho) kp i)
                                 (p2cl_metric (p2cg_dm rho) kp Gl) y = Gl i y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cg_limit]) THEN
  MATCH_MP_TAC P2CL_GLUED_MANIFOLD THEN
  MAP_EVERY EXISTS_TAC [`p2cg_om (rho:num->real) (D:num#num->real^(3,3)finite_sum->real^1)`; `p2cg_tr (rho:num->real) (D:num#num->real^(3,3)finite_sum->real^1)`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `a:num` THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
  EXISTS_TAC `ball(vec 0:real^3,&3 * (rho:num->real)(NUMFST a) / &8)` THEN
  ASM_REWRITE_TAC[p2cg_dm; OPEN_BALL] THEN MATCH_MP_TAC SUBSET_BALL THEN
  MP_TAC(ISPECL (p2cg_std @ [`NUMFST a`]) P2GB_RHO_POS) THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

(* Every level above 0 has a net point. *)

let P2GC_P_POS = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc j.
     p2gb_seq top atlas h x /\ p2gb_levels top atlas h x rho K N0 B NB P Nn yc
     ==> 0 < P (SUC j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `k = (Nn:num->num) j + Nn (SUC j)` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num` o GEN_REWRITE_RULE I [p2gb_seq]) THEN
  UNDISCH_TAC `p2gb_levels (top:num->A topology) (atlas:num->((A->bool)#(A->real^3))->bool) (h:num->A->real^3^3) (x:num->A) (rho:num->real) K (N0:num->num) B (NB:num->num->num) (P:num->num) (Nn:num->num) (yc:num->num->num->A)` THEN
  REWRITE_TAC[p2gb_levels] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`j:num`; `k:num`; `0`] o
                check (fun th -> can (find_term (fun t -> t = `P:num->num`)) (concl th))) THEN
  ANTS_TAC THENL [EXPAND_TAC "k" THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `(yc:num->num->num->A) j k 0`) THEN ANTS_TAC THENL
   [SUBGOAL_THEN `(yc:num->num->num->A) j k 0 IN topspace((top:num->A topology) k)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`j:num`; `k:num`] o
        check (fun th -> can (find_term ((=) `x:num->A`)) (concl th) &&
                         can (find_term ((=) `yc:num->num->num->A`)) (concl th))) THEN
      ANTS_TAC THENL [EXPAND_TAC "k" THEN ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `0` o CONJUNCT2) THEN
      ASM_MESON_TAC[P2CU_BALL_SUBSET; SUBSET];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`(top:num->A topology) k`; `(atlas:num->((A->bool)#(A->real^3))->bool) k`;
                   `(h:num->A->real^3^3) k`; `(yc:num->num->num->A) j k 0`;
                   `(rho:num->real) j`] MFD_CENTRE_IN_BALL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o
      check (fun th -> can (find_term ((=) `rho:num->real`)) (concl th) &&
                       not (can (find_term ((=) `yc:num->num->num->A`)) (concl th)))) THEN
    SIMP_TAC[];
    MESON_TAC[ARITH_RULE `i < n ==> 0 < n`]]);;

(* ------------------------------------------------------------------------- *)
(* The exhaustion W j (the level-(j+1) pieces of radius                     *)
(* rho(j+1)/5) and the covers of its closure.                                *)
(* ------------------------------------------------------------------------- *)

let p2gc_W = new_definition
 `p2gc_W (rho:num->real) (P:num->num) (kp:num->real^3->real^3) j =
    UNIONS {IMAGE (kp (NUMPAIR (SUC j) s)) (ball(vec 0,rho(SUC j) / &5)) | s | s < P (SUC j)}`;;

(* The closure of W j lies in the images of the closed balls. *)

let P2GC_W_CLOSURE = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl (kp:num->real^3->real^3) j.
     p2gb_seq top atlas h x /\ p2gb_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_limit top atlas h yc rho sq D Gl /\
     p2cl_glue (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D) kp
     ==> compact_in (p2cl_top (p2cg_dm rho) kp)
           (UNIONS {IMAGE (kp (NUMPAIR (SUC j) s)) (cball(vec 0,rho(SUC j) / &5)) |
                    s | s < P (SUC j)}) /\
         p2cl_top (p2cg_dm rho) kp closure_of p2gc_W rho P kp j SUBSET
         UNIONS {IMAGE (kp (NUMPAIR (SUC j) s)) (cball(vec 0,rho(SUC j) / &5)) |
                 s | s < P (SUC j)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cg_limit]) THEN
  MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `Gl:num->real^3->real^3^3`; `kp:num->real^3->real^3`]) P2GC_MANIFOLD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (rho:num->real) (SUC j)` (LABEL_TAC "rp") THENL
   [MP_TAC(ISPECL (p2cg_std @ [`SUC j`]) P2GB_RHO_POS) THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `compact_in (p2cl_top (p2cg_dm (rho:num->real)) (kp:num->real^3->real^3))
      (UNIONS {IMAGE (kp (NUMPAIR (SUC j) s)) (cball(vec 0,rho(SUC j) / &5)) |
               s | s < (P:num->num) (SUC j)})`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC COMPACT_IN_UNIONS THEN
    SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `s:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology euclidean (p2cg_dm (rho:num->real) (NUMPAIR (SUC j) s))` THEN CONJ_TAC THENL
     [REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN; COMPACT_CBALL] THEN
      REWRITE_TAC[p2cg_dm; NUMPAIR_DEST; SUBSET; IN_CBALL_0; IN_BALL_0] THEN
      GEN_TAC THEN USE_THEN "rp" MP_TAC THEN REAL_ARITH_TAC;
      MATCH_MP_TAC P2CC_KP_CONTINUOUS THEN
      MAP_EVERY EXISTS_TAC [`p2cg_om (rho:num->real) (D:num#num->real^(3,3)finite_sum->real^1)`; `p2cg_tr (rho:num->real) (D:num#num->real^(3,3)finite_sum->real^1)`] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN CONJ_TAC THENL
   [REWRITE_TAC[p2gc_W] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    MATCH_MP_TAC UNIONS_MONO_IMAGE THEN
    X_GEN_TAC `s:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[BALL_SUBSET_CBALL];
    MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[]]);;

(* The exhaustion. *)

let P2GC_EXHAUST = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl (kp:num->real^3->real^3).
     p2gb_seq top atlas h x /\ p2gb_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_limit top atlas h yc rho sq D Gl /\
     p2cl_glue (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D) kp
     ==> p2cc_xl kp IN topspace(p2cl_top (p2cg_dm rho) kp) /\
         (!k. open_in (p2cl_top (p2cg_dm rho) kp) (p2gc_W rho P kp k) /\
              p2cc_xl kp IN p2gc_W rho P kp k /\
              compact_in (p2cl_top (p2cg_dm rho) kp)
                         (p2cl_top (p2cg_dm rho) kp closure_of p2gc_W rho P kp k) /\
              p2cl_top (p2cg_dm rho) kp closure_of p2gc_W rho P kp k SUBSET
              p2gc_W rho P kp (SUC k)) /\
         UNIONS {p2gc_W rho P kp k | k IN (:num)} = topspace(p2cl_top (p2cg_dm rho) kp)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cg_limit]) THEN
  MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `Gl:num->real^3->real^3^3`; `kp:num->real^3->real^3`]) P2GC_MANIFOLD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!j. &0 < (rho:num->real) j` (LABEL_TAC "rp") THENL
   [GEN_TAC THEN MP_TAC(ISPECL (p2cg_std @ [`j:num`]) P2GB_RHO_POS) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2cc_xl kp IN topspace(p2cl_top (p2cg_dm (rho:num->real)) (kp:num->real^3->real^3))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[p2cc_xl; IN_UNIONS; EXISTS_IN_GSPEC; IN_UNIV] THEN
    EXISTS_TAC `p2cc_a0` THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    REWRITE_TAC[p2cg_dm; CENTRE_IN_BALL] THEN
    USE_THEN "rp" (MP_TAC o SPEC `NUMFST p2cc_a0`) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!b z. z IN p2cg_dm (rho:num->real) b
                      ==> (kp:num->real^3->real^3) b z IN p2gc_W rho (P:num->num) kp (NUMFST b)`
  (LABEL_TAC "up") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                               `kp:num->real^3->real^3`; `b:num`; `z:real^3`]) P2GC_LEVEL_UP) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[p2gc_W; IN_UNIONS; EXISTS_IN_GSPEC] THEN
    EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_BALL_0] THEN
    USE_THEN "rp" (MP_TAC o SPEC `SUC(NUMFST b)`) THEN
    UNDISCH_TAC `norm(w:real^3) <= (rho:num->real) (SUC (NUMFST b)) / &8` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN
    MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                               `Gl:num->real^3->real^3^3`; `kp:num->real^3->real^3`; `k:num`])
                  P2GC_W_CLOSURE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[p2gc_W] THEN MATCH_MP_TAC OPEN_IN_UNIONS THEN
      REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `s:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC P2CL_OPEN_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`p2cg_om (rho:num->real) (D:num#num->real^(3,3)finite_sum->real^1)`; `p2cg_tr (rho:num->real) (D:num#num->real^(3,3)finite_sum->real^1)`] THEN
      ASM_REWRITE_TAC[OPEN_BALL; p2cg_dm; NUMPAIR_DEST] THEN MATCH_MP_TAC SUBSET_BALL THEN
      USE_THEN "rp" (MP_TAC o SPEC `SUC k`) THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[p2gc_W; IN_UNIONS; EXISTS_IN_GSPEC] THEN
      EXISTS_TAC `0` THEN CONJ_TAC THENL
       [MP_TAC(ISPECL (p2cg_std @ [`k:num`]) P2GC_P_POS) THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vec 0:real^3` THEN CONJ_TAC THENL
         [CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2GC_XL_CHART THEN
          MAP_EVERY EXISTS_TAC (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                                            `Gl:num->real^3->real^3^3`]) THEN
          ASM_REWRITE_TAC[];
          REWRITE_TAC[CENTRE_IN_BALL] THEN
          USE_THEN "rp" (MP_TAC o SPEC `SUC k`) THEN
          REAL_ARITH_TAC]];
      MATCH_MP_TAC CLOSED_COMPACT_IN THEN
      EXISTS_TAC `UNIONS {IMAGE ((kp:num->real^3->real^3) (NUMPAIR (SUC k) s))
                                (cball(vec 0,(rho:num->real)(SUC k) / &5)) | s | s < (P:num->num) (SUC k)}` THEN
      ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `UNIONS {IMAGE ((kp:num->real^3->real^3) (NUMPAIR (SUC k) s))
                                (cball(vec 0,(rho:num->real)(SUC k) / &5)) | s | s < (P:num->num) (SUC k)}` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
      X_GEN_TAC `s:num` THEN DISCH_TAC THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
      USE_THEN "up" (MP_TAC o SPECL [`NUMPAIR (SUC k) s`; `w:real^3`]) THEN
      REWRITE_TAC[NUMPAIR_DEST] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[p2cg_dm; NUMPAIR_DEST; IN_BALL_0] THEN
      UNDISCH_TAC `(w:real^3) IN cball(vec 0,(rho:num->real)(SUC k) / &5)` THEN REWRITE_TAC[IN_CBALL_0] THEN
      USE_THEN "rp" (MP_TAC o SPEC `SUC k`) THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [GSYM SUBSET_ANTISYM_EQ] THEN CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC; IN_UNIV] THEN X_GEN_TAC `k:num` THEN
    ASM_REWRITE_TAC[p2gc_W; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `s:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC(SET_RULE `!t:real^3->bool. s SUBSET t /\ t IN u ==> s SUBSET UNIONS u`) THEN
    EXISTS_TAC `IMAGE ((kp:num->real^3->real^3) (NUMPAIR (SUC k) s))
                      (p2cg_dm (rho:num->real) (NUMPAIR (SUC k) s))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[p2cg_dm; NUMPAIR_DEST] THEN
      MATCH_MP_TAC SUBSET_BALL THEN
      USE_THEN "rp" (MP_TAC o SPEC `SUC k`) THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[]];
    ASM_REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_GSPEC; IN_UNIV; IN_IMAGE] THEN
    X_GEN_TAC `p:real^3` THEN
    DISCH_THEN(X_CHOOSE_THEN `b:num` (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `NUMFST b` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "up" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* The closure of W j is covered by the level-(j+2) pieces of radius        *)
(* 2 rho/15 (two levels up: what the embedding of cgemb uses).               *)

let P2GC_COVER_PIECES = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl (kp:num->real^3->real^3) j.
     p2gb_seq top atlas h x /\ p2gb_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_limit top atlas h yc rho sq D Gl /\
     p2cl_glue (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D) kp
     ==> p2cl_top (p2cg_dm rho) kp closure_of p2gc_W rho P kp j SUBSET
         UNIONS {IMAGE (kp (NUMPAIR (j + 2) i)) (ball(vec 0,&2 * rho(j + 2) / &15)) |
                 i | i < P(j + 2)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cg_limit]) THEN
  MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `Gl:num->real^3->real^3^3`; `kp:num->real^3->real^3`; `j:num`])
                P2GC_W_CLOSURE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `UNIONS {IMAGE ((kp:num->real^3->real^3) (NUMPAIR (SUC j) s))
                            (cball(vec 0,(rho:num->real)(SUC j) / &5)) | s | s < (P:num->num) (SUC j)}` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
  X_GEN_TAC `s:num` THEN DISCH_TAC THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `!jj. &0 < (rho:num->real) jj` (LABEL_TAC "rp") THENL
   [X_GEN_TAC `jj:num` THEN MP_TAC(ISPECL (p2cg_std @ [`jj:num`]) P2GB_RHO_POS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `kp:num->real^3->real^3`; `NUMPAIR (SUC j) s`; `w:real^3`])
                P2GC_LEVEL_UP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[p2cg_dm; NUMPAIR_DEST; IN_BALL_0] THEN
    UNDISCH_TAC `(w:real^3) IN cball(vec 0,(rho:num->real)(SUC j) / &5)` THEN REWRITE_TAC[IN_CBALL_0] THEN
    USE_THEN "rp" (MP_TAC o SPEC `SUC j`) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[NUMPAIR_DEST; ARITH_RULE `SUC(SUC j) = j + 2`] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `w':real^3` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC] THEN EXISTS_TAC `i:num` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_IMAGE; IN_BALL_0] THEN EXISTS_TAC `w':real^3` THEN
  ASM_REWRITE_TAC[] THEN USE_THEN "rp" (MP_TAC o SPEC `j + 2`) THEN
  UNDISCH_TAC `norm(w':real^3) <= (rho:num->real) (j + 2) / &8` THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The ball instance.  The levels of pc_p2c_cgglue (bounds on               *)
(* the balls B(x k, j+3), nets of B(x k, j+1)) are general levels of        *)
(* pc_p2c_lcgb, with the thresholds N0 and NB raised to Nn: the centres lie *)
(* in B(x k, j+1), and a ball B(y, rho j) around a level-j centre lies in   *)
(* B(x k, j+2), which the level-(j+1) net covers.                           *)
(* ------------------------------------------------------------------------- *)

let P2GB_OF_BALLS = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc.
     p2gb_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc
     ==> p2gb_levels top atlas h x rho K (\j. MAX (N0 j) (Nn j)) B
                     (\j m. MAX (NB j m) (Nn j)) P Nn yc`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2gb_seq; p2cg_levels; p2gb_levels] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "seq")
    (CONJUNCTS_THEN2 (LABEL_TAC "rho") (CONJUNCTS_THEN2 (LABEL_TAC "inj")
      (CONJUNCTS_THEN2 (LABEL_TAC "fld") (LABEL_TAC "net"))))) THEN
  REWRITE_TAC[ARITH_RULE `MAX a b <= k <=> a <= k /\ b <= k`] THEN
  SUBGOAL_THEN
   `!j k s. (Nn:num->num) j <= k
            ==> (yc:num->num->num->A) j k s IN
                mfd_ball ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k) ((h:num->A->real^3^3) k) ((x:num->A) k) (&j + &1)`
  (LABEL_TAC "in1") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "net" (MP_TAC o SPECL [`j:num`; `k:num`]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j k s. (Nn:num->num) j <= k
            ==> (yc:num->num->num->A) j k s IN
                mfd_ball ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k) ((h:num->A->real^3^3) k) ((x:num->A) k) (&j + &3)`
  (LABEL_TAC "in3") THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(SET_RULE `!s t (y:A). y IN s /\ s SUBSET t ==> y IN t`) THEN
    EXISTS_TAC `mfd_ball ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k) ((h:num->A->real^3^3) k) ((x:num->A) k) (&j + &1)` THEN
    CONJ_TAC THENL
     [USE_THEN "in1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2CU_BALL_MONO THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN USE_THEN "inj" MATCH_MP_TAC THEN
    ASM_SIMP_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN USE_THEN "fld" MATCH_MP_TAC THEN
    ASM_SIMP_TAC[];
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "net" (MP_TAC o SPECL [`j:num`; `k:num`]) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`j:num`; `k:num`; `s:num`] THEN STRIP_TAC THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `p:A` THEN DISCH_TAC THEN
  USE_THEN "seq" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
  SUBGOAL_THEN
   `(p:A) IN mfd_ball ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k) ((h:num->A->real^3^3) k) ((x:num->A) k) (&(SUC j) + &1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!s t (y:A). y IN s /\ s SUBSET t ==> y IN t`) THEN
    EXISTS_TAC `mfd_ball ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k) ((h:num->A->real^3^3) k) ((x:num->A) k) ((&j + &1) + (rho:num->real) j)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!s t (y:A). y IN s /\ s SUBSET t ==> y IN t`) THEN
      EXISTS_TAC `mfd_ball ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k) ((h:num->A->real^3^3) k) ((yc:num->num->num->A) j k s) ((rho:num->real) j)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2CU_BALL_SHIFT THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "in1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2CU_BALL_MONO THEN REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
      USE_THEN "rho" (MP_TAC o SPEC `j:num`) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "net" (MP_TAC o SPEC `p:A` o CONJUNCT2 o CONJUNCT2 o
                  C MP (ASSUME `(Nn:num->num) (SUC j) <= k`) o SPECL [`SUC j`; `k:num`]) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(yc:num->num->num->A) (SUC j) k i IN
    mfd_ball ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k) ((h:num->A->real^3^3) k) ((x:num->A) k) (&(SUC j) + &1)`
  MP_TAC THENL
   [USE_THEN "in1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC
   `(p:A) IN mfd_ball ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k) ((h:num->A->real^3^3) k) ((x:num->A) k) (&(SUC j) + &1)` THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[MFD_JOINABLE_SYM; MFD_JOINABLE_TRANS]);;


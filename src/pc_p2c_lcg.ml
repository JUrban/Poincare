(* ========================================================================= *)
(* Unit pc_p2c_lcg (Part 2C, the general form G of local compactness,        *)
(* P2B_REQ_P2C_LOCAL_COMPACT_G_STATEMENT): the main theorem                  *)
(* P2GH_LOCAL_COMPACT_G.  The CG levels of G (P2GK_LEVELS_G), the glued      *)
(* limit (P2GB_GLUED_LIMIT), the flow subsequence (P2GF_FLOW_SUB), the final *)
(* diagonal with images in U, ball lifts and near-identity                   *)
(* (P2GK_DIAGONAL_Q), the space part (P2GK_SPACE_FROM_DIAG) and the flow     *)
(* part (P2GF_VL_PART).                                                      *)
(* ========================================================================= *)

needs "src/pc_p2c_lcgf.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* G from its space part and its flow part.                                  *)
(* ------------------------------------------------------------------------- *)

(* p2gf_vlpart is defined in unit pc_p2c_lcgf (the flow part of G). *)

let P2GH_G_FROM_PARTS = prove
 (`!u:A->bool.
     (!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
       U z.
        p2ga_hyp V U z
        ==> ?sub top atlas g zl W phi Vl.
              p2gk_space V U z sub top atlas g zl W phi /\
              p2gf_vlpart V sub top atlas g W phi Vl)
     ==> P2B_REQ_P2C_LOCAL_COMPACT_G_STATEMENT u (:real^3)`,
  GEN_TAC THEN REWRITE_TAC[P2GA_HYP_G; p2gk_space; p2gf_vlpart; GSYM CONJ_ASSOC] THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)`; `U:num->A->bool`; `z:num->A`]) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The assembly.                                                              *)
(* ------------------------------------------------------------------------- *)

(* The levels become arbitrarily fine. *)

let P2GH_RHO_SMALL = prove
 (`!d0 (rho:num->real).
     &0 < d0 /\ (!j. rho j <= d0 / &2 pow j / &16)
     ==> !e. &0 < e ==> ?j0. !j. j0 <= j ==> rho j < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`inv(&2)`; `e / d0`] REAL_ARCH_POW_INV) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_DIV] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN EXISTS_TAC `n:num` THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `d0 / &2 pow j / &16` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `d0 / &2 pow j <= d0 * inv(&2) pow n` ASSUME_TAC THENL
   [REWRITE_TAC[real_div; GSYM REAL_POW_INV] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_POW_MONO_INV THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `d0 * inv(&2) pow n < e` ASSUME_TAC THENL
   [UNDISCH_TAC `inv(&2) pow n < e / d0` THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= d0 / &2 pow j` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_POW_LE; REAL_POS];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let p2gh_vty = `:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;;
let p2gh_V = mk_var("V",p2gh_vty);;
let p2gh_TOP = `\k. rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) k) (&0)`;;
let p2gh_ATL = `\k. rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                   (real->A->real^3^3)) k) (&0)`;;
let p2gh_MET = `\k. rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) k) (&0)`;;
let p2gh_std = [p2gh_TOP; p2gh_ATL; p2gh_MET; `z:num->A`; `rho:num->real`; `K:num->real`;
                `N0:num->num`; `B:num->num->real`; `\j:num m:num. (N0:num->num) j`; `P:num->num`;
                `N0:num->num`; `yc:num->num->num->A`];;
let p2gh_ctxl = p2gh_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                            `Gl:num->real^3->real^3^3`; `kp:num->real^3->real^3`];;

let P2GH_G_PARTS = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z.
     p2ga_hyp V U z
     ==> ?sub top atlas g zl W phi Vl.
           p2gk_space V U z sub top atlas g zl W phi /\
           p2gf_vlpart V sub top atlas g W phi Vl`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2GK_LEVELS_G) THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` (X_CHOOSE_THEN `rho:num->real` (X_CHOOSE_THEN `K:num->real`
    (X_CHOOSE_THEN `N0:num->num` (X_CHOOSE_THEN `B:num->num->real` (X_CHOOSE_THEN `P:num->num`
    (X_CHOOSE_THEN `yc:num->num->num->A` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "rhob")
    (CONJUNCTS_THEN2 (LABEL_TAC "inU") (CONJUNCTS_THEN2 (LABEL_TAC "ycov32") (LABEL_TAC "sh32"))))))))))))))) THEN
  MP_TAC(ISPECL p2gh_std P2GB_GLUED_LIMIT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `sq:num->num` (X_CHOOSE_THEN `D:num#num->real^(3,3)finite_sum->real^1`
    (X_CHOOSE_THEN `Gl:num->real^3->real^3^3` (X_CHOOSE_THEN `kp:num->real^3->real^3`
      STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN (list_mk_comb(`p2ge_ctx:(num->A topology)->(num->((A->bool)#(A->real^3))->bool)->
                                       (num->A->real^3^3)->(num->A)->(num->real)->(num->real)->
                                       (num->num)->(num->num->real)->(num->num->num)->(num->num)->
                                       (num->num)->(num->num->num->A)->(num->num)->
                                       (num#num->real^(3,3)finite_sum->real^1)->
                                       (num->real^3->real^3^3)->(num->real^3->real^3)->bool`,
                             p2gh_ctxl))
  ASSUME_TAC THENL [ASM_REWRITE_TAC[p2ge_ctx]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GE_CTX_FACTS) THEN
  MP_TAC(ISPECL p2gh_ctxl P2GC_EXHAUST) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `(:A)` P2GF_GAUGE_EXISTS) THEN DISCH_THEN(X_CHOOSE_TAC `CG:real->real`) THEN
  MP_TAC(ISPECL [p2gh_V; `sq:num->num`; `yc:num->num->num->A`; `rho:num->real`;
                 `CG:real->real`] P2GF_FLOW_SUB) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:num->num` (CONJUNCTS_THEN2 (LABEL_TAC "tinc") (LABEL_TAC "dich"))) THEN
  SUBGOAL_THEN `!n. n <= (t:num->num) n` (LABEL_TAC "tbig") THENL
   [MP_TAC(SPEC `t:num->num` MONOTONE_BIGGER) THEN USE_THEN "tinc" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i k s. (N0:num->num) i <= k
            ==> mfd_ball (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                       (real->A->real^3^3)) k) (&0),rfs_vatlas (V k) (&0))
                         (rfs_vmetric (V k) (&0)) ((yc:num->num->num->A) i k s) ((rho:num->real) i)
                SUBSET (U:num->A->bool) k`
  (LABEL_TAC "ballU") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "inU" (MP_TAC o SPECL [`i:num`; `k:num`; `s:num`]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [p2gh_TOP; p2gh_ATL; p2gh_MET; `z:num->A`;
                 `p2cl_top (p2cg_dm (rho:num->real)) (kp:num->real^3->real^3)`;
                 `p2cl_atlas (p2cg_dm (rho:num->real)) (kp:num->real^3->real^3)`;
                 `p2cl_metric (p2cg_dm (rho:num->real)) (kp:num->real^3->real^3) Gl`;
                 `p2cc_xl (kp:num->real^3->real^3)`;
                 `p2gc_W (rho:num->real) (P:num->num) (kp:num->real^3->real^3)`;
                 `\n. (sq:num->num) ((t:num->num) n)`;
                 `\j k (Fm:real^3->A).
                    p2gk_Q (\k. rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                              (real->A->real^3^3)) k) (&0))
                           (\k. rfs_vatlas (V k) (&0)) (\k. rfs_vmetric (V k) (&0))
                           (yc:num->num->num->A) (rho:num->real) (P:num->num)
                           (kp:num->real^3->real^3) (U:num->A->bool) j k Fm /\
                    p2gk_near3 (\k. rfs_vtop (V k) (&0)) (\k. rfs_vatlas (V k) (&0))
                               (\k. rfs_vmetric (V k) (&0)) yc rho P kp j k Fm`;
                 `\j n. p2ce_F (\k. rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                                  (real->A->real^3^3)) k) (&0))
                               (\k. rfs_vatlas (V k) (&0)) (\k. rfs_vmetric (V k) (&0))
                               (yc:num->num->num->A) (rho:num->real) (kp:num->real^3->real^3)
                               (p2ce_cs (P:num->num) j) ((sq:num->num) ((t:num->num) n)) (P(j + 2))`]
                P2GK_DIAGONAL_Q) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN DISCH_TAC THEN
      FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [p2cg_dsys] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2cg_dsys")) (concl th) &&
        not (is_forall (concl th)))) THEN
      USE_THEN "tinc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `j:num` THEN
    MP_TAC(ISPECL (p2gh_ctxl @ [`j:num`; `0`; `&1`]) P2GE_EMBED_LEVEL) THEN
    ASM_REWRITE_TAC[REAL_LT_01] THEN DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "e1")) THEN
    MP_TAC(ISPECL (p2gh_ctxl @ [`U:num->A->bool`; `j:num`]) P2GK_LEVEL_Q) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "e2")) THEN
    MP_TAC(ISPECL (p2gh_ctxl @ [`j:num`]) P2GK_LEVEL_NEAR3) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `N3:num` (LABEL_TAC "e3")) THEN
    CONJ_TAC THENL
     [EXISTS_TAC `N1 + N2 + N3:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      USE_THEN "tbig" (MP_TAC o SPEC `n:num`) THEN DISCH_TAC THEN
      USE_THEN "e1" (MP_TAC o SPEC `(t:num->num) n`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
      USE_THEN "e2" (MP_TAC o SPEC `(t:num->num) n`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
      USE_THEN "e3" (MP_TAC o SPEC `(t:num->num) n`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`m:num`; `eta:real`] THEN DISCH_TAC THEN
      MP_TAC(ISPECL (p2gh_ctxl @ [`j:num`; `m:num`; `eta:real`]) P2GE_EMBED_LEVEL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `N4:num` (LABEL_TAC "e4")) THEN
      EXISTS_TAC `N4:num` THEN MAP_EVERY X_GEN_TAC [`n:num`; `y:real^3`] THEN STRIP_TAC THEN
      USE_THEN "e4" (MP_TAC o SPEC `(t:num->num) n`) THEN ANTS_TAC THENL
       [USE_THEN "tbig" (MP_TAC o SPEC `n:num`) THEN ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:num->num` (CONJUNCTS_THEN2 (LABEL_TAC "rinc")
    (CONJUNCTS_THEN2 (LABEL_TAC "base") (CONJUNCTS_THEN2 (LABEL_TAC "dif")
    (CONJUNCTS_THEN2 (LABEL_TAC "qq") (LABEL_TAC "lck")))))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  SUBGOAL_THEN `!m n. m < n ==> (sq:num->num) ((t:num->num) ((r:num->num) m)) < sq (t (r n))`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN DISCH_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [p2cg_dsys] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2cg_dsys")) (concl th) &&
      not (is_forall (concl th)))) THEN
    USE_THEN "tinc" MATCH_MP_TAC THEN USE_THEN "rinc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [p2gh_V; `U:num->A->bool`; `z:num->A`; `rho:num->real`; `K:num->real`;
                 `N0:num->num`; `B:num->num->real`; `P:num->num`; `yc:num->num->num->A`;
                 `sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                 `Gl:num->real^3->real^3^3`; `kp:num->real^3->real^3`; `CG:real->real`;
                 `t:num->num`; `r:num->num`] P2GF_VL_PART) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[p2gf_fctx] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2GH_RHO_SMALL THEN EXISTS_TAC `d0:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC
    `Vl:(real->(real^3)topology)#(real->((real^3->bool)#(real^3->real^3))->bool)#
        (real->real^3->real^3^3)`) THEN
  MAP_EVERY EXISTS_TAC
   [`\k. (sq:num->num) ((t:num->num) ((r:num->num) k))`;
    `p2cl_top (p2cg_dm (rho:num->real)) (kp:num->real^3->real^3)`;
    `p2cl_atlas (p2cg_dm (rho:num->real)) (kp:num->real^3->real^3)`;
    `p2cl_metric (p2cg_dm (rho:num->real)) (kp:num->real^3->real^3) Gl`;
    `p2cc_xl (kp:num->real^3->real^3)`;
    `p2gc_W (rho:num->real) (P:num->num) (kp:num->real^3->real^3)`;
    `\k. p2ce_F (\k. rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) k) (&0))
                (\k. rfs_vatlas (V k) (&0)) (\k. rfs_vmetric (V k) (&0))
                (yc:num->num->num->A) (rho:num->real) (kp:num->real^3->real^3)
                (p2ce_cs (P:num->num) k) ((sq:num->num) ((t:num->num) ((r:num->num) k))) (P(k + 2))`;
    `Vl:(real->(real^3)topology)#(real->((real^3->bool)#(real^3->real^3))->bool)#
        (real->real^3->real^3^3)`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2GK_SPACE_FROM_DIAG THEN
  MAP_EVERY EXISTS_TAC [`d0:real`; `rho:num->real`; `P:num->num`; `yc:num->num->num->A`;
                        `N0:num->num`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`j:num`; `k:num`; `p:A`] THEN STRIP_TAC THEN
    USE_THEN "ycov32" (MP_TAC o SPECL [`j:num`; `k:num`; `p:A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `s:num` THEN
    MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET t ==> (x:A) IN s ==> x IN t`) THEN
    MATCH_MP_TAC P2CU_BALL_MONO THEN
    MP_TAC(ISPECL (p2gh_std @ [`j:num`]) P2GB_RHO_POS) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    X_GEN_TAC `k:num` THEN USE_THEN "qq" (MP_TAC o SPEC `k:num`) THEN
    REWRITE_TAC[p2gk_Q] THEN SIMP_TAC[]]);;

(* The main theorem. *)

let P2GH_LOCAL_COMPACT_G = prove
 (`!u:A->bool. P2B_REQ_P2C_LOCAL_COMPACT_G_STATEMENT u (:real^3)`,
  GEN_TAC THEN MATCH_MP_TAC P2GH_G_FROM_PARTS THEN ACCEPT_TAC P2GH_G_PARTS);;


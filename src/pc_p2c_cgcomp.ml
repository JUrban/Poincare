(* ========================================================================= *)
(* Unit pc_p2c_cgcomp (Part 2C, used in the pc_p2c_cg route): completeness   *)
(* and exhaustion of the glued limit.  The D-distance delta to the base      *)
(* point is a proper function on the limit manifold that grows at most like  *)
(* twice the length along curves; its sublevel sets are compact (finitely    *)
(* many chart balls of one level cover them), so closed metric balls are     *)
(* compact and the sets delta < j + 1 exhaust the limit.                     *)
(* ========================================================================= *)

needs "src/pc_p2c_cgglue.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The upper Lipschitz bound of D inside one chart, the base                 *)
(* chart (level 0, net index 0, centred at the base points), and the         *)
(* function delta = D-distance to the centre of the base chart.              *)
(* ------------------------------------------------------------------------- *)

let P2CC_DV_UPPER = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc s D a z z'.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_dsys top atlas h yc rho s D /\
     z IN cball(vec 0,rho(NUMFST a) / &2) /\ z' IN cball(vec 0,rho(NUMFST a) / &2)
     ==> p2cg_dv D a z a z' <= sqrt(&2) * norm(z - z')`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [p2cg_dsys]) THEN
  SUBGOAL_THEN `norm(z:real^3) < rho(NUMFST a) /\ norm(z':real^3) < rho(NUMFST a)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[P2CG_CBALL_NORM; P2CG_RHO_POS]; ALL_TAC] THEN
  MATCH_MP_TAC P2CG_REAL_LIM_LE1 THEN
  MAP_EVERY EXISTS_TAC
   [`\k. p2cg_dk (top:num->A topology) atlas (h:num->A->real^3^3) (yc:num->num->num->A)
                 k a z a z'`;
    `\k:num. sqrt(&2) * norm(z - z':real^3)`; `s:num->num`] THEN
  BETA_TAC THEN ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2CG_D_SEQ THEN EXISTS_TAC `rho:num->real` THEN ASM_REWRITE_TAC[];
    MESON_TAC[];
    EXISTS_TAC `p2cg_nv (N0:num->num) (Nn:num->num) a` THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL (p2cg_std @ [`a:num`; `k:num`; `z:real^3`; `z':real^3`]) P2CG_NCH_LIP) THEN
    ASM_REWRITE_TAC[p2cg_dk] THEN SIMP_TAC[]]);;

(* The base chart: level 0, net index 0, centred at x k. *)

let p2cc_a0 = new_definition
 `p2cc_a0 = NUMPAIR 0 0`;;

let P2CC_A0 = prove
 (`NUMFST p2cc_a0 = 0 /\ NUMSND p2cc_a0 = 0`,
  REWRITE_TAC[p2cc_a0; NUMPAIR_DEST]);;

let P2CC_A0_CTR = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc k.
     p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\ p2cg_nv N0 Nn p2cc_a0 <= k
     ==> p2cg_ctr yc k p2cc_a0 = x k`,
  REWRITE_TAC[p2cg_levels; p2cg_nv; p2cg_ctr; P2CC_A0] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `k:num`] o
                check (fun th -> can (find_term ((=) `yc:num->num->num->A`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]);;

(* The D-distance to the base point, as a function on the glued limit. *)

let p2cc_delta = new_definition
 `p2cc_delta (rho:num->real) (D:num#num->real^(3,3)finite_sum->real^1)
             (kp:num->real^3->real^3) (p:real^3) =
    @r. ?a z. z IN p2cg_dm rho a /\ kp a z = p /\ r = p2cg_dv D p2cc_a0 (vec 0) a z`;;

let P2CC_DV_GLUE_EQ = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc s D (kp:num->real^3->real^3)
    a z b w c u.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_dsys top atlas h yc rho s D /\
     p2cl_glue (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D) kp /\
     z IN p2cg_dm rho a /\ w IN p2cg_dm rho b /\ kp a z = kp b w /\
     u IN cball(vec 0,rho(NUMFST c) / &2)
     ==> p2cg_dv D c u a z = p2cg_dv D c u b w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`a:num`; `b:num`; `z:real^3`; `w:real^3`] o
              GEN_REWRITE_RULE I [p2cl_glue]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `a:num`; `b:num`; `z:real^3`]) P2CG_TR_PROPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[p2cg_dm]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CG_BALL4_CBALL o
              check (fun th -> concl th = `(z:real^3) IN ball(vec 0,rho(NUMFST a) / &4)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CG_BALL4_CBALL o
              check (fun th -> concl th = `(w:real^3) IN ball(vec 0,rho(NUMFST b) / &4)`)) THEN
  SUBGOAL_THEN `p2cg_dv D a (z:real^3) b (w:real^3) = &0 /\ p2cg_dv D b w a z = &0`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                               `a:num`; `z:real^3`; `b:num`; `w:real^3`]) P2CG_DV_SYM) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `p2cg_tr rho D a b (z:real^3) = w` THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                               `c:num`; `u:real^3`; `b:num`; `w:real^3`; `a:num`;
                               `z:real^3`]) P2CG_DV_TRI);
    MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                               `c:num`; `u:real^3`; `a:num`; `z:real^3`; `b:num`;
                               `w:real^3`]) P2CG_DV_TRI)] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let P2CC_DELTA = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc s D (kp:num->real^3->real^3) a z.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_dsys top atlas h yc rho s D /\
     p2cl_glue (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D) kp /\
     z IN p2cg_dm rho a
     ==> p2cc_delta rho D kp (kp a z) = p2cg_dv D p2cc_a0 (vec 0) a z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2cc_delta] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `r:real` THEN BETA_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `b:num` (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(GSYM P2CC_DV_GLUE_EQ) THEN
    MAP_EVERY EXISTS_TAC (p2cg_std @ [`s:num->num`; `kp:num->real^3->real^3`]) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL (p2cg_std @ [`p2cc_a0`]) P2CG_CENTRE_CBALL) THEN
    ASM_SIMP_TAC[];
    DISCH_THEN SUBST1_TAC THEN
    MAP_EVERY EXISTS_TAC [`a:num`; `z:real^3`] THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Points whose D-distance to the base point is below j lie in               *)
(* one of the P j chart balls of radius rho_j/8 of level j (the nets of the  *)
(* approximants, a pigeonhole over the net index).                           *)
(* ------------------------------------------------------------------------- *)

let P2CC_PIGEONHOLE = prove
 (`!(Q:num->num->bool) M N.
     (!n. N <= n ==> ?i. i < M /\ Q n i) ==> ?i. i < M /\ !N'. ?n. N' <= n /\ Q n i`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `!i. i < M ==> ?N'. !n. N' <= n ==> ~((Q:num->num->bool) n i)` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `Nf:num->num`) THEN
  MP_TAC(ISPEC `IMAGE (Nf:num->num) {i | i < M}` num_FINITE) THEN
  SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N + m:num` o
                check (fun th -> can (find_term ((=) `N:num`)) (concl th))) THEN
  REWRITE_TAC[LE_ADD] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o
                check (fun th -> can (find_term ((=) `Nf:num->num`)) (concl th) &&
                                 not (can (find_term ((=) `m:num`)) (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `N + m:num`) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let P2CC_NET_COVER = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc s D b z j.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_dsys top atlas h yc rho s D /\
     z IN cball(vec 0,rho(NUMFST b) / &2) /\ p2cg_dv D p2cc_a0 (vec 0) b z < &j
     ==> ?i. i < P j /\ p2cg_dv D (NUMPAIR j i) (vec 0) b z <= rho j / &8`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [p2cg_dsys]) THEN
  FIRST_ASSUM(LABEL_TAC "big" o MATCH_MP MONOTONE_BIGGER) THEN
  SUBGOAL_THEN `vec 0 IN cball(vec 0:real^3,rho(NUMFST p2cc_a0) / &2) /\
                norm(z:real^3) < rho(NUMFST b)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL (p2cg_std @ [`p2cc_a0`]) P2CG_CENTRE_CBALL) THEN
    ASM_MESON_TAC[P2CG_CBALL_NORM; P2CG_RHO_POS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                 `h:num->A->real^3^3`; `yc:num->num->num->A`; `rho:num->real`;
                 `s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`; `p2cc_a0`; `b:num`;
                 `vec 0:real^3`; `z:real^3`] P2CG_D_SEQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "seq") THEN
  USE_THEN "seq" (MP_TAC o C MP (REAL_ARITH `&0 < &1`) o SPEC `&1`) THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "n1")) THEN
  SUBGOAL_THEN
   `!n. N1 + p2cg_nv (N0:num->num) (Nn:num->num) p2cc_a0 + p2cg_nv N0 Nn b + N0 j + Nn j <= n
        ==> ?i. i < P j /\
                p2cg_dk (top:num->A topology) atlas (h:num->A->real^3^3)
                  (yc:num->num->num->A) ((s:num->num) n) (NUMPAIR j i) (vec 0) b z <
                rho j / &8`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    ABBREV_TAC `k = (s:num->num) n` THEN
    SUBGOAL_THEN `N1 <= n:num /\ p2cg_nv (N0:num->num) (Nn:num->num) p2cc_a0 <= k /\
                  p2cg_nv N0 Nn b <= k /\ (N0:num->num) j + Nn j <= k /\ Nn j <= k`
    STRIP_ASSUME_TAC THENL
     [USE_THEN "big" (MP_TAC o SPEC `n:num`) THEN ASM_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "n1" (MP_TAC o C MP (ASSUME `N1 <= n:num`) o SPEC `n:num`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL (p2cg_std @ [`p2cc_a0`; `k:num`]) P2CG_NCH_BASIC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
    MP_TAC(ISPECL (p2cg_std @ [`k:num`]) P2CC_A0_CTR) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `p2cg_nch (top:num->A topology) atlas (h:num->A->real^3^3)
                    (yc:num->num->num->A) k b z IN
                  mfd_ball ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k)
                    ((h:num->A->real^3^3) k) ((x:num->A) k) (&j + &1)`
    ASSUME_TAC THENL
     [REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL (p2cg_std @ [`k:num`; `p2cc_a0`; `vec 0:real^3`; `b:num`; `z:real^3`])
                      P2CG_DK_JOIN) THEN
        ASM_REWRITE_TAC[NORM_0] THEN
        ANTS_TAC THENL [ASM_MESON_TAC[P2CG_RHO_POS]; ALL_TAC] THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `abs(p2cg_dk (top:num->A topology) atlas (h:num->A->real^3^3)
                           (yc:num->num->num->A) k p2cc_a0 (vec 0) b z -
                         p2cg_dv D p2cc_a0 (vec 0) b z) < &1` THEN
        ASM_REWRITE_TAC[p2cg_dk] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`j:num`; `k:num`] o last o CONJUNCTS o
                GEN_REWRITE_RULE I [p2cg_levels]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `p2cg_nch (top:num->A topology) atlas (h:num->A->real^3^3)
                                (yc:num->num->num->A) k b z` o last o CONJUNCTS) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `i:num` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL (p2cg_std @ [`NUMPAIR j i`; `k:num`]) P2CG_NCH_BASIC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[p2cg_nv; NUMPAIR_DEST] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
    ASM_REWRITE_TAC[p2cg_dk] THEN
    UNDISCH_TAC `mfd_dist ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k)
                   ((h:num->A->real^3^3) k) ((yc:num->num->num->A) j k i)
                   (p2cg_nch top atlas h yc k b z) < rho j / &8` THEN
    REWRITE_TAC[p2cg_ctr; NUMPAIR_DEST];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP P2CC_PIGEONHOLE) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `i:num` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "freq")) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                 `h:num->A->real^3^3`; `yc:num->num->num->A`; `rho:num->real`;
                 `s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`; `NUMPAIR j i`; `b:num`;
                 `vec 0:real^3`; `z:real^3`] P2CG_D_SEQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[NUMPAIR_DEST; CENTRE_IN_CBALL] THEN
    MP_TAC(ISPECL (p2cg_std @ [`j:num`]) P2CG_RHO_POS) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `p2cg_dv D (NUMPAIR j i) (vec 0) b z - rho j / &8`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "n2")) THEN
  USE_THEN "freq" (MP_TAC o SPEC `N2:num`) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  USE_THEN "n2" (MP_TAC o C MP (ASSUME `N2 <= n:num`) o SPEC `n:num`) THEN
  UNDISCH_TAC `p2cg_dk (top:num->A topology) atlas (h:num->A->real^3^3)
                 (yc:num->num->num->A) ((s:num->num) n) (NUMPAIR j i) (vec 0) b z <
               rho j / &8` THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Topology of the glued limit through the pieces: the maps kp i              *)
(* are continuous, functions continuous on every piece have open strict      *)
(* sublevel and superlevel sets, and the sublevel sets of delta are compact.  *)
(* ------------------------------------------------------------------------- *)

let P2CC_KP_CONTINUOUS = prove
 (`!(Dm:num->real^N->bool) Om Tr (kp:num->real^N->B) i.
     p2cl_system Dm Om Tr /\ p2cl_glue Dm Om Tr kp
     ==> continuous_map (subtopology euclidean (Dm i),p2cl_top Dm kp) (kp i)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cl_system]) THEN
  REWRITE_TAC[continuous_map; TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN; INTER_UNIV] THEN
  ASM_SIMP_TAC[P2CL_TOPSPACE] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[p2cl_space; IN_UNIONS; EXISTS_IN_GSPEC; IN_UNIV] THEN
    EXISTS_TAC `i:num` THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `S:B->bool` THEN REWRITE_TAC[P2CL_OPEN_IN] THEN STRIP_TAC THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    EXISTS_TAC `{z | z IN (Dm:num->real^N->bool) i /\ (kp:num->real^N->B) i z IN S}` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

let P2CC_CONT_OPEN = prove
 (`!(Dm:num->real^N->bool) Om Tr (kp:num->real^N->B) (f:B->real) t.
     p2cl_system Dm Om Tr /\ p2cl_glue Dm Om Tr kp /\
     (!i. (lift o (\z. f(kp i z))) continuous_on Dm i) /\ open t
     ==> open_in (p2cl_top Dm kp) {p | p IN topspace(p2cl_top Dm kp) /\ lift(f p) IN t}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cl_system]) THEN
  ASM_SIMP_TAC[P2CL_OPEN_IN; P2CL_TOPSPACE] THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN
  SUBGOAL_THEN `{z | z IN (Dm:num->real^N->bool) i /\
                     (kp:num->real^N->B) i z IN
                     {p | p IN p2cl_space Dm kp /\ lift((f:B->real) p) IN t}} =
                {z | z IN Dm i /\ (lift o (\z. f(kp i z))) z IN t}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; o_THM] THEN X_GEN_TAC `z:real^N` THEN
    EQ_TAC THEN SIMP_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[p2cl_space; IN_UNIONS; EXISTS_IN_GSPEC; IN_UNIV] THEN
    EXISTS_TAC `i:num` THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[ETA_AX]]);;

(* delta on a piece, and its continuity there. *)

let P2CC_DELTA_PIECE_CONT = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc s D (kp:num->real^3->real^3) i.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_dsys top atlas h yc rho s D /\
     p2cl_glue (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D) kp
     ==> (lift o (\z. p2cc_delta rho D kp (kp i z))) continuous_on p2cg_dm rho i`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC `lift o (\z. p2cg_dv D p2cc_a0 (vec 0) i z)` THEN CONJ_TAC THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2CC_DELTA THEN
    MAP_EVERY EXISTS_TAC (filter (fun t -> t <> `rho:num->real`) p2cg_std @ [`s:num->num`]) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `cball(vec 0:real^3,rho(NUMFST i) / &2)` THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                     `h:num->A->real^3^3`; `yc:num->num->num->A`; `rho:num->real`;
                     `s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`; `p2cc_a0`;
                     `i:num`] P2CG_DV_CONT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
      MP_TAC(ISPECL (p2cg_std @ [`p2cc_a0`]) P2CG_CENTRE_CBALL) THEN ASM_SIMP_TAC[];
      REWRITE_TAC[SUBSET; p2cg_dm] THEN MESON_TAC[P2CG_BALL4_CBALL]]]);;

(* Points with delta below j lie in one of the P j chart balls of level j. *)

let P2CC_DELTA_CHART = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc s D (kp:num->real^3->real^3)
    b z j.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_dsys top atlas h yc rho s D /\
     p2cl_glue (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D) kp /\
     z IN p2cg_dm rho b /\ p2cg_dv D p2cc_a0 (vec 0) b z < &j
     ==> ?i w. i < P j /\ norm w <= rho j / &8 /\ kp b z = kp (NUMPAIR j i) w`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CG_BALL4_CBALL o REWRITE_RULE[p2cg_dm] o
              check (fun th -> concl th = `(z:real^3) IN p2cg_dm rho b`)) THEN
  MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `b:num`; `z:real^3`; `j:num`]) P2CC_NET_COVER) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL (p2cg_std @ [`NUMPAIR j i`]) P2CG_CENTRE_CBALL) THEN
  ASM_REWRITE_TAC[NUMPAIR_DEST] THEN STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `NUMPAIR j i`; `vec 0:real^3`; `b:num`; `z:real^3`]) P2CG_DV_SYM) THEN
  ASM_REWRITE_TAC[NUMPAIR_DEST] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:real^3) IN p2cg_om rho D b (NUMPAIR j i)` ASSUME_TAC THENL
   [REWRITE_TAC[P2CG_IN_OM; NUMPAIR_DEST; IN_BALL_0] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `b:num`; `NUMPAIR j i`; `z:real^3`]) P2CG_TR_PROPS) THEN
  ASM_REWRITE_TAC[NUMPAIR_DEST] THEN STRIP_TAC THEN
  EXISTS_TAC `p2cg_tr rho D b (NUMPAIR j i) z` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `p2cg_dv D b z (NUMPAIR j i) (vec 0)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC P2CG_DV_ZERO_NORM THEN
    MAP_EVERY EXISTS_TAC (p2cg_std @ [`s:num->num`]) THEN
    ASM_REWRITE_TAC[NUMPAIR_DEST] THEN
    UNDISCH_TAC `p2cg_tr rho D b (NUMPAIR j i) z IN ball(vec 0,rho j / &4)` THEN
    REWRITE_TAC[IN_BALL_0; IN_CBALL_0] THEN ASM_REAL_ARITH_TAC;
    FIRST_ASSUM(MP_TAC o SPECL [`b:num`; `NUMPAIR j i`; `z:real^3`;
                                `p2cg_tr rho D b (NUMPAIR j i) z`] o
                GEN_REWRITE_RULE I [p2cl_glue]) THEN
    ASM_REWRITE_TAC[p2cg_dm; NUMPAIR_DEST]]);;

(* The sublevel sets of delta are compact. *)

let P2CC_DELTA_COMPACT = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc s D (kp:num->real^3->real^3) R.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_dsys top atlas h yc rho s D /\
     p2cl_system (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D) /\
     p2cl_glue (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D) kp
     ==> compact_in (p2cl_top (p2cg_dm rho) kp)
           {p | p IN topspace(p2cl_top (p2cg_dm rho) kp) /\ p2cc_delta rho D kp p <= R}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cl_system]) THEN
  MP_TAC(SPEC `R:real` REAL_ARCH_SIMPLE) THEN DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  MATCH_MP_TAC CLOSED_COMPACT_IN THEN
  EXISTS_TAC `UNIONS (IMAGE (\i. IMAGE ((kp:num->real^3->real^3) (NUMPAIR (n + 1) i))
                                       (cball(vec 0,rho(n + 1) / &8)))
                            {i | i < P(n + 1)})` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_UNIONS THEN
    SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology euclidean (p2cg_dm rho (NUMPAIR (n + 1) i))` THEN CONJ_TAC THENL
     [REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN; COMPACT_CBALL] THEN
      REWRITE_TAC[p2cg_dm; NUMPAIR_DEST; SUBSET; IN_CBALL_0; IN_BALL_0] THEN
      MP_TAC(ISPECL (p2cg_std @ [`n + 1`]) P2CG_RHO_POS) THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC P2CC_KP_CONTINUOUS THEN
      MAP_EVERY EXISTS_TAC [`p2cg_om rho D`; `p2cg_tr rho D`] THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    X_GEN_TAC `p:real^3` THEN STRIP_TAC THEN
    UNDISCH_TAC `(p:real^3) IN topspace(p2cl_top (p2cg_dm rho) kp)` THEN
    ASM_SIMP_TAC[P2CL_TOPSPACE] THEN
    REWRITE_TAC[p2cl_space; IN_UNIONS; EXISTS_IN_GSPEC; IN_UNIV; IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:num` (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                               `kp:num->real^3->real^3`; `b:num`; `z:real^3`]) P2CC_DELTA) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                               `kp:num->real^3->real^3`; `b:num`; `z:real^3`; `n + 1`])
                  P2CC_DELTA_CHART) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `p2cc_delta rho D kp (p:real^3) <= R` THEN
      ASM_REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `w:real^3` THEN
    ASM_REWRITE_TAC[IN_CBALL_0];
    REWRITE_TAC[closed_in] THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `topspace(p2cl_top (p2cg_dm rho) kp) DIFF
      {p | p IN topspace(p2cl_top (p2cg_dm rho) kp) /\ p2cc_delta rho D kp p <= R} =
      {p | p IN topspace(p2cl_top (p2cg_dm rho) (kp:num->real^3->real^3)) /\
           lift(p2cc_delta rho D kp p) IN {y:real^1 | y$1 > R}}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM; GSYM drop; LIFT_DROP; DE_MORGAN_THM;
                  REAL_NOT_LE; real_gt] THEN MESON_TAC[];
      MATCH_MP_TAC P2CC_CONT_OPEN THEN
      MAP_EVERY EXISTS_TAC [`p2cg_om rho D`; `p2cg_tr rho D`] THEN
      ASM_REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT] THEN X_GEN_TAC `i:num` THEN
      MATCH_MP_TAC P2CC_DELTA_PIECE_CONT THEN
      MAP_EVERY EXISTS_TAC (filter (fun t -> t <> `rho:num->real`) p2cg_std @
                            [`s:num->num`]) THEN
      ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* delta grows at most like twice the length along curves of                 *)
(* the glued limit.  One step: a short curve starting at a point of a chart  *)
(* ball of radius rho/8 stays in the chart (first exit), and there D is      *)
(* sqrt 2-Lipschitz while lengths dominate chart distances by sqrt(1/2).     *)
(* The global estimate subdivides a curve into pieces of small length.       *)
(* ------------------------------------------------------------------------- *)

let P2CC_MANIFOLD = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl (kp:num->real^3->real^3).
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
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
  MAP_EVERY EXISTS_TAC [`p2cg_om rho D`; `p2cg_tr rho D`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `a:num` THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
  EXISTS_TAC `ball(vec 0:real^3,&3 * rho(NUMFST a) / &8)` THEN
  ASM_REWRITE_TAC[p2cg_dm; OPEN_BALL] THEN MATCH_MP_TAC SUBSET_BALL THEN
  MP_TAC(ISPECL (p2cg_std @ [`NUMFST a`]) P2CG_RHO_POS) THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let P2CC_ARITH_SQRT2 = prove
 (`!d L. sqrt(inv(&2)) * d <= L ==> sqrt(&2) * d <= &2 * L`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sqrt(&2) = &2 * sqrt(inv(&2))` SUBST1_TAC THENL
   [REWRITE_TAC[SQRT_INV] THEN
    SUBGOAL_THEN `sqrt(&2) pow 2 = &2 /\ ~(sqrt(&2) = &0)` MP_TAC THENL
     [SIMP_TAC[SQRT_POW_2; REAL_POS] THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
      MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC;
      CONV_TAC REAL_FIELD];
    ASM_REAL_ARITH_TAC]);;

(* One step along a short curve. *)

let P2CC_LOCAL_STEP = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl (kp:num->real^3->real^3)
    c z (gamma:real->real^3).
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_limit top atlas h yc rho sq D Gl /\
     p2cl_glue (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D) kp /\
     mfd_c1_curve (p2cl_top (p2cg_dm rho) kp,p2cl_atlas (p2cg_dm rho) kp) gamma (&0) (&1) /\
     gamma(&0) = kp c z /\ norm z <= rho(NUMFST c) / &8 /\
     mfd_length (p2cl_atlas (p2cg_dm rho) kp) (p2cl_metric (p2cg_dm rho) kp Gl) gamma (&0) (&1)
     < sqrt(inv(&2)) * (rho(NUMFST c) / &16)
     ==> p2cc_delta rho D kp (gamma(&1)) <=
         p2cc_delta rho D kp (gamma(&0)) +
         &2 * mfd_length (p2cl_atlas (p2cg_dm rho) kp) (p2cl_metric (p2cg_dm rho) kp Gl)
                         gamma (&0) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    concl th = `(gamma:real->real^3)(&0) = (kp:num->real^3->real^3) c z`)) THEN
  MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `Gl:num->real^3->real^3^3`; `kp:num->real^3->real^3`])
                P2CC_MANIFOLD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cg_limit]) THEN
  ABBREV_TAC `L = mfd_length (p2cl_atlas (p2cg_dm rho) kp)
                    (p2cl_metric (p2cg_dm rho) kp Gl) (gamma:real->real^3) (&0) (&1)` THEN
  ABBREV_TAC `ch = p2cl_chart (p2cg_dm rho) (kp:num->real^3->real^3) c` THEN
  SUBGOAL_THEN `&0 < rho(NUMFST c)` ASSUME_TAC THENL
   [ASM_MESON_TAC[P2CG_RHO_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3) IN p2cg_dm rho c` ASSUME_TAC THENL
   [REWRITE_TAC[p2cg_dm; IN_BALL_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `SND(ch:(real^3->bool)#(real^3->real^3)) (gamma(&0)) = z /\
                (gamma:real->real^3)(&0) IN FST ch` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `(kp:num->real^3->real^3) c z = (gamma:real->real^3)(&0)`)) THEN
    EXPAND_TAC "ch" THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2CL_CHART_INV THEN
      MAP_EVERY EXISTS_TAC [`p2cg_om rho D`; `p2cg_tr rho D`] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[P2CL_CHART_FST] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (SND(ch:(real^3->bool)#(real^3->real^3))) (FST ch) = p2cg_dm rho c`
  ASSUME_TAC THENL
   [EXPAND_TAC "ch" THEN MATCH_MP_TAC P2CL_CHART_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`p2cg_om rho D`; `p2cg_tr rho D`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y v. y IN p2cg_dm rho c
          ==> inv(&2) * norm v pow 2 <=
              v dot (metric_local (p2cl_atlas (p2cg_dm rho) (kp:num->real^3->real^3)) ch
                       (p2cl_metric (p2cg_dm rho) kp Gl) y ** v) /\
              v dot (metric_local (p2cl_atlas (p2cg_dm rho) kp) ch
                       (p2cl_metric (p2cg_dm rho) kp Gl) y ** v) <= &2 * norm v pow 2`
  (LABEL_TAC "bd") THENL
   [MAP_EVERY X_GEN_TAC [`y:real^3`; `v:real^3`] THEN DISCH_TAC THEN EXPAND_TAC "ch" THEN
    ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^3`; `v:real^3`] o CONJUNCT1 o CONJUNCT2 o
                  SPEC `c:num` o check (fun th -> is_forall(concl th) &&
                    can (find_term (fun t -> is_const t && fst(dest_const t) = "metric_field"))
                        (concl th))) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `(y:real^3) IN p2cg_dm rho c` THEN REWRITE_TAC[p2cg_dm; IN_BALL_0] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `cball(z:real^3,rho(NUMFST c) / &16) SUBSET p2cg_dm rho c` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_CBALL; p2cg_dm; IN_BALL_0] THEN X_GEN_TAC `y:real^3` THEN
    MP_TAC(ISPECL [`y:real^3`; `z:real^3`] NORM_TRIANGLE_SUB) THEN
    REWRITE_TAC[dist] THEN MP_TAC(ISPECL [`z:real^3`; `y:real^3`] NORM_SUB) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN real_interval[&0,&1]
                    ==> (gamma:real->real^3) t IN FST(ch:(real^3->bool)#(real^3->real^3)) /\
                        SND ch (gamma t) IN ball(z,rho(NUMFST c) / &16)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_EXISTS_THM] THEN
    ONCE_REWRITE_TAC[TAUT `(p ==> q) <=> ~(p /\ ~q)`] THEN REWRITE_TAC[NOT_EXISTS_THM] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`p2cl_top (p2cg_dm rho) (kp:num->real^3->real^3)`;
                   `p2cl_atlas (p2cg_dm rho) (kp:num->real^3->real^3)`;
                   `p2cl_metric (p2cg_dm rho) (kp:num->real^3->real^3) Gl`;
                   `gamma:real->real^3`; `FST(ch:(real^3->bool)#(real^3->real^3))`;
                   `SND(ch:(real^3->bool)#(real^3->real^3))`; `rho(NUMFST c) / &16`;
                   `inv(&2)`; `&2`] GRGD_FIRST_EXIT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[PAIR] THEN REPEAT CONJ_TAC THENL
       [EXPAND_TAC "ch" THEN ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC;
        REPEAT GEN_TAC THEN DISCH_TAC THEN USE_THEN "bd" MATCH_MP_TAC THEN ASM SET_TAC[];
        EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[]];
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2cl_top (p2cg_dm rho) (kp:num->real^3->real^3)`;
                 `p2cl_atlas (p2cg_dm rho) (kp:num->real^3->real^3)`;
                 `p2cl_metric (p2cg_dm rho) (kp:num->real^3->real^3) Gl`;
                 `gamma:real->real^3`; `&0`; `&1`; `FST(ch:(real^3->bool)#(real^3->real^3))`;
                 `SND(ch:(real^3->bool)#(real^3->real^3))`; `inv(&2)`; `&2`;
                 `ball(z:real^3,rho(NUMFST c) / &16)`] GRGD_CHART_LENGTH_LOWER) THEN
  ASM_REWRITE_TAC[PAIR] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [EXPAND_TAC "ch" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN USE_THEN "bd" MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`z:real^3`; `rho(NUMFST c) / &16`] BALL_SUBSET_CBALL) THEN ASM SET_TAC[];
    DISCH_TAC] THEN
  SUBGOAL_THEN `?w. w IN p2cg_dm rho c /\ (gamma:real->real^3)(&1) = kp c w` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `&1` o
                  check (fun th -> can (find_term (fun t -> t = `real_interval[&0,&1]`))
                                       (concl th) && is_forall(concl th) &&
                                   not(can (find_term (fun t -> is_const t &&
                                         fst(dest_const t) = "dot")) (concl th)))) THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    EXPAND_TAC "ch" THEN ASM_REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `SND(ch:(real^3->bool)#(real^3->real^3)) (gamma(&1)) = w` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "ch" THEN MATCH_MP_TAC P2CL_CHART_INV THEN
    MAP_EVERY EXISTS_TAC [`p2cg_om rho D`; `p2cg_tr rho D`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `sqrt(inv(&2)) *
               dist(z:real^3,SND(ch:(real^3->bool)#(real^3->real^3)) (gamma(&1))) <= L` THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP P2CC_ARITH_SQRT2) THEN
  REWRITE_TAC[dist] THEN DISCH_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `kp:num->real^3->real^3`; `c:num`; `z:real^3`]) P2CC_DELTA) THEN
  MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `kp:num->real^3->real^3`; `c:num`; `w:real^3`]) P2CC_DELTA) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CG_BALL4_CBALL o REWRITE_RULE[p2cg_dm] o
              check (fun th -> concl th = `(z:real^3) IN p2cg_dm rho c`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CG_BALL4_CBALL o REWRITE_RULE[p2cg_dm] o
              check (fun th -> concl th = `(w:real^3) IN p2cg_dm rho c`)) THEN
  MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `p2cc_a0`; `vec 0:real^3`; `c:num`; `z:real^3`; `c:num`;
                             `w:real^3`]) P2CG_DV_TRI) THEN
  MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `c:num`; `z:real^3`; `w:real^3`]) P2CC_DV_UPPER) THEN
  MP_TAC(ISPECL (p2cg_std @ [`p2cc_a0`]) P2CG_CENTRE_CBALL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* One piece of a curve with small parameter length. *)

let P2CC_PIECE_STEP = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl (kp:num->real^3->real^3)
    (gamma:real->real^3) M t0 t1 j.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_limit top atlas h yc rho sq D Gl /\
     p2cl_glue (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D) kp /\
     mfd_c1_curve (p2cl_top (p2cg_dm rho) kp,p2cl_atlas (p2cg_dm rho) kp) gamma (&0) (&1) /\
     &0 <= t0 /\ t0 <= t1 /\ t1 <= &1 /\
     (!t. t IN real_interval[&0,&1]
          ==> mfd_speed (p2cl_atlas (p2cg_dm rho) kp) (p2cl_metric (p2cg_dm rho) kp Gl) gamma
                        (&0) (&1) t <= M) /\
     M * (t1 - t0) < sqrt(inv(&2)) * (rho j / &16) /\
     p2cc_delta rho D kp (gamma t0) < &j
     ==> p2cc_delta rho D kp (gamma t1) <=
         p2cc_delta rho D kp (gamma t0) +
         &2 * mfd_length (p2cl_atlas (p2cg_dm rho) kp) (p2cl_metric (p2cg_dm rho) kp Gl)
                         gamma t0 t1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `Gl:num->real^3->real^3^3`; `kp:num->real^3->real^3`])
                P2CC_MANIFOLD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cg_limit]) THEN
  SUBGOAL_THEN `(gamma:real->real^3) t0 IN topspace(p2cl_top (p2cg_dm rho) kp)` MP_TAC THENL
   [MATCH_MP_TAC(INST_TYPE [`:3`,`:N`] MFD_C1_CURVE_IN_TOPSPACE) THEN
    MAP_EVERY EXISTS_TAC [`p2cl_atlas (p2cg_dm rho) (kp:num->real^3->real^3)`; `&0`; `&1`] THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC; IN_UNIV; IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:num` (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `kp:num->real^3->real^3`; `b:num`; `z:real^3`; `j:num`])
                P2CC_DELTA_CHART) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                               `kp:num->real^3->real^3`; `b:num`; `z:real^3`]) P2CC_DELTA) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `(gamma:real->real^3) t0 = (kp:num->real^3->real^3) b z`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `mfd_length (p2cl_atlas (p2cg_dm rho) kp) (p2cl_metric (p2cg_dm rho) kp Gl)
               (gamma:real->real^3) t0 t1 <= M * (t1 - t0)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p2cl_top (p2cg_dm rho) (kp:num->real^3->real^3)`;
                   `p2cl_atlas (p2cg_dm rho) (kp:num->real^3->real^3)`;
                   `p2cl_metric (p2cg_dm rho) (kp:num->real^3->real^3) Gl`;
                   `gamma:real->real^3`; `&0`; `&1`; `t0:real`; `t1:real`]
                  GRGD_LENGTH_SUBINTERVAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`t0:real`; `t1:real`; `M:real`] REAL_INTEGRAL_CONST) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC REAL_INTEGRAL_LE THEN REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `real_interval[&0,&1]` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MFD_SPEED_CONTINUOUS THEN
        EXISTS_TAC `p2cl_top (p2cg_dm rho) (kp:num->real^3->real^3)` THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
      X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_c1_curve (p2cl_top (p2cg_dm rho) kp,p2cl_atlas (p2cg_dm rho) kp)
                 (gamma:real->real^3) t0 t1`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GRGD_C1_CURVE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2cl_top (p2cg_dm rho) (kp:num->real^3->real^3)`;
                 `p2cl_atlas (p2cg_dm rho) (kp:num->real^3->real^3)`;
                 `p2cl_metric (p2cg_dm rho) (kp:num->real^3->real^3) Gl`;
                 `gamma:real->real^3`; `t0:real`; `t1:real`;
                 `\x. t0 + (t1 - t0) * x`; `\x:real. t1 - t0`; `&0`; `&1`]
                MFD_LENGTH_REPARAM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POS] THEN BETA_TAC THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_RID; REAL_ADD_RID;
                REAL_ARITH `t0 + (t1 - t0) = t1`; REAL_CONTINUOUS_ON_CONST] THEN
    MP_TAC(ISPECL [`t0:real`; `t1:real`] GRGD_AFFINE_FACTS) THEN ASM_REWRITE_TAC[] THEN
    BETA_TAC THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `gamma' = (gamma:real->real^3) o (\x. t0 + (t1 - t0) * x)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (fun th -> SUBST1_TAC(SYM th) THEN ASSUME_TAC th)) THEN
  SUBGOAL_THEN `(gamma':real->real^3)(&0) = (gamma:real->real^3) t0 /\ gamma'(&1) = gamma t1`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "gamma'" THEN REWRITE_TAC[o_THM] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_RID; REAL_ADD_RID;
                REAL_ARITH `t0 + (t1 - t0) = t1`];
    ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    concl th = `(gamma':real->real^3)(&0) = (gamma:real->real^3) t0`)) THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    concl th = `(gamma':real->real^3)(&1) = (gamma:real->real^3) t1`)) THEN
  MATCH_MP_TAC P2CC_LOCAL_STEP THEN
  MAP_EVERY EXISTS_TAC (filter (fun t -> t <> `rho:num->real`) p2cg_std @
                        [`sq:num->num`; `NUMPAIR j i`; `w:real^3`]) THEN
  ASM_REWRITE_TAC[NUMPAIR_DEST] THEN ASM_REAL_ARITH_TAC);;

(* The global estimate along a curve. *)

let P2CC_CURVE_DELTA = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl (kp:num->real^3->real^3)
    (gamma:real->real^3).
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_limit top atlas h yc rho sq D Gl /\
     p2cl_glue (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D) kp /\
     mfd_c1_curve (p2cl_top (p2cg_dm rho) kp,p2cl_atlas (p2cg_dm rho) kp) gamma (&0) (&1)
     ==> p2cc_delta rho D kp (gamma(&1)) <=
         p2cc_delta rho D kp (gamma(&0)) +
         &2 * mfd_length (p2cl_atlas (p2cg_dm rho) kp) (p2cl_metric (p2cg_dm rho) kp Gl)
                         gamma (&0) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `Gl:num->real^3->real^3^3`; `kp:num->real^3->real^3`])
                P2CC_MANIFOLD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `lg = \t. mfd_length (p2cl_atlas (p2cg_dm rho) kp)
                         (p2cl_metric (p2cg_dm rho) kp Gl) (gamma:real->real^3) (&0) t` THEN
  SUBGOAL_THEN `!t. &0 <= t /\ t <= &1 ==> &0 <= (lg:real->real) t /\ lg t <= lg(&1)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN EXPAND_TAC "lg" THEN BETA_TAC THEN
    MP_TAC(ISPECL [`p2cl_top (p2cg_dm rho) (kp:num->real^3->real^3)`;
                   `p2cl_atlas (p2cg_dm rho) (kp:num->real^3->real^3)`;
                   `p2cl_metric (p2cg_dm rho) (kp:num->real^3->real^3) Gl`;
                   `gamma:real->real^3`; `&0`; `t:real`; `&1`] MFD_LENGTH_COMBINE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`p2cl_top (p2cg_dm rho) (kp:num->real^3->real^3)`;
                   `p2cl_atlas (p2cg_dm rho) (kp:num->real^3->real^3)`;
                   `p2cl_metric (p2cg_dm rho) (kp:num->real^3->real^3) Gl`;
                   `gamma:real->real^3`; `&0`; `t:real`] MFD_LENGTH_POS_LE) THEN
    MP_TAC(ISPECL [`p2cl_top (p2cg_dm rho) (kp:num->real^3->real^3)`;
                   `p2cl_atlas (p2cg_dm rho) (kp:num->real^3->real^3)`;
                   `p2cl_metric (p2cg_dm rho) (kp:num->real^3->real^3) Gl`;
                   `gamma:real->real^3`; `t:real`; `&1`] MFD_LENGTH_POS_LE) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?M. &0 < M /\
                    !t. t IN real_interval[&0,&1]
                        ==> mfd_speed (p2cl_atlas (p2cg_dm rho) kp)
                              (p2cl_metric (p2cg_dm rho) kp Gl) (gamma:real->real^3)
                              (&0) (&1) t <= M`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p2cl_top (p2cg_dm rho) (kp:num->real^3->real^3)`;
                   `p2cl_atlas (p2cg_dm rho) (kp:num->real^3->real^3)`;
                   `p2cl_metric (p2cg_dm rho) (kp:num->real^3->real^3) Gl`;
                   `gamma:real->real^3`; `&0`; `&1`] MFD_SPEED_CONTINUOUS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`mfd_speed (p2cl_atlas (p2cg_dm rho) kp)
                      (p2cl_metric (p2cg_dm rho) kp Gl) (gamma:real->real^3) (&0) (&1)`;
                   `real_interval[&0,&1]`] REAL_COMPACT_CONTINUOUS_IMAGE) THEN
    ASM_REWRITE_TAC[REAL_COMPACT_INTERVAL] THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[real_bounded; FORALL_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_TAC `M0:real`) THEN EXISTS_TAC `abs M0 + &1` THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `p2cc_delta rho D kp ((gamma:real->real^3)(&0)) + &2 * (lg:real->real)(&1) + &1`
              REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `j:num`) THEN
  SUBGOAL_THEN `&0 < sqrt(inv(&2)) * ((rho:num->real) j / &16)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC;
      MP_TAC(ISPECL (p2cg_std @ [`j:num`]) P2CG_RHO_POS) THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPEC `sqrt(inv(&2)) * ((rho:num->real) j / &16)` REAL_ARCH) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num` o SPEC `M:real`) THEN
  SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN REWRITE_TAC[GSYM NOT_LE; LE] THEN DISCH_TAC THEN
    UNDISCH_TAC `M < &n * sqrt(inv(&2)) * ((rho:num->real) j / &16)` THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!m. m <= n
                    ==> p2cc_delta rho D kp ((gamma:real->real^3)(&m / &n)) <=
                        p2cc_delta rho D kp (gamma(&0)) + &2 * (lg:real->real)(&m / &n)`
  (MP_TAC o SPEC `n:num`) THENL
   [INDUCT_TAC THENL
     [DISCH_TAC THEN REWRITE_TAC[real_div; REAL_MUL_LZERO] THEN EXPAND_TAC "lg" THEN
      REWRITE_TAC[mfd_length; REAL_INTEGRAL_REFL] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MP (ARITH_RULE `SUC m <= n ==> m <= n` |> C MP
      (ASSUME `SUC m <= n`))) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= &m / &n /\ &m / &n <= &(SUC m) / &n /\ &(SUC m) / &n <= &1 /\
                  &(SUC m) / &n - &m / &n = inv(&n)` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS];
        ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_OF_NUM_LE] THEN ARITH_TAC;
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LID; REAL_OF_NUM_LE];
        REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN UNDISCH_TAC `&0 < &n` THEN CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    ABBREV_TAC `t0 = &m / &n` THEN ABBREV_TAC `t1 = &(SUC m) / &n` THEN
    MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                               `Gl:num->real^3->real^3^3`; `kp:num->real^3->real^3`;
                               `gamma:real->real^3`; `M:real`; `t0:real`; `t1:real`; `j:num`])
                  P2CC_PIECE_STEP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[GSYM real_div; REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM(MP_TAC o SPEC `t0:real` o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `lg:real->real`)) (concl th))) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `p2cc_delta rho D kp ((gamma:real->real^3)(&0)) + &2 * (lg:real->real)(&1) +
                     &1 <= &j` THEN
        UNDISCH_TAC `p2cc_delta rho D kp ((gamma:real->real^3) t0) <=
                     p2cc_delta rho D kp (gamma(&0)) + &2 * (lg:real->real) t0` THEN
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`p2cl_top (p2cg_dm rho) (kp:num->real^3->real^3)`;
                   `p2cl_atlas (p2cg_dm rho) (kp:num->real^3->real^3)`;
                   `p2cl_metric (p2cg_dm rho) (kp:num->real^3->real^3) Gl`;
                   `gamma:real->real^3`; `&0`; `t0:real`; `t1:real`] MFD_LENGTH_COMBINE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC GRGD_C1_CURVE_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN EXPAND_TAC "lg" THEN BETA_TAC THEN
    DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `p2cc_delta rho D kp ((gamma:real->real^3) t0) <=
                 p2cc_delta rho D kp (gamma(&0)) + &2 * (lg:real->real) t0` THEN
    EXPAND_TAC "lg" THEN BETA_TAC THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[LE_REFL; REAL_DIV_REFL; REAL_LT_IMP_NZ] THEN EXPAND_TAC "lg" THEN
    REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Completeness and the exhaustion.  Closed metric balls lie in              *)
(* sublevel sets of delta (curves of almost minimal length and the curve     *)
(* estimate), so they are compact; the sets delta < k + 1 are open, contain  *)
(* the base point, have compact closures inside the next one, and exhaust.  *)
(* ------------------------------------------------------------------------- *)

(* Curves of almost minimal length (the same as P2BC_DIST_APPROX of the unit  *)
(* pc_p2b_cap, which is not in this closure).                                 *)

let P2CC_DIST_APPROX = prove
 (`!top atlas (g:A->real^N^N) x y e.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_joinable (top,atlas) x y /\ &0 < e
     ==> ?gamma. mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
                 gamma(&0) = x /\ gamma(&1) = y /\
                 mfd_length atlas g gamma (&0) (&1) < mfd_dist (top,atlas) g x y + e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{mfd_length atlas (g:A->real^N^N) gamma (&0) (&1) | gamma |
                   mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
                   gamma(&0) = (x:A) /\ gamma(&1) = y}`;
                 `mfd_dist (top,atlas) (g:A->real^N^N) x y + e`] INF_APPROACH) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; GRGD_IN_LENGTHS] THEN
      UNDISCH_TAC `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) x y` THEN
      REWRITE_TAC[mfd_joinable] THEN
      DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `mfd_length atlas (g:A->real^N^N) gamma (&0) (&1)` THEN
      EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `&0` THEN X_GEN_TAC `L:real` THEN DISCH_TAC THEN
      MATCH_MP_TAC GRGD_LENGTHS_POS_LE THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                            `g:A->real^N^N`; `x:A`; `y:A`] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM mfd_dist] THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[GRGD_IN_LENGTHS] THEN
    DISCH_THEN(X_CHOOSE_THEN `L:real` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    EXISTS_TAC `gamma:real->A` THEN ASM_MESON_TAC[]]);;

(* Closed metric balls lie in sublevel sets of delta. *)

let P2CC_CBALL_SUBLEVEL = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl (kp:num->real^3->real^3)
    p r.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_limit top atlas h yc rho sq D Gl /\
     p2cl_glue (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D) kp
     ==> mfd_cball (p2cl_top (p2cg_dm rho) kp,p2cl_atlas (p2cg_dm rho) kp)
                   (p2cl_metric (p2cg_dm rho) kp Gl) p r SUBSET
         {q | q IN topspace(p2cl_top (p2cg_dm rho) kp) /\
              p2cc_delta rho D kp q <= p2cc_delta rho D kp p + &2 * r + &1}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `Gl:num->real^3->real^3^3`; `kp:num->real^3->real^3`])
                P2CC_MANIFOLD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[SUBSET; mfd_cball; IN_ELIM_THM] THEN X_GEN_TAC `q:real^3` THEN STRIP_TAC THEN
  CONJ_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p2cl_top (p2cg_dm rho) (kp:num->real^3->real^3)`;
                 `p2cl_atlas (p2cg_dm rho) (kp:num->real^3->real^3)`;
                 `p2cl_metric (p2cg_dm rho) (kp:num->real^3->real^3) Gl`;
                 `p:real^3`; `q:real^3`; `inv(&2)`] P2CC_DIST_APPROX) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:real->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `Gl:num->real^3->real^3^3`; `kp:num->real^3->real^3`;
                             `gamma:real->real^3`]) P2CC_CURVE_DELTA) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `mfd_length (p2cl_atlas (p2cg_dm rho) kp) (p2cl_metric (p2cg_dm rho) kp Gl)
                 (gamma:real->real^3) (&0) (&1) <
               mfd_dist (p2cl_top (p2cg_dm rho) kp,p2cl_atlas (p2cg_dm rho) kp)
                 (p2cl_metric (p2cg_dm rho) kp Gl) p q + inv(&2)` THEN
  UNDISCH_TAC `mfd_dist (p2cl_top (p2cg_dm rho) (kp:num->real^3->real^3),
                         p2cl_atlas (p2cg_dm rho) kp)
                 (p2cl_metric (p2cg_dm rho) kp Gl) p q <= r` THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Completeness. *)

let P2CC_COMPLETE = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl (kp:num->real^3->real^3).
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_limit top atlas h yc rho sq D Gl /\
     p2cl_glue (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D) kp
     ==> mfd_complete (p2cl_top (p2cg_dm rho) kp,p2cl_atlas (p2cg_dm rho) kp)
                      (p2cl_metric (p2cg_dm rho) kp Gl)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `Gl:num->real^3->real^3^3`; `kp:num->real^3->real^3`])
                P2CC_MANIFOLD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cg_limit]) THEN
  REWRITE_TAC[mfd_complete] THEN MAP_EVERY X_GEN_TAC [`p:real^3`; `r:real`] THEN DISCH_TAC THEN
  MATCH_MP_TAC CLOSED_COMPACT_IN THEN
  EXISTS_TAC `{q | q IN topspace(p2cl_top (p2cg_dm rho) kp) /\
                   p2cc_delta rho D kp q <=
                   p2cc_delta rho D (kp:num->real^3->real^3) p + &2 * r + &1}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2CC_DELTA_COMPACT THEN
    MAP_EVERY EXISTS_TAC (filter (fun t -> t <> `rho:num->real`) p2cg_std @
                          [`sq:num->num`]) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2CC_CBALL_SUBLEVEL THEN
    MAP_EVERY EXISTS_TAC (filter (fun t -> t <> `rho:num->real`) p2cg_std @
                          [`sq:num->num`]) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MFD_CBALL_CLOSED THEN ASM_REWRITE_TAC[]]);;

(* The exhaustion by the sets delta < k + 1. *)

let p2cc_W = new_definition
 `p2cc_W (rho:num->real) (D:num#num->real^(3,3)finite_sum->real^1)
         (kp:num->real^3->real^3) k =
    {p | p IN topspace(p2cl_top (p2cg_dm rho) kp) /\ p2cc_delta rho D kp p < &k + &1}`;;

let p2cc_xl = new_definition
 `p2cc_xl (kp:num->real^3->real^3) = kp p2cc_a0 (vec 0)`;;

let P2CC_DELTA_LEVEL_SETS = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl (kp:num->real^3->real^3) R.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_limit top atlas h yc rho sq D Gl /\
     p2cl_glue (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D) kp
     ==> open_in (p2cl_top (p2cg_dm rho) kp)
           {p | p IN topspace(p2cl_top (p2cg_dm rho) kp) /\ p2cc_delta rho D kp p < R} /\
         closed_in (p2cl_top (p2cg_dm rho) kp)
           {p | p IN topspace(p2cl_top (p2cg_dm rho) kp) /\ p2cc_delta rho D kp p <= R}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cg_limit]) THEN
  SUBGOAL_THEN `!i. (lift o (\z. p2cc_delta rho D kp ((kp:num->real^3->real^3) i z)))
                    continuous_on p2cg_dm rho i` ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN MATCH_MP_TAC P2CC_DELTA_PIECE_CONT THEN
    MAP_EVERY EXISTS_TAC (filter (fun t -> t <> `rho:num->real`) p2cg_std @ [`sq:num->num`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `{p | p IN topspace(p2cl_top (p2cg_dm rho) kp) /\ p2cc_delta rho D kp p < R} =
      {p | p IN topspace(p2cl_top (p2cg_dm rho) (kp:num->real^3->real^3)) /\
           lift(p2cc_delta rho D kp p) IN {y:real^1 | y$1 < R}}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; GSYM drop; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC P2CC_CONT_OPEN THEN
    MAP_EVERY EXISTS_TAC [`p2cg_om rho D`; `p2cg_tr rho D`] THEN
    ASM_REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT];
    REWRITE_TAC[closed_in] THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `topspace(p2cl_top (p2cg_dm rho) kp) DIFF
      {p | p IN topspace(p2cl_top (p2cg_dm rho) kp) /\ p2cc_delta rho D kp p <= R} =
      {p | p IN topspace(p2cl_top (p2cg_dm rho) (kp:num->real^3->real^3)) /\
           lift(p2cc_delta rho D kp p) IN {y:real^1 | y$1 > R}}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM; GSYM drop; LIFT_DROP; DE_MORGAN_THM;
                  REAL_NOT_LE; real_gt] THEN MESON_TAC[];
      MATCH_MP_TAC P2CC_CONT_OPEN THEN
      MAP_EVERY EXISTS_TAC [`p2cg_om rho D`; `p2cg_tr rho D`] THEN
      ASM_REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT]]]);;

let P2CC_EXHAUST = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl (kp:num->real^3->real^3).
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_limit top atlas h yc rho sq D Gl /\
     p2cl_glue (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D) kp
     ==> p2cc_xl kp IN topspace(p2cl_top (p2cg_dm rho) kp) /\
         p2cc_delta rho D kp (p2cc_xl kp) = &0 /\
         (!k. open_in (p2cl_top (p2cg_dm rho) kp) (p2cc_W rho D kp k) /\
              p2cc_xl kp IN p2cc_W rho D kp k /\
              compact_in (p2cl_top (p2cg_dm rho) kp)
                         (p2cl_top (p2cg_dm rho) kp closure_of p2cc_W rho D kp k) /\
              p2cl_top (p2cg_dm rho) kp closure_of p2cc_W rho D kp k SUBSET
              p2cc_W rho D kp (SUC k)) /\
         UNIONS {p2cc_W rho D kp k | k IN (:num)} = topspace(p2cl_top (p2cg_dm rho) kp)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `Gl:num->real^3->real^3^3`; `kp:num->real^3->real^3`])
                P2CC_MANIFOLD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cg_limit]) THEN
  MP_TAC(ISPECL (p2cg_std @ [`p2cc_a0`]) P2CG_CENTRE_CBALL) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `vec 0 IN p2cg_dm rho p2cc_a0` ASSUME_TAC THENL
   [REWRITE_TAC[p2cg_dm; CENTRE_IN_BALL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `p2cc_delta rho D kp (p2cc_xl kp) = &0` ASSUME_TAC THENL
   [REWRITE_TAC[p2cc_xl] THEN
    MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                               `kp:num->real^3->real^3`; `p2cc_a0`; `vec 0:real^3`])
                  P2CC_DELTA) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC P2CG_DV_DIAG THEN
    MAP_EVERY EXISTS_TAC (p2cg_std @ [`sq:num->num`]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2cc_xl kp IN topspace(p2cl_top (p2cg_dm rho) kp)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[p2cc_xl; IN_UNIONS; EXISTS_IN_GSPEC; IN_UNIV] THEN
    EXISTS_TAC `p2cc_a0` THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "topspace")) (lhs(concl th)))) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN
    MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                               `Gl:num->real^3->real^3^3`; `kp:num->real^3->real^3`;
                               `&k + &1`]) P2CC_DELTA_LEVEL_SETS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                               `kp:num->real^3->real^3`; `&k + &1`]) P2CC_DELTA_COMPACT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `p2cl_top (p2cg_dm rho) kp closure_of p2cc_W rho D kp k SUBSET
                  {p | p IN topspace(p2cl_top (p2cg_dm rho) (kp:num->real^3->real^3)) /\
                       p2cc_delta rho D kp p <= &k + &1}`
    ASSUME_TAC THENL
     [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN ASM_REWRITE_TAC[p2cc_W] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[p2cc_W; IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC CLOSED_COMPACT_IN THEN
      EXISTS_TAC `{p | p IN topspace(p2cl_top (p2cg_dm rho) (kp:num->real^3->real^3)) /\
                       p2cc_delta rho D kp p <= &k + &1}` THEN
      ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF] THEN ASM_REWRITE_TAC[GSYM p2cc_W];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `{p | p IN topspace(p2cl_top (p2cg_dm rho) (kp:num->real^3->real^3)) /\
                       p2cc_delta rho D kp p <= &k + &1}` THEN
      ASM_REWRITE_TAC[GSYM p2cc_W] THEN REWRITE_TAC[p2cc_W; SUBSET; IN_ELIM_THM] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN MESON_TAC[REAL_ARITH `x <= k + &1 ==> x < (k + &1) + &1`]];
    REWRITE_TAC[EXTENSION; IN_UNIONS; EXISTS_IN_GSPEC; IN_UNIV; p2cc_W; IN_ELIM_THM] THEN
    X_GEN_TAC `p:real^3` THEN EQ_TAC THENL [MESON_TAC[]; DISCH_TAC] THEN
    MP_TAC(SPEC `p2cc_delta rho D kp (p:real^3)` REAL_ARCH_SIMPLE) THEN
    DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN EXISTS_TAC `n:num` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* The complete, exhausted limit of a subsequence. *)

let P2CC_COMPLETE_LIMIT = prove
 (`!top atlas (h:num->A->real^3^3) x.
     P2C_REQ_CGT_STATEMENT (:A) /\ p2cu_seq top atlas h x
     ==> ?rho K N0 B NB P Nn yc sq D Gl (kp:num->real^3->real^3).
           p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
           p2cg_limit top atlas h yc rho sq D Gl /\
           p2cl_glue (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D) kp /\
           hausdorff_space (p2cl_top (p2cg_dm rho) kp) /\
           smooth_manifold_atlas (p2cl_top (p2cg_dm rho) kp) (p2cl_atlas (p2cg_dm rho) kp) /\
           riemannian_metric (p2cl_atlas (p2cg_dm rho) kp) (p2cl_metric (p2cg_dm rho) kp Gl) /\
           mfd_complete (p2cl_top (p2cg_dm rho) kp,p2cl_atlas (p2cg_dm rho) kp)
                        (p2cl_metric (p2cg_dm rho) kp Gl) /\
           topspace (p2cl_top (p2cg_dm rho) kp) =
           UNIONS {IMAGE (kp i) (p2cg_dm rho i) | i IN (:num)} /\
           (!i. p2cl_chart (p2cg_dm rho) kp i IN p2cl_atlas (p2cg_dm rho) kp /\
                FST(p2cl_chart (p2cg_dm rho) kp i) = IMAGE (kp i) (p2cg_dm rho i) /\
                !z. z IN p2cg_dm rho i ==> SND(p2cl_chart (p2cg_dm rho) kp i) (kp i z) = z) /\
           (!i y. y IN p2cg_dm rho i
                  ==> metric_local (p2cl_atlas (p2cg_dm rho) kp) (p2cl_chart (p2cg_dm rho) kp i)
                                   (p2cl_metric (p2cg_dm rho) kp Gl) y = Gl i y) /\
           p2cc_xl kp IN topspace(p2cl_top (p2cg_dm rho) kp) /\
           (!k. open_in (p2cl_top (p2cg_dm rho) kp) (p2cc_W rho D kp k) /\
                p2cc_xl kp IN p2cc_W rho D kp k /\
                compact_in (p2cl_top (p2cg_dm rho) kp)
                           (p2cl_top (p2cg_dm rho) kp closure_of p2cc_W rho D kp k) /\
                p2cl_top (p2cg_dm rho) kp closure_of p2cc_W rho D kp k SUBSET
                p2cc_W rho D kp (SUC k)) /\
           UNIONS {p2cc_W rho D kp k | k IN (:num)} = topspace(p2cl_top (p2cg_dm rho) kp)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                 `h:num->A->real^3^3`; `x:num->A`] P2CG_GLUED_LIMIT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`rho:num->real`; `K:num->real`; `N0:num->num`; `B:num->num->real`;
                        `NB:num->num->num`; `P:num->num`; `Nn:num->num`;
                        `yc:num->num->num->A`; `sq:num->num`;
                        `D:num#num->real^(3,3)finite_sum->real^1`;
                        `Gl:num->real^3->real^3^3`; `kp:num->real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2CC_COMPLETE THEN
    MAP_EVERY EXISTS_TAC [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                          `h:num->A->real^3^3`; `x:num->A`; `K:num->real`; `N0:num->num`;
                          `B:num->num->real`; `NB:num->num->num`; `P:num->num`;
                          `Nn:num->num`; `yc:num->num->num->A`; `sq:num->num`;
                          `D:num#num->real^(3,3)finite_sum->real^1`] THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                               `Gl:num->real^3->real^3^3`; `kp:num->real^3->real^3`])
                  P2CC_EXHAUST) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[]]);;


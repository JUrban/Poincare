(* ========================================================================= *)
(* Unit pc_p2a_t964: MT Thm 9.64 (compactness of based 3-dimensional         *)
(* kappa-solutions with R(p,0) = 1) in route form, P2AT64_THM_9_64_ROUTE:    *)
(* P2B_THM_9_64_ROUTE_STATEMENT of pc_p2b_chainstmts, from Lemma 9.65, the   *)
(* final-slice form of Cor 9.53 (P2B_COR_9_53_FINAL_STATEMENT, proved in     *)
(* pc_p2b_close95) and the sequence limit S of pc_p2a_l965.  The limit is a  *)
(* kappa-solution once its final slice has bounded curvature: R is           *)
(* nondecreasing in time on the limit, so abs Rm <= R/2 <= R(0)/2 bounds     *)
(* every slab, and P2BX0_SCALAR_POS_ALL gives non-flatness at all times.     *)
(* ========================================================================= *)

needs "src/pc_p2a_l965.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* R is nondecreasing in time on kappa-solutions and on their limits (S);    *)
(* dR/ds >= 0 on the limit; a bound at the final slice of the limit makes it *)
(* a kappa-solution.                                                         *)
(* ========================================================================= *)

let P2AT64_KSOL_RMONO = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) t1 t2 x.
     P2B_KSOL_DRDT_STATEMENT w /\ p2b_kappa_solution kappa (top,atlas) g /\
     t1 <= t2 /\ t2 <= &0 /\ x IN topspace top
     ==> mfd_scalar atlas (g t1) x <= mfd_scalar atlas (g t2) x`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "drdt") STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `t2 = &0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC P2AL65_KSOL_SCALAR_LE0 THEN
    MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`; `top:B topology`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2B_KSOL_BASIC) THEN
  SUBGOAL_THEN `ricci_flow_on (top,atlas) (t1 - &1) (&0) (g:real->B->real^3^3)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `t1 - &1` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_flow_upto")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[rfs_flow_upto]];
    ALL_TAC] THEN
  MATCH_MP_TAC P2BX0_SCALAR_MONO THEN
  MAP_EVERY EXISTS_TAC [`top:B topology`; `t1 - &1`; `&0`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`s:real`; `dR:real`] THEN STRIP_TAC THEN
    USE_THEN "drdt" (MP_TAC o SPECL [`kappa:real`; `top:B topology`;
                                     `atlas:((B->bool)#(B->real^3))->bool`;
                                     `g:real->B->real^3^3`] o
                     REWRITE_RULE[P2B_KSOL_DRDT_STATEMENT]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`s:real`; `x:B`] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* R is nondecreasing in s on the limit. *)

let P2AT64_SLIM_RMONO = prove
 (`!(w:B->bool) kappa (top:num->B topology) atlas (g:num->real->B->real^3^3) x Q
    top' atlas' g' xl W phi s1 s2 y.
     P2B_KSOL_DRDT_STATEMENT w /\
     p2al65_slim kappa top atlas g x Q (top',atlas') g' xl W phi /\
     s1 <= s2 /\ s2 <= &0 /\ y IN topspace top'
     ==> mfd_scalar atlas' (g' s1) y <= mfd_scalar atlas' (g' s2) y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "drdt") (CONJUNCTS_THEN2 (LABEL_TAC "sl")
    STRIP_ASSUME_TAC)) THEN
  USE_THEN "sl" (STRIP_ASSUME_TAC o REWRITE_RULE[p2al65_slim]) THEN
  MP_TAC(ISPECL [`kappa:real`; `top:num->B topology`; `atlas:num->((B->bool)#(B->real^3))->bool`;
                 `g:num->real->B->real^3^3`; `x:num->B`; `Q:num->real`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->B`; `s1:real`; `y:B`] P2AL65_SLIM_SCALAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`kappa:real`; `top:num->B topology`; `atlas:num->((B->bool)#(B->real^3))->bool`;
                 `g:num->real->B->real^3^3`; `x:num->B`; `Q:num->real`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->B`; `s2:real`; `y:B`] P2AL65_SLIM_SCALAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`kappa:real`; `top:num->B topology`; `atlas:num->((B->bool)#(B->real^3))->bool`;
                 `g:num->real->B->real^3^3`; `x:num->B`; `Q:num->real`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->B`; `y:B`; `&1`] P2AL65_SLIM_NEAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LT_01]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `k0:num`) THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LE) THEN
  MAP_EVERY EXISTS_TAC
   [`\k. mfd_scalar ((atlas:num->((B->bool)#(B->real^3))->bool) k)
                    ((g:num->real->B->real^3^3) k (s1 / (Q:num->real) k)) ((phi:num->B->B) k y) /
         Q k`;
    `\k. mfd_scalar ((atlas:num->((B->bool)#(B->real^3))->bool) k)
                    ((g:num->real->B->real^3^3) k (s2 / (Q:num->real) k)) ((phi:num->B->B) k y) /
         Q k`] THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
  EXISTS_TAC `k0:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN BETA_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
    can (find_term ((=) `k0:num`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2b_ksep")) (concl th) &&
    is_forall(concl th))) THEN
  STRIP_TAC THEN ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
  MATCH_MP_TAC P2AT64_KSOL_RMONO THEN
  MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`; `(top:num->B topology) k`] THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_LE_LDIV_EQ; REAL_MUL_LZERO]);;

(* dR/ds >= 0 on the limit. *)

let P2AT64_SLIM_DRDT = prove
 (`!(w:B->bool) kappa (top:num->B topology) atlas (g:num->real->B->real^3^3) x Q
    top' atlas' g' xl W phi.
     P2B_KSOL_DRDT_STATEMENT w /\
     p2al65_slim kappa top atlas g x Q (top',atlas') g' xl W phi
     ==> !s y dR. s < &0 /\ y IN topspace top' /\
                  ((\t. mfd_scalar atlas' (g' t) y) has_real_derivative dR) (atreal s)
                  ==> &0 <= dR`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC P2BX0_MONO_DERIV_NONNEG THEN
  MAP_EVERY EXISTS_TAC [`\t. mfd_scalar atlas' ((g':real->B->real^3^3) t) y`; `s:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC P2AT64_SLIM_RMONO THEN
  MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`; `top:num->B topology`;
                        `atlas:num->((B->bool)#(B->real^3))->bool`; `g:num->real->B->real^3^3`;
                        `x:num->B`; `Q:num->real`; `top':B topology`; `xl:B`;
                        `W:num->B->bool`; `phi:num->B->B`] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* A bound at the final slice makes the limit a kappa-solution. *)

let P2AT64_SLIM_KSOL = prove
 (`!(w:B->bool) kappa (top:num->B topology) atlas (g:num->real->B->real^3^3) x Q
    top' atlas' g' xl W phi K.
     P2B_KSOL_DRDT_STATEMENT w /\
     p2al65_slim kappa top atlas g x Q (top',atlas') g' xl W phi /\
     mfd_scalar atlas' (g'(&0)) xl = &1 /\
     (!y. y IN topspace top' ==> mfd_rm_norm atlas' (g'(&0)) y <= K)
     ==> p2b_kappa_solution kappa (top',atlas') g' /\ p2b_ksep top' atlas'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "drdt") (CONJUNCTS_THEN2 (LABEL_TAC "sl")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "K")))) THEN
  USE_THEN "sl" (fun th -> STRIP_ASSUME_TAC(MATCH_MP P2AL65_SLIM_BASIC th) THEN
    ASSUME_TAC(MATCH_MP P2AL65_SLIM_SEC th) THEN
    ASSUME_TAC(MATCH_MP P2AL65_SLIM_COMPLETE th) THEN
    ASSUME_TAC(REWRITE_RULE[p2b_kview] (MATCH_MP P2AL65_SLIM_KNC th)) THEN
    ASSUME_TAC(MATCH_MP P2AL65_SLIM_KSEP th) THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[p2al65_slim] th)) THEN
  (* the uniform bound 3K *)
  SUBGOAL_THEN `!s y. s <= &0 /\ y IN topspace top'
                      ==> mfd_rm_norm atlas' ((g':real->B->real^3^3) s) y <= &3 * K`
  (LABEL_TAC "rmU") THENL
   [MAP_EVERY X_GEN_TAC [`s:real`; `y:B`] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_scalar atlas' ((g':real->B->real^3^3) s) y / &2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2BX0_RM_NORM_LE_HALF_SCALAR THEN EXISTS_TAC `top':B topology` THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `mfd_scalar atlas' ((g':real->B->real^3^3) s) y <= mfd_scalar atlas' (g'(&0)) y`
    MP_TAC THENL
     [MATCH_MP_TAC P2AT64_SLIM_RMONO THEN
      MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`; `top:num->B topology`;
                            `atlas:num->((B->bool)#(B->real^3))->bool`;
                            `g:num->real->B->real^3^3`; `x:num->B`; `Q:num->real`;
                            `top':B topology`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `(g':real->B->real^3^3)(&0)`; `y:B`] P2AU_MFD_SCALAR_ABS_3) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "K" (MP_TAC o SPEC `y:B`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `xl:B`; `&3 * K`] P2BX0_SCALAR_POS_ALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 < kappa` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2b_ksep")) (concl th) &&
      is_forall(concl th))) THEN
    SIMP_TAC[p2b_kappa_solution; p2c_kappa_sol];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[p2b_kappa_solution; p2c_kappa_sol] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `xl:B` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN EXISTS_TAC `&3 * K` THEN
    X_GEN_TAC `y:B` THEN DISCH_TAC THEN USE_THEN "rmU" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN EXISTS_TAC `xl:B` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `(g':real->B->real^3^3) t`; `xl:B`] P2AU_MFD_SCALAR_ABS_3) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < mfd_scalar atlas' ((g':real->B->real^3^3) t) xl` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    X_GEN_TAC `a:real` THEN DISCH_TAC THEN EXISTS_TAC `&3 * K` THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `y:B`] THEN STRIP_TAC THEN
    USE_THEN "rmU" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* MT Thm 9.64 in route form.  Lemma 9.65 bounds R on every ball B_0(p k, A) *)
(* of the based kappa-solutions; the sequence limit S (Q k = 1, per-Tl       *)
(* limits along the same subsequence) is complete, connected, sec >= 0,      *)
(* kappa-noncollapsed at all scales, ksep, with R'(pl,0) = 1 and dR'/ds >=   *)
(* 0; the final-slice form of Cor 9.53 bounds abs Rm at s = 0, and           *)
(* P2AT64_SLIM_KSOL makes the limit a kappa-solution.                        *)
(* ========================================================================= *)

let P2AT64_THM_9_64_ROUTE = prove
 (`!w:B->bool. P2B_THM_9_64_ROUTE_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2B_THM_9_64_ROUTE_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "l965") (CONJUNCTS_THEN2 (LABEL_TAC "drdt")
    (CONJUNCTS_THEN2 (LABEL_TAC "AC") (LABEL_TAC "c953f")))) THEN
  REWRITE_TAC[P2B_THM_9_64_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`kappa:real`; `top:num->B topology`;
                       `atlas:num->((B->bool)#(B->real^3))->bool`;
                       `g:num->real->B->real^3^3`; `p:num->B`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "seq")) THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:num->B topology`;
                 `atlas:num->((B->bool)#(B->real^3))->bool`; `g:num->real->B->real^3^3`;
                 `p:num->B`; `\k:num. &1`] P2AL65_SLIM_EXISTS_P3) THEN
  BETA_TAC THEN REWRITE_TAC[SQRT_1; REAL_INV_1; REAL_MUL_RID; REAL_LT_01] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `A:real` THEN DISCH_TAC THEN
    USE_THEN "l965" (MP_TAC o SPECL [`kappa:real`; `A:real`] o
                     REWRITE_RULE[P2B_LEMMA_9_65_STATEMENT]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `Cr:real`) THEN
    MAP_EVERY EXISTS_TAC [`Cr:real`; `0`] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`(top:num->B topology) k`; `(p:num->B) k`] THEN
    REWRITE_TAC[ETA_AX] THEN USE_THEN "seq" (fun th -> ASM_REWRITE_TAC[th]);
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `top':B topology`
    (X_CHOOSE_THEN `atlas':((B->bool)#(B->real^3))->bool` (X_CHOOSE_THEN `g':real->B->real^3^3`
    (X_CHOOSE_THEN `pl:B` (X_CHOOSE_THEN `W:num->B->bool` (X_CHOOSE_THEN `phi:num->B->B`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "sl") (LABEL_TAC "p3")))))))))) THEN
  USE_THEN "sl" (fun th -> STRIP_ASSUME_TAC(MATCH_MP P2AL65_SLIM_BASIC th) THEN
    ASSUME_TAC(MATCH_MP P2AL65_SLIM_SEC th) THEN
    ASSUME_TAC(MATCH_MP P2AL65_SLIM_COMPLETE th) THEN
    ASSUME_TAC(MATCH_MP P2AL65_SLIM_KNC th) THEN
    ASSUME_TAC(MATCH_MP P2AL65_SLIM_KSEP th) THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[p2al65_slim] th)) THEN
  SUBGOAL_THEN `(\k:num. &1) o (sub:num->num) = (\k. &1)` ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar atlas' ((g':real->B->real^3^3)(&0)) pl = &1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`kappa:real`; `(top:num->B topology) o (sub:num->num)`;
                   `(atlas:num->((B->bool)#(B->real^3))->bool) o (sub:num->num)`;
                   `(g:num->real->B->real^3^3) o (sub:num->num)`; `(p:num->B) o (sub:num->num)`;
                   `(\k:num. &1) o (sub:num->num)`; `top':B topology`;
                   `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `pl:B`;
                   `W:num->B->bool`; `phi:num->B->B`; `&0`; `pl:B`] P2AL65_SLIM_SCALAR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    ASM_REWRITE_TAC[o_THM; REAL_DIV_1] THEN
    USE_THEN "seq" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[REALLIM_CONST_EQ; TRIVIAL_LIMIT_SEQUENTIALLY] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `(top:num->B topology) o (sub:num->num)`;
                 `(atlas:num->((B->bool)#(B->real^3))->bool) o (sub:num->num)`;
                 `(g:num->real->B->real^3^3) o (sub:num->num)`; `(p:num->B) o (sub:num->num)`;
                 `(\k:num. &1) o (sub:num->num)`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `pl:B`;
                 `W:num->B->bool`; `phi:num->B->B`] P2AT64_SLIM_DRDT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "c953f" (MP_TAC o SPECL [`kappa:real`; `top':B topology`;
                                    `atlas':((B->bool)#(B->real^3))->bool`;
                                    `g':real->B->real^3^3`; `pl:B`] o
                    REWRITE_RULE[P2B_COR_9_53_FINAL_STATEMENT]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LT_01]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `K:real`) THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `(top:num->B topology) o (sub:num->num)`;
                 `(atlas:num->((B->bool)#(B->real^3))->bool) o (sub:num->num)`;
                 `(g:num->real->B->real^3^3) o (sub:num->num)`; `(p:num->B) o (sub:num->num)`;
                 `(\k:num. &1) o (sub:num->num)`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `pl:B`;
                 `W:num->B->bool`; `phi:num->B->B`; `K:real`] P2AT64_SLIM_KSOL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MAP_EVERY EXISTS_TAC [`sub:num->num`; `top':B topology`;
                        `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`;
                        `pl:B`] THEN
  ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "p3" MP_TAC THEN ASM_REWRITE_TAC[]);;


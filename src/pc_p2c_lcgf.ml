(* ========================================================================= *)
(* Unit pc_p2c_lcgf (Part 2C, the general form G of local compactness): the  *)
(* flow stage.  Flow candidates (a CG chart, a radius, two dyadic times and  *)
(* a curvature bound) whose normal balls persist with bounded curvature give *)
(* sequences of local Ricci flows with uniform bounds (P2CD_SEQHYP_GEN); a   *)
(* dichotomy diagonal makes every candidate either eventually inadmissible   *)
(* or eventually admissible with a local limit flow, along one subsequence   *)
(* and all its further subsequences; the local limits in the CG charts, the  *)
(* region where they live, and the view Vl of the limit flow.                *)
(* ========================================================================= *)

needs "src/pc_p2c_lcgk.ml";;
needs "src/pc_p2c_flasm.ml";;
needs "src/pc_p2c_flseq.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The dichotomy diagonal.  For countably many sequences H d                 *)
(* and admissibility predicates adm d (indices), if every sequence of        *)
(* admissible indices gives uniform bounds (p2ca_seqhyp), there is one       *)
(* subsequence t along which every d is either eventually admissible with a *)
(* local limit, or eventually inadmissible (SUBSEQUENCE_DIAGONALIZATION_LEMMA *)
(* as in P2CA_DIAG); both alternatives pass to further subsequences.         *)
(* The local limit (p2gf_lim) is the local limit flow of p2ca_loclim with    *)
(* two more properties from the context p2cm_ctx of its proof: convergence  *)
(* near every point along converging times and any indices ns j >= j        *)
(* (p2gf_mov, P2CM_CTX_NEAR_SEQ), and a smooth extension past the final time *)
(* (P2CD_UPTO_TOP_CTX).                                                       *)
(* ------------------------------------------------------------------------- *)

let p2gf_mov = new_definition
 `p2gf_mov (V:real^N->bool) a b (Gs:num->real->real^N->real^N^N) G <=>
    !ts t0 ns y0. (!j. a <= ts j /\ ts j <= b) /\ a <= t0 /\ t0 <= b /\
                  ((\j. lift(ts j)) --> lift t0) sequentially /\ (!j. j <= ns j) /\ y0 IN V
                  ==> p2cm_mnear y0 (\j. G (ts j)) (G t0) /\
                      p2ci_near y0 (\j. vectorize o Gs (ns j) (ts j)) (vectorize o G t0)`;;

let p2gf_lim = new_definition
 `p2gf_lim (V:real^N->bool) a b (Gs:num->real->real^N->real^N^N) G <=>
    p2ca_loclim V a b Gs G /\ p2gf_mov V a b Gs G /\
    ?e (Fx:real^(1,N)finite_sum->real^(N,N)finite_prod).
       &0 < e /\ smooth_map_on (interval(lift a,lift(b + e)) PCROSS V) Fx /\
       !t y. a < t /\ t <= b /\ y IN V ==> Fx(pastecart (lift t) y) = vectorize(G t y)`;;

(* The context gives the local limit flow (the end of P2CM_LOCAL_LIMIT). *)

let P2GF_CTX_LOCLIM = prove
 (`!V a b (Gs:num->real->real^N->real^N^N) FF ee c r sub H.
     p2cm_ctx V a b Gs FF ee c r sub H
     ==> p2ca_loclim V a b (\n. Gs (sub n)) (p2cm_lim Gs sub)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2ca_loclim] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2CM_CTX_FLOW THEN
    MAP_EVERY EXISTS_TAC [`FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`;
                          `ee:num->real`; `c:num->real^N`; `r:num->real`;
                          `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`] THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2CM_CTX_METRIC THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`;
                          `FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`;
                          `ee:num->real`; `c:num->real^N`; `r:num->real`;
                          `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`] THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN REWRITE_TAC[TENDSTO_REAL; o_DEF] THEN
    MATCH_MP_TAC P2CM_CTX_ENTRY_LIM THEN
    MAP_EVERY EXISTS_TAC [`V:real^N->bool`; `a:real`; `b:real`;
                          `FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`;
                          `ee:num->real`; `c:num->real^N`; `r:num->real`;
                          `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`] THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2CM_CTX_LCK THEN
    MAP_EVERY EXISTS_TAC [`V:real^N->bool`;
                          `FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`;
                          `ee:num->real`; `c:num->real^N`; `r:num->real`;
                          `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`] THEN
    ASM_REWRITE_TAC[]]);;

(* Under the hypotheses of the local limit theorem, a subsequence has a      *)
(* local limit in the sense of p2gf_lim.                                     *)

let P2GF_LIM_EXISTS = prove
 (`!V a b (Gs:num->real->real^N->real^N^N).
     open V /\ a < b /\ p2ca_seqhyp V a b Gs
     ==> ?sub G. (!m n. m < n ==> sub m < sub n) /\ p2gf_lim V a b (\n. Gs (sub n)) G`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `a:real`; `b:real`; `Gs:num->real->real^N->real^N^N`]
                P2CB_CTX_SEQHYP) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`;
                       `ee:num->real`; `c:num->real^N`; `r:num->real`; `sub:num->num`;
                       `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`] THEN
  DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`sub:num->num`; `p2cm_lim (Gs:num->real->real^N->real^N^N) sub`] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `p2cm_ctx V a b (Gs:num->real->real^N->real^N^N) FF ee c r sub H` THEN
    REWRITE_TAC[p2cm_ctx] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2ca_loclim V a b (\n. (Gs:num->real->real^N->real^N^N) (sub n))
                            (p2cm_lim Gs sub)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2GF_CTX_LOCLIM THEN
    MAP_EVERY EXISTS_TAC [`FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`;
                          `ee:num->real`; `c:num->real^N`; `r:num->real`;
                          `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p2gf_lim] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[p2gf_mov] THEN
    MAP_EVERY X_GEN_TAC [`ts:num->real`; `t0:real`; `ns:num->num`; `y0:real^N`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `?i. &0 < (r:num->real) i /\ (y0:real^N) IN ball((c:num->real^N) i,r i)`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `p2cm_ctx V a b (Gs:num->real->real^N->real^N^N) FF ee c r sub H` THEN
      REWRITE_TAC[p2cm_ctx] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`V:real^N->bool`; `a:real`; `b:real`; `Gs:num->real->real^N->real^N^N`;
                   `FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`;
                   `ee:num->real`; `c:num->real^N`; `r:num->real`; `sub:num->num`;
                   `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`; `i:num`;
                   `ts:num->real`; `t0:real`; `ns:num->num`; `y0:real^N`] P2CM_CTX_NEAR_SEQ) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC P2CD_UPTO_TOP_CTX THEN
  SUBGOAL_THEN `open (V:real^N->bool)` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `p2ca_loclim V a b (\n. (Gs:num->real->real^N->real^N^N) (sub n))
                             (p2cm_lim Gs sub)` THEN
    REWRITE_TAC[p2ca_loclim; lricci_flow] THEN SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `y0:real^N` THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`V:real^N->bool`; `Gs:num->real->real^N->real^N^N`;
                        `FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`;
                        `ee:num->real`; `c:num->real^N`; `r:num->real`; `sub:num->num`;
                        `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`] THEN
  ASM_REWRITE_TAC[SUBSET_REFL]);;

(* Local limits pass to sequences that eventually re-index the given one by *)
(* indices j' >= j (tails and subsequences).                                 *)

let P2GF_LIM_TAIL = prove
 (`!V a b (Gs:num->real->real^N->real^N^N) G (f:num->num) (g:num->num) (N:num).
     p2gf_lim V a b (\n. Gs (f n)) G /\ (!j. N <= j ==> ?j'. j <= j' /\ g j = f j')
     ==> p2gf_lim V a b (\n. Gs (g n)) G`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2gf_lim] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "mov") ASSUME_TAC))
    (LABEL_TAC "tl")) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2CA_LOCLIM_TAIL THEN MAP_EVERY EXISTS_TAC [`f:num->num`; `N:num`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "tl" (X_CHOOSE_TAC `jj:num->num` o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  REWRITE_TAC[p2gf_mov] THEN
  MAP_EVERY X_GEN_TAC [`ts:num->real`; `t0:real`; `ns:num->num`; `y0:real^N`] THEN
  STRIP_TAC THEN
  USE_THEN "mov" (MP_TAC o SPECL
    [`ts:num->real`; `t0:real`;
     `\j. if N <= (ns:num->num) j then (jj:num->num) (ns j) else j`; `y0:real^N`] o
    REWRITE_RULE[p2gf_mov]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN COND_CASES_TAC THEN REWRITE_TAC[LE_REFL] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `(ns:num->num) j` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o BETA_RULE) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2CI_NEAR_EQ THEN
  MAP_EVERY EXISTS_TAC
   [`\j. (vectorize:real^N^N->real^(N,N)finite_prod) o
         (Gs:num->real->real^N->real^N^N) ((f:num->num)
           (if N <= (ns:num->num) j then (jj:num->num) (ns j) else j)) ((ts:num->real) j)`;
    `(vectorize:real^N^N->real^(N,N)finite_prod) o (G:real->real^N->real^N^N) t0`;
    `&1`; `N:num`] THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `z:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `N <= (ns:num->num) n` ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[o_THM] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(ns:num->num) n` o check (fun th ->
    can (find_term ((=) `jj:num->num`)) (concl th) && is_forall (concl th))) THEN
  ASM_SIMP_TAC[]);;

(* The dichotomy predicate. *)

let p2gf_fdich = new_definition
 `p2gf_fdich (adm:num->num->bool) (V:num->real^N->bool) (a:num->real) (b:num->real)
             (H:num->num->real->real^N->real^N^N) d (r:num->num) <=>
    ((?N. !n. N <= n ==> adm d (r n)) /\
     ?G. p2gf_lim (V d) (a d) (b d) (\n. H d (r n)) G) \/
    (?N. !n. N <= n ==> ~adm d (r n))`;;

let P2GF_DICH_TAIL = prove
 (`!(adm:num->num->bool) (V:num->real^N->bool) a b H d (k1:num->num) (k2:num->num) M.
     p2gf_fdich adm V a b H d k1 /\ (!j. M <= j ==> ?j'. j <= j' /\ k2 j = k1 j')
     ==> p2gf_fdich adm V a b H d k2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2gf_fdich] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "tl")) THEN
  STRIP_TAC THENL
   [DISJ1_TAC THEN CONJ_TAC THENL
     [EXISTS_TAC `M + N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      USE_THEN "tl" (MP_TAC o SPEC `n:num`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `j':num` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      EXISTS_TAC `G:real->real^N->real^N^N` THEN
      MP_TAC(ISPECL [`(V:num->real^N->bool) d`; `(a:num->real) d`; `(b:num->real) d`;
                     `(H:num->num->real->real^N->real^N^N) d`;
                     `G:real->real^N->real^N^N`; `k1:num->num`; `k2:num->num`; `M:num`]
                    P2GF_LIM_TAIL) THEN
      ASM_REWRITE_TAC[ETA_AX]];
    DISJ2_TAC THEN EXISTS_TAC `M + N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "tl" (MP_TAC o SPEC `n:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `j':num` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

(* Further subsequences keep the dichotomy. *)

let P2GF_DICH_SUBSEQ = prove
 (`!(adm:num->num->bool) (V:num->real^N->bool) a b H d (t:num->num) (s:num->num).
     p2gf_fdich adm V a b H d t /\ (!m n. m < n ==> s m < s n)
     ==> p2gf_fdich adm V a b H d (\n. t (s n))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC P2GF_DICH_TAIL THEN
  MAP_EVERY EXISTS_TAC [`t:num->num`; `0`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN EXISTS_TAC `(s:num->num) j` THEN
  REWRITE_TAC[] THEN MP_TAC(SPEC `s:num->num` MONOTONE_BIGGER) THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[]);;

let P2GF_DICHOTOMY = prove
 (`!(adm:num->num->bool) (V:num->real^N->bool) (a:num->real) (b:num->real)
    (H:num->num->real->real^N->real^N^N).
     (!d. (?n. adm d n) ==> open(V d) /\ a d < b d) /\
     (!d r. (!n. adm d (r n)) ==> p2ca_seqhyp (V d) (a d) (b d) (\n. H d (r n)))
     ==> ?t. (!m n. m < n ==> t m < t n) /\ !d. p2gf_fdich adm V a b H d t`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "op") (LABEL_TAC "sh")) THEN
  SUBGOAL_THEN
   `!d (r:num->num). ?k. (!m n. m < n ==> k m < k n) /\
                         p2gf_fdich (adm:num->num->bool) (V:num->real^N->bool) a b
                                    (H:num->num->real->real^N->real^N^N) d (r o k)`
  (LABEL_TAC "ex") THENL
   [MAP_EVERY X_GEN_TAC [`d:num`; `r:num->num`] THEN
    ASM_CASES_TAC `INFINITE {n | (adm:num->num->bool) d ((r:num->num) n)}` THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP INFINITE_ENUMERATE) THEN
      DISCH_THEN(X_CHOOSE_THEN `k1:num->num` (CONJUNCTS_THEN2 (LABEL_TAC "k1") (LABEL_TAC "im"))) THEN
      SUBGOAL_THEN `!n. (adm:num->num->bool) d ((r:num->num) ((k1:num->num) n))`
      (LABEL_TAC "ad") THENL
       [GEN_TAC THEN
        SUBGOAL_THEN `(k1:num->num) n IN {n | (adm:num->num->bool) d ((r:num->num) n)}`
        MP_TAC THENL
         [USE_THEN "im" (SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN MESON_TAC[];
          REWRITE_TAC[IN_ELIM_THM]];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`(V:num->real^N->bool) d`; `(a:num->real) d`; `(b:num->real) d`;
                     `\n. (H:num->num->real->real^N->real^N^N) d ((r:num->num) ((k1:num->num) n))`]
                    P2GF_LIM_EXISTS) THEN
      ANTS_TAC THENL
       [USE_THEN "op" (MP_TAC o SPEC `d:num`) THEN ANTS_TAC THENL
         [EXISTS_TAC `(r:num->num) ((k1:num->num) 0)` THEN USE_THEN "ad" (fun th -> REWRITE_TAC[th]);
          STRIP_TAC] THEN
        ASM_REWRITE_TAC[] THEN
        USE_THEN "sh" (MP_TAC o SPECL [`d:num`; `\n. (r:num->num) ((k1:num->num) n)`]) THEN
        REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN USE_THEN "ad" ACCEPT_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `k2:num->num` (X_CHOOSE_THEN `G:real->real^N->real^N^N`
        (CONJUNCTS_THEN2 (LABEL_TAC "k2") (LABEL_TAC "lim")))) THEN
      EXISTS_TAC `\n. (k1:num->num) ((k2:num->num) n)` THEN CONJ_TAC THENL
       [MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
        USE_THEN "k1" MATCH_MP_TAC THEN USE_THEN "k2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[p2gf_fdich; o_THM] THEN DISJ1_TAC THEN CONJ_TAC THENL
       [EXISTS_TAC `0` THEN GEN_TAC THEN DISCH_TAC THEN USE_THEN "ad" (fun th -> REWRITE_TAC[th]);
        EXISTS_TAC `G:real->real^N->real^N^N` THEN USE_THEN "lim" ACCEPT_TAC];
      ALL_TAC] THEN
    EXISTS_TAC `\n:num. n` THEN REWRITE_TAC[o_DEF; ETA_AX] THEN
    REWRITE_TAC[p2gf_fdich] THEN DISJ2_TAC THEN
    UNDISCH_TAC `~INFINITE {n | (adm:num->num->bool) d ((r:num->num) n)}` THEN
    REWRITE_TAC[INFINITE; num_FINITE; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "bd")) THEN EXISTS_TAC `N + 1` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "bd" (MP_TAC o SPEC `n:num`) THEN
    UNDISCH_TAC `N + 1 <= n` THEN MESON_TAC[ARITH_RULE `N + 1 <= n ==> ~(n <= N)`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!d (r:num->num) k1 k2 M.
      p2gf_fdich (adm:num->num->bool) (V:num->real^N->bool) a b
                 (H:num->num->real->real^N->real^N^N) d (r o k1) /\
      (!j. M <= j ==> ?j'. j <= j' /\ k2 j = k1 j')
      ==> p2gf_fdich adm V a b H d (r o k2)`
  (LABEL_TAC "tl") THENL
   [MAP_EVERY X_GEN_TAC [`d:num`; `r:num->num`; `k1:num->num`; `k2:num->num`; `M:num`] THEN
    STRIP_TAC THEN MATCH_MP_TAC P2GF_DICH_TAIL THEN
    MAP_EVERY EXISTS_TAC [`(r:num->num) o (k1:num->num)`; `M:num`] THEN
    ASM_REWRITE_TAC[o_THM] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
      can (find_term (fun t -> t = `k2:num->num`)) (concl th) && is_forall (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `p2gf_fdich (adm:num->num->bool) (V:num->real^N->bool) (a:num->real)
                           (b:num->real) (H:num->num->real->real^N->real^N^N)`
               SUBSEQUENCE_DIAGONALIZATION_LEMMA) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [USE_THEN "ex" ACCEPT_TAC; USE_THEN "tl" ACCEPT_TAC]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `\n:num. n`) THEN REWRITE_TAC[o_DEF; ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* Flow candidates.  A candidate d encodes a CG chart, a radius              *)
(* index, a dyadic scale and two numerators (the persistence start a0 < the *)
(* limit start b < 0) and a curvature bound.  It is admissible at the CG     *)
(* index k if the normal ball of the CG chart in V (sq k) persists over      *)
(* (a0,0] with abs Rm <= K (p2cd_ok); along admissible indices the normal    *)
(* pullbacks satisfy the uniform bounds (P2CD_SEQHYP_GEN), so the dichotomy  *)
(* diagonal applies.                                                          *)
(* ------------------------------------------------------------------------- *)

let p2gf_ch = new_definition `p2gf_ch d = NUMFST d`;;
let p2gf_ri = new_definition `p2gf_ri d = NUMFST(NUMSND d)`;;
let p2gf_e = new_definition `p2gf_e d = NUMFST(NUMSND(NUMSND d))`;;
let p2gf_m1 = new_definition `p2gf_m1 d = NUMFST(NUMSND(NUMSND(NUMSND d)))`;;
let p2gf_m2 = new_definition `p2gf_m2 d = NUMFST(NUMSND(NUMSND(NUMSND(NUMSND d))))`;;
let p2gf_kb = new_definition `p2gf_kb d = NUMSND(NUMSND(NUMSND(NUMSND(NUMSND d))))`;;

let p2gf_r0 = new_definition
 `p2gf_r0 (rho:num->real) d = rho(NUMFST(p2gf_ch d)) / &2 pow (p2gf_ri d)`;;

let p2gf_a0 = new_definition
 `p2gf_a0 d = --(&(p2gf_m1 d) / &2 pow (p2gf_e d))`;;

let p2gf_bt = new_definition
 `p2gf_bt d = --(&(p2gf_m2 d) / &2 pow (p2gf_e d))`;;

let p2gf_K = new_definition `p2gf_K d = &(p2gf_kb d)`;;

let p2gf_valid = new_definition
 `p2gf_valid (CG:real->real) (rho:num->real) d <=>
    1 <= p2gf_ri d /\ 0 < p2gf_m2 d /\ p2gf_m2 d < p2gf_m1 d /\
    CG (p2gf_K d) * p2gf_r0 rho d pow 2 <= &1 /\ p2gf_K d * p2gf_r0 rho d pow 2 <= &1`;;

let p2gf_adm = new_definition
 `p2gf_adm (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                 (real->A->real^3^3))
           (sq:num->num) (yc:num->num->num->A) (rho:num->real) (CG:real->real) d k <=>
    p2gf_valid CG rho d /\
    p2cd_ok (V (sq k)) (p2cg_ctr yc (sq k) (p2gf_ch d))
            (p2cg_frm (\k. rfs_vmetric (V k) (&0)) yc (sq k) (p2gf_ch d))
            (p2gf_r0 rho d) (p2gf_r0 rho d) (p2gf_a0 d) (p2gf_K d)`;;

let p2gf_H = new_definition
 `p2gf_H (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
               (real->A->real^3^3))
         (sq:num->num) (yc:num->num->num->A) d k =
    p2cv_pb (V (sq k)) (&0) (&1) (open_set_atlas (:real^3))
            (p2cd_phi (V (sq k)) (p2cg_ctr yc (sq k) (p2gf_ch d))
                      (p2cg_frm (\k. rfs_vmetric (V k) (&0)) yc (sq k) (p2gf_ch d)))`;;

let p2gf_dom = new_definition
 `p2gf_dom (rho:num->real) d = ball(vec 0:real^3,p2gf_r0 rho d / &2)`;;

(* The gauge constants of P2CD_SEQHYP_GEN as a function of the bound. *)

let p2gf_gauge = new_definition
 `p2gf_gauge (u:A->bool) (CG:real->real) <=>
    !K. &0 <= K
        ==> &0 < CG K /\
            !(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) x E r0 r1 a0 b.
               &0 < r0 /\ a0 < b /\ b < &0 /\ CG K * r0 pow 2 <= &1 /\
               (!n. p2cd_ok (V n) (x n) (E n) r0 r1 a0 K)
               ==> p2ca_seqhyp (ball(vec 0,r0 / &2)) b (&0)
                     (\n. p2cv_pb (V n) (&0) (&1) (open_set_atlas (:real^3))
                                  (p2cd_phi (V n) (x n) (E n)))`;;

let P2GF_GAUGE_EXISTS = prove
 (`!u:A->bool. ?CG. p2gf_gauge u CG`,
  GEN_TAC THEN REWRITE_TAC[p2gf_gauge; GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
  X_GEN_TAC `K:real` THEN DISCH_TAC THEN
  MP_TAC(SPEC `K:real` (INST_TYPE [`:A`,`:A`] P2CD_SEQHYP_GEN)) THEN ASM_REWRITE_TAC[]);;

let P2GF_BT_NEG = prove
 (`!CG (rho:num->real) d. p2gf_valid CG rho d ==> p2gf_a0 d < p2gf_bt d /\ p2gf_bt d < &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2gf_valid; p2gf_a0; p2gf_bt] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &2 pow (p2gf_e d)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_NEG2; REAL_LT_DIV2_EQ; REAL_NEG_LT0; REAL_LT_DIV; REAL_OF_NUM_LT]);;

let P2GF_SEQHYP = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    sq yc rho CG d (r:num->num).
     p2gf_gauge (:A) CG /\ (!n. p2gf_adm V sq yc rho CG d (r n))
     ==> p2ca_seqhyp (p2gf_dom rho d) (p2gf_bt d) (&0) (\n. p2gf_H V sq yc d (r n))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2gf_adm; p2gf_gauge] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "g") ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `0`) THEN
  MP_TAC(SPECL [`CG:real->real`; `rho:num->real`; `d:num`] P2GF_BT_NEG) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "g" (MP_TAC o SPEC `p2gf_K d`) THEN
  ANTS_TAC THENL [REWRITE_TAC[p2gf_K; REAL_POS]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
           (real->A->real^3^3)) ((sq:num->num) ((r:num->num) n))`;
    `\n. p2cg_ctr (yc:num->num->num->A) ((sq:num->num) ((r:num->num) n)) (p2gf_ch d)`;
    `\n. p2cg_frm (\k. rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                      (real->A->real^3^3)) k) (&0))
                  (yc:num->num->num->A) ((sq:num->num) ((r:num->num) n)) (p2gf_ch d)`;
    `p2gf_r0 (rho:num->real) d`; `p2gf_r0 (rho:num->real) d`; `p2gf_a0 d`; `p2gf_bt d`]) THEN
  REWRITE_TAC[p2gf_dom; p2gf_H] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2cd_ok")) (concl th))) THEN
    REWRITE_TAC[p2cd_ok] THEN SIMP_TAC[];
    UNDISCH_TAC `p2gf_valid CG (rho:num->real) d` THEN REWRITE_TAC[p2gf_valid] THEN SIMP_TAC[]]);;

(* The flow subsequence: every candidate is eventually inadmissible or      *)
(* eventually admissible with a local limit flow.                           *)

let P2GF_FLOW_SUB = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    sq yc rho CG.
     p2gf_gauge (:A) CG
     ==> ?t. (!m n. m < n ==> t m < t n) /\
             !d. p2gf_fdich (p2gf_adm V sq yc rho CG) (p2gf_dom rho) p2gf_bt (\d. &0)
                           (p2gf_H V sq yc) d t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2GF_DICHOTOMY THEN CONJ_TAC THENL
   [X_GEN_TAC `d:num` THEN REWRITE_TAC[p2gf_adm] THEN STRIP_TAC THEN
    REWRITE_TAC[p2gf_dom; OPEN_BALL] THEN
    MP_TAC(SPECL [`CG:real->real`; `rho:num->real`; `d:num`] P2GF_BT_NEG) THEN
    ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC P2GF_SEQHYP THEN
    EXISTS_TAC `CG:real->real` THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The local limit in a CG chart along the flow subsequence:                  *)
(* the componentwise limit of the normal pullbacks of the time-s metrics.    *)
(* For a candidate that is eventually admissible with a local limit flow G,  *)
(* this chart limit is G on its domain and time interval.                    *)
(* ------------------------------------------------------------------------- *)

let p2gf_HC = new_definition
 `p2gf_HC (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                (real->A->real^3^3))
          (sq:num->num) (yc:num->num->num->A) a k =
    p2cv_pb (V (sq k)) (&0) (&1) (open_set_atlas (:real^3))
            (p2cd_phi (V (sq k)) (p2cg_ctr yc (sq k) a)
                      (p2cg_frm (\k. rfs_vmetric (V k) (&0)) yc (sq k) a))`;;

let P2GF_H_HC = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    sq yc d k. p2gf_H V sq yc d k = p2gf_HC V sq yc (p2gf_ch d) k`,
  REWRITE_TAC[p2gf_H; p2gf_HC]);;

let p2gf_GG = new_definition
 `p2gf_GG (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                (real->A->real^3^3))
          (sq:num->num) (yc:num->num->num->A) (t:num->num) a s (w:real^3) =
    (lambda p q. reallim sequentially (\n. p2gf_HC V sq yc a (t n) s w$p$q)):real^3^3`;;

let P2GF_REALLIM_EQ = prove
 (`!(f:num->real) l. (f ---> l) sequentially ==> reallim sequentially f = l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[reallim] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `l':real` THEN EQ_TAC THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
  EXISTS_TAC `f:num->real` THEN ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY]);;

let P2GF_GG_EQ = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    sq yc rho t d (G:real->real^3->real^3^3) s w.
     p2ca_loclim (p2gf_dom rho d) (p2gf_bt d) (&0) (\n. p2gf_H V sq yc d (t n)) G /\
     p2gf_bt d <= s /\ s <= &0 /\ w IN p2gf_dom rho d
     ==> p2gf_GG V sq yc t (p2gf_ch d) s w = G s w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2ca_loclim; P2GF_H_HC] THEN STRIP_TAC THEN
  REWRITE_TAC[p2gf_GG] THEN SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN
  X_GEN_TAC `p:num` THEN STRIP_TAC THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC P2GF_REALLIM_EQ THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "sequentially")) (concl th) &&
    not (can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th)))) THEN
  ASM_REWRITE_TAC[DIMINDEX_3] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The context of the flow part.  The CG data of lcgk (levels,               *)
(* glued limit M = p2cl_top (p2cg_dm rho) kp), the flow subsequence t with   *)
(* the dichotomy for every candidate, and the final diagonal r with the     *)
(* near-identity property Q3 (p2gk_near3) of the maps phi k at the indices   *)
(* sq (t (r k)).  The region Omega s of the limit flow: the pieces           *)
(* kp_a(dom d) of the eventually admissible candidates d with chart a, radius *)
(* index at least 3 (so that dom d = ball(0,r0/2) lies well inside the        *)
(* near-identity balls ball(0,rho/7) of p2gk_near3) and limit start b_d < s.  *)
(* ------------------------------------------------------------------------- *)

let p2gf_fctx = new_definition
 `p2gf_fctx (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                  (real->A->real^3^3))
            (U:num->A->bool) (z:num->A) (rho:num->real) (K:num->real) (N0:num->num)
            (B:num->num->real) (P:num->num) (yc:num->num->num->A) (sq:num->num)
            (D:num#num->real^(3,3)finite_sum->real^1) (Gl:num->real^3->real^3^3)
            (kp:num->real^3->real^3) (CG:real->real) (t:num->num) (r:num->num) <=>
    p2ga_hyp V U z /\
    p2ge_ctx (\k. rfs_vtop (V k) (&0)) (\k. rfs_vatlas (V k) (&0)) (\k. rfs_vmetric (V k) (&0))
             z rho K N0 B (\j m. N0 j) P N0 yc sq D Gl kp /\
    (!j k s. N0 j <= k /\ N0 (SUC j) <= k
             ==> mfd_ball (rfs_vtop (V k) (&0),rfs_vatlas (V k) (&0)) (rfs_vmetric (V k) (&0))
                          (yc j k s) (rho j) SUBSET
                 {p | ?i. i < P (SUC j) /\
                          p IN mfd_ball (rfs_vtop (V k) (&0),rfs_vatlas (V k) (&0))
                                        (rfs_vmetric (V k) (&0)) (yc (SUC j) k i)
                                        (rho (SUC j) / &32)}) /\
    (!e. &0 < e ==> ?j0. !j. j0 <= j ==> rho j < e) /\
    p2gf_gauge (:A) CG /\
    (!m n. m < n ==> t m < t n) /\
    (!d. p2gf_fdich (p2gf_adm V sq yc rho CG) (p2gf_dom rho) p2gf_bt (\d. &0)
                    (p2gf_H V sq yc) d t) /\
    (!m n. m < n ==> r m < r n) /\
    (!k. p2gk_near3 (\k. rfs_vtop (V k) (&0)) (\k. rfs_vatlas (V k) (&0))
                    (\k. rfs_vmetric (V k) (&0)) yc rho P kp k (sq (t (r k)))
                    (p2ce_F (\k. rfs_vtop (V k) (&0)) (\k. rfs_vatlas (V k) (&0))
                            (\k. rfs_vmetric (V k) (&0)) yc rho kp (p2ce_cs P k) (sq (t (r k)))
                            (P(k + 2))))`;;

let p2gf_fstd = [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`;
                 `U:num->A->bool`; `z:num->A`; `rho:num->real`; `K:num->real`;
                 `N0:num->num`; `B:num->num->real`; `P:num->num`; `yc:num->num->num->A`;
                 `sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                 `Gl:num->real^3->real^3^3`; `kp:num->real^3->real^3`; `CG:real->real`;
                 `t:num->num`; `r:num->num`];;

(* The maps of the final diagonal. *)

let p2gf_phi = new_definition
 `p2gf_phi (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                 (real->A->real^3^3))
           (yc:num->num->num->A) (rho:num->real) (P:num->num) (kp:num->real^3->real^3)
           (sq:num->num) (t:num->num) (r:num->num) k =
    p2ce_F (\k. rfs_vtop (V k) (&0)) (\k. rfs_vatlas (V k) (&0)) (\k. rfs_vmetric (V k) (&0))
           yc rho kp (p2ce_cs P k) (sq (t (r k))) (P(k + 2))`;;

(* The candidates allowed in the region. *)

let p2gf_okp = new_definition
 `p2gf_okp (P:num->num) d <=>
    3 <= p2gf_ri d /\ ?i s. p2gf_ch d = NUMPAIR i s /\ s < P i`;;

let p2gf_reg = new_definition
 `p2gf_reg (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                (real->A->real^3^3))
          (sq:num->num) (yc:num->num->num->A) (rho:num->real) (CG:real->real) (P:num->num)
          (kp:num->real^3->real^3) (t:num->num) (s:real) =
    UNIONS {IMAGE (kp (p2gf_ch d)) (p2gf_dom rho d) | d |
            p2gf_okp P d /\ (?N. !n. N <= n ==> p2gf_adm V sq yc rho CG d (t n)) /\
            p2gf_bt d < s}`;;

(* Basic facts of the context. *)

let P2GF_FCTX_FACTS = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z rho K N0 B P yc sq D Gl kp CG t r.
     p2gf_fctx V U z rho K N0 B P yc sq D Gl kp CG t r
     ==> p2ge_ctx (\k. rfs_vtop (V k) (&0)) (\k. rfs_vatlas (V k) (&0))
                  (\k. rfs_vmetric (V k) (&0)) z rho K N0 B (\j m. N0 j) P N0 yc sq D Gl kp /\
         p2gb_seq (\k. rfs_vtop (V k) (&0)) (\k. rfs_vatlas (V k) (&0))
                  (\k. rfs_vmetric (V k) (&0)) z /\
         p2gb_levels (\k. rfs_vtop (V k) (&0)) (\k. rfs_vatlas (V k) (&0))
                     (\k. rfs_vmetric (V k) (&0)) z rho K N0 B (\j m. N0 j) P N0 yc /\
         p2cg_limit (\k. rfs_vtop (V k) (&0)) (\k. rfs_vatlas (V k) (&0))
                    (\k. rfs_vmetric (V k) (&0)) yc rho sq D Gl /\
         p2cl_glue (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D) kp /\
         p2cl_system (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D) /\
         (!n. p2c_regular_view (V n)) /\
         (!j. &0 < rho j) /\
         (!m n. m < n ==> sq m < sq n) /\ (!n. n <= sq n) /\
         (!m n. m < n ==> t m < t n) /\ (!n. n <= t n) /\
         (!m n. m < n ==> r m < r n) /\ (!n. n <= r n) /\
         (!k. k <= sq (t (r k)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2gf_fctx] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GE_CTX_FACTS) THEN
  SUBGOAL_THEN `!m n. m < n ==> (sq:num->num) m < sq n` ASSUME_TAC THENL
   [FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [p2cg_dsys] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2cg_dsys")) (concl th) &&
      not (is_forall (concl th))));
    ALL_TAC] THEN
  SUBGOAL_THEN `(!n. n <= (t:num->num) n) /\ (!n. n <= (r:num->num) n)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MONOTONE_BIGGER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `p2ga_hyp (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)) U z` THEN
    REWRITE_TAC[p2ga_hyp] THEN SIMP_TAC[];
    X_GEN_TAC `j:num` THEN
    MP_TAC(ISPECL [`\k. rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                     (real->A->real^3^3)) k) (&0)`;
                   `\k. rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                       (real->A->real^3^3)) k) (&0)`;
                   `\k. rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                        (real->A->real^3^3)) k) (&0)`;
                   `z:num->A`; `rho:num->real`; `K:num->real`; `N0:num->num`;
                   `B:num->num->real`; `\j:num m:num. (N0:num->num) j`; `P:num->num`;
                   `N0:num->num`; `yc:num->num->num->A`; `j:num`] P2GB_RHO_POS) THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `k:num` THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `(r:num->num) k` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `(t:num->num) ((r:num->num) k)` THEN ASM_REWRITE_TAC[]]);;

(* The region is open and increases with the time. *)

let P2GF_OM_MONO = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    sq yc rho CG P kp t s s'.
     s <= s' ==> p2gf_reg V sq yc rho CG P kp t s SUBSET p2gf_reg V sq yc rho CG P kp t s'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2gf_reg] THEN MATCH_MP_TAC SUBSET_UNIONS THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `X:real^3->bool` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:num` THEN
  ASM_MESON_TAC[REAL_LTE_TRANS]);;

let P2GF_OM_OPEN = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z rho K N0 B P yc sq D Gl kp CG t r s.
     p2gf_fctx V U z rho K N0 B P yc sq D Gl kp CG t r
     ==> open_in (p2cl_top (p2cg_dm rho) kp) (p2gf_reg V sq yc rho CG P kp t s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GF_FCTX_FACTS) THEN
  REWRITE_TAC[p2gf_reg] THEN MATCH_MP_TAC OPEN_IN_UNIONS THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC P2CL_OPEN_IMAGE THEN
  MAP_EVERY EXISTS_TAC [`p2cg_om (rho:num->real) (D:num#num->real^(3,3)finite_sum->real^1)`;
                        `p2cg_tr (rho:num->real) (D:num#num->real^(3,3)finite_sum->real^1)`] THEN
  ASM_REWRITE_TAC[p2gf_dom; OPEN_BALL; p2cg_dm] THEN
  MATCH_MP_TAC SUBSET_BALL THEN REWRITE_TAC[p2gf_r0] THEN
  SUBGOAL_THEN `&0 < (rho:num->real) (NUMFST(p2gf_ch d))` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&8 <= &2 pow (p2gf_ri d)` MP_TAC THENL
   [UNDISCH_TAC `p2gf_okp (P:num->num) d` THEN REWRITE_TAC[p2gf_okp] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 pow 3` THEN CONJ_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV; MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SPEC_TAC(`&2 pow (p2gf_ri d)`,`q:real`) THEN
  SPEC_TAC(`(rho:num->real) (NUMFST(p2gf_ch d))`,`x:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `x / q <= x / &8` MP_TAC THENL
   [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The normal charts of the candidates at admissible indices                 *)
(* (parametrizations at all times of the persistence, the time-s chain rule *)
(* of the pullbacks), the representation of the diagonal maps phi k through *)
(* the normal charts by the near-identity maps S k = L o phi k o kp (Q3),    *)
(* S k -> identity, and the convergence of the pulled back normal metrics   *)
(* along moving times (the moving property of the candidate limits).        *)
(* ------------------------------------------------------------------------- *)

let p2gf_S = new_definition
 `p2gf_S (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
               (real->A->real^3^3))
         (yc:num->num->num->A) (rho:num->real) (P:num->num) (kp:num->real^3->real^3)
         (sq:num->num) (t:num->num) (r:num->num) k a =
    \w. p2ce_L (\k. rfs_vtop (V k) (&0)) (\k. rfs_vatlas (V k) (&0))
               (\k. rfs_vmetric (V k) (&0)) yc rho (sq (t (r k))) a
               (p2gf_phi V yc rho P kp sq t r k (kp a w))`;;

let P2GF_NCH_PHI = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    (yc:num->num->num->A) k a.
     p2cg_nch (\k. rfs_vtop (V k) (&0)) (\k. rfs_vatlas (V k) (&0))
              (\k. rfs_vmetric (V k) (&0)) yc k a =
     p2cd_phi (V k) (p2cg_ctr yc k a) (p2cg_frm (\k. rfs_vmetric (V k) (&0)) yc k a)`,
  REWRITE_TAC[FUN_EQ_THM; p2cg_nch; p2cd_phi]);;

(* The normal chart of a persisting normal ball parametrizes it at every     *)
(* time of the persistence (the identity is a diffeomorphism of the slices). *)

let P2GF_OK_PARAM_S = prove
 (`!(W:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x E r0 r1 a0 K s.
     p2cd_ok W x E r0 r1 a0 K /\ a0 < s /\ s <= &0
     ==> smooth_manifold_atlas (rfs_vtop W s) (rfs_vatlas W s) /\
         mfd_param (rfs_vtop W s) (rfs_vatlas W s) (ball(vec 0,r0)) (p2cd_phi W x E)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN p2cd_ok_tac THEN
  MP_TAC(ISPECL [`W:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `x:A`; `E:real^3^3`; `r0:real`; `r1:real`; `a0:real`; `K:real`; `r0:real`]
                P2CD_OK_ONE) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; P2CD_T01] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`W:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `x:A`] P2CD_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (rfs_vtop (W:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s)
                                      (rfs_vatlas W s)` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_persists (W:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3))
                   (IMAGE (p2cd_phi W x E) (ball(vec 0,r0))) a0 (&0)` THEN
    REWRITE_TAC[P2CO_PERSISTS_ALT] THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `mfd_diffeo (rfs_vtop (W:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)) (&0)) (rfs_vatlas W (&0))
               (IMAGE (p2cd_phi W x E) (ball(vec 0,r0)))
               (rfs_vtop W s) (rfs_vatlas W s) (IMAGE (p2cd_phi W x E) (ball(vec 0,r0)))
               (\y:A. y) (\y. y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIFFEO_SYM THEN
    UNDISCH_TAC `p2c_regular_view (W:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                     (real->A->real^3^3))` THEN
    REWRITE_TAC[p2c_regular_view] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    EXISTS_TAC `a0:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MFD_PARAM_EQ THEN
  EXISTS_TAC `(\y:A. y) o p2cd_phi (W:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                      (real->A->real^3^3)) x E` THEN
  ASM_REWRITE_TAC[o_THM] THEN MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
  MAP_EVERY EXISTS_TAC
   [`rfs_vtop (W:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                (real->A->real^3^3)) (&0)`;
    `rfs_vatlas (W:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                  (real->A->real^3^3)) (&0)`;
    `IMAGE (p2cd_phi (W:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                       (real->A->real^3^3)) x E) (ball(vec 0,r0))`;
    `IMAGE (p2cd_phi (W:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                       (real->A->real^3^3)) x E) (ball(vec 0,r0))`;
    `\y:A. y`] THEN
  ASM_REWRITE_TAC[SUBSET_REFL]);;

(* The time-s chain rule for the pullbacks through the normal chart. *)

let P2GF_PB_CHAIN_S = prove
 (`!(W:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x E r0 r1 a0 K s (R:real^3->real^3) z.
     p2cd_ok W x E r0 r1 a0 K /\ a0 < s /\ s <= &0 /\
     R differentiable at z /\ R z IN ball(vec 0,r0)
     ==> rfs_pullback (rfs_vatlas W s) (p2cd_phi W x E o R) (rfs_vmetric W s) z =
         mpullback R (p2cv_pb W (&0) (&1) (open_set_atlas (:real^3)) (p2cd_phi W x E) s) z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`W:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `x:A`; `E:real^3^3`; `r0:real`; `r1:real`; `a0:real`; `K:real`; `s:real`]
                P2GF_OK_PARAM_S) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REWRITE_TAC[P2CD_PB_RFS_FUN] THEN
  MATCH_MP_TAC P2CE_RFS_CHAIN THEN
  MAP_EVERY EXISTS_TAC [`rfs_vtop (W:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) s`; `ball(vec 0:real^3,r0)`] THEN
  ASM_REWRITE_TAC[]);;

(* Q3 at level k: the diagonal map on a chart piece of radius rho/6 goes     *)
(* through the normal chart, by the map S k (smooth there).                  *)

let P2GF_S_REP = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z rho K N0 B P yc sq D Gl kp CG t r k i s w.
     p2gf_fctx V U z rho K N0 B P yc sq D Gl kp CG t r /\
     i <= SUC k /\ s < P i /\ p2cg_nv N0 N0 (NUMPAIR i s) <= sq (t (r k)) /\
     w IN ball(vec 0,rho i / &6)
     ==> p2gf_S V yc rho P kp sq t r k (NUMPAIR i s) w IN ball(vec 0,rho i) /\
         p2gf_phi V yc rho P kp sq t r k (kp (NUMPAIR i s) w) =
         p2cg_nch (\k. rfs_vtop (V k) (&0)) (\k. rfs_vatlas (V k) (&0))
                  (\k. rfs_vmetric (V k) (&0)) yc (sq (t (r k))) (NUMPAIR i s)
                  (p2gf_S V yc rho P kp sq t r k (NUMPAIR i s) w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GF_FCTX_FACTS) THEN
  UNDISCH_TAC `p2gf_fctx (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) U z rho K N0 B P yc sq D Gl kp CG t r` THEN
  REWRITE_TAC[p2gf_fctx] THEN
  DISCH_THEN(MP_TAC o SPEC `k:num` o last o CONJUNCTS) THEN
  REWRITE_TAC[p2gk_near3] THEN DISCH_THEN(MP_TAC o SPECL [`i:num`; `s:num`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `w:real^3` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\k. rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                   (real->A->real^3^3)) k) (&0)`;
                 `\k. rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                     (real->A->real^3^3)) k) (&0)`;
                 `\k. rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                      (real->A->real^3^3)) k) (&0)`;
                 `z:num->A`; `rho:num->real`; `K:num->real`; `N0:num->num`;
                 `B:num->num->real`; `\j:num m:num. (N0:num->num) j`; `P:num->num`;
                 `N0:num->num`; `yc:num->num->num->A`; `NUMPAIR i s`; `(sq:num->num) ((t:num->num) ((r:num->num) k))`]
                P2GE_L_FACTS) THEN
  ASM_REWRITE_TAC[NUMPAIR_DEST] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  DISCH_THEN(MP_TAC o SPEC `p2ce_F (\k. rfs_vtop ((V:num->(real->A topology)#
                                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (&0))
                          (\k. rfs_vatlas (V k) (&0)) (\k. rfs_vmetric (V k) (&0))
                          (yc:num->num->num->A) (rho:num->real) (kp:num->real^3->real^3)
                          (p2ce_cs (P:num->num) k) ((sq:num->num) ((t:num->num) ((r:num->num) k)))
                          (P(k + 2)) (kp (NUMPAIR i s) w)`) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[p2gf_S; p2gf_phi]);;

let P2GF_S_SMOOTH = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z rho K N0 B P yc sq D Gl kp CG t r k i s.
     p2gf_fctx V U z rho K N0 B P yc sq D Gl kp CG t r /\ i <= SUC k /\ s < P i
     ==> smooth_map_on (ball(vec 0,rho i / &6)) (p2gf_S V yc rho P kp sq t r k (NUMPAIR i s))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2gf_fctx] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2gk_near3")) (concl th))) THEN
  REWRITE_TAC[p2gk_near3] THEN DISCH_THEN(MP_TAC o SPECL [`i:num`; `s:num`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
  REWRITE_TAC[p2gf_S; p2gf_phi; ETA_AX]);;

(* S k tends to the identity near every point of ball(0,rho/7), along any   *)
(* indices kk j >= j.                                                        *)

let P2GF_S_NEAR = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z rho K N0 B P yc sq D Gl kp CG t r i s (kk:num->num) w0.
     p2gf_fctx V U z rho K N0 B P yc sq D Gl kp CG t r /\ s < P i /\ (!j. j <= kk j) /\
     w0 IN ball(vec 0,rho i / &7)
     ==> p2ci_near w0 (\j. p2gf_S V yc rho P kp sq t r (kk j) (NUMPAIR i s)) (\w. w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GF_FCTX_FACTS) THEN
  SUBGOAL_THEN `&0 < (rho:num->real) i` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC P2CI_NEAR_OF_PARTIALS THEN
  EXISTS_TAC `(rho:num->real) i / &7 - norm(w0:real^3)` THEN
  SUBGOAL_THEN `!y:real^3. y IN ball(w0,(rho:num->real) i / &7 - norm w0)
                           ==> y IN cball(vec 0,rho i / &7) /\ y IN ball(vec 0,rho i / &6)`
  (LABEL_TAC "yin") THENL
   [X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_BALL; IN_CBALL_0; IN_BALL_0] THEN
    MP_TAC(ISPECL [`w0:real^3`; `y:real^3`] NORM_TRIANGLE_SUB) THEN
    UNDISCH_TAC `(w0:real^3) IN ball(vec 0,(rho:num->real) i / &7)` THEN
    REWRITE_TAC[IN_BALL_0; dist] THEN
    MP_TAC(ISPECL [`w0:real^3`; `y:real^3`] NORM_SUB) THEN
    MP_TAC(ISPECL [`y:real^3`; `w0:real^3`] NORM_TRIANGLE_SUB) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `(w0:real^3) IN ball(vec 0,(rho:num->real) i / &7)` THEN
    REWRITE_TAC[IN_BALL_0] THEN REAL_ARITH_TAC;
    EXISTS_TAC `i:num` THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:real^3,(rho:num->real) i / &6)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC P2GF_S_SMOOTH THEN
      MAP_EVERY EXISTS_TAC [`U:num->A->bool`; `z:num->A`; `K:num->real`; `N0:num->num`;
                            `B:num->num->real`; `D:num#num->real^(3,3)finite_sum->real^1`;
                            `Gl:num->real^3->real^3^3`; `CG:real->real`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(ARITH_RULE `i <= j /\ j <= k ==> i <= SUC k`) THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[SMOOTH_MAP_ON_ID];
    ALL_TAC] THEN
  X_GEN_TAC `l:num list` THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(SPEC `e:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ne:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `i + LENGTH(l:num list) + ne` THEN
  MAP_EVERY X_GEN_TAC [`j:num`; `y:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `i + LENGTH(l:num list) + ne <= (kk:num->num) j` ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `p2gf_fctx (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) U z rho K N0 B P yc sq D Gl kp CG t r` THEN
  REWRITE_TAC[p2gf_fctx] THEN
  DISCH_THEN(MP_TAC o SPEC `(kk:num->num) j` o last o CONJUNCTS) THEN
  REWRITE_TAC[p2gk_near3] THEN DISCH_THEN(MP_TAC o SPECL [`i:num`; `s:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`l:num list`; `y:real^3`] o CONJUNCT2 o CONJUNCT2) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `ALL (\j. 1 <= j /\ j <= dimindex(:3)) l` THEN REWRITE_TAC[DIMINDEX_3];
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; USE_THEN "yin" (MP_TAC o SPEC `y:real^3`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[p2gf_S; p2gf_phi] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `inv(&((kk:num->num) j) + &1)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&ne)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
  REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC);;

(* An eventually admissible candidate has a local limit (the dichotomy).     *)

let P2GF_DICH_ADM = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z rho K N0 B P yc sq D Gl kp CG t r d.
     p2gf_fctx V U z rho K N0 B P yc sq D Gl kp CG t r /\
     (?N. !n. N <= n ==> p2gf_adm V sq yc rho CG d (t n))
     ==> ?G. p2gf_lim (p2gf_dom rho d) (p2gf_bt d) (&0) (\n. p2gf_H V sq yc d (t n)) G`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2gf_fctx] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_TAC `N:num`)) THEN
  DISCH_THEN(MP_TAC o SPEC `d:num` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
             CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  REWRITE_TAC[p2gf_fdich] THEN
  DISCH_THEN(DISJ_CASES_THEN2 (fun th -> MESON_TAC[th]) (X_CHOOSE_TAC `N2:num`)) THEN
  ASM_MESON_TAC[LE_ADD; LE_ADDR]);;

(* The pulled back normal metrics converge near every point of the domain   *)
(* along converging times (moving property and S k -> identity).             *)

let P2GF_PB_NEAR = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z rho K N0 B P yc sq D Gl kp CG t r d i s G (ts:num->real) t0 (kk:num->num) y0.
     p2gf_fctx V U z rho K N0 B P yc sq D Gl kp CG t r /\
     p2gf_ch d = NUMPAIR i s /\ s < P i /\ 3 <= p2gf_ri d /\
     p2gf_lim (p2gf_dom rho d) (p2gf_bt d) (&0) (\n. p2gf_H V sq yc d (t n)) G /\
     (!j. p2gf_bt d <= ts j /\ ts j <= &0) /\ p2gf_bt d <= t0 /\ t0 <= &0 /\
     ((\j. lift(ts j)) --> lift t0) sequentially /\ (!j. j <= kk j) /\
     y0 IN p2gf_dom rho d
     ==> p2cm_mnear y0 (\j. G (ts j)) (G t0) /\
         p2ci_near y0 (\j. vectorize o mpullback (p2gf_S V yc rho P kp sq t r (kk j) (NUMPAIR i s))
                                                (p2gf_H V sq yc d (t (r (kk j))) (ts j)))
                      (vectorize o G t0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GF_FCTX_FACTS) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`ts:num->real`; `t0:real`; `\j. (r:num->num) ((kk:num->num) j)`;
                              `y0:real^3`] o GEN_REWRITE_RULE I [p2gf_mov] o CONJUNCT1 o CONJUNCT2 o
              GEN_REWRITE_RULE I [p2gf_lim] o check (fun th ->
                can (find_term (fun t -> is_const t && fst(dest_const t) = "p2gf_lim")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [X_GEN_TAC `j:num` THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `(kk:num->num) j` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`y0:real^3`;
                 `\j. p2gf_S (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) yc rho P kp sq t r ((kk:num->num) j)
                             (NUMPAIR i s)`;
                 `\w:real^3. w`;
                 `\j. p2gf_H (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) sq yc d ((t:num->num) ((r:num->num)
                                  ((kk:num->num) j))) ((ts:num->real) j)`;
                 `(G:real->real^3->real^3^3) t0`] P2CI_NEAR_MPULLBACK) THEN
  REWRITE_TAC[P2CE_MPULLBACK_ID] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2GF_S_NEAR THEN
  MAP_EVERY EXISTS_TAC [`U:num->A->bool`; `z:num->A`; `K:num->real`; `N0:num->num`;
                        `B:num->num->real`; `D:num#num->real^(3,3)finite_sum->real^1`;
                        `Gl:num->real^3->real^3^3`; `CG:real->real`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(y0:real^3) IN p2gf_dom rho d` THEN
  REWRITE_TAC[p2gf_dom; p2gf_r0; IN_BALL_0] THEN ASM_REWRITE_TAC[NUMPAIR_DEST] THEN
  SUBGOAL_THEN `&8 <= &2 pow (p2gf_ri d)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 pow 3` THEN CONJ_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV; MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (rho:num->real) i` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SPEC_TAC(`&2 pow (p2gf_ri d)`,`q:real`) THEN SPEC_TAC(`(rho:num->real) i`,`x:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `x / q <= x / &8` MP_TAC THENL
   [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Uniform local convergence of the pulled back normal metrics               *)
(* (by the near-identity maps S k) to the candidate limit, uniformly in the  *)
(* time on a compact interval [b,0] (contradiction and compactness, as in    *)
(* P2CM_CTX_LCK, with P2GF_PB_NEAR and P2CM_LCK_NEAR2).                       *)
(* ------------------------------------------------------------------------- *)

let P2GF_LCK_LOCAL = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z rho K N0 B P yc sq D Gl kp CG t r d i q G w0 b m eta.
     p2gf_fctx V U z rho K N0 B P yc sq D Gl kp CG t r /\
     p2gf_ch d = NUMPAIR i q /\ q < P i /\ 3 <= p2gf_ri d /\
     p2gf_lim (p2gf_dom rho d) (p2gf_bt d) (&0) (\n. p2gf_H V sq yc d (t n)) G /\
     p2gf_bt d <= b /\ b <= &0 /\ w0 IN p2gf_dom rho d /\ &0 < eta
     ==> ?e k1. &0 < e /\
                !k s w. k1 <= k /\ b <= s /\ s <= &0 /\ w IN ball(w0,e)
                        ==> lck_dist2 m (G s)
                              (mpullback (p2gf_S V yc rho P kp sq t r k (NUMPAIR i q))
                                         (p2gf_H V sq yc d (t (r k)) s)) w < eta`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `~(!j. ?k s w. j <= k /\ b <= s /\ s <= &0 /\ w IN ball(w0:real^3,inv(&j + &1)) /\
                  eta <= lck_dist2 m ((G:real->real^3->real^3^3) s)
                           (mpullback (p2gf_S (V:num->(real->A topology)#
                                                 (real->((A->bool)#(A->real^3))->bool)#
                                                 (real->A->real^3^3)) yc rho P kp sq t r k
                                                (NUMPAIR i q))
                                      (p2gf_H V sq yc d (t (r k)) s)) w)`
  MP_TAC THENL
   [REWRITE_TAC[SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `kk:num->num` (X_CHOOSE_THEN `ss:num->real`
      (X_CHOOSE_THEN `ww:num->real^3` (LABEL_TAC "bad")))) THEN
    SUBGOAL_THEN `compact(interval[lift b,lift(&0)])` MP_TAC THENL
     [REWRITE_TAC[COMPACT_INTERVAL]; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [compact] THEN
    DISCH_THEN(MP_TAC o SPEC `\j. lift((ss:num->real) j)`) THEN
    ANTS_TAC THENL
     [X_GEN_TAC `j:num` THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN
      USE_THEN "bad" (MP_TAC o SPEC `j:num`) THEN SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[o_DEF] THEN
    DISCH_THEN(X_CHOOSE_THEN `l0:real^1` (X_CHOOSE_THEN `phi:num->num`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "phi") (LABEL_TAC "lim"))))) THEN
    SUBGOAL_THEN `!j. j <= (phi:num->num) j` (LABEL_TAC "pbig") THENL
     [MATCH_MP_TAC MONOTONE_BIGGER THEN USE_THEN "phi" ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `b <= drop l0 /\ drop l0 <= &0` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(l0:real^1) IN interval[lift b,lift(&0)]` THEN
      REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP];
      ALL_TAC] THEN
    MP_TAC(ISPECL
      [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
       `U:num->A->bool`; `z:num->A`; `rho:num->real`; `K:num->real`; `N0:num->num`;
       `B:num->num->real`; `P:num->num`; `yc:num->num->num->A`; `sq:num->num`;
       `D:num#num->real^(3,3)finite_sum->real^1`; `Gl:num->real^3->real^3^3`;
       `kp:num->real^3->real^3`; `CG:real->real`; `t:num->num`; `r:num->num`; `d:num`;
       `i:num`; `q:num`; `G:real->real^3->real^3^3`;
       `\j. (ss:num->real) ((phi:num->num) j)`; `drop l0`;
       `\j. (kk:num->num) ((phi:num->num) j)`; `w0:real^3`] P2GF_PB_NEAR) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[LIFT_DROP] THEN REPEAT CONJ_TAC THENL
       [X_GEN_TAC `j:num` THEN USE_THEN "bad" (MP_TAC o SPEC `(phi:num->num) j`) THEN
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        X_GEN_TAC `j:num` THEN MATCH_MP_TAC LE_TRANS THEN
        EXISTS_TAC `(phi:num->num) j` THEN USE_THEN "pbig" (fun th -> REWRITE_TAC[th]) THEN
        USE_THEN "bad" (MP_TAC o SPEC `(phi:num->num) j`) THEN SIMP_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> MP_TAC(MATCH_MP P2CM_LCK_NEAR2 th)) THEN
    DISCH_THEN(MP_TAC o SPEC `m:num`) THEN REWRITE_TAC[p2ci_near] THEN
    DISCH_THEN(X_CHOOSE_THEN `r1:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (MP_TAC o SPEC `eta:real` o last o CONJUNCTS))) THEN
    ASM_REWRITE_TAC[VECTOR_SUB_RZERO; NORM_LIFT] THEN
    DISCH_THEN(X_CHOOSE_THEN `J1:num` (LABEL_TAC "J1")) THEN
    MP_TAC(SPEC `r1:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `J2:num` STRIP_ASSUME_TAC) THEN
    USE_THEN "J1" (MP_TAC o SPECL [`J1 + J2:num`;
                                   `(ww:num->real^3) ((phi:num->num) (J1 + J2))`]) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[LE_ADD] THEN
      USE_THEN "bad" (MP_TAC o SPEC `(phi:num->num) (J1 + J2)`) THEN
      REWRITE_TAC[IN_BALL] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LT_TRANS THEN
      EXISTS_TAC `inv(&((phi:num->num) (J1 + J2)) + &1)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&J2)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN
      REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
      USE_THEN "pbig" (MP_TAC o SPEC `J1 + J2:num`) THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "bad" (MP_TAC o SPEC `(phi:num->num) (J1 + J2)`) THEN REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_EXISTS_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `j0:num`) THEN
  MAP_EVERY EXISTS_TAC [`inv(&j0 + &1)`; `j0:num`] THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `s:real`; `w:real^3`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `s:real`; `w:real^3`]) THEN
  ASM_REWRITE_TAC[REAL_NOT_LE]);;

(* ------------------------------------------------------------------------- *)
(* The limit metrics Gf s of the flow (the limits, in the                    *)
(* preferred charts of the glued limit, of the pullbacks of the time-s       *)
(* metrics by the diagonal maps) and their identification with the           *)
(* candidate limits: in a chart c over a candidate piece, Gf s is the       *)
(* transition pullback of the candidate limit G s (P2GF_GF_CHART); at time  *)
(* 0 the glued metric is the candidate limit as well (P2GF_G0_CHART).        *)
(* ------------------------------------------------------------------------- *)

let p2gf_Gf = new_definition
 `p2gf_Gf (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                (real->A->real^3^3))
          (sub:num->num) (phi:num->real^3->A)
          (atlas:((real^3->bool)#(real^3->real^3))->bool) (s:real) (p:real^3) =
    (matrify:real^(3,3)finite_prod->real^3^3)
      (lim sequentially
         (\k. vectorize(rfs_pullback (rfs_vatlas (V (sub k)) s)
                          (phi k o chart_inv (chart_at atlas p))
                          (rfs_vmetric (V (sub k)) s) (SND(chart_at atlas p) p))))`;;

let P2GF_LIM_MATRIFY = prove
 (`!(X:num->real^3^3) L.
     ((\k. vectorize(X k)) --> vectorize L) sequentially
     ==> matrify(lim sequentially (\k. vectorize(X k))) = L`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lim sequentially (\k. vectorize((X:num->real^3^3) k)) = vectorize L`
  SUBST1_TAC THENL
   [MATCH_MP_TAC TENDSTO_LIM THEN ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY];
    REWRITE_TAC[MATRIFY_VECTORIZE]]);;

let P2GF_NEAR_PT = prove
 (`!(z0:real^M) (Fs:num->real^M->real^N) f.
     p2ci_near z0 Fs f ==> ((\n. Fs n z0) --> f z0) sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2ci_near; LIM_SEQUENTIALLY; dist] THEN STRIP_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `&0 < e`) o SPEC `e:real`) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N1:num` THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[CENTRE_IN_BALL]);;

(* A chart point over a candidate piece: a small ball maps into the near-    *)
(* identity ball of the candidate chart.                                    *)

let P2GF_TR_BALL = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z rho K N0 B P yc sq D Gl kp CG t r d i q j y.
     p2gf_fctx V U z rho K N0 B P yc sq D Gl kp CG t r /\
     p2gf_ch d = NUMPAIR i q /\ 3 <= p2gf_ri d /\
     y IN p2cg_om rho D j (NUMPAIR i q) /\ p2cg_tr rho D j (NUMPAIR i q) y IN p2gf_dom rho d
     ==> ?e. &0 < e /\ ball(y,e) SUBSET p2cg_om rho D j (NUMPAIR i q) /\
             !y'. y' IN ball(y,e)
                  ==> p2cg_tr rho D j (NUMPAIR i q) y' IN ball(vec 0,rho i / &6)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GF_FCTX_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cl_system] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2cl_system")) (concl th))) THEN
  ABBREV_TAC `w = p2cg_tr (rho:num->real) D j (NUMPAIR i q) (y:real^3)` THEN
  SUBGOAL_THEN `norm(w:real^3) < (rho:num->real) i / &6` ASSUME_TAC THENL
   [UNDISCH_TAC `(w:real^3) IN p2gf_dom rho d` THEN
    ASM_REWRITE_TAC[p2gf_dom; p2gf_r0; IN_BALL_0; NUMPAIR_DEST] THEN
    SUBGOAL_THEN `&8 <= &2 pow (p2gf_ri d)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 pow 3` THEN CONJ_TAC THENL
       [CONV_TAC REAL_RAT_REDUCE_CONV; MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (rho:num->real) i` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SPEC_TAC(`&2 pow (p2gf_ri d)`,`qq:real`) THEN SPEC_TAC(`(rho:num->real) i`,`x:real`) THEN
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `x / qq <= x / &8` MP_TAC THENL
     [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(p2cg_tr (rho:num->real) D j (NUMPAIR i q)) continuous at (y:real^3)`
  MP_TAC THENL
   [MP_TAC(ISPECL [`p2cg_tr (rho:num->real) D j (NUMPAIR i q)`;
                   `p2cg_om (rho:num->real) D j (NUMPAIR i q)`]
                  CONTINUOUS_ON_EQ_CONTINUOUS_AT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
    ANTS_TAC THENL [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_at] THEN
  DISCH_THEN(MP_TAC o SPEC `(rho:num->real) i / &6 - norm(w:real^3)`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `p2cg_om (rho:num->real) D j (NUMPAIR i q)` OPEN_CONTAINS_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min e1 e2` THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(y:real^3,e2)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC;
    X_GEN_TAC `y':real^3` THEN REWRITE_TAC[IN_BALL; IN_BALL_0] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y':real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `e1:real`)) (concl th))) THEN
    ANTS_TAC THENL [REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`w:real^3`; `p2cg_tr (rho:num->real) D j (NUMPAIR i q) (y':real^3)`]
                  NORM_TRIANGLE_SUB) THEN
    REWRITE_TAC[dist] THEN
    MP_TAC(ISPECL [`p2cg_tr (rho:num->real) D j (NUMPAIR i q) (y':real^3)`; `w:real^3`]
                  NORM_TRIANGLE_SUB) THEN
    MP_TAC(ISPECL [`p2cg_tr (rho:num->real) D j (NUMPAIR i q) (y':real^3)`; `w:real^3`]
                  NORM_SUB) THEN
    ASM_REAL_ARITH_TAC]);;

(* The near-identity bound |S k w - w| < 1/(k+1) on cball(0,rho/7) (Q3 with  *)
(* the empty multi-index).                                                   *)

let P2GF_S_C0 = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z rho K N0 B P yc sq D Gl kp CG t r k i q w.
     p2gf_fctx V U z rho K N0 B P yc sq D Gl kp CG t r /\ i <= SUC k /\ q < P i /\
     w IN cball(vec 0,rho i / &7)
     ==> norm(p2gf_S V yc rho P kp sq t r k (NUMPAIR i q) w - w) < inv(&k + &1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2gf_fctx] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2gk_near3")) (concl th))) THEN
  REWRITE_TAC[p2gk_near3] THEN DISCH_THEN(MP_TAC o SPECL [`i:num`; `q:num`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`[]:num list`; `w:real^3`] o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[ALL; LENGTH; LE_0; iterated_partial] THEN
  REWRITE_TAC[p2gf_S; p2gf_phi]);;

(* Over a candidate piece, the pullbacks of the time-s metrics by phi k in  *)
(* any chart j are the transition pullbacks of the normal pullbacks by S k, *)
(* from some k on (s in the persistence interval (a0,0]).                   *)

let P2GF_PB_REP = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z rho K N0 B P yc sq D Gl kp CG t r d i q j s.
     p2gf_fctx V U z rho K N0 B P yc sq D Gl kp CG t r /\
     p2gf_ch d = NUMPAIR i q /\ q < P i /\ 3 <= p2gf_ri d /\
     (?N. !n. N <= n ==> p2gf_adm V sq yc rho CG d (t n)) /\
     p2gf_a0 d < s /\ s <= &0
     ==> ?k0. !k y. k0 <= k /\ y IN p2cg_om rho D j (NUMPAIR i q) /\
                    p2cg_tr rho D j (NUMPAIR i q) y IN p2gf_dom rho d
                    ==> rfs_pullback (rfs_vatlas (V (sq (t (r k)))) s)
                          (p2gf_phi V yc rho P kp sq t r k o kp j)
                          (rfs_vmetric (V (sq (t (r k)))) s) y =
                        mpullback (p2gf_S V yc rho P kp sq t r k (NUMPAIR i q) o
                                   p2cg_tr rho D j (NUMPAIR i q))
                                  (p2gf_H V sq yc d (t (r k)) s) y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_THEN `N:num` (LABEL_TAC "adm"))
      STRIP_ASSUME_TAC))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GF_FCTX_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cl_system] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2cl_system")) (concl th))) THEN
  SUBGOAL_THEN `&0 < p2gf_r0 (rho:num->real) d` ASSUME_TAC THENL
   [REWRITE_TAC[p2gf_r0] THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `p2gf_r0 (rho:num->real) d / &2` REAL_ARCH_INV) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `n1:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `N + i + n1 + p2cg_nv (N0:num->num) N0 (NUMPAIR i q)` THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `y:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `N + i + n1 + p2cg_nv (N0:num->num) N0 (NUMPAIR i q) <= (r:num->num) k /\
                p2cg_nv (N0:num->num) N0 (NUMPAIR i q) <= (sq:num->num) ((t:num->num) (r k))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "adm" (MP_TAC o SPEC `(r:num->num) k`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[p2gf_adm] THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `U:num->A->bool`; `z:num->A`; `rho:num->real`; `K:num->real`; `N0:num->num`;
                 `B:num->num->real`; `P:num->num`; `yc:num->num->num->A`; `sq:num->num`;
                 `D:num#num->real^(3,3)finite_sum->real^1`; `Gl:num->real^3->real^3^3`;
                 `kp:num->real^3->real^3`; `CG:real->real`; `t:num->num`; `r:num->num`;
                 `d:num`; `i:num`; `q:num`; `j:num`; `y:real^3`] P2GF_TR_BALL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tb")))) THEN
  ABBREV_TAC `w = p2cg_tr (rho:num->real) D j (NUMPAIR i q) (y:real^3)` THEN
  SUBGOAL_THEN `(w:real^3) IN ball(vec 0,(rho:num->real) i / &6)` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN USE_THEN "tb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  (* the normal chart at the index *)
  ABBREV_TAC `nc = p2cd_phi ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) ((sq:num->num) ((t:num->num) ((r:num->num) k))))
                     (p2cg_ctr (yc:num->num->num->A) (sq (t (r k))) (NUMPAIR i q))
                     (p2cg_frm (\k. rfs_vmetric (V k) (&0)) yc (sq (t (r k))) (NUMPAIR i q))` THEN
  SUBGOAL_THEN
   `!y'. y' IN ball(y:real^3,e)
         ==> (p2gf_phi (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                          (real->A->real^3^3)) yc rho P kp sq t r k o kp j) y' =
             ((nc:real^3->A) o (p2gf_S V yc rho P kp sq t r k (NUMPAIR i q) o
                                 p2cg_tr rho D j (NUMPAIR i q))) y'`
  ASSUME_TAC THENL
   [X_GEN_TAC `y':real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(y':real^3) IN p2cg_om (rho:num->real) D j (NUMPAIR i q)` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(kp:num->real^3->real^3) j y' = kp (NUMPAIR i q)
                    (p2cg_tr (rho:num->real) D j (NUMPAIR i q) y')` SUBST1_TAC THENL
     [MP_TAC(ISPECL [`p2cg_dm (rho:num->real)`; `p2cg_om (rho:num->real) D`;
                     `p2cg_tr (rho:num->real) D`; `j:num`; `NUMPAIR i q`; `y':real^3`]
                    P2CL_TR_IN) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      UNDISCH_TAC `p2cl_glue (p2cg_dm (rho:num->real)) (p2cg_om rho D) (p2cg_tr rho D)
                             (kp:num->real^3->real^3)` THEN
      REWRITE_TAC[p2cl_glue] THEN
      DISCH_THEN(MP_TAC o SPECL [`j:num`; `NUMPAIR i q`; `y':real^3`;
                                 `p2cg_tr (rho:num->real) D j (NUMPAIR i q) y'`]) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                   `U:num->A->bool`; `z:num->A`; `rho:num->real`; `K:num->real`; `N0:num->num`;
                   `B:num->num->real`; `P:num->num`; `yc:num->num->num->A`; `sq:num->num`;
                   `D:num#num->real^(3,3)finite_sum->real^1`; `Gl:num->real^3->real^3^3`;
                   `kp:num->real^3->real^3`; `CG:real->real`; `t:num->num`; `r:num->num`;
                   `k:num`; `i:num`; `q:num`;
                   `p2cg_tr (rho:num->real) D j (NUMPAIR i q) y'`] P2GF_S_REP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "tb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN EXPAND_TAC "nc" THEN
    REWRITE_TAC[P2GF_NCH_PHI];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) ((sq:num->num) ((t:num->num) ((r:num->num) k)))) s`;
                 `p2gf_phi (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) yc rho P kp sq t r k o kp j`;
                 `(nc:real^3->A) o (p2gf_S (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                              (real->A->real^3^3)) yc rho P kp sq t r k (NUMPAIR i q) o
                                     p2cg_tr rho D j (NUMPAIR i q))`;
                 `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) ((sq:num->num) ((t:num->num) ((r:num->num) k)))) s`;
                 `ball(y:real^3,e)`; `y:real^3`] P2CE_RFS_LOCAL) THEN
  ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[p2gf_H] THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "nc" THEN
  MATCH_MP_TAC P2GF_PB_CHAIN_S THEN
  MAP_EVERY EXISTS_TAC [`p2gf_r0 (rho:num->real) d`; `p2gf_r0 (rho:num->real) d`;
                        `p2gf_a0 d`; `p2gf_K d`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `p2cg_om (rho:num->real) D j (NUMPAIR i q)` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `ball(vec 0:real^3,(rho:num->real) i / &6)` THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN MATCH_MP_TAC P2GF_S_SMOOTH THEN
      MAP_EVERY EXISTS_TAC [`U:num->A->bool`; `z:num->A`; `K:num->real`; `N0:num->num`;
                            `B:num->num->real`; `D:num#num->real^(3,3)finite_sum->real^1`;
                            `Gl:num->real^3->real^3^3`; `CG:real->real`] THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[o_THM] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `U:num->A->bool`; `z:num->A`; `rho:num->real`; `K:num->real`; `N0:num->num`;
                 `B:num->num->real`; `P:num->num`; `yc:num->num->num->A`; `sq:num->num`;
                 `D:num#num->real^(3,3)finite_sum->real^1`; `Gl:num->real^3->real^3^3`;
                 `kp:num->real^3->real^3`; `CG:real->real`; `t:num->num`; `r:num->num`;
                 `k:num`; `i:num`; `q:num`; `w:real^3`] P2GF_S_C0) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `(w:real^3) IN ball(vec 0,(rho:num->real) i / &6)` THEN
    REWRITE_TAC[IN_BALL_0; IN_CBALL_0] THEN
    UNDISCH_TAC `(w:real^3) IN p2gf_dom rho d` THEN
    ASM_REWRITE_TAC[p2gf_dom; p2gf_r0; IN_BALL_0; NUMPAIR_DEST] THEN
    SUBGOAL_THEN `&8 <= &2 pow (p2gf_ri d)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 pow 3` THEN CONJ_TAC THENL
       [CONV_TAC REAL_RAT_REDUCE_CONV; MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (rho:num->real) i` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SPEC_TAC(`&2 pow (p2gf_ri d)`,`qq:real`) THEN SPEC_TAC(`(rho:num->real) i`,`x:real`) THEN
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `x / qq <= x / &8` MP_TAC THENL
     [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC[IN_BALL_0] THEN
  UNDISCH_TAC `(w:real^3) IN p2gf_dom rho d` THEN REWRITE_TAC[p2gf_dom; IN_BALL_0] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `inv(&k + &1) <= inv(&n1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2gf_S (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) yc rho P kp sq t r k (NUMPAIR i q) w`;
                 `w:real^3`] NORM_TRIANGLE_SUB) THEN
  ASM_REAL_ARITH_TAC);;

(* The candidate domains are small: radius index at least 3. *)

let P2GF_DOM_SMALL = prove
 (`!(rho:num->real) d i q w.
     p2gf_ch d = NUMPAIR i q /\ 3 <= p2gf_ri d /\ &0 < rho i /\ w IN p2gf_dom rho d
     ==> norm w < rho i / &16`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(w:real^3) IN p2gf_dom rho d` THEN
  ASM_REWRITE_TAC[p2gf_dom; p2gf_r0; IN_BALL_0; NUMPAIR_DEST] THEN
  SUBGOAL_THEN `&8 <= &2 pow (p2gf_ri d)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 pow 3` THEN CONJ_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV; MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `&0 < (rho:num->real) i` THEN
  SPEC_TAC(`&2 pow (p2gf_ri d)`,`qq:real`) THEN SPEC_TAC(`(rho:num->real) i`,`x:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `x / qq <= x / &8` MP_TAC THENL
   [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The chart pullbacks converge to the transition pullback of the candidate *)
(* limit, at every point over the candidate piece, for s in [b_d,0].        *)

let P2GF_PB_LIM = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z rho K N0 B P yc sq D Gl kp CG t r d i q G j s y.
     p2gf_fctx V U z rho K N0 B P yc sq D Gl kp CG t r /\
     p2gf_ch d = NUMPAIR i q /\ q < P i /\ 3 <= p2gf_ri d /\
     (?N. !n. N <= n ==> p2gf_adm V sq yc rho CG d (t n)) /\
     p2gf_lim (p2gf_dom rho d) (p2gf_bt d) (&0) (\n. p2gf_H V sq yc d (t n)) G /\
     p2gf_bt d <= s /\ s <= &0 /\
     y IN p2cg_om rho D j (NUMPAIR i q) /\ p2cg_tr rho D j (NUMPAIR i q) y IN p2gf_dom rho d
     ==> ((\k. vectorize(rfs_pullback (rfs_vatlas (V (sq (t (r k)))) s)
                           (p2gf_phi V yc rho P kp sq t r k o kp j)
                           (rfs_vmetric (V (sq (t (r k)))) s) y))
          --> vectorize(mpullback (p2cg_tr rho D j (NUMPAIR i q)) (G s) y)) sequentially`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "ev") STRIP_ASSUME_TAC))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GF_FCTX_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cl_system] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2cl_system")) (concl th))) THEN
  SUBGOAL_THEN `p2gf_a0 d < s` ASSUME_TAC THENL
   [USE_THEN "ev" (X_CHOOSE_TAC `N:num`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `N:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2gf_adm")) (concl th))) THEN
    REWRITE_TAC[LE_REFL; p2gf_adm] THEN
    DISCH_THEN(MP_TAC o MATCH_MP P2GF_BT_NEG o CONJUNCT1) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `U:num->A->bool`; `z:num->A`; `rho:num->real`; `K:num->real`; `N0:num->num`;
                 `B:num->num->real`; `P:num->num`; `yc:num->num->num->A`; `sq:num->num`;
                 `D:num#num->real^(3,3)finite_sum->real^1`; `Gl:num->real^3->real^3^3`;
                 `kp:num->real^3->real^3`; `CG:real->real`; `t:num->num`; `r:num->num`;
                 `d:num`; `i:num`; `q:num`; `j:num`; `s:real`] P2GF_PB_REP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `k0:num`) THEN
  MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\k. (vectorize:real^3^3->real^(3,3)finite_prod)
                    (mpullback (p2gf_S (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                         (real->A->real^3^3)) yc rho P kp sq t r k (NUMPAIR i q) o
                                p2cg_tr rho D j (NUMPAIR i q))
                               (p2gf_H V sq yc d ((t:num->num) ((r:num->num) k)) s) y)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `k0:num` THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `U:num->A->bool`; `z:num->A`; `rho:num->real`; `K:num->real`; `N0:num->num`;
                 `B:num->num->real`; `P:num->num`; `yc:num->num->num->A`; `sq:num->num`;
                 `D:num#num->real^(3,3)finite_sum->real^1`; `Gl:num->real^3->real^3^3`;
                 `kp:num->real^3->real^3`; `CG:real->real`; `t:num->num`; `r:num->num`;
                 `d:num`; `i:num`; `q:num`; `j:num`; `y:real^3`] P2GF_TR_BALL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `w = p2cg_tr (rho:num->real) D j (NUMPAIR i q) (y:real^3)` THEN
  SUBGOAL_THEN `norm(w:real^3) < (rho:num->real) i / &16` ASSUME_TAC THENL
   [MATCH_MP_TAC P2GF_DOM_SMALL THEN MAP_EVERY EXISTS_TAC [`d:num`; `q:num`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2ci_near (y:real^3)
      (\k. p2gf_S (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)) yc rho P kp sq t r k (NUMPAIR i q) o
           p2cg_tr rho D j (NUMPAIR i q))
      (p2cg_tr (rho:num->real) D j (NUMPAIR i q))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`y:real^3`; `\k:num. p2cg_tr (rho:num->real) D j (NUMPAIR i q)`;
                   `p2cg_tr (rho:num->real) D j (NUMPAIR i q)`;
                   `\k. p2gf_S (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) yc rho P kp sq t r k (NUMPAIR i q)`;
                   `\w:real^3. w`] P2CI_NEAR_COMPOSE) THEN
    SUBGOAL_THEN `(\w:real^3. w) o p2cg_tr (rho:num->real) D j (NUMPAIR i q) =
                  p2cg_tr rho D j (NUMPAIR i q)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2CI_NEAR_CONST THEN EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `p2cg_om (rho:num->real) D j (NUMPAIR i q)` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                     `U:num->A->bool`; `z:num->A`; `rho:num->real`; `K:num->real`; `N0:num->num`;
                     `B:num->num->real`; `P:num->num`; `yc:num->num->num->A`; `sq:num->num`;
                     `D:num#num->real^(3,3)finite_sum->real^1`; `Gl:num->real^3->real^3^3`;
                     `kp:num->real^3->real^3`; `CG:real->real`; `t:num->num`; `r:num->num`;
                     `i:num`; `q:num`; `\j:num. j`; `w:real^3`] P2GF_S_NEAR) THEN
      REWRITE_TAC[LE_REFL; ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[IN_BALL_0] THEN
      SUBGOAL_THEN `&0 < (rho:num->real) i` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2ci_near (w:real^3)
      (\k. (vectorize:real^3^3->real^(3,3)finite_prod) o
           p2gf_H (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)) sq yc d ((t:num->num) ((r:num->num) k)) s)
      (vectorize o (G:real->real^3->real^3^3) s)`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPECL [`\j:num. s:real`; `s:real`; `r:num->num`; `w:real^3`] o
      GEN_REWRITE_RULE I [p2gf_mov] o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [p2gf_lim] o
      check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "p2gf_lim"))
                           (concl th))) THEN
    ASM_REWRITE_TAC[LIM_CONST] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`y:real^3`;
                 `\k. p2gf_S (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) yc rho P kp sq t r k (NUMPAIR i q) o
                      p2cg_tr rho D j (NUMPAIR i q)`;
                 `p2cg_tr (rho:num->real) D j (NUMPAIR i q)`;
                 `\k. p2gf_H (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) sq yc d ((t:num->num) ((r:num->num) k)) s`;
                 `(G:real->real^3->real^3^3) s`] P2CI_NEAR_MPULLBACK) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP P2GF_NEAR_PT) THEN REWRITE_TAC[o_THM]);;

(* Gf s at a point of a candidate piece, in its preferred chart j. *)

let P2GF_GF_EQ = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z rho K N0 B P yc sq D Gl kp CG t r d i q G s p j.
     p2gf_fctx V U z rho K N0 B P yc sq D Gl kp CG t r /\
     p2gf_ch d = NUMPAIR i q /\ q < P i /\ 3 <= p2gf_ri d /\
     (?N. !n. N <= n ==> p2gf_adm V sq yc rho CG d (t n)) /\
     p2gf_lim (p2gf_dom rho d) (p2gf_bt d) (&0) (\n. p2gf_H V sq yc d (t n)) G /\
     p2gf_bt d <= s /\ s <= &0 /\
     chart_at (p2cl_atlas (p2cg_dm rho) kp) p = p2cl_chart (p2cg_dm rho) kp j /\
     SND(p2cl_chart (p2cg_dm rho) kp j) p IN p2cg_om rho D j (NUMPAIR i q) /\
     p2cg_tr rho D j (NUMPAIR i q) (SND(p2cl_chart (p2cg_dm rho) kp j) p) IN p2gf_dom rho d
     ==> p2gf_Gf V (\k. sq (t (r k))) (p2gf_phi V yc rho P kp sq t r)
                 (p2cl_atlas (p2cg_dm rho) kp) s p =
         mpullback (p2cg_tr rho D j (NUMPAIR i q)) (G s)
                   (SND(p2cl_chart (p2cg_dm rho) kp j) p)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "ev") STRIP_ASSUME_TAC))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GF_FCTX_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cl_system] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2cl_system")) (concl th))) THEN
  ABBREV_TAC `y = SND(p2cl_chart (p2cg_dm rho) (kp:num->real^3->real^3) j) p` THEN
  SUBGOAL_THEN `(y:real^3) IN p2cg_dm rho j` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[p2gf_Gf] THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2GF_LIM_MATRIFY THEN
  MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\k. (vectorize:real^3^3->real^(3,3)finite_prod)
                    (rfs_pullback (rfs_vatlas ((V:num->(real->A topology)#
                                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
                                    ((sq:num->num) ((t:num->num) ((r:num->num) k)))) s)
                       (p2gf_phi V yc rho P kp sq t r k o kp j)
                       (rfs_vmetric (V (sq (t (r k)))) s) y)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN X_GEN_TAC `k:num` THEN
    DISCH_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN MATCH_MP_TAC P2CE_RFS_LOCAL THEN
    EXISTS_TAC `p2cg_dm (rho:num->real) j` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2CL_CHART_INVERSE THEN
    MAP_EVERY EXISTS_TAC [`p2cg_om (rho:num->real) D`; `p2cg_tr (rho:num->real) D`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC P2GF_PB_LIM THEN
  MAP_EVERY EXISTS_TAC [`U:num->A->bool`; `z:num->A`; `K:num->real`; `N0:num->num`;
                        `B:num->num->real`; `Gl:num->real^3->real^3^3`; `CG:real->real`;
                        `d:num`] THEN
  ASM_REWRITE_TAC[]);;

(* Gf s in any chart c over a candidate piece: the transition pullback of the *)
(* candidate limit (the representative in the preferred chart, the Jacobian  *)
(* of the chart transition, the cocycle of the transitions).                 *)

let P2GF_GF_CHART = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z rho K N0 B P yc sq D Gl kp CG t r d i q G s c y.
     p2gf_fctx V U z rho K N0 B P yc sq D Gl kp CG t r /\
     p2gf_ch d = NUMPAIR i q /\ q < P i /\ 3 <= p2gf_ri d /\
     (?N. !n. N <= n ==> p2gf_adm V sq yc rho CG d (t n)) /\
     p2gf_lim (p2gf_dom rho d) (p2gf_bt d) (&0) (\n. p2gf_H V sq yc d (t n)) G /\
     p2gf_bt d <= s /\ s <= &0 /\
     y IN p2cg_om rho D c (NUMPAIR i q) /\ p2cg_tr rho D c (NUMPAIR i q) y IN p2gf_dom rho d
     ==> metric_local (p2cl_atlas (p2cg_dm rho) kp) (p2cl_chart (p2cg_dm rho) kp c)
                      (p2gf_Gf V (\k. sq (t (r k))) (p2gf_phi V yc rho P kp sq t r)
                               (p2cl_atlas (p2cg_dm rho) kp) s) y =
         mpullback (p2cg_tr rho D c (NUMPAIR i q)) (G s) y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "ev") STRIP_ASSUME_TAC))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GF_FCTX_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cl_system] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2cl_system")) (concl th))) THEN
  SUBGOAL_THEN `(y:real^3) IN p2cg_dm rho c` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p2cg_dm (rho:num->real)`; `p2cg_om (rho:num->real) D`;
                 `p2cg_tr (rho:num->real) D`; `kp:num->real^3->real^3`; `c:num`; `y:real^3`]
                P2CL_CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `c':num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `p2cg_tr (rho:num->real) D c c' (y:real^3) IN p2cg_om rho D c' (NUMPAIR i q) /\
                p2cg_tr rho D c' (NUMPAIR i q) (p2cg_tr rho D c c' y) =
                p2cg_tr rho D c (NUMPAIR i q) y`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `U:num->A->bool`; `z:num->A`; `rho:num->real`; `K:num->real`; `N0:num->num`;
                 `B:num->num->real`; `P:num->num`; `yc:num->num->num->A`; `sq:num->num`;
                 `D:num#num->real^(3,3)finite_sum->real^1`; `Gl:num->real^3->real^3^3`;
                 `kp:num->real^3->real^3`; `CG:real->real`; `t:num->num`; `r:num->num`;
                 `d:num`; `i:num`; `q:num`; `G:real->real^3->real^3^3`; `s:real`;
                 `(kp:num->real^3->real^3) c y`; `c':num`] P2GF_GF_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[metric_local] THEN
  SUBGOAL_THEN `chart_inv (p2cl_chart (p2cg_dm rho) (kp:num->real^3->real^3) c) y = kp c y`
  SUBST1_TAC THENL
   [MATCH_MP_TAC P2CL_CHART_INVERSE THEN
    MAP_EVERY EXISTS_TAC [`p2cg_om (rho:num->real) D`; `p2cg_tr (rho:num->real) D`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`p2cg_dm (rho:num->real)`; `p2cg_om (rho:num->real) D`;
                 `p2cg_tr (rho:num->real) D`; `kp:num->real^3->real^3`; `c:num`; `c':num`;
                 `y:real^3`] P2CL_CHART_JAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `transp(matrix(frechet_derivative (p2cg_tr (rho:num->real) D c c') (at y))) **
    mpullback (p2cg_tr rho D c' (NUMPAIR i q)) ((G:real->real^3->real^3^3) s)
              (p2cg_tr rho D c c' y) **
    matrix(frechet_derivative (p2cg_tr rho D c c') (at y)) =
    mpullback (p2cg_tr rho D c c') (mpullback (p2cg_tr rho D c' (NUMPAIR i q)) (G s)) y`
  SUBST1_TAC THENL [REWRITE_TAC[mpullback]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(p2cg_tr (rho:num->real) D c c') differentiable at (y:real^3) /\
    (p2cg_tr rho D c' (NUMPAIR i q)) differentiable at (p2cg_tr rho D c c' y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `p2cg_om (rho:num->real) D c c'`;
      EXISTS_TAC `p2cg_om (rho:num->real) D c' (NUMPAIR i q)`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[P2CE_MPULLBACK_CHAIN] THEN MATCH_MP_TAC P2CG_MPULLBACK_LOCAL THEN
  EXISTS_TAC `p2cg_om (rho:num->real) D c c' INTER p2cg_om rho D c (NUMPAIR i q)` THEN
  ASM_SIMP_TAC[OPEN_INTER; IN_INTER; o_THM]);;

(* Entries of convergent vectorized matrices converge. *)

let P2GF_VEC_ENTRY_LIM = prove
 (`!(X:num->real^3^3) L p q.
     ((\n. vectorize(X n)) --> vectorize L) sequentially
     ==> ((\n. X n$p$q) ---> L$p$q) sequentially`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[TENDSTO_REAL; o_DEF] THEN
  MP_TAC(ISPECL [`sequentially`; `\x:real^(3,3)finite_prod. lift((matrify x:real^3^3)$p$q)`;
                 `\n. (vectorize:real^3^3->real^(3,3)finite_prod) ((X:num->real^3^3) n)`;
                 `(vectorize:real^3^3->real^(3,3)finite_prod) L`] LIM_LINEAR) THEN
  ASM_REWRITE_TAC[LRG_LINEAR_MATRIFY_ENTRY; MATRIFY_VECTORIZE]);;

(* At time 0 the candidate limit is the glued limit metric of its chart. *)

let P2GF_G0_GL = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z rho K N0 B P yc sq D Gl kp CG t r d i q G w.
     p2gf_fctx V U z rho K N0 B P yc sq D Gl kp CG t r /\
     p2gf_ch d = NUMPAIR i q /\ 3 <= p2gf_ri d /\
     (?N. !n. N <= n ==> p2gf_adm V sq yc rho CG d (t n)) /\
     p2gf_lim (p2gf_dom rho d) (p2gf_bt d) (&0) (\n. p2gf_H V sq yc d (t n)) G /\
     w IN p2gf_dom rho d
     ==> G (&0) w = Gl (NUMPAIR i q) w`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `N:num` (LABEL_TAC "adm")) STRIP_ASSUME_TAC)))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GF_FCTX_FACTS) THEN
  SUBGOAL_THEN `p2gf_bt d < &0` ASSUME_TAC THENL
   [USE_THEN "adm" (MP_TAC o SPEC `N:num`) THEN REWRITE_TAC[LE_REFL; p2gf_adm] THEN
    DISCH_THEN(MP_TAC o MATCH_MP P2GF_BT_NEG o CONJUNCT1) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(w:real^3) < (rho:num->real) i / &16` ASSUME_TAC THENL
   [MATCH_MP_TAC P2GF_DOM_SMALL THEN MAP_EVERY EXISTS_TAC [`d:num`; `q:num`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (rho:num->real) i` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the glued limit along all indices, at w *)
  SUBGOAL_THEN
   `((\n. (vectorize:real^3^3->real^(3,3)finite_prod)
            (p2cg_G (\k. rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) k) (&0))
                    (\k. rfs_vatlas (V k) (&0)) (\k. rfs_vmetric (V k) (&0)) yc
                    ((sq:num->num) n) (NUMPAIR i q) w)) -->
     vectorize((Gl:num->real^3->real^3^3) (NUMPAIR i q) w)) sequentially`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `NUMPAIR i q` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
                GEN_REWRITE_RULE I [p2cg_limit] o check (fun th ->
                  can (find_term (fun t -> is_const t && fst(dest_const t) = "p2cg_limit"))
                      (concl th))) THEN
    DISCH_THEN(MP_TAC o SPEC `[]:num list` o CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[ALL; iterated_partial; o_THM; LIM_SEQUENTIALLY; dist] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
    MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `Kn:num` THEN DISCH_TAC THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_BALL_0; NUMPAIR_DEST] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[CART_EQ] THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
  REWRITE_TAC[CART_EQ] THEN X_GEN_TAC `q':num` THEN STRIP_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
  EXISTS_TAC `\n. p2gf_H (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)) sq yc d ((t:num->num) n) (&0) w$p$q'` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPECL [`&0`; `w:real^3`; `p:num`; `q':num`] o CONJUNCT1 o CONJUNCT2 o
      CONJUNCT2 o GEN_REWRITE_RULE I [p2ca_loclim] o CONJUNCT1 o
      GEN_REWRITE_RULE I [p2gf_lim] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2gf_lim")) (concl th))) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL; DIMINDEX_3] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\n. p2cg_G (\k. rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                         (real->A->real^3^3)) k) (&0))
                         (\k. rfs_vatlas (V k) (&0)) (\k. rfs_vmetric (V k) (&0)) yc
                         ((sq:num->num) ((t:num->num) n)) (NUMPAIR i q) w$p$q'` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `N:num` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "adm" (MP_TAC o C MP (ASSUME `N <= n:num`) o SPEC `n:num`) THEN
    REWRITE_TAC[p2gf_adm] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `w:real^3` o CONJUNCT1 o MATCH_MP P2CD_OK_PB0 o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2cd_ok")) (concl th))) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `(w:real^3) IN p2gf_dom rho d` THEN REWRITE_TAC[p2gf_dom; IN_BALL_0] THEN
      SUBGOAL_THEN `&0 < p2gf_r0 (rho:num->real) d` MP_TAC THENL
       [REWRITE_TAC[p2gf_r0] THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[p2gf_H] THEN ASM_REWRITE_TAC[p2cg_G] THEN DISCH_THEN SUBST1_TAC THEN
    REFL_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC P2GF_VEC_ENTRY_LIM THEN
  MP_TAC(ISPECL [`\n. (vectorize:real^3^3->real^(3,3)finite_prod)
                        (p2cg_G (\k. rfs_vtop ((V:num->(real->A topology)#
                                   (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (&0))
                                (\k. rfs_vatlas (V k) (&0)) (\k. rfs_vmetric (V k) (&0)) yc
                                ((sq:num->num) n) (NUMPAIR i q) w)`;
                 `t:num->num`;
                 `(vectorize:real^3^3->real^(3,3)finite_prod) ((Gl:num->real^3->real^3^3) (NUMPAIR i q) w)`]
                LIM_SUBSEQUENCE) THEN
  ASM_REWRITE_TAC[o_DEF]);;

(* At time 0, in any chart c over the piece, the glued metric is the         *)
(* transition pullback of the candidate limit.                               *)

let P2GF_G0_CHART = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z rho K N0 B P yc sq D Gl kp CG t r d i q G c y.
     p2gf_fctx V U z rho K N0 B P yc sq D Gl kp CG t r /\
     p2gf_ch d = NUMPAIR i q /\ 3 <= p2gf_ri d /\
     (?N. !n. N <= n ==> p2gf_adm V sq yc rho CG d (t n)) /\
     p2gf_lim (p2gf_dom rho d) (p2gf_bt d) (&0) (\n. p2gf_H V sq yc d (t n)) G /\
     y IN p2cg_om rho D c (NUMPAIR i q) /\ p2cg_tr rho D c (NUMPAIR i q) y IN p2gf_dom rho d
     ==> metric_local (p2cl_atlas (p2cg_dm rho) kp) (p2cl_chart (p2cg_dm rho) kp c)
                      (p2cl_metric (p2cg_dm rho) kp Gl) y =
         mpullback (p2cg_tr rho D c (NUMPAIR i q)) (G (&0)) y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "ev") STRIP_ASSUME_TAC)))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GF_FCTX_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cg_limit] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2cg_limit")) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cl_system] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2cl_system")) (concl th))) THEN
  SUBGOAL_THEN `(y:real^3) IN p2cg_dm rho c` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p2cg_dm (rho:num->real)`; `p2cg_om (rho:num->real) D`;
                 `p2cg_tr (rho:num->real) D`; `kp:num->real^3->real^3`;
                 `Gl:num->real^3->real^3^3`; `c:num`; `y:real^3`] P2CL_METRIC_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(Gl:num->real^3->real^3^3) c y =
                mpullback (p2cg_tr (rho:num->real) D c (NUMPAIR i q)) (Gl (NUMPAIR i q)) y`
  SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[mpullback] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `U:num->A->bool`; `z:num->A`; `rho:num->real`; `K:num->real`; `N0:num->num`;
                 `B:num->num->real`; `P:num->num`; `yc:num->num->num->A`; `sq:num->num`;
                 `D:num#num->real^(3,3)finite_sum->real^1`; `Gl:num->real^3->real^3^3`;
                 `kp:num->real^3->real^3`; `CG:real->real`; `t:num->num`; `r:num->num`;
                 `d:num`; `i:num`; `q:num`; `G:real->real^3->real^3^3`;
                 `p2cg_tr (rho:num->real) D c (NUMPAIR i q) y`] P2GF_G0_GL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Restricted atlases and metrics of open subsets of one                     *)
(* manifold (generic): the restriction to the whole space, values of         *)
(* restricted metrics depend only on the point, the identity pullback        *)
(* between two restrictions, and double restrictions.                        *)
(* ------------------------------------------------------------------------- *)

let P2GF_RESTRICT_TOPSPACE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool).
     smooth_manifold_atlas top atlas ==> restrict_atlas atlas (topspace top) = atlas`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_RESTRICT_ATLAS] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `psi:A->real^N`] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `U:A->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(U:A->bool) INTER topspace top = U` (fun th -> ASM_MESON_TAC[th]) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U:A->bool`;
                   `psi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1) THEN
    SET_TAC[];
    DISCH_TAC THEN EXISTS_TAC `V:A->bool` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `V:A->bool`;
                   `psi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1) THEN
    SET_TAC[]]);;

(* A restricted metric at x only reads the metric at x. *)

let P2GF_RESTRICT_METRIC_PT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W (g:A->real^N^N) g' x.
     smooth_manifold_atlas top atlas /\ open_in top W /\ x IN W /\ g' x = g x
     ==> restrict_metric atlas W g' x = restrict_metric atlas W g x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `W:A->bool`; `x:A`] P2CF_RESTRICT_METRIC_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[metric_local] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U:A->bool`;
                 `phi:A->real^N`] CHART_INV) THEN
  ASM_SIMP_TAC[]);;

(* The restriction to the whole space. *)

let P2GF_RESTRICT_METRIC_TOPSPACE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) x.
     smooth_manifold_atlas top atlas /\ x IN topspace top
     ==> restrict_metric atlas (topspace top) g x = g x`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[restrict_metric; P2GF_RESTRICT_TOPSPACE] THEN
  MATCH_MP_TAC METRIC_LOCAL_AT THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]);;

(* The identity pullback between two restrictions of one atlas. *)

let P2GF_PB_ID_RESTRICT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W1 W2 (G:A->real^N^N) x.
     smooth_manifold_atlas top atlas /\ open_in top W1 /\ open_in top W2 /\
     x IN W1 /\ x IN W2
     ==> mfd_pullback_metric (restrict_atlas atlas W1) (restrict_atlas atlas W2) (\y. y)
                             (restrict_metric atlas W2 G) x =
         restrict_metric atlas W1 G x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `W1:A->bool`; `x:A`] P2CF_RESTRICT_METRIC_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U1:A->bool` (X_CHOOSE_THEN `phi1:A->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "r1")))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `W2:A->bool`; `x:A`] P2CF_RESTRICT_METRIC_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U2:A->bool` (X_CHOOSE_THEN `phi2:A->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "r2")))))) THEN
  ASM_REWRITE_TAC[mfd_pullback_metric; FST; SND] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U1:A->bool`;
                 `phi1:A->real^N`; `W1:A->bool`; `x:A`] MFDR_CHART_INV_RESTRICT) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
  (* the metric part of the pullback only matters at the point phi2 x *)
  SUBGOAL_THEN
   `mpullback ((phi2:A->real^N) o (\y:A. y) o chart_inv (U1 INTER W1,phi1))
              (metric_local (restrict_atlas atlas W2) (U2 INTER W2,phi2)
                            (restrict_metric atlas W2 (G:A->real^N^N)))
              ((phi1:A->real^N) x) =
    mpullback (phi2 o (\y:A. y) o chart_inv (U1 INTER W1,phi1))
              (metric_local atlas (U2,phi2) G) (phi1 x)`
  SUBST1_TAC THENL
   [REWRITE_TAC[mpullback; o_THM] THEN ASM_REWRITE_TAC[] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC METRIC_LOCAL_RESTRICT THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  (* the map is the chart transition near phi1 x *)
  SUBGOAL_THEN
   `mpullback ((phi2:A->real^N) o (\y:A. y) o chart_inv (U1 INTER W1,phi1))
              (metric_local atlas (U2,phi2) (G:A->real^N^N)) ((phi1:A->real^N) x) =
    mpullback (chart_trans (U1,phi1) (U2,phi2)) (metric_local atlas (U2,phi2) G) (phi1 x)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC P2CG_MPULLBACK_LOCAL THEN
    EXISTS_TAC `IMAGE (phi1:A->real^N) (U1 INTER W1)` THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`subtopology top (W1:A->bool)`; `restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) W1`;
                     `U1 INTER W1:A->bool`; `phi1:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
      ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT; IN_RESTRICT_ATLAS] THEN
      ANTS_TAC THENL [EXISTS_TAC `U1:A->bool` THEN ASM_REWRITE_TAC[]; SIMP_TAC[]];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
      REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER; chart_trans; o_THM] THEN
      X_GEN_TAC `v:A` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U1:A->bool`;
                     `phi1:A->real^N`; `W1:A->bool`; `v:A`] MFDR_CHART_INV_RESTRICT) THEN
      ASM_REWRITE_TAC[IN_INTER] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U1:A->bool`;
                 `phi1:A->real^N`; `U2:A->bool`; `phi2:A->real^N`; `G:A->real^N^N`; `x:A`]
                METRIC_LOCAL_TRANS) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC);;

(* Double restrictions. *)

let P2GF_RESTRICT_METRIC_RESTRICT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) Om W (G:A->real^N^N) x.
     smooth_manifold_atlas top atlas /\ open_in top Om /\ open_in top W /\
     W SUBSET Om /\ x IN W
     ==> restrict_metric (restrict_atlas atlas Om) W (restrict_metric atlas Om G) x =
         restrict_metric atlas W G x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open_in (subtopology top Om) (W:A->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_SUBSET_TOPSPACE THEN ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    MP_TAC(ISPECL [`top:A topology`; `W:A->bool`] OPEN_IN_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology top (Om:A->bool)`; `restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) Om`;
                 `W:A->bool`; `x:A`] P2CF_RESTRICT_METRIC_AT) THEN
  ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT] THEN
  DISCH_THEN(X_CHOOSE_THEN `U':A->bool` (X_CHOOSE_THEN `phi:A->real^N`
    (CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "r1")))))) THEN
  REWRITE_TAC[IN_RESTRICT_ATLAS] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(x:A) IN U INTER Om` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U:A->bool`;
                 `phi:A->real^N`; `Om:A->bool`; `G:A->real^N^N`; `x:A`] METRIC_LOCAL_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `W:A->bool`; `x:A`] P2CF_RESTRICT_METRIC_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U2:A->bool` (X_CHOOSE_THEN `phi2:A->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "r2")))))) THEN
  USE_THEN "r2" (fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `phi2:A->real^N = phi` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `chart_at (restrict_atlas (restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) Om) W) x =
                 (U INTER Om) INTER W,(phi:A->real^N)` THEN
    REWRITE_TAC[RFS_RESTRICT_ATLAS_RESTRICT] THEN
    SUBGOAL_THEN `(Om:A->bool) INTER W = W` SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U:A->bool`;
                 `phi:A->real^N`; `U2:A->bool`; `phi:A->real^N`; `G:A->real^N^N`; `x:A`]
                METRIC_LOCAL_TRANS) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `mpullback (chart_trans (U,phi) (U2,phi)) (metric_local atlas (U2,(phi:A->real^N)) (G:A->real^N^N))
              (phi x) =
    mpullback (\y. y) (metric_local atlas (U2,phi) G) (phi x)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC P2CG_MPULLBACK_LOCAL THEN EXISTS_TAC `IMAGE (phi:A->real^N) U` THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U:A->bool`;
                     `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[];
      REWRITE_TAC[chart_trans; SND] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U:A->bool`;
                     `phi:A->real^N`] CHART_INV) THEN
      ASM_SIMP_TAC[]];
    REWRITE_TAC[P2CE_MPULLBACK_ID]]);;

(* ------------------------------------------------------------------------- *)
(* Region views (generic).  For a manifold (top,atlas) with                  *)
(* metric g, open sets Om s (s < 0) increasing with s, and metrics Gf s, the *)
(* view p2gf_Vl has the slice top at 0 (metric g), subtopology top (Om s)    *)
(* with the restricted atlas and metric for s < 0, and the empty slice for  *)
(* s > 0.  It is regular when near every point of every Om s1, in every     *)
(* chart, the chart representatives form a local Ricci flow on some (a1,0]  *)
(* with a smooth extension past 0 (p2gf_rvhyp).  This is how the limit flow *)
(* of the incomplete limits of G lives (MT Def 5.1 regions, Prop 5.14).     *)
(* ------------------------------------------------------------------------- *)

let p2gf_Vl = new_definition
 `p2gf_Vl (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)
          (Om:real->A->bool) (Gf:real->A->real^3^3) =
    (\s. if s = &0 then top else if s < &0 then subtopology top (Om s)
         else discrete_topology {}),
    (\s. if s < &0 then restrict_atlas atlas (Om s) else atlas),
    (\s. if s < &0 then restrict_metric atlas (Om s) (Gf s) else g)`;;

let P2GF_VL_PARTS = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) Om Gf s.
     rfs_vtop (p2gf_Vl top atlas g Om Gf) s =
       (if s = &0 then top else if s < &0 then subtopology top (Om s)
        else discrete_topology {}) /\
     rfs_vatlas (p2gf_Vl top atlas g Om Gf) s =
       (if s < &0 then restrict_atlas atlas (Om s) else atlas) /\
     rfs_vmetric (p2gf_Vl top atlas g Om Gf) s =
       (if s < &0 then restrict_metric atlas (Om s) (Gf s) else g)`,
  REWRITE_TAC[p2gf_Vl; rfs_vtop; rfs_vatlas; rfs_vmetric]);;

let p2gf_rvhyp = new_definition
 `p2gf_rvhyp (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)
             (Om:real->A->bool) (Gf:real->A->real^3^3) <=>
    hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
    (?c. c IN atlas /\ ~(FST c = {})) /\
    (!s. s < &0 ==> open_in top (Om s)) /\
    (!s s'. s <= s' /\ s' < &0 ==> Om s SUBSET Om s') /\
    (!c s1 y0. c IN atlas /\ s1 < &0 /\ y0 IN IMAGE (SND c) (FST c INTER Om s1)
       ==> ?a1 e O (Fx:real^(1,3)finite_sum->real^(3,3)finite_prod).
             a1 < s1 /\ &0 < e /\ open O /\ y0 IN O /\
             (!s. a1 < s /\ s < &0 ==> O SUBSET IMAGE (SND c) (FST c INTER Om s)) /\
             lricci_flow O a1 (&0) (\s. metric_local atlas c (if s = &0 then g else Gf s)) /\
             smooth_map_on (interval(lift a1,lift e) PCROSS O) Fx /\
             (!s y. a1 < s /\ s <= &0 /\ y IN O
                    ==> Fx(pastecart (lift s) y) =
                        vectorize(metric_local atlas c (if s = &0 then g else Gf s) y)))`;;

(* Chart images of open sets are open. *)

let P2GF_CHART_IMAGE_OPEN = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) c W.
     smooth_manifold_atlas top atlas /\ c IN atlas /\ open_in top W
     ==> open (IMAGE (SND c) (FST c INTER W))`,
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `c:(A->bool)#(A->real^N)` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology top (W:A->bool)`; `restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) W`;
                 `U INTER W:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT; IN_RESTRICT_ATLAS] THEN
  ANTS_TAC THENL [EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[]; SIMP_TAC[]]);;

(* The slices. *)

let P2GF_RV_SLICE = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) Om Gf t.
     p2gf_rvhyp top atlas g Om Gf /\
     ~(topspace(rfs_vtop (p2gf_Vl top atlas g Om Gf) t) = {})
     ==> hausdorff_space (rfs_vtop (p2gf_Vl top atlas g Om Gf) t) /\
         smooth_manifold_atlas (rfs_vtop (p2gf_Vl top atlas g Om Gf) t)
                               (rfs_vatlas (p2gf_Vl top atlas g Om Gf) t) /\
         riemannian_metric (rfs_vatlas (p2gf_Vl top atlas g Om Gf) t)
                           (rfs_vmetric (p2gf_Vl top atlas g Om Gf) t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2gf_rvhyp; P2GF_VL_PARTS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) MP_TAC) THEN
  ASM_CASES_TAC `t = &0` THEN ASM_REWRITE_TAC[REAL_LT_REFL] THEN
  ASM_CASES_TAC `t < &0` THEN ASM_REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY] THEN
  DISCH_TAC THEN ASM_SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY; SMOOTH_MANIFOLD_ATLAS_RESTRICT] THEN
  MATCH_MP_TAC P2CQ_REGION_RIEM THEN EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^3)` THEN DISCH_TAC THEN
  MATCH_MP_TAC MFDR_METRIC_FIELD_LOCAL THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2GF_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`c:(A->bool)#(A->real^3)`; `t:real`; `y:real^3`] o
    check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "lricci_flow"))
                         (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:real` (X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `O:real^3->bool`
    (X_CHOOSE_THEN `Fx:real^(1,3)finite_sum->real^(3,3)finite_prod` STRIP_ASSUME_TAC)))) THEN
  EXISTS_TAC `O:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o GEN_REWRITE_RULE I [lricci_flow] o
    check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "lricci_flow"))
                         (concl th))) THEN
  DISCH_THEN(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[]);;

(* Sets persisting in the region view. *)

let P2GF_RV_PERSISTS = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) Om Gf W a b.
     p2gf_rvhyp top atlas g Om Gf /\ a < b /\ rfs_persists (p2gf_Vl top atlas g Om Gf) W a b
     ==> b <= &0 /\ open_in top W /\ (!s. a < s /\ s < &0 ==> W SUBSET Om s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2gf_rvhyp; P2CO_PERSISTS_ALT; P2GF_VL_PARTS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "per"))) THEN
  SUBGOAL_THEN `b <= &0` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(b = &0) /\ ~(b < &0)` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "per" (MP_TAC o C MP (CONJ (ASSUME `a < b`) (SPEC `b:real` REAL_LE_REFL)) o
                    SPEC `b:real`) THEN
    REWRITE_TAC[ASSUME `~(b = &0)`; ASSUME `~(b < &0)`] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [smooth_manifold_atlas] o CONJUNCT1) THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `c:(A->bool)#(A->real^3)` STRIP_ASSUME_TAC o check (fun th ->
      is_exists(concl th))) THEN
    MP_TAC(ISPEC `c:(A->bool)#(A->real^3)` PAIR_SURJECTIVE) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^3`] THEN DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[FST]) THEN
    DISCH_THEN(MP_TAC o SPECL [`U:A->bool`; `phi:A->real^3`]) THEN
    ASM_REWRITE_TAC[OPEN_IN_DISCRETE_TOPOLOGY; SUBSET_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (W:A->bool)` ASSUME_TAC THENL
   [REMOVE_THEN "per" (MP_TAC o C MP (CONJ (ASSUME `a < b`) (SPEC `b:real` REAL_LE_REFL)) o
                       SPEC `b:real`) THEN
    ASM_CASES_TAC `b = &0` THEN ASM_REWRITE_TAC[] THENL [SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `b < &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[OPEN_IN_OPEN_SUBTOPOLOGY];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!s. a < s /\ s <= b /\ s < &0 ==> (W:A->bool) SUBSET Om s` ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    REMOVE_THEN "per" (MP_TAC o C MP (CONJ (ASSUME `a < s`) (ASSUME `s <= b`)) o SPEC `s:real`) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NE; OPEN_IN_OPEN_SUBTOPOLOGY];
    ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_CASES_TAC `s <= b` THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(Om:real->A->bool) b` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 2)) THEN ASM_REAL_ARITH_TAC]);;

(* The slice at a time b <= 0, restricted to a set W of it. *)

let P2GF_RV_RESTRICT = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) Om Gf W b.
     p2gf_rvhyp top atlas g Om Gf /\ b <= &0 /\ open_in top W /\
     (b < &0 ==> W SUBSET Om b)
     ==> subtopology (rfs_vtop (p2gf_Vl top atlas g Om Gf) b) W = subtopology top W /\
         restrict_atlas (rfs_vatlas (p2gf_Vl top atlas g Om Gf) b) W = restrict_atlas atlas W`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2gf_rvhyp; P2GF_VL_PARTS] THEN STRIP_TAC THEN
  ASM_CASES_TAC `b = &0` THEN ASM_REWRITE_TAC[REAL_LT_REFL] THEN
  SUBGOAL_THEN `b < &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY; RFS_RESTRICT_ATLAS_RESTRICT] THEN
  SUBGOAL_THEN `(Om:real->A->bool) b INTER W = W` (fun th -> REWRITE_TAC[th]) THEN
  ASM SET_TAC[]);;

(* The family p2c_vfam of the region view on W is the restriction of the    *)
(* metrics Gt s = (if s = 0 then g else Gf s) to W.                          *)

let P2GF_RV_VFAM = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) Om Gf W b s x.
     p2gf_rvhyp top atlas g Om Gf /\ s <= b /\ b <= &0 /\ open_in top W /\
     (s < &0 ==> W SUBSET Om s) /\ (b < &0 ==> W SUBSET Om b) /\ x IN W
     ==> p2c_vfam (p2gf_Vl top atlas g Om Gf) W b s x =
         restrict_metric atlas W (if s = &0 then g else Gf s) x`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rv") STRIP_ASSUME_TAC) THEN
  USE_THEN "rv" (STRIP_ASSUME_TAC o REWRITE_RULE[p2gf_rvhyp]) THEN
  SUBGOAL_THEN `(W:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?Ob. open_in top (Ob:A->bool) /\ W SUBSET Ob /\
         rfs_vatlas (p2gf_Vl top atlas g Om (Gf:real->A->real^3^3)) b =
         restrict_atlas atlas Ob /\
         (!y. y IN Ob ==> rfs_vmetric (p2gf_Vl top atlas g Om Gf) b y =
                          restrict_metric atlas Ob (if b = &0 then g else Gf b) y)`
  (X_CHOOSE_THEN `Ob:A->bool` STRIP_ASSUME_TAC) THENL
   [REWRITE_TAC[P2GF_VL_PARTS] THEN ASM_CASES_TAC `b < &0` THENL
     [EXISTS_TAC `(Om:real->A->bool) b` THEN ASM_SIMP_TAC[REAL_LT_IMP_NE];
      ALL_TAC] THEN
    SUBGOAL_THEN `b = &0` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `topspace top:A->bool` THEN
    ASM_SIMP_TAC[P2GF_RESTRICT_TOPSPACE; OPEN_IN_TOPSPACE; REAL_LT_REFL] THEN
    REPEAT STRIP_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2GF_RESTRICT_METRIC_TOPSPACE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p2c_vfam] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (subtopology top Ob)
                  (restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) (Ob:A->bool)) /\
                open_in (subtopology top Ob) (W:A->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT; OPEN_IN_OPEN_SUBTOPOLOGY]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `restrict_metric (restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) (Ob:A->bool)) W
                (restrict_metric atlas Ob (if s = &0 then g else (Gf:real->A->real^3^3) s)) x` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2GF_RESTRICT_METRIC_PT THEN EXISTS_TAC `subtopology top (Ob:A->bool)` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(x:A) IN Ob` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `s < &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[P2GF_VL_PARTS; REAL_LT_IMP_NE] THEN
    MATCH_MP_TAC P2GF_PB_ID_RESTRICT THEN EXISTS_TAC `top:A topology` THEN
    ASM_SIMP_TAC[] THEN ASM SET_TAC[];
    MATCH_MP_TAC P2GF_RESTRICT_METRIC_RESTRICT THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[]]);;

(* Local Ricci flows in space-time give a Ricci flow. *)

let P2GF_LRF_LOCAL = prove
 (`!(O:real^N->bool) a b (G:real->real^N->real^N^N).
     open O /\ a < b /\
     (!t0 y0. a < t0 /\ t0 < b /\ y0 IN O
              ==> ?a' b' O'. a' < t0 /\ t0 < b' /\ open O' /\ y0 IN O' /\ O' SUBSET O /\
                             lricci_flow O' a' b' G)
     ==> lricci_flow O a b G`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "loc"))) THEN
  REWRITE_TAC[lricci_flow] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN MATCH_MP_TAC MFDR_METRIC_FIELD_LOCAL THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    REMOVE_THEN "loc" (MP_TAC o C MP (CONJ (ASSUME `a < t`) (CONJ (ASSUME `t < b`)
                        (ASSUME `(y:real^N) IN O`))) o SPECL [`t:real`; `y:real^N`]) THEN
    REWRITE_TAC[lricci_flow] THEN
    DISCH_THEN(X_CHOOSE_THEN `a':real` (X_CHOOSE_THEN `b':real` (X_CHOOSE_THEN `O':real^N->bool`
      STRIP_ASSUME_TAC))) THEN
    EXISTS_TAC `O':real^N->bool` THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN
    REWRITE_TAC[FORALL_IN_PCROSS] THEN
    MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^N`] THEN
    REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN STRIP_TAC THEN
    REMOVE_THEN "loc" (MP_TAC o C MP (CONJ (ASSUME `a < drop x`) (CONJ (ASSUME `drop x < b`)
                        (ASSUME `(y:real^N) IN O`))) o SPECL [`drop x`; `y:real^N`]) THEN
    REWRITE_TAC[lricci_flow] THEN
    DISCH_THEN(X_CHOOSE_THEN `a':real` (X_CHOOSE_THEN `b':real` (X_CHOOSE_THEN `O':real^N->bool`
      STRIP_ASSUME_TAC))) THEN
    EXISTS_TAC `interval(lift a',lift b') PCROSS (O':real^N->bool)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP];
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`; `i:num`; `j:num`] THEN STRIP_TAC THEN
    REMOVE_THEN "loc" (MP_TAC o C MP (CONJ (ASSUME `a < t`) (CONJ (ASSUME `t < b`)
                        (ASSUME `(y:real^N) IN O`))) o SPECL [`t:real`; `y:real^N`]) THEN
    REWRITE_TAC[lricci_flow] THEN
    DISCH_THEN(X_CHOOSE_THEN `a':real` (X_CHOOSE_THEN `b':real` (X_CHOOSE_THEN `O':real^N->bool`
      STRIP_ASSUME_TAC))) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* The chart representatives over a persisting set are a local Ricci flow. *)

let P2GF_RV_CHART_RF = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) Om Gf W a b c.
     p2gf_rvhyp top atlas g Om Gf /\ a < b /\ b <= &0 /\ open_in top W /\
     (!s. a < s /\ s < &0 ==> W SUBSET Om s) /\ c IN atlas
     ==> lricci_flow (IMAGE (SND c) (FST c INTER W)) a b
                     (\s. metric_local atlas c (if s = &0 then g else Gf s))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rv") STRIP_ASSUME_TAC) THEN
  USE_THEN "rv" (STRIP_ASSUME_TAC o REWRITE_RULE[p2gf_rvhyp]) THEN
  MATCH_MP_TAC P2GF_LRF_LOCAL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2GF_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t0:real`; `y0:real^3`] THEN STRIP_TAC THEN
  ABBREV_TAC `s1 = (a + t0) / &2` THEN
  SUBGOAL_THEN `a < s1 /\ s1 < t0 /\ s1 < &0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`c:(A->bool)#(A->real^3)`; `s1:real`; `y0:real^3`] o
    check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "lricci_flow"))
                         (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y0:real^3) IN IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c INTER W)` THEN
    MATCH_MP_TAC(SET_RULE `(s:A->bool) SUBSET t
                           ==> (y:real^3) IN IMAGE (f:A->real^3) (u INTER s)
                           ==> y IN IMAGE f (u INTER t)`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:real` (X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `O:real^3->bool`
    (X_CHOOSE_THEN `Fx:real^(1,3)finite_sum->real^(3,3)finite_prod` STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`a1:real`; `&0`;
                        `O INTER IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c INTER W)`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2GF_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[IN_INTER];
    SET_TAC[];
    MATCH_MP_TAC RFA_LRICCI_FLOW_SUBSET THEN EXISTS_TAC `O:real^3->bool` THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2GF_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
    ASM_REWRITE_TAC[]]);;

(* Gluing an extension past the top time to the flow on a longer interval. *)

let P2GF_GLUE_TOP = prove
 (`!a a' b U (u:real^(1,N)finite_sum->real^K) Fx e.
     open U /\ a < a' /\ a' < b /\ &0 < e /\
     smooth_map_on (interval(lift a,lift b) PCROSS U) u /\
     smooth_map_on (interval(lift a',lift(b + e)) PCROSS U) Fx /\
     (!t y. a' < t /\ t <= b /\ y IN U ==> Fx(pastecart (lift t) y) = u(pastecart (lift t) y))
     ==> ?Fx'. smooth_map_on (interval(lift a,lift(b + e)) PCROSS U) Fx' /\
               (!t y. a < t /\ t <= b /\ y IN U ==> Fx'(pastecart (lift t) y) =
                                                    (if t < b then u(pastecart (lift t) y)
                                                     else Fx(pastecart (lift t) y)))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `m = (a' + b) / &2` THEN
  SUBGOAL_THEN `a' < m /\ m < b` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `\z:real^(1,N)finite_sum. if drop(fstcart z) < m then (u:real^(1,N)finite_sum->real^K) z
                                       else Fx z` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN
    REWRITE_TAC[FORALL_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^N`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `drop x < m` THENL
     [EXISTS_TAC `interval(lift a,lift m) PCROSS (U:real^N->bool)` THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN EXISTS_TAC `u:real^(1,N)finite_sum->real^K` THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; FORALL_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP;
                   FSTCART_PASTECART] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `interval(lift a,lift b) PCROSS (U:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL; SUBSET_INTERVAL_1; LIFT_DROP] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXISTS_TAC `interval(lift a',lift(b + e)) PCROSS (U:real^N->bool)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN EXISTS_TAC `Fx:real^(1,N)finite_sum->real^K` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; FORALL_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP;
                 FSTCART_PASTECART] THEN
    MAP_EVERY X_GEN_TAC [`x':real^1`; `y':real^N`] THEN STRIP_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(SPEC `x':real^1` (CONJUNCT1 LIFT_DROP)) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
    REWRITE_TAC[FSTCART_PASTECART; LIFT_DROP] THEN
    ASM_CASES_TAC `t < m` THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `t < b` (fun th -> REWRITE_TAC[th]) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* Local continuity data of the one-sided extension lemmas from a local     *)
(* smooth function agreeing with f on the slab.                              *)

let P2GF_LOCAL_DATA = prove
 (`!(f:real^M->real^K) Fs Ts S S0.
     open Ts /\ smooth_map_on Ts Fs /\ S SUBSET Ts /\ open S0 /\ S0 SUBSET S /\
     (!z. z IN S ==> f z = Fs z)
     ==> f continuous_on S /\
         !l. ALL (\i. 1 <= i /\ i <= dimindex(:M)) l
             ==> ?h. h continuous_on S /\ !w. w IN S0 ==> h w = iterated_partial l f w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_EQ THEN EXISTS_TAC `Fs:real^M->real^K` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `Ts:real^M->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
  EXISTS_TAC `iterated_partial l (Fs:real^M->real^K)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `Ts:real^M->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SMOOTH_MAP_ON_ITERATED_PARTIAL];
    X_GEN_TAC `w:real^M` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN EXISTS_TAC `S0:real^M->bool` THEN
    ASM_SIMP_TAC[] THEN ASM SET_TAC[]]);;

(* The chart representatives over a set persisting up to 0 extend smoothly *)
(* past 0 (P2CD_UPTO_TOP_LOC on (a/2,0] from the local extensions of the     *)
(* hypothesis, glued to the flow on (a,0)).                                  *)

let P2GF_RV_TOPEXT = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) Om Gf W a c.
     p2gf_rvhyp top atlas g Om Gf /\ a < &0 /\ open_in top W /\
     (!s. a < s /\ s < &0 ==> W SUBSET Om s) /\ c IN atlas
     ==> ?e Fx. &0 < e /\
                smooth_map_on (interval(lift a,lift(&0 + e)) PCROSS
                               IMAGE (SND c) (FST c INTER W)) Fx /\
                !t y. a < t /\ t <= &0 /\ y IN IMAGE (SND c) (FST c INTER W)
                      ==> Fx(pastecart (lift t) y) =
                          (vectorize:real^3^3->real^(3,3)finite_prod)
                            (metric_local atlas c (if t = &0 then g else Gf t) y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rv") STRIP_ASSUME_TAC) THEN
  USE_THEN "rv" (STRIP_ASSUME_TAC o REWRITE_RULE[p2gf_rvhyp]) THEN
  SUBGOAL_THEN `open (IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c INTER W))` ASSUME_TAC THENL
   [MATCH_MP_TAC P2GF_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lricci_flow (IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c INTER W)) a (&0)
                (\s. metric_local atlas c (if s = &0 then g else (Gf:real->A->real^3^3) s))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2GF_RV_CHART_RF THEN EXISTS_TAC `top:A topology` THEN
    EXISTS_TAC `Om:real->A->bool` THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  ABBREV_TAC `a' = a / &2` THEN
  SUBGOAL_THEN `a < a' /\ a' < &0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "a'" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`a':real`; `&0`; `IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c INTER W)`;
                 `\t y. (vectorize:real^3^3->real^(3,3)finite_prod)
                          (metric_local atlas (c:(A->bool)#(A->real^3))
                             (if t = &0 then g else (Gf:real->A->real^3^3) t) y)`]
                P2CD_UPTO_TOP_LOC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `interval(lift a,lift(&0)) PCROSS
                  IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c INTER W)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL; SUBSET_INTERVAL_1; LIFT_DROP] THEN
        ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `lricci_flow (IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c INTER W)) a (&0)
                       (\s. metric_local atlas c (if s = &0 then g else (Gf:real->A->real^3^3) s))` THEN
        REWRITE_TAC[lricci_flow] THEN SIMP_TAC[]];
      ALL_TAC] THEN
    X_GEN_TAC `y0:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`c:(A->bool)#(A->real^3)`; `a':real`; `y0:real^3`] o
      check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "lricci_flow"))
                           (concl th) && is_forall(concl th))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y0:real^3) IN IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c INTER W)` THEN
      MATCH_MP_TAC(SET_RULE `(s:A->bool) SUBSET t
                             ==> (y:real^3) IN IMAGE (f:A->real^3) (u INTER s)
                             ==> y IN IMAGE f (u INTER t)`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `a1:real` (X_CHOOSE_THEN `e1:real` (X_CHOOSE_THEN `O1:real^3->bool`
      (X_CHOOSE_THEN `Fx1:real^(1,3)finite_sum->real^(3,3)finite_prod` STRIP_ASSUME_TAC)))) THEN
    EXISTS_TAC `O1 INTER IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c INTER W)` THEN
    ASM_SIMP_TAC[OPEN_INTER; IN_INTER; INTER_SUBSET] THEN
    MATCH_MP_TAC P2GF_LOCAL_DATA THEN
    MAP_EVERY EXISTS_TAC [`Fx1:real^(1,3)finite_sum->real^(3,3)finite_prod`;
                          `interval(lift a1,lift e1) PCROSS (O1:real^3->bool)`] THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_INTER] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_PCROSS; PASTECART_IN_PCROSS; IN_ELIM_THM; IN_INTERVAL_1;
                  IN_INTER; LIFT_DROP] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL; SUBSET; IN_ELIM_THM;
                                                 IN_INTERVAL_1; LIFT_DROP] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[FORALL_IN_PCROSS; IN_ELIM_THM; IN_INTER; FSTCART_PASTECART;
                  SNDCART_PASTECART] THEN
      MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^3`] THEN STRIP_TAC THEN
      MP_TAC(SPEC `x:real^1` (CONJUNCT1 LIFT_DROP)) THEN
      DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [SYM th]) THEN
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `FF:real^(1,3)finite_sum->real^(3,3)finite_prod`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `smooth_map_on (interval(lift a,lift(&0)) PCROSS IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c INTER W))
      (\z. (vectorize:real^3^3->real^(3,3)finite_prod)
             (metric_local atlas c
                (if drop(fstcart z) = &0 then g else (Gf:real->A->real^3^3) (drop(fstcart z)))
                (sndcart z)))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `lricci_flow (IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c INTER W)) a (&0)
                   (\s. metric_local atlas c (if s = &0 then g else (Gf:real->A->real^3^3) s))` THEN
    REWRITE_TAC[lricci_flow] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real`; `a':real`; `&0`; `IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c INTER W)`;
                 `\z. (vectorize:real^3^3->real^(3,3)finite_prod)
                        (metric_local atlas (c:(A->bool)#(A->real^3))
                           (if drop(fstcart z) = &0 then g else (Gf:real->A->real^3^3) (drop(fstcart z)))
                           (sndcart z))`;
                 `FF:real^(1,3)finite_sum->real^(3,3)finite_prod`; `e:real`] P2GF_GLUE_TOP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Fx:real^(1,3)finite_sum->real^(3,3)finite_prod` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`e:real`; `Fx:real^(1,3)finite_sum->real^(3,3)finite_prod`] THEN
  ASM_SIMP_TAC[] THEN MAP_EVERY X_GEN_TAC [`t:real`; `y:real^3`] THEN STRIP_TAC THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `t = &0` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`&0`; `y:real^3`] o check (fun th ->
    can (find_term ((=) `FF:real^(1,3)finite_sum->real^(3,3)finite_prod`)) (concl th) &&
    not (can (find_term ((=) `Fx:real^(1,3)finite_sum->real^(3,3)finite_prod`)) (concl th)) &&
    is_forall(concl th))) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL]);;

(* Flows up to b on sets persisting over (a,b]. *)

let P2GF_RV_UPTO = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) Om Gf W a b.
     p2gf_rvhyp top atlas g Om Gf /\ a < b /\ b <= &0 /\ open_in top W /\
     (!s. a < s /\ s < &0 ==> W SUBSET Om s)
     ==> rfs_flow_upto (subtopology top W,restrict_atlas atlas W) a b
                       (\s. restrict_metric atlas W (if s = &0 then g else Gf s))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rv") STRIP_ASSUME_TAC) THEN
  USE_THEN "rv" (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o REWRITE_RULE[p2gf_rvhyp]) THEN
  MATCH_MP_TAC P2CQ_REGION_UPTO THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^3)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `!b'. a < b' /\ b' <= &0
                     ==> lricci_flow (IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c INTER W)) a b'
                           (\s. metric_local atlas c (if s = &0 then g else (Gf:real->A->real^3^3) s))`
  (LABEL_TAC "lf") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2GF_RV_CHART_RF THEN EXISTS_TAC `top:A topology` THEN
    EXISTS_TAC `Om:real->A->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "lf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ASM_CASES_TAC `b = &0` THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
      EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` THEN CONJ_TAC THENL
       [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^3))->bool) g` THEN
        REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        CONJ_TAC THENL
         [MATCH_MP_TAC P2GF_CHART_IMAGE_OPEN THEN
          MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
          ASM_REWRITE_TAC[];
          SET_TAC[]]];
      ALL_TAC] THEN
    USE_THEN "lf" (MP_TAC o SPEC `b / &2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[lricci_flow] THEN DISCH_THEN(MP_TAC o SPEC `b:real` o CONJUNCT1 o CONJUNCT2 o
      CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `b = &0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `Om:real->A->bool`; `Gf:real->A->real^3^3`; `W:A->bool`; `a:real`;
                   `c:(A->bool)#(A->real^3)`] P2GF_RV_TOPEXT) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `--(b / &2)` THEN
  EXISTS_TAC `\z. (vectorize:real^3^3->real^(3,3)finite_prod)
                    (metric_local atlas (c:(A->bool)#(A->real^3))
                       (if drop(fstcart z) = &0 then g else (Gf:real->A->real^3^3) (drop(fstcart z)))
                       (sndcart z))` THEN
  REWRITE_TAC[REAL_ARITH `b + --(b / &2) = b / &2`; FSTCART_PASTECART; SNDCART_PASTECART;
              LIFT_DROP] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "lf" (MP_TAC o SPEC `b / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[lricci_flow] THEN SIMP_TAC[]);;

(* Flows from a on sets open at a (and persisting over (a,b]). *)

let P2GF_RV_FROM = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) Om Gf W a b.
     p2gf_rvhyp top atlas g Om Gf /\ a < b /\ b <= &0 /\ open_in top W /\
     (!s. a <= s /\ s < &0 ==> W SUBSET Om s)
     ==> ricci_flow_from (subtopology top W,restrict_atlas atlas W) a b
                         (\s. restrict_metric atlas W (if s = &0 then g else Gf s))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rv") STRIP_ASSUME_TAC) THEN
  USE_THEN "rv" (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o REWRITE_RULE[p2gf_rvhyp]) THEN
  SUBGOAL_THEN `a < &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC P2CQ_REGION_FROM THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^3)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `open (IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c INTER W))` ASSUME_TAC THENL
   [MATCH_MP_TAC P2GF_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lricci_flow (IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c INTER W)) a b
      (\s. metric_local atlas c (if s = &0 then g else (Gf:real->A->real^3^3) s))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2GF_RV_CHART_RF THEN EXISTS_TAC `top:A topology` THEN
    EXISTS_TAC `Om:real->A->bool` THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the local extensions at time a *)
  SUBGOAL_THEN
   `!y0. y0 IN IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c INTER W)
         ==> ?a1 e O (Fx:real^(1,3)finite_sum->real^(3,3)finite_prod).
               a1 < a /\ &0 < e /\ open O /\ y0 IN O /\
               lricci_flow O a1 (&0)
                 (\s. metric_local atlas c (if s = &0 then g else (Gf:real->A->real^3^3) s)) /\
               smooth_map_on (interval(lift a1,lift e) PCROSS O) Fx /\
               (!s y. a1 < s /\ s <= &0 /\ y IN O
                      ==> Fx(pastecart (lift s) y) =
                          vectorize(metric_local atlas c (if s = &0 then g else Gf s) y))`
  (LABEL_TAC "loc") THENL
   [X_GEN_TAC `y0:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`c:(A->bool)#(A->real^3)`; `a:real`; `y0:real^3`] o
      check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "lricci_flow"))
                           (concl th) && is_forall(concl th) &&
                       can (find_term (fun t -> is_const t && fst(dest_const t) = "smooth_map_on"))
                           (concl th))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y0:real^3) IN IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c INTER W)` THEN
      MATCH_MP_TAC(SET_RULE `(s:A->bool) SUBSET t
                             ==> (y:real^3) IN IMAGE (f:A->real^3) (u INTER s)
                             ==> y IN IMAGE f (u INTER t)`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL];
      REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN STRIP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC MFDR_METRIC_FIELD_LOCAL THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y0:real^3` THEN DISCH_TAC THEN
    USE_THEN "loc" (MP_TAC o C MP (ASSUME
      `(y0:real^3) IN IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c INTER W)`) o SPEC `y0:real^3`) THEN
    DISCH_THEN(X_CHOOSE_THEN `a1:real` (X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `O:real^3->bool`
      (X_CHOOSE_THEN `Fx:real^(1,3)finite_sum->real^(3,3)finite_prod` STRIP_ASSUME_TAC)))) THEN
    EXISTS_TAC `O:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:real` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
      GEN_REWRITE_RULE I [lricci_flow] o check (fun th ->
        can (find_term ((=) `O:real^3->bool`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "lricci_flow")) (concl th))) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real`; `b:real`; `IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c INTER W)`;
                 `\t y. (vectorize:real^3^3->real^(3,3)finite_prod)
                          (metric_local atlas (c:(A->bool)#(A->real^3))
                             (if t = &0 then g else (Gf:real->A->real^3^3) t) y)`]
                P2CB_UPTO) THEN
  REWRITE_TAC[pde_upto] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `lricci_flow (IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c INTER W)) a b
                   (\s. metric_local atlas c (if s = &0 then g else (Gf:real->A->real^3^3) s))` THEN
    REWRITE_TAC[lricci_flow] THEN SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `y0:real^3` THEN DISCH_TAC THEN
  USE_THEN "loc" (MP_TAC o C MP (ASSUME
    `(y0:real^3) IN IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c INTER W)`) o SPEC `y0:real^3`) THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:real` (X_CHOOSE_THEN `e1:real` (X_CHOOSE_THEN `O1:real^3->bool`
    (X_CHOOSE_THEN `Fx1:real^(1,3)finite_sum->real^(3,3)finite_prod` STRIP_ASSUME_TAC)))) THEN
  EXISTS_TAC `O1 INTER IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c INTER W)` THEN
  ASM_SIMP_TAC[OPEN_INTER; IN_INTER; INTER_SUBSET] THEN
  MATCH_MP_TAC P2GF_LOCAL_DATA THEN
  MAP_EVERY EXISTS_TAC [`Fx1:real^(1,3)finite_sum->real^(3,3)finite_prod`;
                        `interval(lift a1,lift e1) PCROSS (O1:real^3->bool)`] THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_INTER] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_PCROSS; PASTECART_IN_PCROSS; IN_ELIM_THM; IN_INTERVAL_1;
                IN_INTER; LIFT_DROP] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL; SUBSET; IN_ELIM_THM;
                                               IN_INTERVAL_1; LIFT_DROP] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[FORALL_IN_PCROSS; IN_ELIM_THM; IN_INTER; FSTCART_PASTECART;
                SNDCART_PASTECART] THEN
    MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^3`] THEN STRIP_TAC THEN
    MP_TAC(SPEC `x:real^1` (CONJUNCT1 LIFT_DROP)) THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [SYM th]) THEN
    CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

(* Congruence of flows from a time (mirror of P2CF_RFU_CONG). *)

let P2GF_RFF_CONG = prove
 (`!top atlas a b (g:real->A->real^3^3) g'.
     ricci_flow_from (top,atlas) a b g /\
     (!t x. a <= t /\ t < b /\ x IN topspace top ==> g' t x = g t x)
     ==> ricci_flow_from (top,atlas) a b g'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ricci_flow_from] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 (LABEL_TAC "on") (CONJUNCTS_THEN2 (LABEL_TAC "ga") (LABEL_TAC "ext")))
    (LABEL_TAC "eq")) THEN
  USE_THEN "on" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2CF_RFO_CONG THEN EXISTS_TAC `g:real->A->real^3^3` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    REMOVE_THEN "eq" MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    MATCH_MP_TAC PDE_RIEMANNIAN_METRIC_CONG THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `(g:real->A->real^3^3) a`] THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    REMOVE_THEN "eq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    X_GEN_TAC `c:(A->bool)#(A->real^3)` THEN DISCH_TAC THEN
    USE_THEN "ext" (fun th -> MP_TAC(MP (SPEC `c:(A->bool)#(A->real^3)` th)
                                        (ASSUME `(c:(A->bool)#(A->real^3)) IN atlas`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real`
      (X_CHOOSE_THEN `FF:real^(1,3)finite_sum->real^(3,3)finite_prod`
        STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`e:real`; `FF:real^(1,3)finite_sum->real^(3,3)finite_prod`] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^3`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `c:(A->bool)#(A->real^3)`; `(g:real->A->real^3^3) t`;
                   `(g':real->A->real^3^3) t`] PDE_METRIC_LOCAL_CONG) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [X_GEN_TAC `x:A` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
      REMOVE_THEN "eq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* The slices at times s <= 0 are restrictions of (top,atlas). *)

let P2GF_RV_SLICE_FORM = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) Om Gf s.
     p2gf_rvhyp top atlas g Om Gf /\ s <= &0
     ==> ?Os. open_in top Os /\ (s < &0 ==> Os = Om s) /\ (s = &0 ==> Os = topspace top) /\
              rfs_vtop (p2gf_Vl top atlas g Om Gf) s = subtopology top Os /\
              rfs_vatlas (p2gf_Vl top atlas g Om Gf) s = restrict_atlas atlas Os`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2gf_rvhyp; P2GF_VL_PARTS] THEN STRIP_TAC THEN
  ASM_CASES_TAC `s < &0` THENL
   [EXISTS_TAC `(Om:real->A->bool) s` THEN ASM_SIMP_TAC[REAL_LT_IMP_NE];
    ALL_TAC] THEN
  SUBGOAL_THEN `s = &0` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `topspace top:A->bool` THEN
  ASM_SIMP_TAC[OPEN_IN_TOPSPACE; SUBTOPOLOGY_TOPSPACE; P2GF_RESTRICT_TOPSPACE; REAL_LT_REFL]);;

(* The identity is a diffeomorphism between the slices containing W. *)

let P2GF_RV_DIFFEO = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) Om Gf W s b.
     p2gf_rvhyp top atlas g Om Gf /\ s <= &0 /\ b <= &0 /\ open_in top W /\
     (s < &0 ==> W SUBSET Om s) /\ (b < &0 ==> W SUBSET Om b)
     ==> mfd_diffeo (rfs_vtop (p2gf_Vl top atlas g Om Gf) s)
                    (rfs_vatlas (p2gf_Vl top atlas g Om Gf) s) W
                    (rfs_vtop (p2gf_Vl top atlas g Om Gf) b)
                    (rfs_vatlas (p2gf_Vl top atlas g Om Gf) b) W (\y:A. y) (\y. y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rv") STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `Om:real->A->bool`; `Gf:real->A->real^3^3`; `s:real`] P2GF_RV_SLICE_FORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Os:A->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `Om:real->A->bool`; `Gf:real->A->real^3^3`; `b:real`] P2GF_RV_SLICE_FORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Ob:A->bool` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "rv" (STRIP_ASSUME_TAC o REWRITE_RULE[p2gf_rvhyp]) THEN
  SUBGOAL_THEN `(W:A->bool) SUBSET Os /\ W SUBSET Ob` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_CASES_TAC `s < &0` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `s = &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_MESON_TAC[OPEN_IN_SUBSET];
      ASM_CASES_TAC `b < &0` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `b = &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_MESON_TAC[OPEN_IN_SUBSET]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `Os:A->bool`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `Ob:A->bool`;
                 `W:A->bool`; `W:A->bool`; `\y:A. y`; `\y:A. y`] APX_MFD_DIFFEO_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC MFD_DIFFEO_ID THEN ASM_REWRITE_TAC[]);;

(* The region view is regular. *)

let P2GF_RVIEW_REGULAR = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) Om Gf.
     p2gf_rvhyp top atlas g Om Gf ==> p2c_regular_view (p2gf_Vl top atlas g Om Gf)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[p2gf_rvhyp]) THEN
  SUBGOAL_THEN
   `!W a b. a < b /\ rfs_persists (p2gf_Vl top atlas g Om Gf) W a b
            ==> p2c_vflow (p2gf_Vl top atlas (g:A->real^3^3) Om Gf) W a b`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`W:A->bool`; `a:real`; `b:real`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `Om:real->A->bool`; `Gf:real->A->real^3^3`; `W:A->bool`; `a:real`; `b:real`]
                  P2GF_RV_PERSISTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `b < &0 ==> (W:A->bool) SUBSET (Om:real->A->bool) b` ASSUME_TAC THENL
     [DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[p2c_vflow] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `Om:real->A->bool`; `Gf:real->A->real^3^3`; `W:A->bool`; `b:real`]
                  P2GF_RV_RESTRICT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2CF_RFU_CONG THEN
    EXISTS_TAC `\s. restrict_metric (atlas:((A->bool)#(A->real^3))->bool) W
                      (if s = &0 then g else (Gf:real->A->real^3^3) s)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2GF_RV_UPTO THEN EXISTS_TAC `Om:real->A->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC P2GF_RV_VFAM THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:A) IN topspace(subtopology top W)` THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC THEN NO_TAC) THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p2c_regular_view] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN MATCH_MP_TAC P2GF_RV_SLICE THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`W:A->bool`; `a:real`; `b:real`] THEN STRIP_TAC THEN
    REWRITE_TAC[p2c_vflow_from] THEN ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `Om:real->A->bool`; `Gf:real->A->real^3^3`; `W:A->bool`; `a:real`; `b:real`]
                  P2GF_RV_PERSISTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `a < &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(W:A->bool) SUBSET (Om:real->A->bool) a` ASSUME_TAC THENL
     [UNDISCH_TAC `open_in (rfs_vtop (p2gf_Vl top atlas g Om (Gf:real->A->real^3^3)) a) W` THEN
      ASM_SIMP_TAC[P2GF_VL_PARTS; REAL_LT_IMP_NE; OPEN_IN_OPEN_SUBTOPOLOGY];
      ALL_TAC] THEN
    SUBGOAL_THEN `b < &0 ==> (W:A->bool) SUBSET (Om:real->A->bool) b` ASSUME_TAC THENL
     [DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `Om:real->A->bool`; `Gf:real->A->real^3^3`; `W:A->bool`; `b:real`]
                  P2GF_RV_RESTRICT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2GF_RFF_CONG THEN
    EXISTS_TAC `\s. restrict_metric (atlas:((A->bool)#(A->real^3))->bool) W
                      (if s = &0 then g else (Gf:real->A->real^3^3) s)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2GF_RV_FROM THEN EXISTS_TAC `Om:real->A->bool` THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_CASES_TAC `(s:real) = a` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC P2GF_RV_VFAM THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:A) IN topspace(subtopology top W)` THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC THEN NO_TAC) THEN
    DISCH_TAC THEN ASM_CASES_TAC `(t:real) = a` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`W:A->bool`; `a:real`; `b:real`; `s:real`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `Om:real->A->bool`; `Gf:real->A->real^3^3`; `W:A->bool`; `a:real`; `b:real`]
                  P2GF_RV_PERSISTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MATCH_MP_TAC P2GF_RV_DIFFEO THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    MAP_EVERY X_GEN_TAC [`W:A->bool`; `a:real`; `b:real`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `Om:real->A->bool`; `Gf:real->A->real^3^3`; `W:A->bool`; `a:real`; `b:real`]
                  P2GF_RV_PERSISTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `a < &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC P2GF_RV_DIFFEO THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      TRY DISCH_TAC THEN
      UNDISCH_TAC `open_in (rfs_vtop (p2gf_Vl top atlas g Om (Gf:real->A->real^3^3)) a) W` THEN
      ASM_SIMP_TAC[P2GF_VL_PARTS; REAL_LT_IMP_NE; OPEN_IN_OPEN_SUBTOPOLOGY];
      DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* The limit flow of G as a region view.  The local flow                     *)
(* hypothesis of p2gf_rvhyp near every point of a candidate piece, in every *)
(* chart of the glued limit: the transition pullback of the candidate limit *)
(* flow and of its smooth extension past 0 (the space-time pullback of a     *)
(* smooth family by a diffeomorphism is smooth, as in LRICCI_FLOW_PULLBACK). *)
(* ------------------------------------------------------------------------- *)

let P2GF_ST_PULLBACK_SMOOTH = prove
 (`!U U' a b (h:real^N->real^N) h' (G:real->real^N->real^N^N).
     diffeomorphism_on U' U h h' /\
     smooth_map_on (interval(lift a,lift b) PCROSS U)
                   (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                          (G (drop(fstcart z)) (sndcart z)))
     ==> smooth_map_on (interval(lift a,lift b) PCROSS U')
           (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                  (mpullback h (G (drop(fstcart z))) (sndcart z)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[diffeomorphism_on]
    (ASSUME `diffeomorphism_on (U':real^N->bool) U (h:real^N->real^N) h'`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z. vectorize(mpullback (h:real^N->real^N)
                    ((G:real->real^N->real^N^N) (drop(fstcart z))) (sndcart z))) =
    (vectorize:real^N^N->real^(N,N)finite_prod) o
    (\z. transp(matrix(frechet_derivative h (at (sndcart z)))) **
         G (drop(fstcart z)) (h(sndcart z)) **
         matrix(frechet_derivative h (at (sndcart z))))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; mpullback]; ALL_TAC] THEN
  SUBGOAL_THEN `open(interval(lift a,lift b) PCROSS (U':real^N->bool))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (interval(lift a,lift b) PCROSS (U':real^N->bool))
      ((vectorize:real^N^N->real^(N,N)finite_prod) o
       (\z. matrix(frechet_derivative (h:real^N->real^N) (at (sndcart z)))))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(vectorize:real^N^N->real^(N,N)finite_prod) o
      (\z. matrix(frechet_derivative (h:real^N->real^N) (at (sndcart z)))) =
      (vectorize o (\x. matrix(frechet_derivative h (at x)))) o
      (sndcart:real^(1,N)finite_sum->real^N)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `U':real^N->bool` THEN
    ASM_SIMP_TAC[LRG_SMOOTH_JACOBIAN; LRG_SMOOTH_LINEAR; LINEAR_SNDCART] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; SNDCART_PASTECART] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC LRG_SMOOTH_MATMUL THEN ASM_SIMP_TAC[LRG_SMOOTH_TRANSP] THEN
  MATCH_MP_TAC LRG_SMOOTH_MATMUL THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(vectorize:real^N^N->real^(N,N)finite_prod) o
    (\z. (G:real->real^N->real^N^N) (drop(fstcart z))
                                    ((h:real^N->real^N) (sndcart z))) =
    (\z. vectorize(G (drop(fstcart z)) (sndcart z))) o
    (\z:real^(1,N)finite_sum. pastecart (fstcart z) (h(sndcart z)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `interval(lift a,lift b) PCROSS (U:real^N->bool)` THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; FSTCART_PASTECART;
                SNDCART_PASTECART; PASTECART_IN_PCROSS] THEN
    ASM SET_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
    ASM_SIMP_TAC[LRG_SMOOTH_LINEAR; LINEAR_FSTCART] THEN
    SUBGOAL_THEN
     `(\z:real^(1,N)finite_sum. (h:real^N->real^N) (sndcart z)) = h o sndcart`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `U':real^N->bool` THEN
    ASM_SIMP_TAC[LRG_SMOOTH_LINEAR; LINEAR_SNDCART] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; SNDCART_PASTECART] THEN
    SIMP_TAC[]]);;

(* The metrics of the limit flow at all times s <= 0 (g at 0). *)

let p2gf_Gt = new_definition
 `p2gf_Gt (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                (real->A->real^3^3))
          (yc:num->num->num->A) (rho:num->real) (P:num->num) (kp:num->real^3->real^3)
          (sq:num->num) (t:num->num) (r:num->num) (Gl:num->real^3->real^3^3) (s:real) =
    if s = &0 then p2cl_metric (p2cg_dm rho) kp Gl
    else p2gf_Gf V (\k. sq (t (r k))) (p2gf_phi V yc rho P kp sq t r)
                 (p2cl_atlas (p2cg_dm rho) kp) s`;;

(* The candidate piece in a chart j: local flow and smooth extension. *)

let P2GF_PIECE_FLOW = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z rho K N0 B P yc sq D Gl kp CG t r d i q G j y0.
     p2gf_fctx V U z rho K N0 B P yc sq D Gl kp CG t r /\
     p2gf_ch d = NUMPAIR i q /\ q < P i /\ 3 <= p2gf_ri d /\
     (?N. !n. N <= n ==> p2gf_adm V sq yc rho CG d (t n)) /\
     p2gf_lim (p2gf_dom rho d) (p2gf_bt d) (&0) (\n. p2gf_H V sq yc d (t n)) G /\
     y0 IN p2cg_om rho D j (NUMPAIR i q) /\ p2cg_tr rho D j (NUMPAIR i q) y0 IN p2gf_dom rho d
     ==> ?e O (Fx:real^(1,3)finite_sum->real^(3,3)finite_prod).
           &0 < e /\ open O /\ y0 IN O /\
           (!y. y IN O ==> y IN p2cg_om rho D j (NUMPAIR i q) /\
                           p2cg_tr rho D j (NUMPAIR i q) y IN p2gf_dom rho d) /\
           lricci_flow O (p2gf_bt d) (&0)
             (\s. metric_local (p2cl_atlas (p2cg_dm rho) kp) (p2cl_chart (p2cg_dm rho) kp j)
                    (p2gf_Gt V yc rho P kp sq t r Gl s)) /\
           smooth_map_on (interval(lift(p2gf_bt d),lift e) PCROSS O) Fx /\
           (!s y. p2gf_bt d < s /\ s <= &0 /\ y IN O
                  ==> Fx(pastecart (lift s) y) =
                      vectorize(metric_local (p2cl_atlas (p2cg_dm rho) kp)
                                  (p2cl_chart (p2cg_dm rho) kp j)
                                  (p2gf_Gt V yc rho P kp sq t r Gl s) y))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "ev") STRIP_ASSUME_TAC))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GF_FCTX_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cl_system] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2cl_system")) (concl th))) THEN
  FIRST_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o GEN_REWRITE_RULE I [p2gf_lim] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2gf_lim")) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2ca_loclim] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2ca_loclim")) (concl th))) THEN
  ABBREV_TAC `U0 = p2gf_dom rho d INTER p2cg_om (rho:num->real) D (NUMPAIR i q) j` THEN
  SUBGOAL_THEN `open (U0:real^3->bool) /\ U0 SUBSET p2cg_om rho D (NUMPAIR i q) j /\
                U0 SUBSET p2gf_dom rho d` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "U0" THEN ASM_SIMP_TAC[OPEN_INTER; p2gf_dom; OPEN_BALL; INTER_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2cg_dm (rho:num->real)`; `p2cg_om (rho:num->real) D`;
                 `p2cg_tr (rho:num->real) D`; `NUMPAIR i q`; `j:num`; `U0:real^3->bool`]
                P2CE_TR_DIFFEO) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `O = IMAGE (p2cg_tr (rho:num->real) D (NUMPAIR i q) j) U0` THEN
  SUBGOAL_THEN `!y. y IN O ==> y IN p2cg_om (rho:num->real) D j (NUMPAIR i q) /\
                               p2cg_tr rho D j (NUMPAIR i q) y IN p2gf_dom rho d`
  (LABEL_TAC "inO") THENL
   [EXPAND_TAC "O" THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `w:real^3` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(w:real^3) IN p2cg_om (rho:num->real) D (NUMPAIR i q) j` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y0:real^3) IN O` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `p2cg_tr (rho:num->real) D j (NUMPAIR i q) y0` THEN
    ASM_SIMP_TAC[] THEN EXPAND_TAC "U0" THEN ASM_SIMP_TAC[IN_INTER];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `Fd:real^(1,3)finite_sum->real^(3,3)finite_prod`
    STRIP_ASSUME_TAC) o check (fun th -> is_exists(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "smooth_map_on")) (concl th))) THEN
  (* the transition pullback of the candidate limit *)
  SUBGOAL_THEN
   `!s y. p2gf_bt d <= s /\ s <= &0 /\ y IN O
          ==> metric_local (p2cl_atlas (p2cg_dm rho) kp) (p2cl_chart (p2cg_dm rho) kp j)
                (p2gf_Gt (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) (yc:num->num->num->A) rho P kp sq t r Gl s) y =
              mpullback (p2cg_tr (rho:num->real) D j (NUMPAIR i q))
                        ((G:real->real^3->real^3^3) s) y`
  (LABEL_TAC "id") THENL
   [MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN STRIP_TAC THEN
    USE_THEN "inO" (MP_TAC o C MP (ASSUME `(y:real^3) IN O`) o SPEC `y:real^3`) THEN
    STRIP_TAC THEN REWRITE_TAC[p2gf_Gt] THEN COND_CASES_TAC THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC P2GF_G0_CHART THEN
      MAP_EVERY EXISTS_TAC
       [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
        `U:num->A->bool`; `z:num->A`; `K:num->real`; `N0:num->num`;
        `B:num->num->real`; `P:num->num`; `yc:num->num->num->A`; `sq:num->num`;
        `CG:real->real`; `t:num->num`; `r:num->num`; `d:num`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2GF_GF_CHART THEN
      MAP_EVERY EXISTS_TAC [`U:num->A->bool`; `z:num->A`; `K:num->real`; `N0:num->num`;
                            `B:num->num->real`; `Gl:num->real^3->real^3^3`; `CG:real->real`;
                            `d:num`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`e:real`; `O:real^3->bool`;
    `\zz:real^(1,3)finite_sum. (vectorize:real^3^3->real^(3,3)finite_prod)
        (mpullback (p2cg_tr (rho:num->real) D j (NUMPAIR i q))
           (\w. (matrify:real^(3,3)finite_prod->real^3^3)
                  ((Fd:real^(1,3)finite_sum->real^(3,3)finite_prod) (pastecart (fstcart zz) w)))
           (sndcart zz))`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RFA_LRICCI_FLOW_EQ THEN
    EXISTS_TAC `\s. mpullback (p2cg_tr (rho:num->real) D j (NUMPAIR i q))
                              ((G:real->real^3->real^3^3) s)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LRICCI_FLOW_PULLBACK THEN
      MAP_EVERY EXISTS_TAC [`U0:real^3->bool`; `p2cg_tr (rho:num->real) D (NUMPAIR i q) j`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFA_LRICCI_FLOW_SUBSET THEN
      EXISTS_TAC `p2gf_dom rho d` THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      USE_THEN "id" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    MP_TAC(ISPECL [`U0:real^3->bool`; `O:real^3->bool`; `p2gf_bt d`; `e:real`;
                   `p2cg_tr (rho:num->real) D j (NUMPAIR i q)`;
                   `p2cg_tr (rho:num->real) D (NUMPAIR i q) j`;
                   `\s w. (matrify:real^(3,3)finite_prod->real^3^3)
                            ((Fd:real^(1,3)finite_sum->real^(3,3)finite_prod) (pastecart (lift s) w))`]
                  P2GF_ST_PULLBACK_SMOOTH) THEN
    REWRITE_TAC[LIFT_DROP; VECTORIZE_MATRIFY; PASTECART_FST_SND; ETA_AX] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `interval(lift(p2gf_bt d),lift(&0 + e)) PCROSS p2gf_dom rho d` THEN
    ASM_REWRITE_TAC[REAL_ADD_LID] THEN MATCH_MP_TAC PCROSS_MONO THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN STRIP_TAC THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN AP_TERM_TAC THEN
    USE_THEN "inO" (MP_TAC o C MP (ASSUME `(y:real^3) IN O`) o SPEC `y:real^3`) THEN
    STRIP_TAC THEN
    USE_THEN "id" (fun th -> MP_TAC(SPECL [`s:real`; `y:real^3`] th)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[mpullback] THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `p2cg_tr (rho:num->real) D j (NUMPAIR i q) y`] o
      check (fun th -> can (find_term ((=) `Fd:real^(1,3)finite_sum->real^(3,3)finite_prod`))
                           (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MATRIFY_VECTORIZE]]);;

(* The limit flow of G satisfies the region-view hypothesis. *)

let P2GF_RVHYP_G = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z rho K N0 B P yc sq D Gl kp CG t r.
     p2gf_fctx V U z rho K N0 B P yc sq D Gl kp CG t r
     ==> p2gf_rvhyp (p2cl_top (p2cg_dm rho) kp) (p2cl_atlas (p2cg_dm rho) kp)
                    (p2cl_metric (p2cg_dm rho) kp Gl)
                    (p2gf_reg V sq yc rho CG P kp t)
                    (p2gf_Gf V (\k. sq (t (r k))) (p2gf_phi V yc rho P kp sq t r)
                             (p2cl_atlas (p2cg_dm rho) kp))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GF_FCTX_FACTS) THEN
  MP_TAC(ISPECL [`\k. rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                   (real->A->real^3^3)) k) (&0)`;
                 `\k. rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                     (real->A->real^3^3)) k) (&0)`;
                 `\k. rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                      (real->A->real^3^3)) k) (&0)`;
                 `z:num->A`; `rho:num->real`; `K:num->real`; `N0:num->num`;
                 `B:num->num->real`; `\j:num m:num. (N0:num->num) j`; `P:num->num`;
                 `N0:num->num`; `yc:num->num->num->A`; `sq:num->num`;
                 `D:num#num->real^(3,3)finite_sum->real^1`; `Gl:num->real^3->real^3^3`;
                 `kp:num->real^3->real^3`] P2GC_MANIFOLD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[p2gf_rvhyp] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [EXISTS_TAC `p2cl_chart (p2cg_dm (rho:num->real)) (kp:num->real^3->real^3) 0` THEN
    ASM_REWRITE_TAC[IMAGE_EQ_EMPTY; p2cg_dm; BALL_EQ_EMPTY; REAL_NOT_LE] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2GF_OM_OPEN THEN
    MAP_EVERY EXISTS_TAC [`U:num->A->bool`; `z:num->A`; `K:num->real`; `N0:num->num`;
                          `B:num->num->real`; `D:num#num->real^(3,3)finite_sum->real^1`;
                          `Gl:num->real^3->real^3^3`; `r:num->num`] THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2GF_OM_MONO THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[P2CL_IN_ATLAS_ALT; LEFT_IMP_EXISTS_THM; RIGHT_AND_EXISTS_THM;
              LEFT_AND_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c:(real^3->bool)#(real^3->real^3)`; `s1:real`; `y0:real^3`; `j:num`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ceq") (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REMOVE_THEN "ceq" SUBST_ALL_TAC THEN
  ASM_REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^3` (CONJUNCTS_THEN2 SUBST1_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 (LABEL_TAC "peq") ASSUME_TAC))
                     ASSUME_TAC))) THEN
  REMOVE_THEN "peq" SUBST_ALL_TAC THEN
  ASM_SIMP_TAC[] THEN
  UNDISCH_TAC `(kp:num->real^3->real^3) j y IN
                p2gf_reg (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) sq (yc:num->num->num->A) rho CG P kp t s1` THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[p2gf_reg; IN_UNIONS; EXISTS_IN_GSPEC; IN_IMAGE]) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
    (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC))) THEN
  UNDISCH_TAC `p2gf_okp (P:num->num) d` THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[p2gf_okp]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `q:num`
    STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `(kp:num->real^3->real^3) j y = kp (NUMPAIR i q) w` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^3) IN p2cg_dm rho (NUMPAIR i q)` ASSUME_TAC THENL
   [UNDISCH_TAC `(w:real^3) IN p2gf_dom rho d` THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET t ==> (w:real^3) IN s ==> w IN t`) THEN
    REWRITE_TAC[p2gf_dom; p2cg_dm; p2gf_r0] THEN ASM_REWRITE_TAC[NUMPAIR_DEST] THEN
    MATCH_MP_TAC SUBSET_BALL THEN
    SUBGOAL_THEN `&8 <= &2 pow (p2gf_ri d)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 pow 3` THEN CONJ_TAC THENL
       [CONV_TAC REAL_RAT_REDUCE_CONV; MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (rho:num->real) i` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SPEC_TAC(`&2 pow (p2gf_ri d)`,`qq:real`) THEN SPEC_TAC(`(rho:num->real) i`,`x:real`) THEN
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `x / qq <= x / &8` MP_TAC THENL
     [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [UNDISCH_TAC `&0 < x` THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_INV2 THEN UNDISCH_TAC `&8 <= qq` THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    UNDISCH_TAC `&0 < x` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN p2cg_om (rho:num->real) D j (NUMPAIR i q) /\
                p2cg_tr rho D j (NUMPAIR i q) y = w` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2cl_glue (p2cg_dm (rho:num->real)) (p2cg_om rho D) (p2cg_tr rho D)
                           (kp:num->real^3->real^3)` THEN
    REWRITE_TAC[p2cl_glue] THEN
    DISCH_THEN(MP_TAC o SPECL [`j:num`; `NUMPAIR i q`; `y:real^3`; `w:real^3`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `U:num->A->bool`; `z:num->A`; `rho:num->real`; `K:num->real`; `N0:num->num`;
                 `B:num->num->real`; `P:num->num`; `yc:num->num->num->A`; `sq:num->num`;
                 `D:num#num->real^(3,3)finite_sum->real^1`; `Gl:num->real^3->real^3^3`;
                 `kp:num->real^3->real^3`; `CG:real->real`; `t:num->num`; `r:num->num`;
                 `d:num`] P2GF_DICH_ADM) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `G:real->real^3->real^3^3`) THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `U:num->A->bool`; `z:num->A`; `rho:num->real`; `K:num->real`; `N0:num->num`;
                 `B:num->num->real`; `P:num->num`; `yc:num->num->num->A`; `sq:num->num`;
                 `D:num#num->real^(3,3)finite_sum->real^1`; `Gl:num->real^3->real^3^3`;
                 `kp:num->real^3->real^3`; `CG:real->real`; `t:num->num`; `r:num->num`;
                 `d:num`; `i:num`; `q:num`; `G:real->real^3->real^3^3`; `j:num`; `y:real^3`]
                P2GF_PIECE_FLOW) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `O:real^3->bool`
    (X_CHOOSE_THEN `Fx:real^(1,3)finite_sum->real^(3,3)finite_prod` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`p2gf_bt d`; `e:real`; `O:real^3->bool`;
                        `Fx:real^(1,3)finite_sum->real^(3,3)finite_prod`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN REWRITE_TAC[SUBSET; IN_IMAGE; IN_INTER] THEN
    X_GEN_TAC `y':real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y':real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `O:real^3->bool`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2gf_dom")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXISTS_TAC `(kp:num->real^3->real^3) j y'` THEN
    SUBGOAL_THEN `(y':real^3) IN p2cg_dm rho j` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`p2cg_dm (rho:num->real)`; `p2cg_om (rho:num->real) D`;
                     `p2cg_tr (rho:num->real) D`; `j:num`; `NUMPAIR i q`; `y':real^3`] P2CL_TR_IN) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN CONJ_TAC THENL
     [EXISTS_TAC `y':real^3` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[p2gf_reg; IN_UNIONS; EXISTS_IN_GSPEC] THEN EXISTS_TAC `d:num` THEN
    SUBGOAL_THEN
     `p2gf_okp (P:num->num) d /\
      (?N. !n. N <= n ==> p2gf_adm (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) sq yc rho CG d ((t:num->num) n)) /\
      p2gf_bt d < s`
    (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[p2gf_okp] THEN REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        MAP_EVERY EXISTS_TAC [`i:num`; `q:num`] THEN ASM_REWRITE_TAC[];
        ASM_MESON_TAC[];
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `p2cg_tr (rho:num->real) D j (NUMPAIR i q) y'` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`p2cg_dm (rho:num->real)`; `p2cg_om (rho:num->real) D`;
                   `p2cg_tr (rho:num->real) D`; `j:num`; `NUMPAIR i q`; `y':real^3`] P2CL_TR_IN) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `p2cl_glue (p2cg_dm (rho:num->real)) (p2cg_om rho D) (p2cg_tr rho D)
                           (kp:num->real^3->real^3)` THEN
    REWRITE_TAC[p2cl_glue] THEN
    DISCH_THEN(MP_TAC o SPECL [`j:num`; `NUMPAIR i q`; `y':real^3`;
                               `p2cg_tr (rho:num->real) D j (NUMPAIR i q) y'`]) THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `lricci_flow O (p2gf_bt d) (&0)
                  (\s. metric_local (p2cl_atlas (p2cg_dm rho) kp) (p2cl_chart (p2cg_dm rho) kp j)
                         (p2gf_Gt (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                     (real->A->real^3^3)) yc rho P kp sq t r Gl s))` THEN
    REWRITE_TAC[p2gf_Gt];
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN REWRITE_TAC[p2gf_Gt]]);;

let P2GF_VL_REGULAR_G = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z rho K N0 B P yc sq D Gl kp CG t r.
     p2gf_fctx V U z rho K N0 B P yc sq D Gl kp CG t r
     ==> p2c_regular_view
           (p2gf_Vl (p2cl_top (p2cg_dm rho) kp) (p2cl_atlas (p2cg_dm rho) kp)
                    (p2cl_metric (p2cg_dm rho) kp Gl)
                    (p2gf_reg V sq yc rho CG P kp t)
                    (p2gf_Gf V (\k. sq (t (r k))) (p2gf_phi V yc rho P kp sq t r)
                             (p2cl_atlas (p2cg_dm rho) kp)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2GF_RVIEW_REGULAR THEN
  MATCH_MP_TAC P2GF_RVHYP_G THEN
  MAP_EVERY EXISTS_TAC [`U:num->A->bool`; `z:num->A`; `K:num->real`; `N0:num->num`;
                        `B:num->num->real`; `D:num#num->real^(3,3)finite_sum->real^1`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The region contains every X of the X-clause.  For p in X                  *)
(* and a < b <= 0: a deep CG chart (i,q) at p (P2GK_DEEP_PAIR_AT) with rho_i *)
(* small, so that the normal ball of radius rho_i/8 lies in phi_k(X)          *)
(* (P2GK_NEAR_BALL_IN, P2GK_SMALL_PIECE_IN), a dyadic start a < a0 < bt < b   *)
(* and an integer curvature bound give a candidate admissible at all t(r k)  *)
(* (P2GF_ADM_FROM_BALL), hence eventually admissible along t (dichotomy).     *)
(* Then X lies in every Omega s, a < s < 0, and X persists in the view.        *)
(* ------------------------------------------------------------------------- *)

let p2gf_vstd =
  [`\k. rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) k) (&0)`;
   `\k. rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                       (real->A->real^3^3)) k) (&0)`;
   `\k. rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                        (real->A->real^3^3)) k) (&0)`;
   `z:num->A`; `rho:num->real`; `K:num->real`; `N0:num->num`;
   `B:num->num->real`; `\j:num m:num. (N0:num->num) j`; `P:num->num`;
   `N0:num->num`; `yc:num->num->num->A`];;

let p2gf_vctx = p2gf_vstd @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `Gl:num->real^3->real^3^3`; `kp:num->real^3->real^3`];;

(* The persistence and curvature part of the X-clause of p2gf_vlpart. *)

let p2gf_xhyp = new_definition
 `p2gf_xhyp (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                  (real->A->real^3^3))
            (sub:num->num) (phi:num->real^3->A) (X:real^3->bool) a Kb N <=>
    !k. N <= k
        ==> rfs_persists (V (sub k)) (IMAGE (phi k) X) a (&0) /\
            !s y. a < s /\ s <= &0 /\ y IN IMAGE (phi k) X
                  ==> mfd_rm_norm (rfs_vatlas (V (sub k)) s) (rfs_vmetric (V (sub k)) s) y <= Kb`;;

(* Dyadic times a < -m1/2^e < -m2/2^e < b. *)

let P2GF_DYADIC_BETWEEN = prove
 (`!a b. a < b /\ b <= &0
         ==> ?e m1 m2. 0 < m2 /\ m2 < m1 /\
                       a < --(&m1 / &2 pow e) /\ --(&m2 / &2 pow e) < b`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`inv(&2)`; `(b - a) / &2`] REAL_ARCH_POW_INV) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `e:num`) THEN
  SUBGOAL_THEN `&0 < &2 pow e` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&2 < (b - a) * &2 pow e` ASSUME_TAC THENL
   [SUBGOAL_THEN `inv(&2 pow e) * &2 pow e < (b - a) / &2 * &2 pow e` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[GSYM REAL_POW_INV];
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `?n. --b * &2 pow e < &n` MP_TAC THENL
   [MP_TAC(SPEC `--b * &2 pow e + &1` REAL_ARCH_SIMPLE) THEN
    MATCH_MP_TAC MONO_EXISTS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "min"))) THEN
  SUBGOAL_THEN `&0 <= --b * &2 pow e` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&n <= --b * &2 pow e + &1` ASSUME_TAC THENL
   [USE_THEN "min" (MP_TAC o SPEC `n - 1`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_NOT_LT] THEN
    SUBGOAL_THEN `&n = &(n - 1) + &1` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`e:num`; `n + 1`; `n:num`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `x < --a ==> a < --x`) THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `--b < x ==> --x < b`) THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ]]);;

(* A bound c (x/8)^2 <= 1 from x S <= 1 and c <= S. *)

let P2GF_SMALL_SQ = prove
 (`!c S x. &0 <= c /\ c <= S /\ &0 < x /\ x < &1 /\ x * S <= &1
           ==> c * (x / &8) pow 2 <= &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `c * (x / &8) pow 2 <= S * (x / &8) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN `(x * S) * x <= &1 * x` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `S * (x / &8) pow 2 = ((x * S) * x) / &64` ASSUME_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Admissibility at one index from a ball of the CG chart inside a set Y    *)
(* that persists over (a,0] with abs Rm <= Kb.                                *)

let P2GF_ADM_FROM_BALL = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z rho K N0 B P yc sq D Gl kp CG t r d i q n (Y:A->bool) a Kb.
     p2gf_fctx V U z rho K N0 B P yc sq D Gl kp CG t r /\
     p2gf_ch d = NUMPAIR i q /\ p2gf_valid CG rho d /\ N0 i + N0 i <= sq n /\
     rfs_persists (V (sq n)) Y a (&0) /\ a <= p2gf_a0 d /\ Kb <= p2gf_K d /\
     (!s y. a < s /\ s <= &0 /\ y IN Y
            ==> mfd_rm_norm (rfs_vatlas (V (sq n)) s) (rfs_vmetric (V (sq n)) s) y <= Kb) /\
     rfs_vball (V (sq n)) (&0) (yc i (sq n) q) (p2gf_r0 rho d) SUBSET Y
     ==> p2gf_adm V sq yc rho CG d n`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "rm") (LABEL_TAC "sub"))))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GF_FCTX_FACTS) THEN
  MP_TAC(SPECL [`CG:real->real`; `rho:num->real`; `d:num`] P2GF_BT_NEG) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2gf_valid]) THEN
  SUBGOAL_THEN `&0 <= p2gf_K d` ASSUME_TAC THENL [REWRITE_TAC[p2gf_K; REAL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `p2gf_a0 d < &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `a < &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < p2gf_r0 (rho:num->real) d /\ p2gf_r0 rho d <= rho i` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[p2gf_r0] THEN ASM_REWRITE_TAC[NUMPAIR_DEST] THEN
    SUBGOAL_THEN `&1 <= &2 pow (p2gf_ri d)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE_1 THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (rho:num->real) i` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &2 pow (p2gf_ri d)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LE_LDIV_EQ] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o BETA_RULE o SPEC `(sq:num->num) n` o
              GEN_REWRITE_RULE I [p2gb_seq]) THEN
  MP_TAC(ISPECL (p2gf_vstd @ [`NUMPAIR i q`; `(sq:num->num) n`]) P2GB_CHART_OK) THEN
  ASM_REWRITE_TAC[p2cg_nv; NUMPAIR_DEST; p2cg_ctr] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open_in (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) ((sq:num->num) n)) (&0)) (Y:A->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_persists ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) ((sq:num->num) n)) (Y:A->bool) a (&0)` THEN
    REWRITE_TAC[P2CO_PERSISTS_ALT] THEN DISCH_THEN(MP_TAC o SPEC `&0`) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_inj_ball (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) ((sq:num->num) n)) (&0),rfs_vatlas (V (sq n)) (&0))
                 (rfs_vmetric (V (sq n)) (&0)) ((yc:num->num->num->A) i (sq n) q) (p2gf_r0 (rho:num->real) d)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_INJ_BALL_MONO THEN EXISTS_TAC `(rho:num->real) i` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `rfs_persists ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)) ((sq:num->num) n))
                 (rfs_vball (V (sq n)) (&0) ((yc:num->num->num->A) i (sq n) q) (p2gf_r0 (rho:num->real) d))
                 (p2gf_a0 d) (&0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2CD_PERSISTS_MONO THEN EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2CO_PERSISTS_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`Y:A->bool`; `&0`] THEN
    ASM_SIMP_TAC[P2CR_REGULAR_FROM_SMOOTH; REAL_LE_REFL; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[P2CO_VBALL] THEN MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s y. p2gf_a0 d < s /\ s <= &0 /\
          y IN rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)) ((sq:num->num) n)) (&0) ((yc:num->num->num->A) i (sq n) q)
                         (p2gf_r0 (rho:num->real) d)
          ==> mfd_rm_norm (rfs_vatlas (V (sq n)) s) (rfs_vmetric (V (sq n)) s) y <= p2gf_K d`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Kb:real` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "rm" MATCH_MP_TAC THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "sub" (MP_TAC o SPEC `y:A` o REWRITE_RULE[SUBSET]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p2gf_adm; p2cd_ok] THEN ASM_REWRITE_TAC[p2cg_ctr; NUMPAIR_DEST; REAL_LE_REFL]);;

(* The deep candidate at a point p of X. *)

let P2GF_DEEP_CAND = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z rho K N0 B P yc sq D Gl kp CG t r X a Kb N1 p b.
     p2gf_fctx V U z rho K N0 B P yc sq D Gl kp CG t r /\
     open_in (p2cl_top (p2cg_dm rho) kp) X /\
     p2gf_xhyp V (\k. sq (t (r k))) (p2gf_phi V yc rho P kp sq t r) X a Kb N1 /\
     p IN X /\ a < b /\ b <= &0
     ==> ?d i q w0. p2gf_ch d = NUMPAIR i q /\ q < P i /\ p2gf_ri d = 3 /\
                    (?N. !n. N <= n ==> p2gf_adm V sq yc rho CG d (t n)) /\
                    a < p2gf_a0 d /\ p2gf_bt d < b /\
                    w0 IN cball(vec 0,rho i / &32) /\ kp (NUMPAIR i q) w0 = p`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "X") STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GF_FCTX_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2gf_fctx]) THEN
  (* the small pieces at p lie in X *)
  MP_TAC(ISPECL (p2gf_vctx @ [`X:real^3->bool`; `p:real^3`]) P2GK_SMALL_PIECE_IN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "small"))) THEN
  (* an integer curvature bound *)
  MP_TAC(SPEC `max Kb (&0)` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `kb:num`) THEN
  SUBGOAL_THEN `&0 < (CG:real->real) (&kb)` ASSUME_TAC THENL
   [UNDISCH_TAC `p2gf_gauge (:A) (CG:real->real)` THEN REWRITE_TAC[p2gf_gauge] THEN
    DISCH_THEN(MP_TAC o SPEC `&kb`) THEN REWRITE_TAC[REAL_POS] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (CG:real->real) (&kb) + &kb + &1` ASSUME_TAC THENL
   [MP_TAC(SPEC `kb:num` REAL_POS) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* a level threshold *)
  SUBGOAL_THEN `?j0. !j. j0 <= j
                         ==> (rho:num->real) j < min e (min (&1) (inv((CG:real->real) (&kb) +
                                                                     &kb + &1)))`
  (X_CHOOSE_THEN `j0:num` (LABEL_TAC "j0")) THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `rho:num->real`)) (concl th) &&
      (try is_exists(snd(dest_imp(snd(dest_forall(concl th))))) with Failure _ -> false))) THEN
    REWRITE_TAC[REAL_LT_MIN; REAL_LT_01] THEN ASM_SIMP_TAC[REAL_LT_INV];
    ALL_TAC] THEN
  (* the deep pair at p *)
  SUBGOAL_THEN `(p:real^3) IN topspace(p2cl_top (p2cg_dm (rho:num->real)) (kp:num->real^3->real^3))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p2cl_top (p2cg_dm (rho:num->real)) (kp:num->real^3->real^3)`;
                   `X:real^3->bool`] OPEN_IN_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL (p2gf_vctx @ [`p:real^3`]) P2GK_DEEP_PAIR_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `j0:num`) THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `q:num` (X_CHOOSE_THEN `w0:real^3`
    STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `&0 < (rho:num->real) i` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(rho:num->real) i < e /\ rho i < &1 /\
                rho i * ((CG:real->real) (&kb) + &kb + &1) <= &1`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "j0" (MP_TAC o C MP (ASSUME `j0 <= (i:num)`) o SPEC `i:num`) THEN
    REWRITE_TAC[REAL_LT_MIN] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    SUBGOAL_THEN `(rho:num->real) i * ((CG:real->real) (&kb) + &kb + &1) <
                  inv(CG (&kb) + &kb + &1) * (CG (&kb) + &kb + &1)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE ((kp:num->real^3->real^3) (NUMPAIR i q)) (ball(vec 0,(rho:num->real) i / &6))
                SUBSET X` (LABEL_TAC "pieceX") THENL
   [USE_THEN "small" (MP_TAC o SPECL [`NUMPAIR i q`; `w0:real^3`]) THEN
    REWRITE_TAC[NUMPAIR_DEST] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* dyadic times *)
  MP_TAC(SPECL [`a:real`; `b:real`] P2GF_DYADIC_BETWEEN) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:num` (X_CHOOSE_THEN `m1:num` (X_CHOOSE_THEN `m2:num`
    STRIP_ASSUME_TAC))) THEN
  (* the candidate *)
  SUBGOAL_THEN `?d. p2gf_ch d = NUMPAIR i q /\ p2gf_ri d = 3 /\ p2gf_e d = e2 /\
                    p2gf_m1 d = m1 /\ p2gf_m2 d = m2 /\ p2gf_kb d = kb`
  (X_CHOOSE_THEN `d:num` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `NUMPAIR (NUMPAIR i q) (NUMPAIR 3 (NUMPAIR e2 (NUMPAIR m1 (NUMPAIR m2 kb))))` THEN
    REWRITE_TAC[p2gf_ch; p2gf_ri; p2gf_e; p2gf_m1; p2gf_m2; p2gf_kb; NUMPAIR_DEST];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2gf_r0 (rho:num->real) d = rho i / &8` (LABEL_TAC "r0") THENL
   [REWRITE_TAC[p2gf_r0] THEN ASM_REWRITE_TAC[NUMPAIR_DEST] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `p2gf_a0 d = --(&m1 / &2 pow e2) /\ p2gf_bt d = --(&m2 / &2 pow e2) /\
                p2gf_K d = &kb`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[p2gf_a0; p2gf_bt; p2gf_K]; ALL_TAC] THEN
  SUBGOAL_THEN `p2gf_valid CG (rho:num->real) d` ASSUME_TAC THENL
   [REWRITE_TAC[p2gf_valid] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONJ_TAC THEN MATCH_MP_TAC P2GF_SMALL_SQ THEN
    EXISTS_TAC `(CG:real->real) (&kb) + &kb + &1` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `kb:num` REAL_POS) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the CG balls lie in phi_k(X) *)
  SUBGOAL_THEN
   `?k2. !k. k2 <= k
             ==> rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) (sq (t (r k)))) (&0)
                           (yc i (sq (t (r k))) q) ((rho:num->real) i / &8) SUBSET
                 IMAGE (p2gf_phi V yc rho P kp sq t r k) X`
  (X_CHOOSE_THEN `k2:num` (LABEL_TAC "ballX")) THENL
   [MP_TAC(SPEC `(rho:num->real) i / &56` REAL_ARCH_INV) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    DISCH_THEN(X_CHOOSE_THEN `n0:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `n0 + i + N0 i + N0 (i:num)` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `i <= SUC k /\ inv(&k + &1) <= (rho:num->real) i / &56 /\
                  p2cg_nv N0 N0 (NUMPAIR i q) <= (sq:num->num) ((t:num->num) ((r:num->num) k))`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&n0)` THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
        REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
        REWRITE_TAC[p2cg_nv; NUMPAIR_DEST] THEN MATCH_MP_TAC LE_TRANS THEN
        EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL (p2gf_vctx @ [`k:num`; `(sq:num->num) ((t:num->num) ((r:num->num) k))`;
                               `p2gf_phi (V:num->(real->A topology)#
                                            (real->((A->bool)#(A->real^3))->bool)#
                                            (real->A->real^3^3)) yc rho P kp sq t r k`;
                               `i:num`; `q:num`]) P2GK_NEAR_BALL_IN) THEN
    REWRITE_TAC[p2gf_phi] THEN ASM_REWRITE_TAC[P2CO_VBALL] THEN
    MP_TAC(ISPECL [`vec 0:real^3`; `(rho:num->real) i / &7`; `(rho:num->real) i / &6`]
                  SUBSET_BALL) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "pieceX" MP_TAC THEN SET_TAC[];
    ALL_TAC] THEN
  (* admissible at all large t (r k) *)
  SUBGOAL_THEN `!k. N1 + k2 + N0 i + (N0:num->num) (i:num) <= k
                    ==> p2gf_adm (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) sq yc rho CG d (t ((r:num->num) k))`
  (LABEL_TAC "admk") THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "X" (MP_TAC o SPEC `k:num` o GEN_REWRITE_RULE I [p2gf_xhyp]) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; BETA_TAC THEN STRIP_TAC] THEN
    MP_TAC(ISPECL (p2gf_fstd @ [`d:num`; `i:num`; `q:num`; `(t:num->num) ((r:num->num) k)`;
                               `IMAGE (p2gf_phi (V:num->(real->A topology)#
                                                   (real->((A->bool)#(A->real^3))->bool)#
                                                   (real->A->real^3^3)) yc rho P kp sq t r k)
                                      (X:real^3->bool)`; `a:real`; `Kb:real`])
                  P2GF_ADM_FROM_BALL) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      USE_THEN "ballX" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[]];
    ALL_TAC] THEN
  (* eventually admissible along t by the dichotomy *)
  SUBGOAL_THEN `?N. !n. N <= n
                        ==> p2gf_adm (V:num->(real->A topology)#
                                        (real->((A->bool)#(A->real^3))->bool)#
                                        (real->A->real^3^3)) sq yc rho CG d ((t:num->num) n)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `d:num` o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2gf_fdich")) (concl th))) THEN
    REWRITE_TAC[p2gf_fdich] THEN
    DISCH_THEN(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[CONJUNCT1 th])
      (X_CHOOSE_THEN `N2:num` (LABEL_TAC "inadm"))) THEN
    USE_THEN "admk" (MP_TAC o SPEC `N2 + N1 + k2 + N0 i + (N0:num->num) (i:num)`) THEN
    ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    USE_THEN "inadm" (MP_TAC o SPEC `(r:num->num) (N2 + N1 + k2 + N0 i + (N0:num->num) (i:num))`) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `N2 + N1 + k2 + N0 i + (N0:num->num) (i:num)` THEN
      ASM_REWRITE_TAC[LE_ADD];
      MESON_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`d:num`; `i:num`; `q:num`; `w0:real^3`] THEN
  ASM_REWRITE_TAC[]);;

(* The converse of P2GF_RV_PERSISTS at the top time 0. *)

let P2GF_RV_PERSISTS_INTRO = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) Om Gf W a.
     p2gf_rvhyp top atlas g Om Gf /\ open_in top W /\
     (!s. a < s /\ s < &0 ==> W SUBSET Om s)
     ==> rfs_persists (p2gf_Vl top atlas g Om Gf) W a (&0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2gf_rvhyp; P2CO_PERSISTS_ALT; P2GF_VL_PARTS] THEN
  STRIP_TAC THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  ASM_CASES_TAC `s = &0` THEN ASM_REWRITE_TAC[REAL_LT_REFL] THEN
  SUBGOAL_THEN `s < &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT; OPEN_IN_OPEN_SUBTOPOLOGY]);;

(* X lies in the region at every time of (a,0]. *)

let P2GF_X_IN_REG = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z rho K N0 B P yc sq D Gl kp CG t r X a Kb N1 s.
     p2gf_fctx V U z rho K N0 B P yc sq D Gl kp CG t r /\
     open_in (p2cl_top (p2cg_dm rho) kp) X /\
     p2gf_xhyp V (\k. sq (t (r k))) (p2gf_phi V yc rho P kp sq t r) X a Kb N1 /\
     a < s /\ s <= &0
     ==> X SUBSET p2gf_reg V sq yc rho CG P kp t s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SUBSET] THEN X_GEN_TAC `p:real^3` THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL (p2gf_fstd @ [`X:real^3->bool`; `a:real`; `Kb:real`; `N1:num`; `p:real^3`;
                             `s:real`]) P2GF_DEEP_CAND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` (X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `q:num`
    (X_CHOOSE_THEN `w0:real^3` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GF_FCTX_FACTS) THEN
  SUBGOAL_THEN `&0 < (rho:num->real) i` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[p2gf_reg; UNIONS_GSPEC; IN_ELIM_THM] THEN EXISTS_TAC `d:num` THEN
  ASM_REWRITE_TAC[p2gf_okp; IN_IMAGE; LE_REFL] THEN CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`i:num`; `q:num`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `w0:real^3` THEN ASM_REWRITE_TAC[p2gf_dom; p2gf_r0; NUMPAIR_DEST; IN_BALL_0] THEN
  UNDISCH_TAC `(w0:real^3) IN cball(vec 0,(rho:num->real) i / &32)` THEN
  REWRITE_TAC[IN_CBALL_0] THEN ASM_REAL_ARITH_TAC);;

(* The flow on X: persistence in the region view and p2c_vflow. *)

let P2GF_X_VFLOW = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z rho K N0 B P yc sq D Gl kp CG t r X a Kb N1.
     p2gf_fctx V U z rho K N0 B P yc sq D Gl kp CG t r /\
     open_in (p2cl_top (p2cg_dm rho) kp) X /\
     p2gf_xhyp V (\k. sq (t (r k))) (p2gf_phi V yc rho P kp sq t r) X a Kb N1 /\ a < &0
     ==> rfs_persists
           (p2gf_Vl (p2cl_top (p2cg_dm rho) kp) (p2cl_atlas (p2cg_dm rho) kp)
                    (p2cl_metric (p2cg_dm rho) kp Gl)
                    (p2gf_reg V sq yc rho CG P kp t)
                    (p2gf_Gf V (\k. sq (t (r k))) (p2gf_phi V yc rho P kp sq t r)
                             (p2cl_atlas (p2cg_dm rho) kp))) X a (&0) /\
         p2c_vflow
           (p2gf_Vl (p2cl_top (p2cg_dm rho) kp) (p2cl_atlas (p2cg_dm rho) kp)
                    (p2cl_metric (p2cg_dm rho) kp Gl)
                    (p2gf_reg V sq yc rho CG P kp t)
                    (p2gf_Gf V (\k. sq (t (r k))) (p2gf_phi V yc rho P kp sq t r)
                             (p2cl_atlas (p2cg_dm rho) kp))) X a (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `rfs_persists
      (p2gf_Vl (p2cl_top (p2cg_dm (rho:num->real)) (kp:num->real^3->real^3))
               (p2cl_atlas (p2cg_dm rho) kp) (p2cl_metric (p2cg_dm rho) kp Gl)
               (p2gf_reg (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) sq yc rho CG P kp t)
               (p2gf_Gf V (\k. sq (t (r k))) (p2gf_phi V yc rho P kp sq t r)
                        (p2cl_atlas (p2cg_dm rho) kp))) X a (&0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2GF_RV_PERSISTS_INTRO THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2GF_RVHYP_G) THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN MATCH_MP_TAC P2GF_X_IN_REG THEN
    MAP_EVERY EXISTS_TAC [`U:num->A->bool`; `z:num->A`; `K:num->real`; `N0:num->num`;
                          `B:num->num->real`; `D:num#num->real^(3,3)finite_sum->real^1`;
                          `Gl:num->real^3->real^3^3`; `r:num->num`; `a:real`; `Kb:real`;
                          `N1:num`] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [p2c_regular_view] o
              MATCH_MP P2GF_VL_REGULAR_G) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The C^m convergence in the charts of the region view.                     *)
(* P2GF_PB_REP uniform in the chart and the time, the normal pullbacks are   *)
(* metric fields at all large indices, the transfer of lck_dist2 from the     *)
(* chart of the candidate to the preferred chart of the view (P2GF_LCK_CORE,  *)
(* the analogue of P2GE_LCK_TRANSFER for the times of the flow).               *)
(* ------------------------------------------------------------------------- *)

(* P2GF_PB_REP with a threshold that does not depend on the chart and time. *)

let P2GF_PB_REP_U = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z rho K N0 B P yc sq D Gl kp CG t r d i q.
     p2gf_fctx V U z rho K N0 B P yc sq D Gl kp CG t r /\
     p2gf_ch d = NUMPAIR i q /\ q < P i /\ 3 <= p2gf_ri d /\
     (?N. !n. N <= n ==> p2gf_adm V sq yc rho CG d (t n))
     ==> ?k0. !k j s y. k0 <= k /\ p2gf_a0 d < s /\ s <= &0 /\
                        y IN p2cg_om rho D j (NUMPAIR i q) /\
                        p2cg_tr rho D j (NUMPAIR i q) y IN p2gf_dom rho d
                        ==> rfs_pullback (rfs_vatlas (V (sq (t (r k)))) s)
                              (p2gf_phi V yc rho P kp sq t r k o kp j)
                              (rfs_vmetric (V (sq (t (r k)))) s) y =
                            mpullback (p2gf_S V yc rho P kp sq t r k (NUMPAIR i q) o
                                       p2cg_tr rho D j (NUMPAIR i q))
                                      (p2gf_H V sq yc d (t (r k)) s) y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `N:num` (LABEL_TAC "adm")))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GF_FCTX_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cl_system] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2cl_system")) (concl th))) THEN
  SUBGOAL_THEN `&0 < p2gf_r0 (rho:num->real) d` ASSUME_TAC THENL
   [REWRITE_TAC[p2gf_r0] THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `p2gf_r0 (rho:num->real) d / &2` REAL_ARCH_INV) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `n1:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `N + i + n1 + p2cg_nv (N0:num->num) N0 (NUMPAIR i q)` THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `j:num`; `s:real`; `y:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `N + i + n1 + p2cg_nv (N0:num->num) N0 (NUMPAIR i q) <= (r:num->num) k /\
                p2cg_nv (N0:num->num) N0 (NUMPAIR i q) <= (sq:num->num) ((t:num->num) (r k))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "adm" (MP_TAC o SPEC `(r:num->num) k`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[p2gf_adm] THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `U:num->A->bool`; `z:num->A`; `rho:num->real`; `K:num->real`; `N0:num->num`;
                 `B:num->num->real`; `P:num->num`; `yc:num->num->num->A`; `sq:num->num`;
                 `D:num#num->real^(3,3)finite_sum->real^1`; `Gl:num->real^3->real^3^3`;
                 `kp:num->real^3->real^3`; `CG:real->real`; `t:num->num`; `r:num->num`;
                 `d:num`; `i:num`; `q:num`; `j:num`; `y:real^3`] P2GF_TR_BALL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tb")))) THEN
  ABBREV_TAC `w = p2cg_tr (rho:num->real) D j (NUMPAIR i q) (y:real^3)` THEN
  SUBGOAL_THEN `(w:real^3) IN ball(vec 0,(rho:num->real) i / &6)` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN USE_THEN "tb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  (* the normal chart at the index *)
  ABBREV_TAC `nc = p2cd_phi ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) ((sq:num->num) ((t:num->num) ((r:num->num) k))))
                     (p2cg_ctr (yc:num->num->num->A) (sq (t (r k))) (NUMPAIR i q))
                     (p2cg_frm (\k. rfs_vmetric (V k) (&0)) yc (sq (t (r k))) (NUMPAIR i q))` THEN
  SUBGOAL_THEN
   `!y'. y' IN ball(y:real^3,e)
         ==> (p2gf_phi (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                          (real->A->real^3^3)) yc rho P kp sq t r k o kp j) y' =
             ((nc:real^3->A) o (p2gf_S V yc rho P kp sq t r k (NUMPAIR i q) o
                                 p2cg_tr rho D j (NUMPAIR i q))) y'`
  ASSUME_TAC THENL
   [X_GEN_TAC `y':real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(y':real^3) IN p2cg_om (rho:num->real) D j (NUMPAIR i q)` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(kp:num->real^3->real^3) j y' = kp (NUMPAIR i q)
                    (p2cg_tr (rho:num->real) D j (NUMPAIR i q) y')` SUBST1_TAC THENL
     [MP_TAC(ISPECL [`p2cg_dm (rho:num->real)`; `p2cg_om (rho:num->real) D`;
                     `p2cg_tr (rho:num->real) D`; `j:num`; `NUMPAIR i q`; `y':real^3`]
                    P2CL_TR_IN) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      UNDISCH_TAC `p2cl_glue (p2cg_dm (rho:num->real)) (p2cg_om rho D) (p2cg_tr rho D)
                             (kp:num->real^3->real^3)` THEN
      REWRITE_TAC[p2cl_glue] THEN
      DISCH_THEN(MP_TAC o SPECL [`j:num`; `NUMPAIR i q`; `y':real^3`;
                                 `p2cg_tr (rho:num->real) D j (NUMPAIR i q) y'`]) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                   `U:num->A->bool`; `z:num->A`; `rho:num->real`; `K:num->real`; `N0:num->num`;
                   `B:num->num->real`; `P:num->num`; `yc:num->num->num->A`; `sq:num->num`;
                   `D:num#num->real^(3,3)finite_sum->real^1`; `Gl:num->real^3->real^3^3`;
                   `kp:num->real^3->real^3`; `CG:real->real`; `t:num->num`; `r:num->num`;
                   `k:num`; `i:num`; `q:num`;
                   `p2cg_tr (rho:num->real) D j (NUMPAIR i q) y'`] P2GF_S_REP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "tb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN EXPAND_TAC "nc" THEN
    REWRITE_TAC[P2GF_NCH_PHI];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) ((sq:num->num) ((t:num->num) ((r:num->num) k)))) s`;
                 `p2gf_phi (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) yc rho P kp sq t r k o kp j`;
                 `(nc:real^3->A) o (p2gf_S (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                              (real->A->real^3^3)) yc rho P kp sq t r k (NUMPAIR i q) o
                                     p2cg_tr rho D j (NUMPAIR i q))`;
                 `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) ((sq:num->num) ((t:num->num) ((r:num->num) k)))) s`;
                 `ball(y:real^3,e)`; `y:real^3`] P2CE_RFS_LOCAL) THEN
  ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[p2gf_H] THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "nc" THEN
  MATCH_MP_TAC P2GF_PB_CHAIN_S THEN
  MAP_EVERY EXISTS_TAC [`p2gf_r0 (rho:num->real) d`; `p2gf_r0 (rho:num->real) d`;
                        `p2gf_a0 d`; `p2gf_K d`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `p2cg_om (rho:num->real) D j (NUMPAIR i q)` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `ball(vec 0:real^3,(rho:num->real) i / &6)` THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN MATCH_MP_TAC P2GF_S_SMOOTH THEN
      MAP_EVERY EXISTS_TAC [`U:num->A->bool`; `z:num->A`; `K:num->real`; `N0:num->num`;
                            `B:num->num->real`; `D:num#num->real^(3,3)finite_sum->real^1`;
                            `Gl:num->real^3->real^3^3`; `CG:real->real`] THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[o_THM] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `U:num->A->bool`; `z:num->A`; `rho:num->real`; `K:num->real`; `N0:num->num`;
                 `B:num->num->real`; `P:num->num`; `yc:num->num->num->A`; `sq:num->num`;
                 `D:num#num->real^(3,3)finite_sum->real^1`; `Gl:num->real^3->real^3^3`;
                 `kp:num->real^3->real^3`; `CG:real->real`; `t:num->num`; `r:num->num`;
                 `k:num`; `i:num`; `q:num`; `w:real^3`] P2GF_S_C0) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `(w:real^3) IN ball(vec 0,(rho:num->real) i / &6)` THEN
    REWRITE_TAC[IN_BALL_0; IN_CBALL_0] THEN
    UNDISCH_TAC `(w:real^3) IN p2gf_dom rho d` THEN
    ASM_REWRITE_TAC[p2gf_dom; p2gf_r0; IN_BALL_0; NUMPAIR_DEST] THEN
    SUBGOAL_THEN `&8 <= &2 pow (p2gf_ri d)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 pow 3` THEN CONJ_TAC THENL
       [CONV_TAC REAL_RAT_REDUCE_CONV; MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (rho:num->real) i` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SPEC_TAC(`&2 pow (p2gf_ri d)`,`qq:real`) THEN SPEC_TAC(`(rho:num->real) i`,`x:real`) THEN
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `x / qq <= x / &8` MP_TAC THENL
     [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC[IN_BALL_0] THEN
  UNDISCH_TAC `(w:real^3) IN p2gf_dom rho d` THEN REWRITE_TAC[p2gf_dom; IN_BALL_0] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `inv(&k + &1) <= inv(&n1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2gf_S (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) yc rho P kp sq t r k (NUMPAIR i q) w`;
                 `w:real^3`] NORM_TRIANGLE_SUB) THEN
  ASM_REAL_ARITH_TAC);;
(* The normal pullbacks are metric fields on the candidate domain at all    *)
(* large indices of the final diagonal, uniformly in the time.               *)

let P2GF_H_FIELD = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z rho K N0 B P yc sq D Gl kp CG t r d.
     p2gf_fctx V U z rho K N0 B P yc sq D Gl kp CG t r /\
     (?N. !n. N <= n ==> p2gf_adm V sq yc rho CG d (t n))
     ==> ?k0. !k s. k0 <= k /\ p2gf_bt d <= s /\ s <= &0
                    ==> metric_field (p2gf_dom rho d) (p2gf_H V sq yc d (t (r k)) s)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `N:num` (LABEL_TAC "adm"))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GF_FCTX_FACTS) THEN
  SUBGOAL_THEN `p2gf_gauge (:A) (CG:real->real)` ASSUME_TAC THENL
   [UNDISCH_TAC `p2gf_fctx (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) U z rho K N0 B P yc sq D Gl kp CG t r` THEN
    REWRITE_TAC[p2gf_fctx] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`; `sq:num->num`; `yc:num->num->num->A`; `rho:num->real`;
                 `CG:real->real`; `d:num`; `\n. (t:num->num) (n + N)`] P2GF_SEQHYP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:num` THEN USE_THEN "adm" MATCH_MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[p2ca_seqhyp] THEN DISCH_THEN(LABEL_TAC "mf" o CONJUNCT1) THEN
  EXISTS_TAC `N:num` THEN MAP_EVERY X_GEN_TAC [`k:num`; `s:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(r:num->num) k = (r k - N) + N` SUBST1_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `(N:num) <= r ==> r = (r - N) + N`) THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "mf" (MP_TAC o SPECL [`(r:num->num) k - N`; `s:real`]) THEN
  ASM_REWRITE_TAC[]);;

(* The core of the transfer: two representatives that are pullbacks by the  *)
(* chart transition Tr j a on an open set O have the lck_dist2 of the        *)
(* candidate chart (LCK_DIST2_PULLBACK; Sk near the identity, a diffeo).      *)

let P2GF_LCK_CORE = prove
 (`!(Dm:num->real^3->bool) Om Tr j a (Gs:real^3->real^3^3) Hs (Sk:real^3->real^3) R' W w s0
    O (MA:real^3->real^3^3) PB m v.
     p2cl_system Dm Om Tr /\
     metric_field W Gs /\ metric_field W Hs /\ &0 < s0 /\ ball(w,s0) SUBSET W /\
     diffeomorphism_on (ball(w,s0)) (IMAGE Sk (ball(w,s0))) Sk R' /\
     IMAGE Sk (ball(w,s0)) SUBSET W /\
     open O /\ v IN O /\ O SUBSET Om j a /\ IMAGE (Tr j a) O SUBSET ball(w,s0) /\
     (!y. y IN O ==> MA y = mpullback (Tr j a) Gs y) /\
     (!y. y IN O ==> PB y = mpullback (Sk o Tr j a) Hs y)
     ==> lck_dist2 m MA PB v = lck_dist2 m Gs (mpullback Sk Hs) (Tr j a v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cl_system]) THEN
  MP_TAC(ISPECL [`Dm:num->real^3->bool`; `Om:num->num->real^3->bool`;
                 `Tr:num->num->real^3->real^3`; `j:num`; `a:num`; `O:real^3->bool`]
                P2CE_TR_DIFFEO) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `diffeomorphism_on O (IMAGE ((Tr:num->num->real^3->real^3) j a) O)
                                  (Tr j a) (Tr a j)` ASSUME_TAC THENL
   [MATCH_MP_TAC DIFFEOMORPHISM_ON_SYM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (Sk:real^3->real^3) (ball(w,s0))) /\
                smooth_map_on (ball(w:real^3,s0)) Sk`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on (ball(w:real^3,s0)) (IMAGE (Sk:real^3->real^3) (ball(w,s0)))
                                   Sk (R':real^3->real^3)` THEN
    SIMP_TAC[diffeomorphism_on];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (IMAGE ((Tr:num->num->real^3->real^3) j a) O) Gs /\
                metric_field (IMAGE ((Tr:num->num->real^3->real^3) j a) O)
                             (mpullback (Sk:real^3->real^3) Hs)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `W:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `ball(w:real^3,s0)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
      MAP_EVERY EXISTS_TAC [`IMAGE (Sk:real^3->real^3) (ball(w,s0))`; `R':real^3->real^3`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
      EXISTS_TAC `W:real^3->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `lck_dist2 m (mpullback ((Tr:num->num->real^3->real^3) j a) Gs)
                          (mpullback (Tr j a) (mpullback (Sk:real^3->real^3) Hs)) v` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LCK_DIST2_LOCAL THEN EXISTS_TAC `O:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2CE_MPULLBACK_CHAIN THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `(Om:num->num->real^3->bool) j a` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `ball(w:real^3,s0)` THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN ASM SET_TAC[]];
    MP_TAC(ISPECL [`m:num`; `IMAGE ((Tr:num->num->real^3->real^3) j a) O`; `O:real^3->bool`;
                   `(Tr:num->num->real^3->real^3) j a`; `(Tr:num->num->real^3->real^3) a j`;
                   `Gs:real^3->real^3^3`; `mpullback (Sk:real^3->real^3) Hs`; `v:real^3`]
                  LCK_DIST2_PULLBACK) THEN
    ASM_REWRITE_TAC[]]);;

(* The transfer at a time s < 0: the preferred chart of the restricted atlas *)
(* of the region (generic glued limit).                                      *)

let P2GF_TRANSFER_NEG = prove
 (`!(Dm:num->real^3->bool) Om Tr (kp:num->real^3->real^3) a Os (Gf:real^3->real^3^3)
    (Gs:real^3->real^3^3) Hs (Sk:real^3->real^3) R' W w s0
    (atl:((A->bool)#(A->real^3))->bool) (gm:A->real^3^3) (Fk:real^3->A) m.
     p2cl_system Dm Om Tr /\ p2cl_glue Dm Om Tr kp /\
     smooth_manifold_atlas (p2cl_top Dm kp) (p2cl_atlas Dm kp) /\
     open_in (p2cl_top Dm kp) Os /\ kp a w IN Os /\ w IN Dm a /\
     metric_field W Gs /\ metric_field W Hs /\ &0 < s0 /\ ball(w,s0) SUBSET W /\
     diffeomorphism_on (ball(w,s0)) (IMAGE Sk (ball(w,s0))) Sk R' /\
     IMAGE Sk (ball(w,s0)) SUBSET W /\
     (!c y. y IN Om c a /\ Tr c a y IN ball(w,s0)
            ==> metric_local (p2cl_atlas Dm kp) (p2cl_chart Dm kp c) Gf y =
                mpullback (Tr c a) Gs y) /\
     (!c y. y IN Om c a /\ Tr c a y IN ball(w,s0)
            ==> rfs_pullback atl (Fk o kp c) gm y = mpullback (Sk o Tr c a) Hs y)
     ==> lck_dist2 m
           (metric_local (restrict_atlas (p2cl_atlas Dm kp) Os)
              (chart_at (restrict_atlas (p2cl_atlas Dm kp) Os) (kp a w))
              (restrict_metric (p2cl_atlas Dm kp) Os Gf))
           (rfs_pullback atl
              (Fk o chart_inv (chart_at (restrict_atlas (p2cl_atlas Dm kp) Os) (kp a w))) gm)
           (SND(chart_at (restrict_atlas (p2cl_atlas Dm kp) Os) (kp a w)) (kp a w)) =
         lck_dist2 m Gs (mpullback Sk Hs) w`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "gf") (LABEL_TAC "pb")))))))))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cl_system]) THEN
  MP_TAC(ISPECL [`p2cl_top (Dm:num->real^3->bool) (kp:num->real^3->real^3)`;
                 `p2cl_atlas (Dm:num->real^3->bool) (kp:num->real^3->real^3)`;
                 `Os:real^3->bool`; `(kp:num->real^3->real^3) a w`] MFDR_CHART_AT_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Uc:real^3->bool` (X_CHOOSE_THEN `phi:real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `?c. Uc = FST(p2cl_chart (Dm:num->real^3->bool) (kp:num->real^3->real^3) c) /\
                    phi = SND(p2cl_chart Dm kp c)`
  (X_CHOOSE_THEN `c:num` (CONJUNCTS_THEN SUBST_ALL_TAC)) THENL
   [UNDISCH_TAC `(Uc:real^3->bool,(phi:real^3->real^3)) IN
                 p2cl_atlas (Dm:num->real^3->bool) (kp:num->real^3->real^3)` THEN
    REWRITE_TAC[P2CL_IN_ATLAS_ALT] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:num` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[FST; SND];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `p2cl_chart (Dm:num->real^3->bool) (kp:num->real^3->real^3) c IN p2cl_atlas Dm kp`
  ASSUME_TAC THENL [REWRITE_TAC[P2CL_IN_ATLAS_ALT] THEN MESON_TAC[]; ALL_TAC] THEN
  (* the coordinate of the point in the chart c *)
  SUBGOAL_THEN `?v. v IN (Dm:num->real^3->bool) c /\ (kp:num->real^3->real^3) c v = kp a w`
  (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THENL
   [UNDISCH_TAC `(kp:num->real^3->real^3) a w IN FST(p2cl_chart (Dm:num->real^3->bool) kp c)` THEN
    REWRITE_TAC[P2CL_CHART_FST; IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^3) IN (Om:num->num->real^3->bool) a c /\
                (Tr:num->num->real^3->real^3) a c w = v`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2cl_glue (Dm:num->real^3->bool) Om Tr (kp:num->real^3->real^3)` THEN
    REWRITE_TAC[p2cl_glue] THEN
    DISCH_THEN(MP_TAC o SPECL [`a:num`; `c:num`; `w:real^3`; `v:real^3`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^3) IN (Om:num->num->real^3->bool) c a /\
                (Tr:num->num->real^3->real^3) c a v = w`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `SND(p2cl_chart (Dm:num->real^3->bool) (kp:num->real^3->real^3) c) (kp a w) = v`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(kp:num->real^3->real^3) c v = kp a w`)) THEN
    MATCH_MP_TAC P2CL_CHART_INV THEN
    MAP_EVERY EXISTS_TAC [`Om:num->num->real^3->bool`; `Tr:num->num->real^3->real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the open set of the core *)
  ABBREV_TAC `O = {y | y IN (Om:num->num->real^3->bool) c a /\
                       (Tr:num->num->real^3->real^3) c a y IN ball(w,s0)} INTER
                  IMAGE (SND(p2cl_chart (Dm:num->real^3->bool) (kp:num->real^3->real^3) c))
                        (FST(p2cl_chart Dm kp c) INTER Os)` THEN
  SUBGOAL_THEN `open (O:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_SIMP_TAC[OPEN_BALL] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[ETA_AX];
      MATCH_MP_TAC P2GF_CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`p2cl_top (Dm:num->real^3->bool) (kp:num->real^3->real^3)`;
                            `p2cl_atlas (Dm:num->real^3->bool) (kp:num->real^3->real^3)`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN O
                    ==> y IN (Om:num->num->real^3->bool) c a /\
                        (Tr:num->num->real^3->real^3) c a y IN ball(w,s0) /\
                        ?x. x IN FST(p2cl_chart (Dm:num->real^3->bool) (kp:num->real^3->real^3) c) /\
                            x IN Os /\ y = SND(p2cl_chart Dm kp c) x`
  (LABEL_TAC "inO") THENL
   [EXPAND_TAC "O" THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^3) IN O` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_IMAGE] THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN EXISTS_TAC `(kp:num->real^3->real^3) a w` THEN
    ASM_REWRITE_TAC[IN_INTER] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(kp:num->real^3->real^3) c v = kp a w`)) THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2CL_CHART_INV THEN
    MAP_EVERY EXISTS_TAC [`Om:num->num->real^3->bool`; `Tr:num->num->real^3->real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* chart_inv of the restricted chart on O *)
  SUBGOAL_THEN
   `!y. y IN O ==> chart_inv (FST(p2cl_chart (Dm:num->real^3->bool) (kp:num->real^3->real^3) c)
                                INTER Os,SND(p2cl_chart Dm kp c)) y = kp c y`
  (LABEL_TAC "cinv") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "inO" (MP_TAC o C MP (ASSUME `(y:real^3) IN O`) o SPEC `y:real^3`) THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC o CONJUNCT2 o CONJUNCT2) THEN
    UNDISCH_TAC `(x:real^3) IN FST(p2cl_chart (Dm:num->real^3->bool) (kp:num->real^3->real^3) c)` THEN
    REWRITE_TAC[P2CL_CHART_FST; IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
    SUBGOAL_THEN `SND(p2cl_chart (Dm:num->real^3->bool) (kp:num->real^3->real^3) c) (kp c u) = u`
    ASSUME_TAC THENL
     [MATCH_MP_TAC P2CL_CHART_INV THEN
      MAP_EVERY EXISTS_TAC [`Om:num->num->real^3->bool`; `Tr:num->num->real^3->real^3`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `y:real^3 = u` SUBST_ALL_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`p2cl_top (Dm:num->real^3->bool) (kp:num->real^3->real^3)`;
                   `p2cl_atlas (Dm:num->real^3->bool) (kp:num->real^3->real^3)`;
                   `FST(p2cl_chart (Dm:num->real^3->bool) (kp:num->real^3->real^3) c)`;
                   `SND(p2cl_chart (Dm:num->real^3->bool) (kp:num->real^3->real^3) c)`;
                   `Os:real^3->bool`; `(kp:num->real^3->real^3) c u`] MFDR_CHART_INV_RESTRICT) THEN
    ASM_SIMP_TAC[IN_INTER; PAIR; P2CL_CHART_FST; FUN_IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN `O SUBSET (Om:num->num->real^3->bool) c a /\
                IMAGE ((Tr:num->num->real^3->real^3) c a) O SUBSET ball(w,s0)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      USE_THEN "inO" (MP_TAC o C MP (ASSUME `(y:real^3) IN O`) o SPEC `y:real^3`) THEN
      SIMP_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      USE_THEN "inO" (MP_TAC o C MP (ASSUME `(y:real^3) IN O`) o SPEC `y:real^3`) THEN
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN O
        ==> metric_local (restrict_atlas (p2cl_atlas (Dm:num->real^3->bool) (kp:num->real^3->real^3)) Os)
              (FST(p2cl_chart Dm kp c) INTER Os,SND(p2cl_chart Dm kp c))
              (restrict_metric (p2cl_atlas Dm kp) Os (Gf:real^3->real^3^3)) y =
            mpullback ((Tr:num->num->real^3->real^3) c a) Gs y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "inO" (MP_TAC o C MP (ASSUME `(y:real^3) IN O`) o SPEC `y:real^3`) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `x:real^3` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (ASSUME_TAC o SYM)))))) THEN
    MP_TAC(ISPECL [`p2cl_top (Dm:num->real^3->bool) (kp:num->real^3->real^3)`;
                   `p2cl_atlas (Dm:num->real^3->bool) (kp:num->real^3->real^3)`;
                   `FST(p2cl_chart (Dm:num->real^3->bool) (kp:num->real^3->real^3) c)`;
                   `SND(p2cl_chart (Dm:num->real^3->bool) (kp:num->real^3->real^3) c)`;
                   `Os:real^3->bool`; `Gf:real^3->real^3^3`; `y:real^3`]
                  P2CF_METRIC_LOCAL_RESTRICT_ON) THEN
    ASM_REWRITE_TAC[PAIR] THEN ANTS_TAC THENL
     [REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "gf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN O
        ==> rfs_pullback (atl:((A->bool)#(A->real^3))->bool)
              ((Fk:real^3->A) o
               chart_inv (FST(p2cl_chart (Dm:num->real^3->bool) (kp:num->real^3->real^3) c)
                          INTER Os,SND(p2cl_chart Dm kp c))) (gm:A->real^3^3) y =
            mpullback ((Sk:real^3->real^3) o (Tr:num->num->real^3->real^3) c a) Hs y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "inO" (MP_TAC o C MP (ASSUME `(y:real^3) IN O`) o SPEC `y:real^3`) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o CONJUNCT1)) THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `rfs_pullback (atl:((A->bool)#(A->real^3))->bool)
                  ((Fk:real^3->A) o (kp:num->real^3->real^3) c) (gm:A->real^3^3) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2CE_RFS_LOCAL THEN EXISTS_TAC `O:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `y':real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
      AP_TERM_TAC THEN USE_THEN "cinv" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "pb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `lck_dist2 m (Gs:real^3->real^3^3) (mpullback (Sk:real^3->real^3) Hs)
                        ((Tr:num->num->real^3->real^3) c a v)` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC P2GF_LCK_CORE THEN
  MAP_EVERY EXISTS_TAC [`Dm:num->real^3->bool`; `Om:num->num->real^3->bool`; `R':real^3->real^3`;
                        `W:real^3->bool`; `w:real^3`; `s0:real`; `O:real^3->bool`] THEN
  ASM_REWRITE_TAC[]);;

(* The transfer at the time 0: the preferred chart of the glued atlas.      *)

let P2GF_TRANSFER_ZERO = prove
 (`!(Dm:num->real^3->bool) Om Tr (kp:num->real^3->real^3) a (g:real^3->real^3^3)
    (Gs:real^3->real^3^3) Hs (Sk:real^3->real^3) R' W w s0
    (atl:((A->bool)#(A->real^3))->bool) (gm:A->real^3^3) (Fk:real^3->A) m.
     p2cl_system Dm Om Tr /\ p2cl_glue Dm Om Tr kp /\ w IN Dm a /\
     metric_field W Gs /\ metric_field W Hs /\ &0 < s0 /\ ball(w,s0) SUBSET W /\
     diffeomorphism_on (ball(w,s0)) (IMAGE Sk (ball(w,s0))) Sk R' /\
     IMAGE Sk (ball(w,s0)) SUBSET W /\
     (!c y. y IN Om c a /\ Tr c a y IN ball(w,s0)
            ==> metric_local (p2cl_atlas Dm kp) (p2cl_chart Dm kp c) g y =
                mpullback (Tr c a) Gs y) /\
     (!c y. y IN Om c a /\ Tr c a y IN ball(w,s0)
            ==> rfs_pullback atl (Fk o kp c) gm y = mpullback (Sk o Tr c a) Hs y)
     ==> lck_dist2 m
           (metric_local (p2cl_atlas Dm kp) (chart_at (p2cl_atlas Dm kp) (kp a w)) g)
           (rfs_pullback atl (Fk o chart_inv (chart_at (p2cl_atlas Dm kp) (kp a w))) gm)
           (SND(chart_at (p2cl_atlas Dm kp) (kp a w)) (kp a w)) =
         lck_dist2 m Gs (mpullback Sk Hs) w`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "gf") (LABEL_TAC "pb"))))))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cl_system]) THEN
  MP_TAC(ISPECL [`Dm:num->real^3->bool`; `Om:num->num->real^3->bool`;
                 `Tr:num->num->real^3->real^3`; `kp:num->real^3->real^3`; `a:num`; `w:real^3`]
                P2CL_CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(Tr:num->num->real^3->real^3) a c w IN (Om:num->num->real^3->bool) c a /\
                Tr c a (Tr a c w) = w` STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `O = {y | y IN (Om:num->num->real^3->bool) c a /\
                       (Tr:num->num->real^3->real^3) c a y IN ball(w,s0)}` THEN
  SUBGOAL_THEN `open (O:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_SIMP_TAC[OPEN_BALL] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN O <=> y IN (Om:num->num->real^3->bool) c a /\
                               (Tr:num->num->real^3->real^3) c a y IN ball(w,s0)`
  (LABEL_TAC "inO") THENL
   [EXPAND_TAC "O" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `(Tr:num->num->real^3->real^3) a c w IN O /\
                O SUBSET (Om:num->num->real^3->bool) c a /\
                IMAGE ((Tr:num->num->real^3->real^3) c a) O SUBSET ball(w,s0)`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "inO" (fun th -> REWRITE_TAC[th; SUBSET; FORALL_IN_IMAGE]) THEN
    ASM_SIMP_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN O
        ==> metric_local (p2cl_atlas (Dm:num->real^3->bool) (kp:num->real^3->real^3))
              (p2cl_chart Dm kp c) (g:real^3->real^3^3) y =
            mpullback ((Tr:num->num->real^3->real^3) c a) Gs y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN USE_THEN "inO" (fun th -> REWRITE_TAC[th]) THEN
    STRIP_TAC THEN USE_THEN "gf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN O
        ==> rfs_pullback (atl:((A->bool)#(A->real^3))->bool)
              ((Fk:real^3->A) o chart_inv (p2cl_chart (Dm:num->real^3->bool)
                                                       (kp:num->real^3->real^3) c))
              (gm:A->real^3^3) y =
            mpullback ((Sk:real^3->real^3) o (Tr:num->num->real^3->real^3) c a) Hs y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `rfs_pullback (atl:((A->bool)#(A->real^3))->bool)
                  ((Fk:real^3->A) o (kp:num->real^3->real^3) c) (gm:A->real^3^3) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2CE_RFS_LOCAL THEN EXISTS_TAC `O:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `y':real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN
      MATCH_MP_TAC P2CL_CHART_INVERSE THEN
      MAP_EVERY EXISTS_TAC [`Om:num->num->real^3->bool`; `Tr:num->num->real^3->real^3`] THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      UNDISCH_TAC `(y:real^3) IN O` THEN USE_THEN "inO" (fun th -> REWRITE_TAC[th]) THEN
      STRIP_TAC THEN USE_THEN "pb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `lck_dist2 m (Gs:real^3->real^3^3) (mpullback (Sk:real^3->real^3) Hs)
                        ((Tr:num->num->real^3->real^3) c a (Tr a c w))` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC P2GF_LCK_CORE THEN
  MAP_EVERY EXISTS_TAC [`Dm:num->real^3->bool`; `Om:num->num->real^3->bool`; `R':real^3->real^3`;
                        `W:real^3->bool`; `w:real^3`; `s0:real`; `O:real^3->bool`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The X-clause convergence.  The region view of the flow                   *)
(* (p2gf_VL), the lck_dist2 of the X-clause in its preferred charts         *)
(* (p2gf_lckv), its transfer to the candidate chart at every time of         *)
(* (bt d,0] (P2GF_TRANSFER_NEG for s < 0, P2GF_TRANSFER_ZERO for s = 0).     *)
(* ------------------------------------------------------------------------- *)

let p2gf_VL = new_definition
 `p2gf_VL (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                (real->A->real^3^3))
          (yc:num->num->num->A) (rho:num->real) (P:num->num) (kp:num->real^3->real^3)
          (sq:num->num) (t:num->num) (r:num->num) (CG:real->real) (Gl:num->real^3->real^3^3) =
    p2gf_Vl (p2cl_top (p2cg_dm rho) kp) (p2cl_atlas (p2cg_dm rho) kp)
            (p2cl_metric (p2cg_dm rho) kp Gl) (p2gf_reg V sq yc rho CG P kp t)
            (p2gf_Gf V (\k. sq (t (r k))) (p2gf_phi V yc rho P kp sq t r)
                     (p2cl_atlas (p2cg_dm rho) kp))`;;

let p2gf_lckv = new_definition
 `p2gf_lckv (Vl:(real->(real^3)topology)#(real->((real^3->bool)#(real^3->real^3))->bool)#
                 (real->real^3->real^3^3))
            (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3))
            (sub:num->num) (phi:num->real^3->A) m k s y =
    lck_dist2 m
      (metric_local (rfs_vatlas Vl s) (chart_at (rfs_vatlas Vl s) y) (rfs_vmetric Vl s))
      (rfs_pullback (rfs_vatlas (V (sub k)) s)
         (phi k o chart_inv (chart_at (rfs_vatlas Vl s) y)) (rfs_vmetric (V (sub k)) s))
      (SND(chart_at (rfs_vatlas Vl s) y) y)`;;

(* The transfer for the region view at a time s of (bt d,0]. *)

let P2GF_LCK_TRANSFER_S = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z rho K N0 B P yc sq D Gl kp CG t r d i q G k s w s0 R' m.
     p2gf_fctx V U z rho K N0 B P yc sq D Gl kp CG t r /\
     p2gf_ch d = NUMPAIR i q /\ q < P i /\ 3 <= p2gf_ri d /\
     (?N. !n. N <= n ==> p2gf_adm V sq yc rho CG d (t n)) /\
     p2gf_lim (p2gf_dom rho d) (p2gf_bt d) (&0) (\n. p2gf_H V sq yc d (t n)) G /\
     (!j s y. p2gf_a0 d < s /\ s <= &0 /\ y IN p2cg_om rho D j (NUMPAIR i q) /\
              p2cg_tr rho D j (NUMPAIR i q) y IN p2gf_dom rho d
              ==> rfs_pullback (rfs_vatlas (V (sq (t (r k)))) s)
                    (p2gf_phi V yc rho P kp sq t r k o kp j) (rfs_vmetric (V (sq (t (r k)))) s) y =
                  mpullback (p2gf_S V yc rho P kp sq t r k (NUMPAIR i q) o
                             p2cg_tr rho D j (NUMPAIR i q))
                            (p2gf_H V sq yc d (t (r k)) s) y) /\
     metric_field (p2gf_dom rho d) (p2gf_H V sq yc d (t (r k)) s) /\
     p2gf_bt d < s /\ s <= &0 /\ w IN p2gf_dom rho d /\
     &0 < s0 /\ ball(w,s0) SUBSET p2gf_dom rho d /\
     diffeomorphism_on (ball(w,s0))
       (IMAGE (p2gf_S V yc rho P kp sq t r k (NUMPAIR i q)) (ball(w,s0)))
       (p2gf_S V yc rho P kp sq t r k (NUMPAIR i q)) R' /\
     IMAGE (p2gf_S V yc rho P kp sq t r k (NUMPAIR i q)) (ball(w,s0)) SUBSET p2gf_dom rho d
     ==> p2gf_lckv (p2gf_VL V yc rho P kp sq t r CG Gl) V (\k. sq (t (r k)))
                   (p2gf_phi V yc rho P kp sq t r) m k s (kp (NUMPAIR i q) w) =
         lck_dist2 m (G s) (mpullback (p2gf_S V yc rho P kp sq t r k (NUMPAIR i q))
                                      (p2gf_H V sq yc d (t (r k)) s)) w`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "pb") (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GF_FCTX_FACTS) THEN
  SUBGOAL_THEN `smooth_manifold_atlas (p2cl_top (p2cg_dm (rho:num->real)) (kp:num->real^3->real^3))
                                      (p2cl_atlas (p2cg_dm rho) kp)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP P2GF_RVHYP_G) THEN REWRITE_TAC[p2gf_rvhyp] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2gf_a0 d < p2gf_bt d` ASSUME_TAC THENL
   [FIRST_ASSUM(X_CHOOSE_THEN `N1:num` (MP_TAC o SPEC `N1:num`) o check (fun th ->
      is_exists(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2gf_adm")) (concl th))) THEN
    REWRITE_TAC[LE_REFL; p2gf_adm] THEN DISCH_THEN(MP_TAC o MATCH_MP P2GF_BT_NEG o CONJUNCT1) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s'. p2gf_bt d <= s' /\ s' <= &0
                     ==> metric_field (p2gf_dom rho d) ((G:real->real^3->real^3^3) s')`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p2gf_lim (p2gf_dom rho d) (p2gf_bt d) (&0)
                   (\n. p2gf_H (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) sq yc d (t n)) G` THEN
    REWRITE_TAC[p2gf_lim; p2ca_loclim] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^3) IN p2cg_dm rho (NUMPAIR i q)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`rho:num->real`; `d:num`; `i:num`; `q:num`; `w:real^3`] P2GF_DOM_SMALL) THEN
    ASM_REWRITE_TAC[p2cg_dm; NUMPAIR_DEST; IN_BALL_0] THEN
    SUBGOAL_THEN `&0 < (rho:num->real) i` MP_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[p2gf_lckv; p2gf_VL; P2GF_VL_PARTS] THEN
  ASM_CASES_TAC `s = &0` THENL
   [POP_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[REAL_LT_REFL] THEN
    MATCH_MP_TAC P2GF_TRANSFER_ZERO THEN
    MAP_EVERY EXISTS_TAC [`p2cg_om (rho:num->real) D`; `p2cg_tr (rho:num->real) D`;
                          `R':real^3->real^3`; `p2gf_dom (rho:num->real) d`; `s0:real`] THEN
    ASM_SIMP_TAC[REAL_LE_REFL; REAL_LT_IMP_LE] THEN CONJ_TAC THEN
    MAP_EVERY X_GEN_TAC [`c:num`; `y:real^3`] THEN STRIP_TAC THENL
     [MATCH_MP_TAC P2GF_G0_CHART THEN
      MAP_EVERY EXISTS_TAC [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)`;
                            `U:num->A->bool`; `z:num->A`; `K:num->real`; `N0:num->num`;
                            `B:num->num->real`; `P:num->num`; `yc:num->num->num->A`;
                            `sq:num->num`; `CG:real->real`; `t:num->num`; `r:num->num`;
                            `d:num`] THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      USE_THEN "pb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `s < &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(kp:num->real^3->real^3) (NUMPAIR i q) w IN
                p2gf_reg (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) sq yc rho CG P kp t s`
  ASSUME_TAC THENL
   [REWRITE_TAC[p2gf_reg; UNIONS_GSPEC; IN_ELIM_THM] THEN EXISTS_TAC `d:num` THEN
    ASM_REWRITE_TAC[p2gf_okp; IN_IMAGE] THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`i:num`; `q:num`] THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `w:real^3` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC P2GF_TRANSFER_NEG THEN
  MAP_EVERY EXISTS_TAC [`p2cg_om (rho:num->real) D`; `p2cg_tr (rho:num->real) D`;
                        `R':real^3->real^3`; `p2gf_dom (rho:num->real) d`; `s0:real`] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; P2GF_OM_OPEN] THEN TRY(CONJ_TAC THENL
   [MATCH_MP_TAC P2GF_OM_OPEN THEN
    MAP_EVERY EXISTS_TAC [`U:num->A->bool`; `z:num->A`; `K:num->real`; `N0:num->num`;
                          `B:num->num->real`; `D:num#num->real^(3,3)finite_sum->real^1`;
                          `Gl:num->real^3->real^3^3`; `r:num->num`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC]) THEN
  CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`c:num`; `y:real^3`] THEN STRIP_TAC THENL
   [MATCH_MP_TAC P2GF_GF_CHART THEN
    MAP_EVERY EXISTS_TAC [`U:num->A->bool`; `z:num->A`; `K:num->real`; `N0:num->num`;
                          `B:num->num->real`; `Gl:num->real^3->real^3^3`; `CG:real->real`;
                          `d:num`] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM SET_TAC[];
    USE_THEN "pb" MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]]]);;

(* Elementary ball bounds. *)

let P2GF_BALL_CHAIN = prove
 (`!(w0:real^3) w u rr R.
     norm w0 <= R /\ w IN ball(w0,rr) /\ u IN ball(w,rr)
     ==> norm w < R + rr /\ norm u < R + &2 * rr /\ u IN ball(w0,&2 * rr)`,
  REWRITE_TAC[IN_BALL; dist] THEN CONV_TAC NORM_ARITH);;

(* The candidate domains of radius index 3. *)

let P2GF_DOM_3 = prove
 (`!(rho:num->real) d i q.
     p2gf_ch d = NUMPAIR i q /\ p2gf_ri d = 3
     ==> p2gf_dom rho d = ball(vec 0,rho i / &16)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[p2gf_dom; p2gf_r0; NUMPAIR_DEST] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

(* The local uniform estimate near a point of X. *)

let P2GF_LOCAL_LCK_FLOW = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z rho K N0 B P yc sq D Gl kp CG t r X a Kb N1 p b m eta.
     p2gf_fctx V U z rho K N0 B P yc sq D Gl kp CG t r /\
     open_in (p2cl_top (p2cg_dm rho) kp) X /\
     p2gf_xhyp V (\k. sq (t (r k))) (p2gf_phi V yc rho P kp sq t r) X a Kb N1 /\
     p IN X /\ a < b /\ b <= &0 /\ &0 < eta
     ==> ?O N. open_in (p2cl_top (p2cg_dm rho) kp) O /\ p IN O /\
               !n y s. N <= n /\ y IN O /\ b <= s /\ s <= &0
                       ==> p2gf_lckv (p2gf_VL V yc rho P kp sq t r CG Gl) V (\k. sq (t (r k)))
                                     (p2gf_phi V yc rho P kp sq t r) m n s y < eta`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GF_FCTX_FACTS) THEN
  MP_TAC(ISPECL (p2gf_fstd @ [`X:real^3->bool`; `a:real`; `Kb:real`; `N1:num`; `p:real^3`;
                             `b:real`]) P2GF_DEEP_CAND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` (X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `q:num`
    (X_CHOOSE_THEN `w0:real^3` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))))) THEN
  SUBGOAL_THEN `&0 < (rho:num->real) i` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `p2gf_dom (rho:num->real) d = ball(vec 0,rho i / &16)` (LABEL_TAC "dom") THENL
   [MATCH_MP_TAC P2GF_DOM_3 THEN EXISTS_TAC `q:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(w0:real^3) <= (rho:num->real) i / &32` ASSUME_TAC THENL
   [UNDISCH_TAC `(w0:real^3) IN cball(vec 0,(rho:num->real) i / &32)` THEN
    REWRITE_TAC[IN_CBALL_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w0:real^3) IN p2gf_dom rho d` ASSUME_TAC THENL
   [USE_THEN "dom" SUBST1_TAC THEN REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the candidate limit and its local estimate *)
  MP_TAC(ISPECL (p2gf_fstd @ [`d:num`]) P2GF_DICH_ADM) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `G:real->real^3->real^3^3`) THEN
  MP_TAC(ISPECL (p2gf_fstd @ [`d:num`; `i:num`; `q:num`; `G:real->real^3->real^3^3`;
                             `w0:real^3`; `b:real`; `m:num`; `eta:real`]) P2GF_LCK_LOCAL) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE; LE_REFL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (X_CHOOSE_THEN `k1:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lck")))) THEN
  (* the maps S n are diffeomorphisms near w0 *)
  MP_TAC(ISPECL (p2gf_fstd @ [`i:num`; `q:num`; `\j:num. j`; `w0:real^3`]) P2GF_S_NEAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LE_REFL; IN_BALL_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP P2CE_NEAR_ID_DIFFEO) THEN REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `rd:real` (X_CHOOSE_THEN `Nd:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dd")))) THEN
  (* the metric fields and the pullback representation *)
  MP_TAC(ISPECL (p2gf_fstd @ [`d:num`]) P2GF_H_FIELD) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `kH:num` (LABEL_TAC "hf")) THEN
  MP_TAC(ISPECL (p2gf_fstd @ [`d:num`; `i:num`; `q:num`]) P2GF_PB_REP_U) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `kP:num` (LABEL_TAC "pbu")) THEN
  MP_TAC(SPEC `(rho:num->real) i / &64` REAL_ARCH_INV) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `nS:num` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `rr = min e1 (min rd ((rho:num->real) i / &64)) / &2` THEN
  SUBGOAL_THEN `&0 < rr /\ rr < e1 /\ &2 * rr <= rd /\ &2 * rr <= (rho:num->real) i / &64`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "rr" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `IMAGE ((kp:num->real^3->real^3) (NUMPAIR i q)) (ball(w0,rr))` THEN
  EXISTS_TAC `(k1:num) + Nd + kH + kP + nS + i` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2CL_OPEN_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`p2cg_om (rho:num->real) D`; `p2cg_tr (rho:num->real) D`] THEN
    ASM_REWRITE_TAC[OPEN_BALL; p2cg_dm; NUMPAIR_DEST] THEN
    REWRITE_TAC[SUBSET; IN_BALL_0; IN_BALL; dist] THEN X_GEN_TAC `u:real^3` THEN
    MP_TAC(ISPECL [`u:real^3`; `w0:real^3`] NORM_TRIANGLE_SUB) THEN
    REWRITE_TAC[NORM_SUB] THEN ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `(kp:num->real^3->real^3) (NUMPAIR i q) w0 = p` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `y:real^3`; `s:real`] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `w:real^3` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) STRIP_ASSUME_TAC)) THEN
  (* the diffeomorphism on ball(w,rr) *)
  USE_THEN "dd" (MP_TAC o SPECL [`n:num`; `ball(w:real^3,rr)`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`w0:real^3`; `w:real^3`; `u:real^3`; `rr:real`;
                   `(rho:num->real) i / &32`] P2GF_BALL_CHAIN) THEN
    ASM_REWRITE_TAC[IN_BALL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `Ri:real^3->real^3`) THEN
  SUBGOAL_THEN `p2gf_bt d < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ball(w:real^3,rr) SUBSET p2gf_dom rho d /\ (w:real^3) IN p2gf_dom rho d /\
                IMAGE (p2gf_S (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) yc rho P kp sq t r n (NUMPAIR i q))
                      (ball(w,rr)) SUBSET p2gf_dom rho d`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "dom" SUBST1_TAC THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_BALL_0] THEN
    REPEAT CONJ_TAC THENL
     [X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`w0:real^3`; `w:real^3`; `u:real^3`; `rr:real`;
                     `(rho:num->real) i / &32`] P2GF_BALL_CHAIN) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`w0:real^3`; `w:real^3`; `w:real^3`; `rr:real`;
                     `(rho:num->real) i / &32`] P2GF_BALL_CHAIN) THEN
      ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`w0:real^3`; `w:real^3`; `u:real^3`; `rr:real`;
                     `(rho:num->real) i / &32`] P2GF_BALL_CHAIN) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(ISPECL (p2gf_fstd @ [`n:num`; `i:num`; `q:num`; `u:real^3`]) P2GF_S_C0) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[IN_CBALL_0] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `inv(&n + &1) <= inv(&nS)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN
        REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPECL [`p2gf_S (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) yc rho P kp sq t r n (NUMPAIR i q) u`;
                     `u:real^3`] NORM_TRIANGLE_SUB) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL (p2gf_fstd @ [`d:num`; `i:num`; `q:num`; `G:real->real^3->real^3^3`; `n:num`;
                             `s:real`; `w:real^3`; `rr:real`; `Ri:real^3->real^3`; `m:num`])
                P2GF_LCK_TRANSFER_S) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LE_REFL] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`j:num`; `s':real`; `y':real^3`] THEN STRIP_TAC THEN
      USE_THEN "pbu" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      USE_THEN "hf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    DISCH_THEN SUBST1_TAC] THEN
  USE_THEN "lck" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `(w:real^3) IN ball(w0,rr)` THEN REWRITE_TAC[IN_BALL] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The flow part of G.  p2gf_vlpart: a regular view on the glued limit with  *)
(* slice (top,atlas,g) at 0 in which every X of the X-clause flows and the   *)
(* pulled back metrics converge in C^m on compact subsets of X uniformly on  *)
(* [b,0], b > a.  P2GF_VL_PART: the region view p2gf_VL is such a view.      *)
(* ------------------------------------------------------------------------- *)

let p2gf_vlpart = new_definition
 `p2gf_vlpart (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3))
              (sub:num->num) (top:(real^3)topology)
              (atlas:((real^3->bool)#(real^3->real^3))->bool) (g:real^3->real^3^3)
              (W:num->real^3->bool) (phi:num->real^3->A)
              (Vl:(real->(real^3)topology)#(real->((real^3->bool)#(real^3->real^3))->bool)#
                  (real->real^3->real^3^3)) <=>
    p2c_regular_view Vl /\
    rfs_vtop Vl (&0) = top /\ rfs_vatlas Vl (&0) = atlas /\ rfs_vmetric Vl (&0) = g /\
    (!X a. open_in top X /\ compact_in top (top closure_of X) /\ a < &0 /\
           (?Kb N. !k. N <= k
                       ==> X SUBSET W k /\
                           rfs_persists (V (sub k)) (IMAGE (phi k) X) a (&0) /\
                           !s y. a < s /\ s <= &0 /\ y IN IMAGE (phi k) X
                                 ==> mfd_rm_norm (rfs_vatlas (V (sub k)) s)
                                                 (rfs_vmetric (V (sub k)) s) y <= Kb)
           ==> p2c_vflow Vl X a (&0) /\
               !K m eta b. compact_in top K /\ K SUBSET X /\ a < b /\ &0 < eta
                 ==> ?k0. !k s y. k0 <= k /\ b <= s /\ s <= &0 /\ y IN K
                                  ==> lck_dist2 m
                                        (metric_local (rfs_vatlas Vl s)
                                           (chart_at (rfs_vatlas Vl s) y)
                                           (rfs_vmetric Vl s))
                                        (rfs_pullback (rfs_vatlas (V (sub k)) s)
                                           (phi k o chart_inv
                                              (chart_at (rfs_vatlas Vl s) y))
                                           (rfs_vmetric (V (sub k)) s))
                                        (SND(chart_at (rfs_vatlas Vl s) y) y) < eta)`;;

(* Uniformity on compact subsets of X (P2CE_COMPACT_EVENTUALLY). *)

let P2GF_LCK_UNIFORM_FLOW = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z rho K N0 B P yc sq D Gl kp CG t r X a Kb N1 Kc m eta b.
     p2gf_fctx V U z rho K N0 B P yc sq D Gl kp CG t r /\
     open_in (p2cl_top (p2cg_dm rho) kp) X /\
     p2gf_xhyp V (\k. sq (t (r k))) (p2gf_phi V yc rho P kp sq t r) X a Kb N1 /\
     compact_in (p2cl_top (p2cg_dm rho) kp) Kc /\ Kc SUBSET X /\ a < b /\ &0 < eta
     ==> ?k0. !k s y. k0 <= k /\ b <= s /\ s <= &0 /\ y IN Kc
                      ==> p2gf_lckv (p2gf_VL V yc rho P kp sq t r CG Gl) V (\k. sq (t (r k)))
                                    (p2gf_phi V yc rho P kp sq t r) m k s y < eta`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `b <= &0` THENL
   [ALL_TAC; EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC] THEN
  MP_TAC(ISPECL [`p2cl_top (p2cg_dm (rho:num->real)) (kp:num->real^3->real^3)`;
                 `Kc:real^3->bool`;
                 `\n y. !s. b <= s /\ s <= &0
                          ==> p2gf_lckv (p2gf_VL (V:num->(real->A topology)#
                                                   (real->((A->bool)#(A->real^3))->bool)#
                                                   (real->A->real^3^3)) yc rho P kp sq t r CG Gl)
                                        V (\k. sq (t (r k))) (p2gf_phi V yc rho P kp sq t r)
                                        m n s y < eta`] P2CE_COMPACT_EVENTUALLY) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL (p2gf_fstd @ [`X:real^3->bool`; `a:real`; `Kb:real`; `N1:num`; `y:real^3`;
                               `b:real`; `m:num`; `eta:real`]) P2GF_LOCAL_LCK_FLOW) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN MESON_TAC[];
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MESON_TAC[]]);;

(* The flow part. *)

let P2GF_VL_PART = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z rho K N0 B P yc sq D Gl kp CG t r.
     p2gf_fctx V U z rho K N0 B P yc sq D Gl kp CG t r
     ==> ?Vl. p2gf_vlpart V (\k. sq (t (r k))) (p2cl_top (p2cg_dm rho) kp)
                          (p2cl_atlas (p2cg_dm rho) kp) (p2cl_metric (p2cg_dm rho) kp Gl)
                          (p2gc_W rho P kp)
                          (\k. p2ce_F (\k. rfs_vtop (V k) (&0)) (\k. rfs_vatlas (V k) (&0))
                                      (\k. rfs_vmetric (V k) (&0)) yc rho kp (p2ce_cs P k)
                                      (sq (t (r k))) (P(k + 2)))
                          Vl`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  EXISTS_TAC `p2gf_VL (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)) yc rho P kp sq t r CG Gl` THEN
  REWRITE_TAC[p2gf_vlpart] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[p2gf_VL] THEN MATCH_MP_TAC P2GF_VL_REGULAR_G THEN
    MAP_EVERY EXISTS_TAC [`U:num->A->bool`; `z:num->A`; `K:num->real`; `N0:num->num`;
                          `B:num->num->real`; `D:num#num->real^(3,3)finite_sum->real^1`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[p2gf_VL; P2GF_VL_PARTS];
    REWRITE_TAC[p2gf_VL; P2GF_VL_PARTS; REAL_LT_REFL];
    REWRITE_TAC[p2gf_VL; P2GF_VL_PARTS; REAL_LT_REFL];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`X:real^3->bool`; `a:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `Kb:real` (X_CHOOSE_THEN `N1:num` (LABEL_TAC "xh")))))) THEN
  SUBGOAL_THEN `p2gf_xhyp (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)) (\k. sq (t (r k)))
                          (p2gf_phi V yc rho P kp sq t r) X a Kb N1`
  ASSUME_TAC THENL
   [REWRITE_TAC[p2gf_xhyp; p2gf_phi] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "xh" (MP_TAC o C MP (ASSUME `N1 <= (k:num)`) o SPEC `k:num`) THEN SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL (p2gf_fstd @ [`X:real^3->bool`; `a:real`; `Kb:real`; `N1:num`])
                  P2GF_X_VFLOW) THEN
    ASM_REWRITE_TAC[p2gf_VL] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`Kc:real^3->bool`; `m:num`; `eta:real`; `b:real`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL (p2gf_fstd @ [`X:real^3->bool`; `a:real`; `Kb:real`; `N1:num`; `Kc:real^3->bool`;
                             `m:num`; `eta:real`; `b:real`]) P2GF_LCK_UNIFORM_FLOW) THEN
  ASM_REWRITE_TAC[p2gf_lckv; p2gf_phi]);;


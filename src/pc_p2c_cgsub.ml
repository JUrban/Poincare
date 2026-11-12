(* ========================================================================= *)
(* Unit pc_p2c_cgsub (Part 2C, used in the pc_p2c_cg route): subsequences.   *)
(* A diagonal Arzela-Ascoli theorem for countably many families of functions *)
(* (eventually bounded and equicontinuous on compact sets), and C-infinity   *)
(* limits: if all iterated partials converge locally uniformly, the limit is *)
(* smooth and its partials are the limits of the partials.                   *)
(* ========================================================================= *)

needs "src/pc_p2c_cgtrans.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Diagonal Arzela-Ascoli (SUBSEQUENCE_DIAGONALIZATION_LEMMA                  *)
(* and ARZELA_ASCOLI), for families f i n that are bounded and               *)
(* equicontinuous on the compact set s i from the index N i on.              *)
(* ------------------------------------------------------------------------- *)

let P2CS_AA_DIAG = prove
 (`!(f:num->num->real^M->real^N) s M N.
     (!i. compact (s i)) /\
     (!i n x. N i <= n /\ x IN s i ==> norm(f i n x) <= M i) /\
     (!i x e. x IN s i /\ &0 < e
              ==> ?d. &0 < d /\
                      !n y. N i <= n /\ y IN s i /\ norm(x - y) < d
                            ==> norm(f i n x - f i n y) < e)
     ==> ?r. (!m n:num. m < n ==> r m < r n) /\
             !i. ?g. g continuous_on s i /\
                     !e. &0 < e
                         ==> ?K. !n x. K <= n /\ x IN s i
                                       ==> norm(f i (r n) x - g x) < e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "bd") (LABEL_TAC "eq"))) THEN
  ABBREV_TAC `f' = \i n. if (N:num->num) i <= n then (f:num->num->real^M->real^N) i n
                          else (\x:real^M. vec 0:real^N)` THEN
  MP_TAC(ISPEC
   `\i (r:num->num). ?g:real^M->real^N.
       g continuous_on s i /\
       !e. &0 < e ==> ?K. !n x. K <= n /\ x IN s i
                                ==> norm((f':num->num->real^M->real^N) i (r n) x - g x) < e`
   SUBSEQUENCE_DIAGONALIZATION_LEMMA) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`i:num`; `r:num->num`] THEN
      MP_TAC(ISPECL [`\n:num. (f':num->num->real^M->real^N) i ((r:num->num) n)`; `(s:num->real^M->bool) i`;
                     `max ((M:num->real) i) (&0)`] ARZELA_ASCOLI) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [MAP_EVERY X_GEN_TAC [`n:num`; `x:real^M`] THEN DISCH_TAC THEN
          EXPAND_TAC "f'" THEN REWRITE_TAC[] THEN COND_CASES_TAC THENL
           [TRANS_TAC REAL_LE_TRANS `(M:num->real) i` THEN
            CONJ_TAC THENL [USE_THEN "bd" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
                            REAL_ARITH_TAC];
            REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC];
          MAP_EVERY X_GEN_TAC [`x:real^M`; `e:real`] THEN STRIP_TAC THEN
          USE_THEN "eq" (MP_TAC o SPECL [`i:num`; `x:real^M`; `e:real`]) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
          DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
          EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
          MAP_EVERY X_GEN_TAC [`n:num`; `y:real^M`] THEN STRIP_TAC THEN
          EXPAND_TAC "f'" THEN REWRITE_TAC[] THEN COND_CASES_TAC THENL
           [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
            ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0]]];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `g:real^M->real^N` (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `k:num->num` STRIP_ASSUME_TAC))) THEN
      EXISTS_TAC `k:num->num` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `g:real^M->real^N` THEN ASM_REWRITE_TAC[o_THM] THEN
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[GE] THEN MESON_TAC[];
      MAP_EVERY X_GEN_TAC [`i:num`; `r:num->num`; `k1:num->num`; `k2:num->num`; `N0:num`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `g:real^M->real^N` STRIP_ASSUME_TAC)
        ASSUME_TAC) THEN
      EXISTS_TAC `g:real^M->real^N` THEN ASM_REWRITE_TAC[o_THM] THEN
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[o_THM] THEN
      DISCH_THEN(X_CHOOSE_TAC `K0:num`) THEN EXISTS_TAC `K0 + N0:num` THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `x:real^M`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> can (term_match []
        `!j:num. N <= j ==> ?j'. j <= j' /\ (k2:num->num) j = (k1:num->num) j'`) (concl th))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `\n:num. n`) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num->num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `k:num->num` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN REWRITE_TAC[o_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^M->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `g:real^M->real^N` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `K0:num`) THEN EXISTS_TAC `K0 + (N:num->num) i` THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `x:real^M`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `x:real^M`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  EXPAND_TAC "f'" THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `(N:num->num) i <= (k:num->num) n` (fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPEC `k:num->num` MONOTONE_BIGGER) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `n:num`) THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* C-infinity limits.  If all iterated partials of smooth maps               *)
(* Fs n converge uniformly on an open convex set U, to H l for the list l,    *)
(* then H [] is smooth on U and its iterated partials are the H l           *)
(* (HAS_DERIVATIVE_SEQUENCE and SMOOTH_MAP_ON_PARTIAL_FAMILY).                *)
(* ------------------------------------------------------------------------- *)

let P2CS_UNIF_LIM = prove
 (`!(f:num->real^M->real^N) g s x.
     (!e. &0 < e ==> ?N. !n y. N <= n /\ y IN s ==> norm(f n y - g y) < e) /\ x IN s
     ==> ((\n. f n x) --> g x) sequentially`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIM_SEQUENTIALLY; dist] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN ASM_MESON_TAC[]);;

let P2CS_LIMIT_HAS_DERIVATIVE = prove
 (`!(Fs:num->real^M->real^N) H U l x.
     open U /\ convex U /\ x IN U /\
     (!n. smooth_map_on U (Fs n)) /\
     (!e. &0 < e
          ==> ?N. !n y. N <= n /\ y IN U
                        ==> norm(iterated_partial l (Fs n) y - H l y) < e) /\
     (!i. 1 <= i /\ i <= dimindex(:M)
          ==> !e. &0 < e
                  ==> ?N. !n y. N <= n /\ y IN U
                                ==> norm(iterated_partial (CONS i l) (Fs n) y -
                                         H (CONS i l) y) < e)
     ==> (H l has_derivative
          (\v. vsum(1..dimindex(:M)) (\i. v$i % H (CONS i l) x))) (at x)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "u0") (LABEL_TAC "u1")))))) THEN
  SUBGOAL_THEN
   `!e. &0 < e
        ==> ?N. !n y i. N <= n /\ y IN U /\ 1 <= i /\ i <= dimindex(:M)
                        ==> norm(iterated_partial (CONS i l) ((Fs:num->real^M->real^N) n) y -
                                 H (CONS i l) y) < e`
  (LABEL_TAC "u2") THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "u1" (MP_TAC o GEN `i:num` o DISCH `1 <= i /\ i <= dimindex(:M)` o
      SPEC `e:real` o UNDISCH o SPEC `i:num`) THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_THEN `Nf:num->num` (LABEL_TAC "nf")) THEN
    MP_TAC(ISPEC `IMAGE (Nf:num->num) (1..dimindex(:M))` num_FINITE) THEN
    SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; FORALL_IN_IMAGE; IN_NUMSEG] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "nb")) THEN EXISTS_TAC `N:num` THEN
    REPEAT STRIP_TAC THEN REMOVE_THEN "nf" (MP_TAC o SPEC `i:num`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REMOVE_THEN "nb" (MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^M->bool`; `\n. iterated_partial l ((Fs:num->real^M->real^N) n)`;
                 `\n (y:real^M) (v:real^M). vsum(1..dimindex(:M))
                           (\i. v$i % iterated_partial (CONS i l) ((Fs:num->real^M->real^N) n) y)`;
                 `\(y:real^M) (v:real^M). vsum(1..dimindex(:M)) (\i. v$i % (H:(num)list->real^M->real^N) (CONS i l) y)`]
                HAS_DERIVATIVE_SEQUENCE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`n:num`; `y:real^M`] THEN DISCH_TAC THEN
      MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
      REWRITE_TAC[iterated_partial] THEN
      MATCH_MP_TAC TEXT_HAS_DERIVATIVE_PARTIALS THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^M->bool` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL];
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 < e / &(dimindex(:M))` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN
        ASM_REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ; DIMINDEX_NONZERO];
        ALL_TAC] THEN
      USE_THEN "u2" (MP_TAC o C MP (ASSUME `&0 < e / &(dimindex(:M))`) o
                     SPEC `e / &(dimindex(:M))`) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `y:real^M`; `h:real^M`] THEN
      REWRITE_TAC[GE] THEN STRIP_TAC THEN REWRITE_TAC[GSYM VSUM_SUB_NUMSEG] THEN
      REWRITE_TAC[GSYM VECTOR_SUB_LDISTRIB] THEN
      TRANS_TAC REAL_LE_TRANS
       `sum(1..dimindex(:M)) (\i:num. norm(h:real^M) * e / &(dimindex(:M)))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[NORM_MUL] THEN
        MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE] THEN
        ASM_SIMP_TAC[COMPONENT_LE_NORM; REAL_LT_IMP_LE];
        REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB] THEN
        SIMP_TAC[REAL_DIV_LMUL; REAL_OF_NUM_EQ; DIMINDEX_NONZERO;
                 REAL_ARITH `n * (h * e / n) = h * (n * e / n)`] THEN
        REWRITE_TAC[REAL_MUL_SYM; REAL_LE_REFL]];
      EXISTS_TAC `x:real^M` THEN EXISTS_TAC `(H:(num)list->real^M->real^N) l x` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2CS_UNIF_LIM THEN
      EXISTS_TAC `U:real^M->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^M->real^N` (LABEL_TAC "g" o BETA_RULE)) THEN
  SUBGOAL_THEN `!y. y IN U ==> (g:real^M->real^N) y = (H:(num)list->real^M->real^N) l y`
  (LABEL_TAC "geq") THENL
   [X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
    EXISTS_TAC `\n. iterated_partial l ((Fs:num->real^M->real^N) n) y` THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
     [USE_THEN "g" (MP_TAC o SPEC `y:real^M`) THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC P2CS_UNIF_LIM THEN EXISTS_TAC `U:real^M->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `x:real^M` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
  MAP_EVERY EXISTS_TAC [`g:real^M->real^N`; `d:real`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN USE_THEN "geq" MATCH_MP_TAC THEN
    UNDISCH_TAC `ball(x:real^M,d) SUBSET U` THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[DIST_SYM];
    USE_THEN "g" (MP_TAC o C MP (ASSUME `(x:real^M) IN U`) o SPEC `x:real^M`) THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    SIMP_TAC[HAS_DERIVATIVE_WITHIN_OPEN; ASSUME `(x:real^M) IN U`;
             ASSUME `open(U:real^M->bool)`]]);;

let P2CS_CINF_LIMIT = prove
 (`!(Fs:num->real^M->real^N) H U.
     open U /\ convex U /\ (!n. smooth_map_on U (Fs n)) /\
     (!l. ALL (\i. 1 <= i /\ i <= dimindex(:M)) l
          ==> !e. &0 < e
                  ==> ?N. !n y. N <= n /\ y IN U
                                ==> norm(iterated_partial l (Fs n) y - H l y) < e)
     ==> smooth_map_on U (H []) /\
         !l x. ALL (\i. 1 <= i /\ i <= dimindex(:M)) l /\ x IN U
               ==> iterated_partial l (H []) x = H l x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!l x. ALL (\i. 1 <= i /\ i <= dimindex(:M)) l /\ x IN U
          ==> ((H:(num)list->real^M->real^N) l has_derivative
               (\v. vsum(1..dimindex(:M)) (\i. v$i % H (CONS i l) x))) (at x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2CS_LIMIT_HAS_DERIVATIVE THEN
    EXISTS_TAC `Fs:num->real^M->real^N` THEN EXISTS_TAC `U:real^M->bool` THEN
    ASM_SIMP_TAC[] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^M->bool`; `H:(num)list->real^M->real^N`]
                SMOOTH_MAP_ON_PARTIAL_FAMILY_ITERATED) THEN
  MP_TAC(ISPECL [`U:real^M->bool`; `H:(num)list->real^M->real^N`]
                SMOOTH_MAP_ON_PARTIAL_FAMILY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `[]:(num)list`) THEN
  REWRITE_TAC[ALL] THEN DISCH_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`l:num list`; `[]:(num)list`; `x:real^M`]) THEN
  ASM_REWRITE_TAC[ALL; APPEND_NIL]);;

(* ------------------------------------------------------------------------- *)
(* Countable index types, and the C-infinity subsequence:                   *)
(* smooth maps with jet bounds of every order on open sets V i containing    *)
(* closed balls cball(c i,r i) have a common subsequence whose iterated      *)
(* partials all converge uniformly on the open balls to the partials of     *)
(* smooth limits H i.                                                        *)
(* ------------------------------------------------------------------------- *)

let P2CS_AA_DIAG_GEN = prove
 (`!(f:I->num->real^M->real^N) s M N.
     COUNTABLE(:I) /\
     (!i. compact (s i)) /\
     (!i n x. N i <= n /\ x IN s i ==> norm(f i n x) <= M i) /\
     (!i x e. x IN s i /\ &0 < e
              ==> ?d. &0 < d /\
                      !n y. N i <= n /\ y IN s i /\ norm(x - y) < d
                            ==> norm(f i n x - f i n y) < e)
     ==> ?r. (!m n:num. m < n ==> r m < r n) /\
             !i. ?g. g continuous_on s i /\
                     !e. &0 < e
                         ==> ?K. !n x. K <= n /\ x IN s i
                                       ==> norm(f i (r n) x - g x) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `(:I)` COUNTABLE_AS_IMAGE) THEN
  ASM_REWRITE_TAC[UNIV_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `en:num->I`) THEN
  MP_TAC(ISPECL [`\j:num. (f:I->num->real^M->real^N) (en j)`; `\j:num. (s:I->real^M->bool) (en j)`;
                 `\j:num. (M:I->real) (en j)`; `\j:num. (N:I->num) (en j)`] P2CS_AA_DIAG) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:num->num` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:I` THEN
  SUBGOAL_THEN `?j:num. (en:num->I) j = i` (X_CHOOSE_THEN `j:num` (SUBST1_TAC o SYM)) THENL
   [UNDISCH_TAC `(:I) = IMAGE (en:num->I) (:num)` THEN
    REWRITE_TAC[EXTENSION; IN_UNIV; IN_IMAGE] THEN MESON_TAC[];
    ASM_REWRITE_TAC[]]);;

(* Mean-value bounds for iterated partials from jet bounds of the next order. *)

let P2CS_PARTIAL_LIPSCHITZ = prove
 (`!(g:real^M->real^N) V s l m B.
     open V /\ convex s /\ s SUBSET V /\ smooth_map_on V g /\
     ALL (\j. 1 <= j /\ j <= dimindex(:M)) l /\ LENGTH l + 1 <= m /\
     (!y. y IN V ==> pde_jetn m g y <= B)
     ==> !x y. x IN s /\ y IN s
               ==> norm(iterated_partial l g x - iterated_partial l g y) <=
                   (&(dimindex(:M)) * B) * norm(x - y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC DIFFERENTIABLE_BOUND THEN
  EXISTS_TAC `\(y:real^M) (v:real^M). vsum(1..dimindex(:M))
                     (\j. v$j % iterated_partial (CONS j l) (g:real^M->real^N) y)` THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
    REWRITE_TAC[iterated_partial; ETA_AX] THEN MATCH_MP_TAC TEXT_HAS_DERIVATIVE_PARTIALS THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `V:real^M->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^M) IN V` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `\v:real^M. vsum(1..dimindex(:M))
                     (\j. v$j % iterated_partial (CONS j l) (g:real^M->real^N) y)` ONORM) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`\j (v:real^M). v$j % iterated_partial (CONS j l) (g:real^M->real^N) y`;
                   `1..dimindex(:M)`] LINEAR_COMPOSE_VSUM) THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN BETA_TAC THEN
    DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`\v:real^M. v`; `iterated_partial (CONS j l) (g:real^M->real^N) y`;
                   `j:num`] LINEAR_VMUL_COMPONENT) THEN
    ASM_REWRITE_TAC[LINEAR_ID];
    ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN X_GEN_TAC `v:real^M` THEN BETA_TAC THEN
  TRANS_TAC REAL_LE_TRANS
   `sum(1..dimindex(:M)) (\j:num. norm(v:real^M) * B)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[NORM_MUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE] THEN
    ASM_SIMP_TAC[COMPONENT_LE_NORM] THEN
    TRANS_TAC REAL_LE_TRANS `pde_jetn m (g:real^M->real^N) y` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC P2CT_JETN_TERM_LE THEN
    ASM_REWRITE_TAC[ALL; LENGTH] THEN ASM_ARITH_TAC;
    REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB] THEN REAL_ARITH_TAC]);;

let P2CS_COUNTABLE_LISTS = prove
 (`COUNTABLE(:I) ==> COUNTABLE(:I#(num)list)`,
  DISCH_TAC THEN REWRITE_TAC[GSYM CROSS_UNIV] THEN MATCH_MP_TAC COUNTABLE_CROSS THEN
  ASM_SIMP_TAC[COUNTABLE_LIST; NUM_COUNTABLE]);;

let P2CS_JET_SUBSEQ = prove
 (`!(Fs:I->num->real^M->real^N) V c r.
     COUNTABLE(:I) /\
     (!i. open (V i) /\ cball(c i,r i) SUBSET V i) /\
     (!i. ?N. !n. N <= n ==> smooth_map_on (V i) (Fs i n)) /\
     (!i m. ?B N. !n y. N <= n /\ y IN V i ==> pde_jetn m (Fs i n) y <= B)
     ==> ?sub H. (!m n:num. m < n ==> sub m < sub n) /\
                 !i. smooth_map_on (ball(c i,r i)) (H i) /\
                     !l. ALL (\j. 1 <= j /\ j <= dimindex(:M)) l
                         ==> !e. &0 < e
                                 ==> ?K. !n y. K <= n /\ y IN ball(c i,r i)
                                               ==> norm(iterated_partial l (Fs i (sub n)) y -
                                                        iterated_partial l (H i) y) < e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "V")
    (CONJUNCTS_THEN2 MP_TAC MP_TAC))) THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `Bf:I->num->real` (X_CHOOSE_THEN `Nb:I->num->num` (LABEL_TAC "jet"))) THEN
  DISCH_THEN(X_CHOOSE_THEN `Ns:I->num` (LABEL_TAC "sm")) THEN
  ABBREV_TAC `ok = \l:num list. ALL (\j. 1 <= j /\ j <= dimindex(:M)) l` THEN
  MP_TAC(ISPECL
   [`\(il:I#(num)list) n. if (ok:num list->bool) (SND il)
                          then iterated_partial (SND il) ((Fs:I->num->real^M->real^N) (FST il) n)
                          else (\y:real^M. vec 0:real^N)`;
    `\il:I#(num)list. cball((c:I->real^M) (FST il),(r:I->real) (FST il))`;
    `\il:I#(num)list. abs((Bf:I->num->real) (FST il) (LENGTH(SND il)))`;
    `\il:I#(num)list. (Ns:I->num) (FST il) + (Nb:I->num->num) (FST il) (LENGTH(SND il)) +
                      Nb (FST il) (LENGTH(SND il) + 1)`] P2CS_AA_DIAG_GEN) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM] THEN BETA_TAC THEN REWRITE_TAC[FST; SND; COMPACT_CBALL] THEN
    ASM_SIMP_TAC[P2CS_COUNTABLE_LISTS] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`i:I`; `l:num list`; `n:num`; `x:real^M`] THEN STRIP_TAC THEN
      COND_CASES_TAC THENL [ALL_TAC; BETA_TAC THEN REWRITE_TAC[NORM_0; REAL_ABS_POS]] THEN
      TRANS_TAC REAL_LE_TRANS `pde_jetn (LENGTH(l:num list)) ((Fs:I->num->real^M->real^N) i n) x` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC P2CT_JETN_TERM_LE THEN REWRITE_TAC[LE_REFL] THEN
        UNDISCH_TAC `(ok:num list->bool) l` THEN EXPAND_TAC "ok" THEN REWRITE_TAC[];
        MATCH_MP_TAC(REAL_ARITH `x <= b ==> x <= abs b`) THEN
        USE_THEN "jet" MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        USE_THEN "V" (MP_TAC o SPEC `i:I`) THEN ASM SET_TAC[]];
      MAP_EVERY X_GEN_TAC [`i:I`; `l:num list`; `x:real^M`; `e:real`] THEN STRIP_TAC THEN
      ASM_CASES_TAC `(ok:num list->bool) l` THEN ASM_REWRITE_TAC[] THENL
       [ALL_TAC;
        EXISTS_TAC `&1` THEN BETA_TAC THEN REWRITE_TAC[REAL_LT_01; VECTOR_SUB_REFL; NORM_0] THEN
        ASM_REWRITE_TAC[]] THEN
      ABBREV_TAC `L = &(dimindex(:M)) * abs((Bf:I->num->real) i (LENGTH(l:num list) + 1))` THEN
      SUBGOAL_THEN `&0 <= L` ASSUME_TAC THENL
       [EXPAND_TAC "L" THEN MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS; REAL_ABS_POS];
        ALL_TAC] THEN
      EXISTS_TAC `e / (L + &1)` THEN
      ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 <= L ==> &0 < L + &1`] THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `y:real^M`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`(Fs:I->num->real^M->real^N) i n`; `(V:I->real^M->bool) i`;
                     `cball((c:I->real^M) i,(r:I->real) i)`; `l:num list`;
                     `LENGTH(l:num list) + 1`;
                     `abs((Bf:I->num->real) i (LENGTH(l:num list) + 1))`]
                    P2CS_PARTIAL_LIPSCHITZ) THEN
      ANTS_TAC THENL
       [USE_THEN "V" (STRIP_ASSUME_TAC o SPEC `i:I`) THEN
        ASM_REWRITE_TAC[CONVEX_CBALL; LE_REFL] THEN REPEAT CONJ_TAC THENL
         [USE_THEN "sm" MATCH_MP_TAC THEN ASM_ARITH_TAC;
          UNDISCH_TAC `(ok:num list->bool) l` THEN EXPAND_TAC "ok" THEN REWRITE_TAC[];
          X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN
          MATCH_MP_TAC(REAL_ARITH `x <= b ==> x <= abs b`) THEN
          USE_THEN "jet" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPECL [`x:real^M`; `y:real^M`]) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `L * d < e ==> a <= L * d ==> a < e`) THEN
      TRANS_TAC REAL_LET_TRANS `L * e / (L + &1)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 <= L ==> &0 < L + &1`; REAL_LT_LDIV_EQ;
                   REAL_ARITH `L * e / (L + &1) = (L * e) / (L + &1)`] THEN
      ASM_SIMP_TAC[REAL_LT_LMUL_EQ; REAL_ARITH `L * e < e * (L + &1) <=> &0 < e`]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN BETA_TAC THEN REWRITE_TAC[FST; SND] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:I->(num)list->real^M->real^N` (LABEL_TAC "g")) THEN
  EXISTS_TAC `sub:num->num` THEN
  EXISTS_TAC `\i:I. (g:I->(num)list->real^M->real^N) i []` THEN BETA_TAC THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i:I` THEN
  MP_TAC(ISPECL [`\n. (Fs:I->num->real^M->real^N) i (sub(n + (Ns:I->num) i))`;
                 `(g:I->(num)list->real^M->real^N) i`;
                 `ball((c:I->real^M) i,(r:I->real) i)`] P2CS_CINF_LIMIT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[OPEN_BALL; CONVEX_BALL] THEN BETA_TAC THEN CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `(V:I->real^M->bool) i` THEN CONJ_TAC THENL
       [USE_THEN "V" (MP_TAC o SPEC `i:I`) THEN
        MP_TAC(ISPECL [`(c:I->real^M) i`; `(r:I->real) i`] BALL_SUBSET_CBALL) THEN
        SET_TAC[];
        USE_THEN "sm" MATCH_MP_TAC THEN
        MP_TAC(ISPEC `sub:num->num` MONOTONE_BIGGER) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o SPEC `n + (Ns:I->num) i`) THEN ARITH_TAC];
      X_GEN_TAC `l:num list` THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      USE_THEN "g" (MP_TAC o SPECL [`i:I`; `l:num list`]) THEN
      DISCH_THEN(MP_TAC o C MP (ASSUME `&0 < e`) o SPEC `e:real` o CONJUNCT2) THEN
      DISCH_THEN(X_CHOOSE_TAC `K0:num`) THEN EXISTS_TAC `K0:num` THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `y:real^M`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`n + (Ns:I->num) i`; `y:real^M`]) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL [ASM_ARITH_TAC; ASM_MESON_TAC[SUBSET; BALL_SUBSET_CBALL]];
        ALL_TAC] THEN
      SUBGOAL_THEN `(ok:num list->bool) l` (fun th -> REWRITE_TAC[th]) THEN
      EXPAND_TAC "ok" THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `l:num list` THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  USE_THEN "g" (MP_TAC o SPECL [`i:I`; `l:num list`]) THEN
  DISCH_THEN(MP_TAC o C MP (ASSUME `&0 < e`) o SPEC `e:real` o CONJUNCT2) THEN
  DISCH_THEN(X_CHOOSE_TAC `K0:num`) THEN EXISTS_TAC `K0:num` THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `y:real^M`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `y:real^M`] o check (is_forall o concl)) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[SUBSET; BALL_SUBSET_CBALL]; ALL_TAC] THEN
  SUBGOAL_THEN `(ok:num list->bool) l` (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "ok" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`l:num list`; `y:real^M`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;


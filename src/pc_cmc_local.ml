(* ========================================================================= *)
(* Unit pc_cmc_local: the local theory of planar almost-harmonic sequences   *)
(* (Colding-Minicozzi 2008, Lemma B.23 locally): on a ball where the energy  *)
(* is eventually below e0, the replacements on the 1/8-ball (CM_REPLACEMENT) *)
(* have uniform bounds of all orders on the 1/16-ball (CM_EPS_REG), a        *)
(* subsequence converges with all derivatives (Arzela-Ascoli and             *)
(* diagonalization) to a smooth harmonic map, and the sequence converges to  *)
(* it in W^{1,2} on the 1/32-ball (property (B) and the Poincare inequality  *)
(* WAN_POINCARE0):                                                           *)
(*   - smoothness from a family of continuous successive derivatives;        *)
(*   - C^infinity compactness (CMC_CINF_COMPACT);                            *)
(*   - harmonic replacement with bounds of all orders (CMC_REP_ONE);         *)
(*   - L^2 convergence of maps and weak partials (CMC_LOCAL_CONV);           *)
(*   - continuity of the Euler-Lagrange density of pc_hm_rmin_fv and         *)
(*     harmonicity of limits (CMC_HARMONIC_LIMIT);                           *)
(*   - the local theorem CMC_LOCAL.                                          *)
(* ========================================================================= *)

needs "src/pc_cmc_dens.ml";;
needs "src/pc_wan_sob2r.ml";;
needs "src/pc_hm_rmin_fv.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Smoothness from a family of derivatives.                                  *)
(* ------------------------------------------------------------------------- *)

let CMC_PD_HAS_DERIVATIVE = prove
 (`!(f:real^2->real^K) f' x i.
     (f has_derivative f') (at x) ==> partial_derivative i f x = f' (basis i)`,
  REWRITE_TAC[partial_derivative] THEN MESON_TAC[FRECHET_DERIVATIVE_AT]);;

let CMC_D2_BASIS = prove
 (`!(a1:real^K) a2 i.
     1 <= i /\ i <= 2
     ==> (basis i:real^2)$1 % a1 + (basis i:real^2)$2 % a2 = if i = 1 then a1 else a2`,
  REWRITE_TAC[ARITH_RULE `1 <= i /\ i <= 2 <=> i = 1 \/ i = 2`] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
  VECTOR_ARITH_TAC);;

let CMC_SMOOTH_FAMILY = prove
 (`!s (g:(num)list->real^2->real^K).
     open s /\ (!l. ALL (\i. 1 <= i /\ i <= 2) l ==> (g l) continuous_on s) /\
     (!l x. ALL (\i. 1 <= i /\ i <= 2) l /\ x IN s
            ==> (g l has_derivative (\h. h$1 % g (CONS 1 l) x + h$2 % g (CONS 2 l) x))
                (at x))
     ==> (!l. ALL (\i. 1 <= i /\ i <= 2) l ==> smooth_map_on s (g l)) /\
         (!m l x. ALL (\i. 1 <= i /\ i <= 2) m /\ ALL (\i. 1 <= i /\ i <= 2) l /\ x IN s
                  ==> iterated_partial m (g l) x = g (APPEND m l) x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[smooth_map_on] THEN
    SUBGOAL_THEN `!n l. ALL (\i. 1 <= i /\ i <= 2) l
                        ==> continuously_differentiable n s ((g:(num)list->real^2->real^K) l)`
    (fun th -> MESON_TAC[th]) THEN
    INDUCT_TAC THENL [ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_0]; ALL_TAC] THEN
    X_GEN_TAC `l:(num)list` THEN DISCH_TAC THEN
    REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_SUC] THEN
    EXISTS_TAC `\x (h:real^2). h$1 % (g:(num)list->real^2->real^K) (CONS 1 l) x +
                               h$2 % g (CONS 2 l) x` THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN ASM_SIMP_TAC[];
      X_GEN_TAC `h:real^2` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THEN MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_CMUL_OPEN THEN
      ASM_REWRITE_TAC[ETA_AX] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[ALL] THEN ARITH_TAC];
    ALL_TAC] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[iterated_partial; APPEND] THEN
  MAP_EVERY X_GEN_TAC [`l:(num)list`; `x:real^2`] THEN
  REWRITE_TAC[ALL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `partial_derivative h (iterated_partial t ((g:(num)list->real^2->real^K) l)) x =
                partial_derivative h (g (APPEND t l)) x` SUBST1_TAC THENL
   [MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `(\h':real^2. h'$1 % (g:(num)list->real^2->real^K) (CONS 1 (APPEND t l)) x +
                           h'$2 % g (CONS 2 (APPEND t l)) x) (basis h)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CMC_PD_HAS_DERIVATIVE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[ALL_APPEND];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN ASM_SIMP_TAC[CMC_D2_BASIS] THEN
  SUBGOAL_THEN `h = 1 \/ h = 2` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Compactness in C^infinity: a sequence of smooth maps on ball(a,2rho) with *)
(* uniform bounds on every iterated partial has a subsequence whose iterated *)
(* partials all converge uniformly on ball(a,rho) to those of a smooth map   *)
(* (Arzela-Ascoli for each list of indices, diagonalization over an          *)
(* enumeration of all lists, HAS_DERIVATIVE_SEQUENCE, CMC_SMOOTH_FAMILY).    *)
(* ------------------------------------------------------------------------- *)

let CMC_FD_PARTIALS = prove
 (`!(f:real^2->real^K) x h.
     f differentiable (at x)
     ==> frechet_derivative f (at x) h =
         h$1 % partial_derivative 1 f x + h$2 % partial_derivative 2 f x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[partial_derivative] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN DISCH_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [CML_BASIS_EXPAND2] THEN
  ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL]);;

let CMC_IPD_HAS_DERIVATIVE = prove
 (`!s (v:real^2->real^K) l x.
     open s /\ smooth_map_on s v /\ x IN s
     ==> (iterated_partial l v has_derivative
          (\h. h$1 % iterated_partial (CONS 1 l) v x +
               h$2 % iterated_partial (CONS 2 l) v x)) (at x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on s (iterated_partial l (v:real^2->real^K))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL]; ALL_TAC] THEN
  SUBGOAL_THEN `iterated_partial l (v:real^2->real^K) differentiable (at x)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FRECHET_DERIVATIVE_WORKS]) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; iterated_partial] THEN GEN_TAC THEN
  ASM_SIMP_TAC[CMC_FD_PARTIALS]);;

(* Lipschitz bound of a map from a bound on its two partials (convex open). *)

let CMC_LIP_FROM_PARTIALS = prove
 (`!s (f:real^2->real^K) B.
     open s /\ convex s /\ smooth_map_on s f /\
     (!x. x IN s ==> norm(partial_derivative 1 f x) <= B /\ norm(partial_derivative 2 f x) <= B)
     ==> !x y. x IN s /\ y IN s ==> norm(f x - f y) <= (&2 * B) * norm(x - y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^2->real^K`;
                 `\x (h:real^2). h$1 % partial_derivative 1 (f:real^2->real^K) x +
                        h$2 % partial_derivative 2 f x`;
                 `s:real^2->bool`; `&2 * B`] DIFFERENTIABLE_BOUND) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `f:real^2->real^K`; `[]:(num)list`; `x:real^2`]
                  CMC_IPD_HAS_DERIVATIVE) THEN
    ASM_REWRITE_TAC[iterated_partial];
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(x:real^2) IN s`)) THEN
    SUBGOAL_THEN `linear (\h:real^2. h$1 % partial_derivative 1 (f:real^2->real^K) x +
                                      h$2 % partial_derivative 2 f x)` ASSUME_TAC THENL
     [MATCH_MP_TAC LINEAR_COMPOSE_ADD THEN CONJ_TAC THEN
      MATCH_MP_TAC LINEAR_VMUL_COMPONENT THEN REWRITE_TAC[LINEAR_ID; DIMINDEX_2] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[ONORM_LE_EQ] THEN
    X_GEN_TAC `h:real^2` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm((h:real^2)$1 % partial_derivative 1 (f:real^2->real^K) x) +
                norm(h$2 % partial_derivative 2 f x)` THEN
    REWRITE_TAC[NORM_TRIANGLE] THEN
    SUBGOAL_THEN `norm((h:real^2)$1 % partial_derivative 1 (f:real^2->real^K) x) <= B * norm(h:real^2) /\
                  norm(h$2 % partial_derivative 2 f x) <= B * norm h` MP_TAC THENL
     [REWRITE_TAC[NORM_MUL] THEN CONJ_TAC THEN GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE; REAL_ABS_POS] THEN
      SIMP_TAC[COMPONENT_LE_NORM; DIMINDEX_2; ARITH];
      REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Arzela-Ascoli for one list of indices, the diagonal subsequence for all   *)
(* lists, and the smooth limit.                                              *)
(* ------------------------------------------------------------------------- *)

let CMC_AA_ONE = prove
 (`!(FF:num->real^2->real^K) a rho M L.
     &0 < rho /\ (!n x. x IN cball(a,rho) ==> norm(FF n x) <= M) /\
     (!n x y. x IN cball(a,rho) /\ y IN cball(a,rho)
              ==> norm(FF n x - FF n y) <= L * norm(x - y))
     ==> ?g (r:num->num). (!m n. m < n ==> r m < r n) /\
               !e. &0 < e
                   ==> ?N. !n x. N <= n /\ x IN cball(a,rho) ==> norm(FF (r n) x - g x) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`FF:num->real^2->real^K`; `cball(a:real^2,rho)`; `M:real`] ARZELA_ASCOLI) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[COMPACT_CBALL] THEN MAP_EVERY X_GEN_TAC [`x:real^2`; `e:real`] THEN
    STRIP_TAC THEN EXISTS_TAC `e / (abs L + &1)` THEN
    SUBGOAL_THEN `&0 < abs L + &1` ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV] THEN MAP_EVERY X_GEN_TAC [`n:num`; `y:real^2`] THEN
    STRIP_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `L * norm(x - y:real^2)` THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `abs L * norm(x - y:real^2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(abs L + &1) * norm(x - y:real^2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^2->real^K` (CONJUNCTS_THEN2 (K ALL_TAC)
    (X_CHOOSE_THEN `r:num->num` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`g:real^2->real^K`; `r:num->num`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[GE]);;

(* The diagonal subsequence for all lists of indices.                        *)

let CMC_CINF_SUBSEQ = prove
 (`!(v:num->real^2->real^K) a rho B.
     &0 < rho /\ (!j. smooth_map_on (ball(a,&2 * rho)) (v j)) /\
     (!l j x. ALL (\i. 1 <= i /\ i <= 2) l /\ x IN ball(a,&2 * rho)
              ==> norm(iterated_partial l (v j) x) <= B (LENGTH l))
     ==> ?(t:num->num) (g:(num)list->real^2->real^K).
           (!m n. m < n ==> t m < t n) /\
           !l. ALL (\i. 1 <= i /\ i <= 2) l
               ==> !e. &0 < e
                       ==> ?N. !n x. N <= n /\ x IN cball(a,rho)
                                     ==> norm(iterated_partial l (v (t n)) x - g l x) < e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "BD"))) THEN
  SUBGOAL_THEN `cball(a:real^2,rho) SUBSET ball(a,&2 * rho)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* Each list separately. *)
  SUBGOAL_THEN
   `!l (r:num->num). ALL (\i. 1 <= i /\ i <= 2) l
          ==> ?k:num->num. (!m n. m < n ==> k m < k n) /\
                  ?g. !e. &0 < e
                          ==> ?N. !n x. N <= n /\ x IN cball(a,rho)
                                        ==> norm(iterated_partial l ((v:num->real^2->real^K)
                                                    (r(k n))) x - g x) < e`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\n. iterated_partial l ((v:num->real^2->real^K) ((r:num->num) n))`;
                   `a:real^2`; `rho:real`; `(B:num->real) (LENGTH (l:(num)list))`;
                   `&2 * (B:num->real) (LENGTH (l:(num)list) + 1)`] CMC_AA_ONE) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN USE_THEN "BD" MATCH_MP_TAC THEN ASM SET_TAC[];
        ALL_TAC] THEN
      X_GEN_TAC `n:num` THEN REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`ball(a:real^2,&2 * rho)`;
                     `iterated_partial l ((v:num->real^2->real^K) ((r:num->num)(n:num)))`;
                     `(B:num->real) (LENGTH (l:(num)list) + 1)`] CMC_LIP_FROM_PARTIALS) THEN
      ASM_SIMP_TAC[OPEN_BALL; CONVEX_BALL; SMOOTH_MAP_ON_ITERATED_PARTIAL] THEN
      ANTS_TAC THENL
       [X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
        REWRITE_TAC[GSYM(CONJUNCT2 iterated_partial)] THEN CONJ_TAC THENL
         [USE_THEN "BD" (MP_TAC o SPECL [`CONS 1 (l:(num)list)`; `(r:num->num) n`;
                                         `z:real^2`]);
          USE_THEN "BD" (MP_TAC o SPECL [`CONS 2 (l:(num)list)`; `(r:num->num) n`;
                                         `z:real^2`])] THEN
        (ANTS_TAC THENL [ASM_REWRITE_TAC[ALL] THEN ARITH_TAC; REWRITE_TAC[LENGTH; ADD1]]);
        DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[]];
      MESON_TAC[]];
    ALL_TAC] THEN
  (* Enumerate the lists and diagonalize. *)
  MP_TAC(ISPEC `(:(num)list)` COUNTABLE_AS_IMAGE) THEN
  ANTS_TAC THENL
   [SIMP_TAC[COUNTABLE_LIST; NUM_COUNTABLE] THEN SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->(num)list` (ASSUME_TAC o SYM)) THEN
  MP_TAC(ISPEC
   `\i (r:num->num). ALL (\i. 1 <= i /\ i <= 2) ((f:num->(num)list) i)
          ==> ?g. !e. &0 < e
                      ==> ?N. !n x. N <= n /\ x IN cball(a,rho)
                                    ==> norm(iterated_partial (f i) ((v:num->real^2->real^K)
                                                (r n)) x - g x) < e`
   SUBSEQUENCE_DIAGONALIZATION_LEMMA) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`i:num`; `r:num->num`] THEN
      ASM_CASES_TAC `ALL (\i. 1 <= i /\ i <= 2) ((f:num->(num)list) i)` THENL
       [FIRST_X_ASSUM(MP_TAC o SPECL [`(f:num->(num)list) i`; `r:num->num`]) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(X_CHOOSE_THEN `k:num->num` (CONJUNCTS_THEN2 ASSUME_TAC
          (X_CHOOSE_TAC `g:real^2->real^K`))) THEN
        EXISTS_TAC `k:num->num` THEN ASM_REWRITE_TAC[o_THM] THEN
        EXISTS_TAC `g:real^2->real^K` THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[] THEN EXISTS_TAC `\n:num. n` THEN ARITH_TAC];
      MAP_EVERY X_GEN_TAC [`i:num`; `r:num->num`; `k1:num->num`; `k2:num->num`; `N0:num`] THEN
      REWRITE_TAC[o_THM] THEN
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "KK")) THEN
      MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^2->real^K` THEN
      DISCH_THEN(LABEL_TAC "CV") THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      USE_THEN "CV" (X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1") o C MATCH_MP (ASSUME `&0 < e`)) THEN
      EXISTS_TAC `N0 + N1:num` THEN MAP_EVERY X_GEN_TAC [`n:num`; `x:real^2`] THEN
      STRIP_TAC THEN
      USE_THEN "KK" (MP_TAC o SPEC `n:num`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `n':num` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "N1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `\n:num. n`) THEN REWRITE_TAC[o_DEF] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:num->num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t:num->num` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!l. ?g:real^2->real^K.
          ALL (\i. 1 <= i /\ i <= 2) l
          ==> !e. &0 < e
                  ==> ?N. !n x. N <= n /\ x IN cball(a,rho)
                                ==> norm(iterated_partial l ((v:num->real^2->real^K)
                                           ((t:num->num) n)) x - g x) < e`
  MP_TAC THENL
   [X_GEN_TAC `l:(num)list` THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `?i. (f:num->(num)list) i = l` (X_CHOOSE_THEN `i:num` (SUBST_ALL_TAC o SYM))
    THENL
     [UNDISCH_TAC `IMAGE (f:num->(num)list) (:num) = (:(num)list)` THEN SET_TAC[];
      ASM_SIMP_TAC[]];
    REWRITE_TAC[SKOLEM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The limit of the diagonal subsequence is smooth, with the limits of the   *)
(* iterated partials as its iterated partials.                               *)
(* ------------------------------------------------------------------------- *)

let CMC_CINF_COMPACT = prove
 (`!(v:num->real^2->real^K) a rho B.
     &0 < rho /\ (!j. smooth_map_on (ball(a,&2 * rho)) (v j)) /\
     (!l j x. ALL (\i. 1 <= i /\ i <= 2) l /\ x IN ball(a,&2 * rho)
              ==> norm(iterated_partial l (v j) x) <= B (LENGTH l))
     ==> ?(t:num->num) u.
           (!m n. m < n ==> t m < t n) /\ smooth_map_on (ball(a,rho)) u /\
           !l. ALL (\i. 1 <= i /\ i <= 2) l
               ==> (!x. x IN ball(a,rho) ==> norm(iterated_partial l u x) <= B (LENGTH l)) /\
                   !e. &0 < e
                       ==> ?N. !n x. N <= n /\ x IN ball(a,rho)
                                     ==> norm(iterated_partial l (v (t n)) x -
                                              iterated_partial l u x) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`v:num->real^2->real^K`; `a:real^2`; `rho:real`; `B:num->real`]
                CMC_CINF_SUBSEQ) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:num->num` (X_CHOOSE_THEN `g:(num)list->real^2->real^K`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "UC")))) THEN
  SUBGOAL_THEN `ball(a:real^2,rho) SUBSET cball(a,rho) /\ cball(a,rho) SUBSET ball(a,&2 * rho)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* Pointwise limits on the open ball. *)
  SUBGOAL_THEN
   `!l x. ALL (\i. 1 <= i /\ i <= 2) l /\ x IN ball(a,rho)
          ==> ((\n. iterated_partial l ((v:num->real^2->real^K) ((t:num->num) n)) x) --> g l x)
              sequentially`
  (LABEL_TAC "PL") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[LIM_SEQUENTIALLY; dist] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "UC" (MP_TAC o C MATCH_MP (ASSUME `ALL (\i. 1 <= i /\ i <= 2) (l:(num)list)`)) THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC[];
    ALL_TAC] THEN
  (* Continuity of the limits. *)
  SUBGOAL_THEN
   `!l. ALL (\i. 1 <= i /\ i <= 2) l ==> (g:(num)list->real^2->real^K) l continuous_on ball(a,rho)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `cball(a:real^2,rho)` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`sequentially`;
                   `\n. iterated_partial l ((v:num->real^2->real^K) ((t:num->num) n))`;
                   `(g:(num)list->real^2->real^K) l`; `cball(a:real^2,rho)`]
                  CONTINUOUS_UNIFORM_LIMIT) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(a:real^2,&2 * rho)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL; OPEN_BALL];
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      USE_THEN "UC" (MP_TAC o C MATCH_MP (ASSUME `ALL (\i. 1 <= i /\ i <= 2) (l:(num)list)`)) THEN
      DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
      EXISTS_TAC `N:num` THEN ASM_MESON_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  (* Derivatives of the limits. *)
  SUBGOAL_THEN
   `!l x. ALL (\i. 1 <= i /\ i <= 2) l /\ x IN ball(a,rho)
          ==> ((g:(num)list->real^2->real^K) l has_derivative
               (\h. h$1 % g (CONS 1 l) x + h$2 % g (CONS 2 l) x)) (at x)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`l:(num)list`; `x0:real^2`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL
     [`ball(a:real^2,rho)`;
      `\n. iterated_partial l ((v:num->real^2->real^K) ((t:num->num) n))`;
      `\n x (h:real^2). h$1 % iterated_partial (CONS 1 l) ((v:num->real^2->real^K) ((t:num->num) n)) x +
                        h$2 % iterated_partial (CONS 2 l) (v ((t:num->num) n)) x`;
      `\x (h:real^2). h$1 % (g:(num)list->real^2->real^K) (CONS 1 l) x +
                      h$2 % g (CONS 2 l) x`] HAS_DERIVATIVE_SEQUENCE) THEN
    REWRITE_TAC[CONVEX_BALL] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MAP_EVERY X_GEN_TAC [`n:num`; `x:real^2`] THEN DISCH_TAC THEN
        MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
        MATCH_MP_TAC CMC_IPD_HAS_DERIVATIVE THEN
        EXISTS_TAC `ball(a:real^2,&2 * rho)` THEN ASM_REWRITE_TAC[OPEN_BALL] THEN
        ASM SET_TAC[];
        X_GEN_TAC `e:real` THEN DISCH_TAC THEN
        SUBGOAL_THEN `ALL (\i. 1 <= i /\ i <= 2) (CONS 1 (l:(num)list)) /\
                      ALL (\i. 1 <= i /\ i <= 2) (CONS 2 (l:(num)list))`
        STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[ALL] THEN ARITH_TAC; ALL_TAC] THEN
        USE_THEN "UC" (MP_TAC o C MATCH_MP
          (ASSUME `ALL (\i. 1 <= i /\ i <= 2) (CONS 1 (l:(num)list))`)) THEN
        USE_THEN "UC" (MP_TAC o C MATCH_MP
          (ASSUME `ALL (\i. 1 <= i /\ i <= 2) (CONS 2 (l:(num)list))`)) THEN
        DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
        DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
        DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
        DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
        EXISTS_TAC `N1 + N2:num` THEN
        MAP_EVERY X_GEN_TAC [`n:num`; `x:real^2`; `h:real^2`] THEN STRIP_TAC THEN
        REWRITE_TAC[VECTOR_ARITH
         `(a % x + b % y) - (a % x' + b % y'):real^K = a % (x - x') + b % (y - y')`] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `abs((h:real^2)$1) * e / &2 + abs(h$2) * e / &2` THEN CONJ_TAC THENL
         [MATCH_MP_TAC(NORM_ARITH
           `norm(x:real^K) <= a /\ norm(y:real^K) <= b ==> norm(x + y) <= a + b`) THEN
          REWRITE_TAC[NORM_MUL] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
          REWRITE_TAC[REAL_ABS_POS] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
          (CONJ_TAC THENL [ASM_ARITH_TAC; ASM SET_TAC[]]);
          SUBGOAL_THEN `abs((h:real^2)$1) <= norm h /\ abs(h$2) <= norm h` MP_TAC THENL
           [SIMP_TAC[COMPONENT_LE_NORM; DIMINDEX_2; ARITH]; ALL_TAC] THEN
          SUBGOAL_THEN `&0 <= e / &2` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          REWRITE_TAC[IMP_IMP] THEN
          DISCH_THEN(fun th -> MP_TAC(CONJ (MATCH_MP REAL_LE_RMUL (CONJ (CONJUNCT1(CONJUNCT2 th)) (CONJUNCT1 th)))
                                          (MATCH_MP REAL_LE_RMUL (CONJ (CONJUNCT2(CONJUNCT2 th)) (CONJUNCT1 th))))) THEN
          REAL_ARITH_TAC];
        MAP_EVERY EXISTS_TAC [`x0:real^2`; `(g:(num)list->real^2->real^K) l x0`] THEN
        ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `G:real^2->real^K` (LABEL_TAC "GD")) THEN
    SUBGOAL_THEN `!x. x IN ball(a:real^2,rho) ==> G x = (g:(num)list->real^2->real^K) l x`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
      EXISTS_TAC `\n. iterated_partial l ((v:num->real^2->real^K) ((t:num->num) n)) x` THEN
      ASM_SIMP_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
      USE_THEN "GD" (MP_TAC o C MATCH_MP (ASSUME `(x:real^2) IN ball(a,rho)`)) THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    MAP_EVERY EXISTS_TAC [`G:real^2->real^K`; `ball(a:real^2,rho)`] THEN
    ASM_SIMP_TAC[OPEN_BALL] THEN
    REMOVE_THEN "GD" (MP_TAC o C MATCH_MP (ASSUME `(x0:real^2) IN ball(a,rho)`)) THEN
    ASM_SIMP_TAC[HAS_DERIVATIVE_WITHIN_OPEN; OPEN_BALL];
    ALL_TAC] THEN
  (* The smooth limit. *)
  MP_TAC(ISPECL [`ball(a:real^2,rho)`; `g:(num)list->real^2->real^K`] CMC_SMOOTH_FAMILY) THEN
  ASM_SIMP_TAC[OPEN_BALL] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`t:num->num`; `(g:(num)list->real^2->real^K) []`] THEN
  ASM_SIMP_TAC[ALL] THEN X_GEN_TAC `l:(num)list` THEN DISCH_TAC THEN
  REWRITE_TAC[APPEND_NIL] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
    EXISTS_TAC `\n. iterated_partial l ((v:num->real^2->real^K) ((t:num->num) n)) x` THEN
    ASM_SIMP_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN MATCH_MP_TAC ALWAYS_EVENTUALLY THEN
    GEN_TAC THEN REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "UC" (MP_TAC o C MATCH_MP (ASSUME `ALL (\i. 1 <= i /\ i <= 2) (l:(num)list)`)) THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Harmonic replacement of a planar map on a small-energy ball, with the     *)
(* small-energy bounds of all orders (CM_REPLACEMENT, CM_EPS_REG).           *)
(* ------------------------------------------------------------------------- *)

(* The constants of the two CM statements, packaged.                         *)

let CMC_REP_CONSTS = prove
 (`!S (G:real^K->real^K^K) d.
     CM_EPS_REG_STATEMENT (:K) /\ CM_REPLACEMENT_STATEMENT (:K) /\ cm_target S G d
     ==> ?eL (C:num->real).
           &0 < eL /\ (!k. &0 < C k) /\
           (!(a:real^2) r (u:real^2->real^K) l x.
               &0 < r /\ cm_harmonic S G (ball(a,r)) u /\ wan_w12 (ball(a,r)) u /\
               wan_gdir (ball(a,r)) G u <= eL /\
               ALL (\i. 1 <= i /\ i <= 2) l /\ ~(l = []) /\ x IN ball(a,r / &2)
               ==> r pow (LENGTH l) * norm(iterated_partial l u x)
                   <= C (LENGTH l) * sqrt(wan_gdir (ball(a,r)) G u)) /\
           (!(a:real^2) r (u:real^2->real^K).
               &0 < r /\ cm_cmap S (ball(a,r)) u /\ wan_gdir (ball(a,r)) G u <= eL
               ==> ?w. cm_minimizer S G (ball(a,r)) w /\
                       wan_w120 (ball(a,r)) (\x. w x - u x) /\
                       cm_cmap S (ball(a,r)) w /\ cm_harmonic S G (ball(a,r)) w /\
                       (!x. x IN sphere(a,r) ==> w x = u x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CM_EPS_REG_STATEMENT; CM_REPLACEMENT_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "EPSS") (CONJUNCTS_THEN2 (LABEL_TAC "REPS")
    ASSUME_TAC)) THEN
  REMOVE_THEN "EPSS" (MP_TAC o SPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (X_CHOOSE_THEN `C:num->real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "EPS"))))) THEN
  REMOVE_THEN "REPS" (MP_TAC o SPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` (X_CHOOSE_THEN `C2:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "R1") (K ALL_TAC)))))) THEN
  MAP_EVERY EXISTS_TAC [`min e1 e2`; `C:num->real`] THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "EPS" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `min e1 e2` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN
    USE_THEN "R1" (MP_TAC o SPECL [`a:real^2`; `r:real`; `u:real^2->real^K`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `min e1 e2` THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[]]);;

(* Planar maps are C^0 /\ W^{1,2} maps into S on balls.                        *)

let CMC_PMAP_CMAP = prove
 (`!S (w:real^2->real^K) a r.
     cmc_pmap S w /\ compact S /\ &0 < r ==> cm_cmap S (ball(a,r)) w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cm_cmap] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CMC_PMAP_W12 THEN EXISTS_TAC `S:real^K->bool` THEN
    ASM_REWRITE_TAC[OPEN_BALL; BOUNDED_BALL];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cmc_pmap]) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `(:real^2)` THEN ASM_REWRITE_TAC[SUBSET_UNIV]);;

let CMC_PMAP_WMAP = prove
 (`!S (w:real^2->real^K) a r.
     cmc_pmap S w /\ compact S /\ &0 < r ==> cm_wmap S (ball(a,r)) w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cm_wmap] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CMC_PMAP_W12 THEN EXISTS_TAC `S:real^K->bool` THEN
    ASM_REWRITE_TAC[OPEN_BALL; BOUNDED_BALL];
    ALL_TAC] THEN
  EXISTS_TAC `{}:real^2->bool` THEN REWRITE_TAC[NEGLIGIBLE_EMPTY] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cmc_pmap]) THEN ASM_REWRITE_TAC[]);;

(* The replacement of one map on one ball: the minimizer has at most the     *)
(* energy of the map and satisfies the bounds of all orders.                  *)

let CMC_REP_ONE = prove
 (`!S (G:real^K->real^K^K) d eL (C:num->real) (w:real^2->real^K) a r.
     cm_target S G d /\ &0 < eL /\ (!k. &0 < C k) /\
     (!(a:real^2) r (u:real^2->real^K) l x.
         &0 < r /\ cm_harmonic S G (ball(a,r)) u /\ wan_w12 (ball(a,r)) u /\
         wan_gdir (ball(a,r)) G u <= eL /\
         ALL (\i. 1 <= i /\ i <= 2) l /\ ~(l = []) /\ x IN ball(a,r / &2)
         ==> r pow (LENGTH l) * norm(iterated_partial l u x)
             <= C (LENGTH l) * sqrt(wan_gdir (ball(a,r)) G u)) /\
     (!(a:real^2) r (u:real^2->real^K).
         &0 < r /\ cm_cmap S (ball(a,r)) u /\ wan_gdir (ball(a,r)) G u <= eL
         ==> ?w. cm_minimizer S G (ball(a,r)) w /\
                 wan_w120 (ball(a,r)) (\x. w x - u x) /\
                 cm_cmap S (ball(a,r)) w /\ cm_harmonic S G (ball(a,r)) w /\
                 (!x. x IN sphere(a,r) ==> w x = u x)) /\
     cmc_pmap S w /\ &0 < r /\ wan_gdir (ball(a,r)) G w <= eL
     ==> ?v. cm_minimizer S G (ball(a,r)) v /\
             wan_w120 (ball(a,r)) (\x. v x - w x) /\
             cm_harmonic S G (ball(a,r)) v /\ wan_w12 (ball(a,r)) v /\
             &0 <= wan_gdir (ball(a,r)) G v /\
             wan_gdir (ball(a,r)) G v <= wan_gdir (ball(a,r)) G w /\
             !l x. ALL (\i. 1 <= i /\ i <= 2) l /\ ~(l = []) /\ x IN ball(a,r / &2)
                   ==> r pow (LENGTH l) * norm(iterated_partial l v x)
                       <= C (LENGTH l) * sqrt(wan_gdir (ball(a,r)) G w)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "CP") (CONJUNCTS_THEN2 (LABEL_TAC "EPS")
      (CONJUNCTS_THEN2 (LABEL_TAC "REP") STRIP_ASSUME_TAC))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_target]) THEN
  REMOVE_THEN "REP" (MP_TAC o SPECL [`a:real^2`; `r:real`; `w:real^2->real^K`]) THEN
  ASM_SIMP_TAC[CMC_PMAP_CMAP] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^2->real^K` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `v:real^2->real^K` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `wan_w12 (ball(a:real^2,r)) (v:real^2->real^K)` ASSUME_TAC THENL
   [UNDISCH_TAC `cm_cmap S (ball(a:real^2,r)) (v:real^2->real^K)` THEN SIMP_TAC[cm_cmap];
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `&0 <= wan_gdir (ball(a:real^2,r)) G (v:real^2->real^K)` ASSUME_TAC THENL
   [FIRST_ASSUM(X_CHOOSE_THEN `lam0:real` (X_CHOOSE_THEN `Lam0:real` STRIP_ASSUME_TAC) o
      MATCH_MP HMD_TARGET_ELLIPTIC) THEN
    MP_TAC(ISPECL [`ball(a:real^2,r)`; `G:real^K->real^K^K`; `v:real^2->real^K`;
                   `lam0:real`; `Lam0:real`] HMD_GDIR_BOUNDS) THEN
    ASM_SIMP_TAC[OPEN_BALL; REAL_LT_IMP_LE];
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `wan_gdir (ball(a:real^2,r)) G (v:real^2->real^K) <=
                wan_gdir (ball(a,r)) G (w:real^2->real^K)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `cm_minimizer S G (ball(a:real^2,r)) (v:real^2->real^K)` THEN
    REWRITE_TAC[cm_minimizer; cm_gen] THEN
    DISCH_THEN(MP_TAC o SPEC `w:real^2->real^K` o CONJUNCT2) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[CMC_PMAP_WMAP] THEN
      MP_TAC(ISPECL [`ball(a:real^2,r)`; `\x. (v:real^2->real^K) x - w x`] WAN_W120_NEG) THEN
      ASM_REWRITE_TAC[OPEN_BALL; VECTOR_NEG_SUB];
      REAL_ARITH_TAC];
    ASM_REWRITE_TAC[]] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(C:num->real) (LENGTH (l:(num)list)) *
              sqrt(wan_gdir (ball(a:real^2,r)) G (v:real^2->real^K))` THEN
  CONJ_TAC THENL
   [USE_THEN "EPS" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `wan_gdir (ball(a:real^2,r)) G (w:real^2->real^K)` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_MESON_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Strong convergence on the small ball: the replacements are W^{1,2}- close *)
(* to the maps (property (B) of cmc_ah and the Poincare inequality), and     *)
(* converge uniformly with their first partials to the smooth limit.         *)
(* ------------------------------------------------------------------------- *)

(* The global weak partial of a planar map minus the classical partial of a *)
(* smooth W^{1,2} map: L^2 on s, with norm controlled by the Dirichlet      *)
(* energy of the difference.                                                  *)

let CMC_WD_DIFF_SMOOTH = prove
 (`!S (w:real^2->real^K) v s i.
     cmc_pmap S w /\ compact S /\ open s /\ bounded s /\ smooth_map_on s v /\
     wan_w12 s v /\ 1 <= i /\ i <= 2
     ==> (\x. wan_wd (:real^2) i w x - partial_derivative i v x) IN lspace s (&2) /\
         lnorm s (&2) (\x. wan_wd (:real^2) i w x - partial_derivative i v x) pow 2
         <= wan_dir s (\x. w x - v x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_w12 s (w:real^2->real^K)` ASSUME_TAC THENL
   [MATCH_MP_TAC CMC_PMAP_W12 THEN EXISTS_TAC `S:real^K->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `w:real^2->real^K`; `v:real^2->real^K`] WAN_DIR_SUB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `i:num`; `\x. (w:real^2->real^K) x - v x`] WAN_WD_WORKS) THEN
  ASM_REWRITE_TAC[DIMINDEX_2] THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_wpd s i (\x. (w:real^2->real^K) x - v x)
                  (\x. wan_wd (:real^2) i w x - partial_derivative i v x)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_WPD_SUB THEN CONJ_TAC THENL
     [REWRITE_TAC[ETA_AX] THEN
      MP_TAC(ISPECL [`S:real^K->bool`; `w:real^2->real^K`; `s:real^2->bool`; `i:num`]
                    CMC_WD_RESTRICT) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC WAN_WPD_C1 THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `smooth_map_on s (v:real^2->real^K)` THEN SIMP_TAC[smooth_map_on]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `i:num`; `\x. (w:real^2->real^K) x - v x`;
                 `\x. wan_wd (:real^2) i (w:real^2->real^K) x - partial_derivative i v x`]
                WAN_WD_UNIQUE) THEN
  ASM_REWRITE_TAC[DIMINDEX_2] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^2->bool`;
                 `{x | x IN s /\
                       ~(wan_wd s i (\x. (w:real^2->real^K) x - v x) x =
                         (\x. wan_wd (:real^2) i w x - partial_derivative i v x) x)}`;
                 `wan_wd s i (\x. (w:real^2->real^K) x - v x)`;
                 `\x. wan_wd (:real^2) i (w:real^2->real^K) x - partial_derivative i v x`;
                 `&2`] WAN_LSPACE_LNORM_SPIKE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o GSYM) (ASSUME_TAC o SYM)) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (is_eq o concl)) THEN
  ASM_SIMP_TAC[WAN_SOB_LNORM2_SQ] THEN
  MATCH_MP_TAC WAN_WD_SQ_LE_DIR THEN ASM_REWRITE_TAC[DIMINDEX_2]);;

(* Uniform convergence to 0 on a set of finite measure gives L^2           *)
(* convergence to 0.                                                         *)

let CMC_SMALL_FRACTION = prove
 (`!m e. &0 <= m /\ &0 < e ==> &0 < e / (m + &1) /\ m * e / (m + &1) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < e / (m + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `m * e / (m + &1) = e - e / (m + &1)` SUBST1_TAC THENL
   [MATCH_MP_TAC(REAL_FIELD `~(m + &1 = &0) ==> m * e / (m + &1) = e - e / (m + &1)`) THEN
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let CMC_BOUNDED_LNORM = prove
 (`!s (f:real^2->real^K) c.
     measurable s /\ f measurable_on s /\ (!x. x IN s ==> norm(f x) <= c)
     ==> f IN lspace s (&2) /\ lnorm s (&2) f <= measure s rpow (inv(&2)) * abs c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\x:real^2. abs c % basis 1:real^K) IN lspace s (&2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LSPACE_CONST]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(abs c % basis 1:real^K) = abs c` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_MUL] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_GE_1; LE_REFL; REAL_ABS_ABS; REAL_MUL_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^2->real^K) IN lspace s (&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`s:real^2->bool`; `&2`; `f:real^2->real^K`;
                          `\x:real^2. abs c % basis 1:real^K`] LSPACE_BOUNDED_MEASURABLE) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_MESON_TAC[REAL_ARITH `x <= c ==> x <= abs c`];
    ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `lnorm s (&2) (\x:real^2. abs c % basis 1:real^K)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC LNORM_MONO THEN EXISTS_TAC `{}:real^2->bool` THEN
    ASM_REWRITE_TAC[NEGLIGIBLE_EMPTY; DIFF_EMPTY] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_MESON_TAC[REAL_ARITH `x <= c ==> x <= abs c`];
    ASM_SIMP_TAC[LNORM_CONST; REAL_ARITH `&0 < &2`; REAL_LE_REFL]]);;

let CMC_UNIF_LNORM = prove
 (`!s (f:num->real^2->real^K).
     measurable s /\ (!n. f n measurable_on s) /\
     (!n. ?M. !x. x IN s ==> norm(f n x) <= M) /\
     (!e. &0 < e ==> ?N. !n x. N <= n /\ x IN s ==> norm(f n x) < e)
     ==> (!n. f n IN lspace s (&2)) /\
         ((\n. lnorm s (&2) (f n)) ---> &0) sequentially`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "BD") (LABEL_TAC "UC")))) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN USE_THEN "BD" (X_CHOOSE_TAC `M:real` o SPEC `n:num`) THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `(f:num->real^2->real^K) n`; `M:real`]
                  CMC_BOUNDED_LNORM) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= measure(s:real^2->bool) rpow (inv(&2))` ASSUME_TAC THENL
   [MATCH_MP_TAC RPOW_POS_LE THEN ASM_SIMP_TAC[MEASURE_POS_LE]; ALL_TAC] THEN
  MP_TAC(SPECL [`measure(s:real^2->bool) rpow (inv(&2))`; `e:real`] CMC_SMALL_FRACTION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "UC" (MP_TAC o SPEC `e / (measure(s:real^2->bool) rpow (inv(&2)) + &1)`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `(f:num->real^2->real^K) n`;
                 `e / (measure(s:real^2->bool) rpow (inv(&2)) + &1)`] CMC_BOUNDED_LNORM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= lnorm s (&2) ((f:num->real^2->real^K) n)` ASSUME_TAC THENL
   [MATCH_MP_TAC LNORM_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`lnorm s (&2) ((f:num->real^2->real^K) n) <=
     measure(s:real^2->bool) rpow inv (&2) *
     abs(e / (measure(s:real^2->bool) rpow inv (&2) + &1))`;
    `&0 <= lnorm s (&2) ((f:num->real^2->real^K) n)`;
    `measure(s:real^2->bool) rpow inv (&2) * e /
     (measure(s:real^2->bool) rpow inv (&2) + &1) < e`;
    `&0 < e / (measure(s:real^2->bool) rpow inv (&2) + &1)`] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* L^2 convergence of the maps and of their weak partials on the small ball, *)
(* from (B), Poincare and the uniform convergence of the replacements.       *)
(* ------------------------------------------------------------------------- *)

let CMC_SQ_NULL = prove
 (`!(x:num->real) eta c.
     (!j. &0 <= x j /\ x j pow 2 <= c * eta j) /\ (eta ---> &0) sequentially
     ==> (x ---> &0) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`sequentially`; `eta:num->real`; `c:real`] REALLIM_NULL_LMUL) THEN
  ASM_REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN DISCH_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e pow 2`) THEN ASM_SIMP_TAC[REAL_POW_LT] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `n:num`) THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  MATCH_MP_TAC REAL_POW_LT2_REV THEN EXISTS_TAC `2` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`(x:num->real) n pow 2 <= c * (eta:num->real) n`;
    `abs(c * (eta:num->real) n) < e pow 2`] THEN
  REAL_ARITH_TAC);;

let CMC_L2_SUM_NULL = prove
 (`!s (f:num->real^2->real^K) g h.
     (!j. f j IN lspace s (&2)) /\ ((\j. lnorm s (&2) (f j)) ---> &0) sequentially /\
     (!j. g j IN lspace s (&2)) /\ ((\j. lnorm s (&2) (g j)) ---> &0) sequentially /\
     (!j x. x IN s ==> h j x = f j x + g j x)
     ==> (!j. h j IN lspace s (&2)) /\
         ((\j. lnorm s (&2) (h j)) ---> &0) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!j. (h:num->real^2->real^K) j IN lspace s (&2) /\
        lnorm s (&2) (h j) =
        lnorm s (&2) (\x. (f:num->real^2->real^K) j x + (g:num->real^2->real^K) j x)`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN
    SUBGOAL_THEN `(\x. (f:num->real^2->real^K) j x + (g:num->real^2->real^K) j x)
                  IN lspace s (&2)` ASSUME_TAC
    THENL
     [MATCH_MP_TAC LSPACE_ADD THEN ASM_REWRITE_TAC[ETA_AX] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `{}:real^2->bool`; `(h:num->real^2->real^K) j`;
                   `\x. (f:num->real^2->real^K) j x + (g:num->real^2->real^K) j x`; `&2`]
                  WAN_LSPACE_LNORM_SPIKE) THEN
    ASM_SIMP_TAC[NEGLIGIBLE_EMPTY; DIFF_EMPTY];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\j. lnorm s (&2) ((f:num->real^2->real^K) j) + lnorm s (&2) ((g:num->real^2->real^K) j)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `j:num` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC LNORM_POS_LE THEN MATCH_MP_TAC LSPACE_ADD THEN ASM_REWRITE_TAC[ETA_AX] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      MATCH_MP_TAC LNORM_TRIANGLE THEN ASM_REWRITE_TAC[ETA_AX] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV];
    MP_TAC(ISPECL [`sequentially`; `\j. lnorm s (&2) ((f:num->real^2->real^K) j)`;
                   `\j. lnorm s (&2) ((g:num->real^2->real^K) j)`; `&0`; `&0`]
                  REALLIM_ADD) THEN
    ASM_REWRITE_TAC[REAL_ADD_LID]]);;

(* ------------------------------------------------------------------------- *)
(* The L^2 convergence on the small ball.                                    *)
(* ------------------------------------------------------------------------- *)

(* (B) and the Poincare inequality: the maps are L^2-close to the           *)
(* replacements on the replacement ball, with the weak partials.             *)

let CMC_REP_CLOSE = prove
 (`!S (w:num->real^2->real^K) (v:num->real^2->real^K) eta a R.
     compact S /\ &0 < R /\ (eta ---> &0) sequentially /\
     (!j. cmc_pmap S (w j)) /\
     (!j. smooth_map_on (ball(a,R)) (v j) /\ wan_w12 (ball(a,R)) (v j) /\
          wan_w120 (ball(a,R)) (\x. v j x - w j x) /\
          wan_dir (ball(a,R)) (\x. w j x - v j x) <= eta j)
     ==> (!j. (\x. w j x - v j x) IN lspace (ball(a,R)) (&2)) /\
         ((\j. lnorm (ball(a,R)) (&2) (\x. w j x - v j x)) ---> &0) sequentially /\
         !i. 1 <= i /\ i <= 2
             ==> (!j. (\x. wan_wd (:real^2) i (w j) x - partial_derivative i (v j) x)
                      IN lspace (ball(a,R)) (&2)) /\
                 ((\j. lnorm (ball(a,R)) (&2)
                         (\x. wan_wd (:real^2) i (w j) x - partial_derivative i (v j) x))
                  ---> &0) sequentially`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "V"))))) THEN
  SUBGOAL_THEN `!j. wan_w120 (ball(a:real^2,R)) (\x. (w:num->real^2->real^K) j x - v j x)`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN
    MP_TAC(ISPECL [`ball(a:real^2,R)`;
                   `\x. (v:num->real^2->real^K) j x - (w:num->real^2->real^K) j x`]
                  WAN_W120_NEG) THEN
    ASM_REWRITE_TAC[OPEN_BALL; VECTOR_NEG_SUB];
    ALL_TAC] THEN
  SUBGOAL_THEN `!j. &0 <= wan_dir (ball(a:real^2,R))
                         (\x. (w:num->real^2->real^K) j x - v j x)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC WAN_DIR_POS THEN
    UNDISCH_TAC `!j. wan_w120 (ball(a:real^2,R))
                       (\x. (w:num->real^2->real^K) j x - v j x)` THEN
    SIMP_TAC[wan_w120];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN
    UNDISCH_TAC `!j. wan_w120 (ball(a:real^2,R))
                       (\x. (w:num->real^2->real^K) j x - v j x)` THEN
    SIMP_TAC[wan_w120; wan_w12];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CMC_SQ_NULL THEN
    MAP_EVERY EXISTS_TAC [`eta:num->real`; `&4 * R pow 2`] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `j:num` THEN CONJ_TAC THENL
     [MATCH_MP_TAC LNORM_POS_LE THEN
      UNDISCH_TAC `!j. wan_w120 (ball(a:real^2,R))
                         (\x. (w:num->real^2->real^K) j x - v j x)` THEN
      SIMP_TAC[wan_w120; wan_w12];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&4 * R pow 2 * wan_dir (ball(a:real^2,R))
                                (\x. (w:num->real^2->real^K) j x - v j x)` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`(:2)`; `(:K)`] WAN_POINCARE0) THEN
      REWRITE_TAC[WAN_POINCARE0_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
      EXISTS_TAC `a:real^2` THEN ASM_REWRITE_TAC[OPEN_BALL; SUBSET_REFL];
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [REWRITE_TAC[REAL_LE_MUL; REAL_POS; REAL_LE_POW_2] THEN
                      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS; REAL_LE_POW_2];
                      ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!j. (\x. wan_wd (:real^2) i ((w:num->real^2->real^K) j) x -
             partial_derivative i (v j) x) IN lspace (ball(a:real^2,R)) (&2) /\
        lnorm (ball(a,R)) (&2)
          (\x. wan_wd (:real^2) i (w j) x - partial_derivative i (v j) x) pow 2
        <= wan_dir (ball(a,R)) (\x. w j x - v j x)`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN MATCH_MP_TAC CMC_WD_DIFF_SMOOTH THEN
    EXISTS_TAC `S:real^K->bool` THEN ASM_REWRITE_TAC[OPEN_BALL; BOUNDED_BALL] THEN
    USE_THEN "V" (MP_TAC o SPEC `j:num`) THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CMC_SQ_NULL THEN
  MAP_EVERY EXISTS_TAC [`eta:num->real`; `&1`] THEN ASM_REWRITE_TAC[REAL_MUL_LID] THEN
  X_GEN_TAC `j:num` THEN CONJ_TAC THENL
   [MATCH_MP_TAC LNORM_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `wan_dir (ball(a:real^2,R)) (\x. (w:num->real^2->real^K) j x - v j x)` THEN
  ASM_REWRITE_TAC[] THEN USE_THEN "V" (MP_TAC o SPEC `j:num`) THEN SIMP_TAC[]);;

(* Restriction of L^2 convergence to a measurable subset.                    *)

let CMC_L2_RESTRICT_NULL = prove
 (`!s t (f:num->real^2->real^K).
     (!j. f j IN lspace s (&2)) /\ ((\j. lnorm s (&2) (f j)) ---> &0) sequentially /\
     lebesgue_measurable t /\ t SUBSET s
     ==> (!j. f j IN lspace t (&2)) /\ ((\j. lnorm t (&2) (f j)) ---> &0) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!j. (f:num->real^2->real^K) j IN lspace t (&2)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\j. lnorm s (&2) ((f:num->real^2->real^K) j)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `j:num` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC LNORM_POS_LE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC WAN_LNORM2_SUBSET_LE THEN ASM_REWRITE_TAC[]]);;

let CMC_PD_CONTINUOUS = prove
 (`!s (f:real^2->real^K) i.
     open s /\ smooth_map_on s f ==> (partial_derivative i f) continuous_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
  MP_TAC(ISPECL [`[i:num]`; `s:real^2->bool`; `f:real^2->real^K`]
                SMOOTH_MAP_ON_ITERATED_PARTIAL) THEN
  ASM_REWRITE_TAC[iterated_partial]);;

(* The L^2 convergence on the small ball.                                    *)

let CMC_LOCAL_CONV = prove
 (`!S (w:num->real^2->real^K) (v:num->real^2->real^K) u eta a R rho.
     compact S /\ &0 < rho /\ rho <= R /\ (eta ---> &0) sequentially /\
     (!j. cmc_pmap S (w j)) /\
     (!j. smooth_map_on (ball(a,R)) (v j) /\ wan_w12 (ball(a,R)) (v j) /\
          wan_w120 (ball(a,R)) (\x. v j x - w j x) /\
          wan_dir (ball(a,R)) (\x. w j x - v j x) <= eta j) /\
     smooth_map_on (ball(a,rho)) u /\
     (?M. !j x. x IN ball(a,rho)
               ==> norm(v j x - u x) <= M /\
                   !i. 1 <= i /\ i <= 2
                       ==> norm(partial_derivative i (v j) x - partial_derivative i u x)
                           <= M) /\
     (!e. &0 < e
          ==> ?N. !j x. N <= j /\ x IN ball(a,rho)
                       ==> norm(v j x - u x) < e /\
                           !i. 1 <= i /\ i <= 2
                               ==> norm(partial_derivative i (v j) x -
                                        partial_derivative i u x) < e)
     ==> (!j. (\x. w j x - u x) IN lspace (ball(a,rho)) (&2)) /\
         ((\j. lnorm (ball(a,rho)) (&2) (\x. w j x - u x)) ---> &0) sequentially /\
         !i. 1 <= i /\ i <= 2
             ==> (!j. (\x. wan_wd (:real^2) i (w j) x - partial_derivative i u x)
                      IN lspace (ball(a,rho)) (&2)) /\
                 ((\j. lnorm (ball(a,rho)) (&2)
                         (\x. wan_wd (:real^2) i (w j) x - partial_derivative i u x))
                  ---> &0) sequentially`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "V")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_TAC `M:real`)
      (LABEL_TAC "UC"))))))))) THEN
  SUBGOAL_THEN `&0 < R` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ball(a:real^2,rho) SUBSET ball(a,R)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_BALL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `lebesgue_measurable(ball(a:real^2,rho)) /\ measurable(ball(a:real^2,rho))`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; OPEN_BALL; MEASURABLE_BALL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `w:num->real^2->real^K`; `v:num->real^2->real^K`;
                 `eta:num->real`; `a:real^2`; `R:real`] CMC_REP_CLOSE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D"))) THEN
  (* Continuity of the replacements and of their partials on the small ball. *)
  SUBGOAL_THEN
   `!j i. ((v:num->real^2->real^K) j) continuous_on ball(a,rho) /\
          (partial_derivative i (v j)) continuous_on ball(a,rho)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `ball(a:real^2,R)` THEN ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      USE_THEN "V" (MP_TAC o SPEC `j:num`) THEN SIMP_TAC[];
      MATCH_MP_TAC CMC_PD_CONTINUOUS THEN REWRITE_TAC[OPEN_BALL] THEN
      USE_THEN "V" (MP_TAC o SPEC `j:num`) THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(u:real^2->real^K) continuous_on ball(a,rho) /\
    !i. (partial_derivative i u) continuous_on ball(a,rho)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; CMC_PD_CONTINUOUS; OPEN_BALL]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`ball(a:real^2,rho)`;
                   `\j x. wan_wd (:real^2) i ((w:num->real^2->real^K) j) x -
                          partial_derivative i ((v:num->real^2->real^K) j) x`;
                   `\j x. partial_derivative i ((v:num->real^2->real^K) j) x -
                          partial_derivative i (u:real^2->real^K) x`;
                   `\j x. wan_wd (:real^2) i ((w:num->real^2->real^K) j) x -
                          partial_derivative i (u:real^2->real^K) x`] CMC_L2_SUM_NULL) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[VECTOR_ARITH `(a - b) + (b - c):real^K = a - c`] THEN
    ONCE_REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`ball(a:real^2,R)`; `ball(a:real^2,rho)`;
                     `\j x. wan_wd (:real^2) i ((w:num->real^2->real^K) j) x -
                            partial_derivative i ((v:num->real^2->real^K) j) x`]
                    CMC_L2_RESTRICT_NULL) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "D" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`ball(a:real^2,rho)`;
                   `\j x. partial_derivative i ((v:num->real^2->real^K) j) x -
                          partial_derivative i (u:real^2->real^K) x`] CMC_UNIF_LNORM) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[ETA_AX];
      GEN_TAC THEN EXISTS_TAC `M:real` THEN ASM_MESON_TAC[];
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      USE_THEN "UC" (MP_TAC o SPEC `e:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN ASM_MESON_TAC[]]] THEN
  MP_TAC(ISPECL [`ball(a:real^2,rho)`;
                 `\j x. (w:num->real^2->real^K) j x - (v:num->real^2->real^K) j x`;
                 `\j x. (v:num->real^2->real^K) j x - (u:real^2->real^K) x`;
                 `\j x. (w:num->real^2->real^K) j x - (u:real^2->real^K) x`]
                CMC_L2_SUM_NULL) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[VECTOR_ARITH `(a - b) + (b - c):real^K = a - c`] THEN
  ONCE_REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`ball(a:real^2,R)`; `ball(a:real^2,rho)`;
                   `\j x. (w:num->real^2->real^K) j x - (v:num->real^2->real^K) j x`]
                  CMC_L2_RESTRICT_NULL) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(a:real^2,rho)`;
                 `\j x. (v:num->real^2->real^K) j x - (u:real^2->real^K) x`] CMC_UNIF_LNORM) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[ETA_AX];
    GEN_TAC THEN EXISTS_TAC `M:real` THEN ASM_MESON_TAC[];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "UC" (MP_TAC o SPEC `e:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Joint continuity of the Euler-Lagrange density hmrm_eld of pc_hm_rmin_fv  *)
(* in its four vector arguments (point of the tube, partial of the map,      *)
(* variation, partial of the variation); limits along sequences and bounds   *)
(* on compact sets.                                                          *)
(* ------------------------------------------------------------------------- *)

let CMC_MDERIV_CONT = prove
 (`!V (M:real^K->real^K^K) D (y:real^N->real^K) (w:real^N->real^K).
     open V /\ smooth_map_on V ((vectorize:real^K^K->real^(K,K)finite_prod) o M) /\
     y continuous_on D /\ w continuous_on D /\ (!z. z IN D ==> y z IN V)
     ==> ((vectorize:real^K^K->real^(K,K)finite_prod) o (\z. mderiv M (y z) (w z)))
         continuous_on D`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `FF = (vectorize:real^K^K->real^(K,K)finite_prod) o (M:real^K->real^K^K)` THEN
  MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC `\z. matrix(frechet_derivative (FF:real^K->real^(K,K)finite_prod)
                           (at ((y:real^N->real^K) z))) ** (w:real^N->real^K) z` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[o_THM; mderiv; VECTORIZE_MATRIFY] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `linear(frechet_derivative (FF:real^K->real^(K,K)finite_prod)
                    (at ((y:real^N->real^K) z)))` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`V:real^K->bool`; `FF:real^K->real^(K,K)finite_prod`]
                    SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `(y:real^N->real^K) z`) THEN ASM_SIMP_TAC[] THEN
      SIMP_TAC[has_derivative];
      ASM_SIMP_TAC[MATRIX_WORKS]];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MATRIX_VECTOR_MUL THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(vectorize:real^K^(K,K)finite_prod->real^((K,K)finite_prod,K)finite_prod) o
    (\z. matrix(frechet_derivative (FF:real^K->real^(K,K)finite_prod)
                  (at ((y:real^N->real^K) z)))) =
    ((vectorize:real^K^(K,K)finite_prod->real^((K,K)finite_prod,K)finite_prod) o
     (\x. matrix(frechet_derivative FF (at x)))) o y`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `V:real^K->bool` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC GRGD_JACOBIAN_CONTINUOUS THEN ASM_REWRITE_TAC[];
    ASM SET_TAC[]]);;

(* The four coordinates of a point of the jet space.                         *)

let cmc_e1 = new_definition
 `cmc_e1 (z:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum) = fstcart z`;;

let cmc_e2 = new_definition
 `cmc_e2 (z:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum) = fstcart(sndcart z)`;;

let cmc_e3 = new_definition
 `cmc_e3 (z:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum) = fstcart(sndcart(sndcart z))`;;

let cmc_e4 = new_definition
 `cmc_e4 (z:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum) = sndcart(sndcart(sndcart z))`;;

let CMC_E_CONT = prove
 (`!(s:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum->bool).
     cmc_e1 continuous_on s /\ cmc_e2 continuous_on s /\
     cmc_e3 continuous_on s /\ cmc_e4 continuous_on s`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `cmc_e1 = (fstcart:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum->real^K) /\
    cmc_e2 = (fstcart:real^(K,(K,K)finite_sum)finite_sum->real^K) o
             (sndcart:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum->
                      real^(K,(K,K)finite_sum)finite_sum) /\
    cmc_e3 = (fstcart:real^(K,K)finite_sum->real^K) o
             (sndcart:real^(K,(K,K)finite_sum)finite_sum->real^(K,K)finite_sum) o
             (sndcart:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum->
                      real^(K,(K,K)finite_sum)finite_sum) /\
    cmc_e4 = (sndcart:real^(K,K)finite_sum->real^K) o
             (sndcart:real^(K,(K,K)finite_sum)finite_sum->real^(K,K)finite_sum) o
             (sndcart:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum->
                      real^(K,(K,K)finite_sum)finite_sum)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; cmc_e1; cmc_e2; cmc_e3; cmc_e4]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
  REPEAT(MATCH_MP_TAC LINEAR_COMPOSE THEN CONJ_TAC) THEN
  REWRITE_TAC[LINEAR_FSTCART; LINEAR_SNDCART]);;

(* Joint continuity of the Euler-Lagrange density on the tube.               *)

let CMC_ELD_CONT = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> (\z. lift(hmrm_eld S G (cmc_e1 z) (cmc_e2 z) (cmc_e3 z) (cmc_e4 z)))
         continuous_on {z | cmc_e1 z IN cm_tube S d}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  ABBREV_TAC `D = {z:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum |
                   cmc_e1 z IN cm_tube S d}` THEN
  SUBGOAL_THEN `!z:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum.
                  z IN D ==> cmc_e1 z IN cm_tube S d`
  ASSUME_TAC THENL [EXPAND_TAC "D" THEN SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  MP_TAC(ISPEC `D:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum->bool` CMC_E_CONT) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `((vectorize:real^K^K->real^(K,K)finite_prod) o
     (\z:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum.
        jacobian (closest_point S) (at (cmc_e1 z)))) continuous_on D`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(vectorize:real^K^K->real^(K,K)finite_prod) o
      (\z:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum.
         jacobian (closest_point S) (at (cmc_e1 z))) =
      ((vectorize:real^K^K->real^(K,K)finite_prod) o
       (\y. jacobian (closest_point S) (at y))) o cmc_e1`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cm_tube S d:real^K->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((vectorize:real^K^K->real^(K,K)finite_prod) o
     (\z:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum. (G:real^K->real^K^K) (cmc_e1 z)))
    continuous_on D`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(vectorize:real^K^K->real^(K,K)finite_prod) o
      (\z:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum. (G:real^K->real^K^K) (cmc_e1 z)) =
      ((vectorize:real^K^K->real^(K,K)finite_prod) o G) o cmc_e1`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^K)` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((vectorize:real^K^K->real^(K,K)finite_prod) o
     (\z:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum.
        mderiv (\y. jacobian (closest_point S) (at y)) (cmc_e1 z) (cmc_e3 z)))
    continuous_on D`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMC_MDERIV_CONT THEN EXISTS_TAC `cm_tube S d:real^K->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((vectorize:real^K^K->real^(K,K)finite_prod) o
     (\z:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum.
        mderiv (G:real^K->real^K^K) (cmc_e1 z)
               (jacobian (closest_point S) (at (cmc_e1 z)) ** cmc_e3 z)))
    continuous_on D`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMC_MDERIV_CONT THEN EXISTS_TAC `(:real^K)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    MATCH_MP_TAC CONTINUOUS_ON_MATRIX_VECTOR_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[hmrm_eld; LIFT_ADD; LIFT_CMUL] THEN
  MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
      MATCH_MP_TAC CONTINUOUS_ON_MATRIX_VECTOR_MUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_MATRIX_VECTOR_MUL THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_MATRIX_VECTOR_MUL THEN ASM_REWRITE_TAC[]]);;

(* Sequential continuity and bounds of the density.                          *)

let CMC_ELD_LIM = prove
 (`!S (G:real^K->real^K^K) d p q h k (pj:num->real^K) qj hj kj.
     cm_target S G d /\ p IN S /\
     (pj --> p) sequentially /\ (qj --> q) sequentially /\
     (hj --> h) sequentially /\ (kj --> k) sequentially
     ==> ((\j. hmrm_eld S G (pj j) (qj j) (hj j) (kj j)) ---> hmrm_eld S G p q h k)
         sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CMC_ELD_CONT) THEN
  ABBREV_TAC `D = {z:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum |
                   cmc_e1 z IN cm_tube S d}` THEN
  SUBGOAL_THEN `open(D:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum->bool)` ASSUME_TAC
  THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `(:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum)` CMC_E_CONT) THEN
    SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  ABBREV_TAC `z0:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum =
              pastecart p (pastecart q (pastecart h k))` THEN
  SUBGOAL_THEN `(z0:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum) IN D` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["D"; "z0"] THEN
    REWRITE_TAC[IN_ELIM_THM; cmc_e1; FSTCART_PASTECART] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. lift(hmrm_eld S (G:real^K->real^K^K) (cmc_e1 z) (cmc_e2 z) (cmc_e3 z) (cmc_e4 z)))
    continuous (at (z0:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum))`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\j. pastecart ((pj:num->real^K) j)
                    (pastecart ((qj:num->real^K) j)
                               (pastecart ((hj:num->real^K) j) ((kj:num->real^K) j))))
     --> (z0:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum)) sequentially`
  ASSUME_TAC THENL
   [EXPAND_TAC "z0" THEN REPEAT(MATCH_MP_TAC LIM_PASTECART THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\z. lift(hmrm_eld S (G:real^K->real^K^K) (cmc_e1 z) (cmc_e2 z) (cmc_e3 z) (cmc_e4 z))`;
    `sequentially`;
    `\j. pastecart ((pj:num->real^K) j)
                   (pastecart ((qj:num->real^K) j)
                              (pastecart ((hj:num->real^K) j) ((kj:num->real^K) j)))`;
    `z0:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum`] LIM_CONTINUOUS_FUNCTION) THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "z0" THEN
  REWRITE_TAC[cmc_e1; cmc_e2; cmc_e3; cmc_e4; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  REWRITE_TAC[TENDSTO_REAL; o_DEF]);;

let CMC_ELD_BOUND = prove
 (`!S (G:real^K->real^K^K) d M.
     cm_target S G d
     ==> ?C. !p q h k. p IN S /\ norm q <= M /\ norm h <= M /\ norm k <= M
                       ==> abs(hmrm_eld S G p q h k) <= C`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CMC_ELD_CONT) THEN
  ABBREV_TAC `Kc:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum->bool =
              S PCROSS (cball(vec 0:real^K,M) PCROSS
                        (cball(vec 0:real^K,M) PCROSS cball(vec 0:real^K,M)))` THEN
  SUBGOAL_THEN `compact(Kc:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum->bool)`
  ASSUME_TAC THENL
   [EXPAND_TAC "Kc" THEN ASM_SIMP_TAC[COMPACT_PCROSS; COMPACT_CBALL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. lift(hmrm_eld S (G:real^K->real^K^K) (cmc_e1 z) (cmc_e2 z) (cmc_e3 z) (cmc_e4 z)))
    continuous_on (Kc:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum->bool)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET)) THEN
    EXPAND_TAC "Kc" THEN
    REWRITE_TAC[SUBSET; FORALL_IN_PCROSS; IN_ELIM_THM; cmc_e1; FSTCART_PASTECART] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\z. lift(hmrm_eld S (G:real^K->real^K^K) (cmc_e1 z) (cmc_e2 z) (cmc_e3 z) (cmc_e4 z))`;
    `Kc:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum->bool`] COMPACT_CONTINUOUS_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `C:real` THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (p:real^K) (pastecart (q:real^K)
                                        (pastecart (h:real^K) (k:real^K)))`) THEN
  REWRITE_TAC[cmc_e1; cmc_e2; cmc_e3; cmc_e4; FSTCART_PASTECART; SNDCART_PASTECART;
              NORM_LIFT] THEN
  DISCH_THEN MATCH_MP_TAC THEN EXPAND_TAC "Kc" THEN
  ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_CBALL_0]);;

(* Smooth maps on a neighbourhood of the closure of a bounded open set are  *)
(* W^{1,2} there, with their classical partials as weak partials.           *)

let CMC_W12_SMOOTH_SUB = prove
 (`!s (f:real^2->real^K) t.
     open s /\ smooth_map_on s f /\ open t /\ bounded t /\ closure t SUBSET s
     ==> wan_w12 t f /\
         (!i. 1 <= i /\ i <= 2 ==> wan_wpd t i f (\x. partial_derivative i f x)) /\
         ?B. !x. x IN t
                 ==> norm(f x) <= B /\
                     !i. 1 <= i /\ i <= 2 ==> norm(partial_derivative i f x) <= B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact(closure t:real^2->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COMPACT_CLOSURE]; ALL_TAC] THEN
  SUBGOAL_THEN `(t:real^2->bool) SUBSET s` ASSUME_TAC THENL
   [MP_TAC(ISPEC `t:real^2->bool` CLOSURE_SUBSET) THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!g:real^2->real^K. g continuous_on s
                ==> ?B. !x. x IN closure t ==> norm(g x) <= B`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`g:real^2->real^K`; `closure t:real^2->bool`]
                  COMPACT_CONTINUOUS_IMAGE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
      REWRITE_TAC[bounded; FORALL_IN_IMAGE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^2->real^K) continuous_on s /\
                (partial_derivative 1 f) continuous_on s /\
                (partial_derivative 2 f) continuous_on s`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; CMC_PD_CONTINUOUS]; ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `B0:real` o C MATCH_MP
    (ASSUME `(f:real^2->real^K) continuous_on s`)) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `B1:real` o C MATCH_MP
    (ASSUME `(partial_derivative 1 (f:real^2->real^K)) continuous_on s`)) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `B2:real` o C MATCH_MP
    (ASSUME `(partial_derivative 2 (f:real^2->real^K)) continuous_on s`)) THEN
  SUBGOAL_THEN `!x. x IN t ==> norm((f:real^2->real^K) x) <= B0 /\
                               norm(partial_derivative 1 f x) <= B1 /\
                               norm(partial_derivative 2 f x) <= B2`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(ISPEC `t:real^2->bool` CLOSURE_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `measurable(t:real^2->bool) /\ lebesgue_measurable(t:real^2->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MEASURABLE_OPEN; LEBESGUE_MEASURABLE_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!g:real^2->real^K c. g continuous_on s /\ (!x. x IN t ==> norm(g x) <= c)
                         ==> g IN lspace t (&2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`t:real^2->bool`; `g:real^2->real^K`; `c:real`] CMC_BOUNDED_LNORM) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:2)`; `(:K)`] WAN_W12_C1) THEN REWRITE_TAC[WAN_W12_C1_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`t:real^2->bool`; `f:real^2->real^K`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[DIMINDEX_2] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`s:real^2->bool`; `t:real^2->bool`; `f:real^2->real^K`]
                    SMOOTH_MAP_ON_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[smooth_map_on];
      FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `B0:real` THEN ASM_SIMP_TAC[];
      REWRITE_TAC[ARITH_RULE `1 <= i /\ i <= 2 <=> i = 1 \/ i = 2`] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[ETA_AX] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[DIMINDEX_2]; ALL_TAC] THEN
  EXISTS_TAC `max B0 (max B1 B2)` THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[REAL_ARITH `x <= a ==> x <= max a (max b c)`]; ALL_TAC] THEN
  SUBGOAL_THEN `i = 1 \/ i = 2` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[REAL_ARITH `x <= b ==> x <= max a (max b c)`;
                REAL_ARITH `x <= c ==> x <= max a (max b c)`]);;

(* ------------------------------------------------------------------------- *)
(* Limits of harmonic maps converging with first partials (pointwise, with   *)
(* bounded partials) to a smooth S-valued map are harmonic: the weak         *)
(* Euler-Lagrange integrals of HMRM_FIRST_VARIATION_W12 pass to the limit by *)
(* dominated convergence.                                                    *)
(* ------------------------------------------------------------------------- *)

let CMC_ELD_SPIKE = prove
 (`!S (G:real^K->real^K^K) (f:real^2->real^K) (phi:real^2->real^K) t i.
     open t /\ wan_w12 t f /\ 1 <= i /\ i <= 2 /\
     wan_wpd t i f (\x. partial_derivative i f x)
     ==> integral t (\x. lift(hmrm_eld S G (f x) (wan_wd t i f x) (phi x)
                                       (partial_derivative i phi x))) =
         integral t (\x. lift(hmrm_eld S G (f x) (partial_derivative i f x) (phi x)
                                       (partial_derivative i phi x))) /\
         ((\x. lift(hmrm_eld S G (f x) (wan_wd t i f x) (phi x)
                             (partial_derivative i phi x))) integrable_on t <=>
          (\x. lift(hmrm_eld S G (f x) (partial_derivative i f x) (phi x)
                             (partial_derivative i phi x))) integrable_on t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:real^2->bool`; `i:num`; `f:real^2->real^K`;
                 `\x. partial_derivative i (f:real^2->real^K) x`] WAN_WD_UNIQUE) THEN
  ASM_REWRITE_TAC[DIMINDEX_2] THEN DISCH_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_SPIKE; MATCH_MP_TAC INTEGRABLE_SPIKE_EQ] THEN
  EXISTS_TAC `{x | x IN t /\ ~(wan_wd t i (f:real^2->real^K) x = partial_derivative i f x)}` THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN MESON_TAC[]);;

let CMC_HARMONIC_LIMIT = prove
 (`!S (G:real^K->real^K^K) d (v:num->real^2->real^K) u s M.
     cm_target S G d /\ open s /\
     (!j. cm_harmonic S G s (v j)) /\
     smooth_map_on s u /\ (!x. x IN s ==> u x IN S) /\
     (!x. x IN s ==> ((\j. v j x) --> u x) sequentially) /\
     (!i x. 1 <= i /\ i <= 2 /\ x IN s
            ==> ((\j. partial_derivative i (v j) x) --> partial_derivative i u x)
                sequentially) /\
     (!j i x. 1 <= i /\ i <= 2 /\ x IN s ==> norm(partial_derivative i (v j) x) <= M)
     ==> cm_harmonic S G s u`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "HV") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "L0")
    (CONJUNCTS_THEN2 (LABEL_TAC "L1") (LABEL_TAC "BD")))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  ASM_REWRITE_TAC[cm_harmonic] THEN
  MAP_EVERY X_GEN_TAC [`phi:real^2->real^K`; `t:real^2->bool`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(t:real^2->bool) SUBSET s` ASSUME_TAC THENL
   [MP_TAC(ISPEC `t:real^2->bool` CLOSURE_SUBSET) THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!j. smooth_map_on s ((v:num->real^2->real^K) j) /\
                    (!x. x IN s ==> v j x IN S)`
  ASSUME_TAC THENL
   [GEN_TAC THEN USE_THEN "HV" (MP_TAC o SPEC `j:num`) THEN SIMP_TAC[cm_harmonic];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. wan_w12 t ((v:num->real^2->real^K) j) /\
        (!i. 1 <= i /\ i <= 2 ==> wan_wpd t i (v j) (\x. partial_derivative i (v j) x))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `(v:num->real^2->real^K) j`; `t:real^2->bool`]
                  CMC_W12_SMOOTH_SUB) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_w12 t (u:real^2->real^K) /\
    (!i. 1 <= i /\ i <= 2 ==> wan_wpd t i u (\x. partial_derivative i u x))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^2->bool`; `u:real^2->real^K`; `t:real^2->bool`]
                  CMC_W12_SMOOTH_SUB) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?Mp. !x. x IN t ==> norm((phi:real^2->real^K) x) <= Mp /\
                       !i. 1 <= i /\ i <= 2 ==> norm(partial_derivative i phi x) <= Mp`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:real^2)`; `phi:real^2->real^K`; `t:real^2->bool`]
                  CMC_W12_SMOOTH_SUB) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [wan_vtest]) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `max M Mp`]
                CMC_ELD_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `C:real` (LABEL_TAC "C")) THEN
  (* The first variation of the limit. *)
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `t:real^2->bool`;
                 `u:real^2->real^K`; `phi:real^2->real^K`] HMRM_FIRST_VARIATION_W12) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IU") (LABEL_TAC "DU")) THEN
  SUBGOAL_THEN
   `sum(1..2) (\i. drop(integral t
       (\x. lift(hmrm_eld S G ((u:real^2->real^K) x) (wan_wd t i u x)
                          ((phi:real^2->real^K) x) (partial_derivative i phi x))))) = &0`
  ASSUME_TAC THENL
   [ALL_TAC;
    REMOVE_THEN "DU" MP_TAC THEN ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO]] THEN
  (* The vanishing first variations of the sequence. *)
  SUBGOAL_THEN
   `!j. sum(1..2) (\i. drop(integral t
          (\x. lift(hmrm_eld S G ((v:num->real^2->real^K) j x) (wan_wd t i (v j) x)
                             ((phi:real^2->real^K) x) (partial_derivative i phi x))))) = &0 /\
        (!i. 1 <= i /\ i <= 2
             ==> (\x. lift(hmrm_eld S G ((v:num->real^2->real^K) j x) (wan_wd t i (v j) x)
                             ((phi:real^2->real^K) x) (partial_derivative i phi x)))
                 integrable_on t)`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `t:real^2->bool`;
                   `(v:num->real^2->real^K) j`; `phi:real^2->real^K`]
                  HMRM_FIRST_VARIATION_W12) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DV")) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `((\e. cm_gen G t (\x. closest_point S ((v:num->real^2->real^K) j x + e % phi x)))
       has_real_derivative &0) (atreal (&0))`
    (LABEL_TAC "D0") THENL
     [USE_THEN "HV" (MP_TAC o SPEC `j:num`) THEN REWRITE_TAC[cm_harmonic] THEN
      DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REMOVE_THEN "DV" (fun th1 -> REMOVE_THEN "D0" (fun th2 ->
      MP_TAC(MATCH_MP REAL_DERIVATIVE_UNIQUE_ATREAL (CONJ th1 th2)))) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* Dominated convergence for each of the two integrals. *)
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> ((\j. integral t
               (\x. lift(hmrm_eld S G ((v:num->real^2->real^K) j x) (wan_wd t i (v j) x)
                                  ((phi:real^2->real^K) x) (partial_derivative i phi x))))
             --> integral t
               (\x. lift(hmrm_eld S G ((u:real^2->real^K) x) (wan_wd t i u x)
                                  (phi x) (partial_derivative i phi x)))) sequentially`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `u:real^2->real^K`;
                   `phi:real^2->real^K`; `t:real^2->bool`; `i:num`] CMC_ELD_SPIKE) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN
    SUBGOAL_THEN
     `!j. integral t
            (\x. lift(hmrm_eld S G ((v:num->real^2->real^K) j x) (wan_wd t i (v j) x)
                               ((phi:real^2->real^K) x) (partial_derivative i phi x))) =
          integral t
            (\x. lift(hmrm_eld S G (v j x) (partial_derivative i (v j) x)
                               (phi x) (partial_derivative i phi x))) /\
          (\x. lift(hmrm_eld S G (v j x) (partial_derivative i (v j) x)
                             (phi x) (partial_derivative i phi x))) integrable_on t`
    ASSUME_TAC THENL
     [X_GEN_TAC `j:num` THEN
      MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `(v:num->real^2->real^K) j`;
                     `phi:real^2->real^K`; `t:real^2->bool`; `i:num`] CMC_ELD_SPIKE) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
      ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[]] THEN
    MP_TAC(ISPECL
     [`\j x. lift(hmrm_eld S G ((v:num->real^2->real^K) j x) (partial_derivative i (v j) x)
                           ((phi:real^2->real^K) x) (partial_derivative i phi x))`;
      `\x. lift(hmrm_eld S G ((u:real^2->real^K) x) (partial_derivative i u x)
                         ((phi:real^2->real^K) x) (partial_derivative i phi x))`;
      `\x:real^2. lift C`; `t:real^2->bool`] DOMINATED_CONVERGENCE) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ALL_TAC; SIMP_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[INTEGRABLE_ON_CONST] THEN DISJ2_TAC THEN ASM_SIMP_TAC[MEASURABLE_OPEN];
      MAP_EVERY X_GEN_TAC [`j:num`; `x:real^2`] THEN DISCH_TAC THEN
      REWRITE_TAC[NORM_LIFT; LIFT_DROP] THEN USE_THEN "C" MATCH_MP_TAC THEN
      SUBGOAL_THEN `(x:real^2) IN s` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[];
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `M:real` THEN
        CONJ_TAC THENL [USE_THEN "BD" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Mp:real` THEN
        CONJ_TAC THENL [ASM_MESON_TAC[]; REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Mp:real` THEN
        CONJ_TAC THENL [ASM_MESON_TAC[]; REAL_ARITH_TAC]];
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(x:real^2) IN s` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                     `(u:real^2->real^K) x`; `partial_derivative i (u:real^2->real^K) x`;
                     `(phi:real^2->real^K) x`; `partial_derivative i (phi:real^2->real^K) x`;
                     `\j. (v:num->real^2->real^K) j x`;
                     `\j. partial_derivative i ((v:num->real^2->real^K) j) x`;
                     `\j:num. (phi:real^2->real^K) x`;
                     `\j:num. partial_derivative i (phi:real^2->real^K) x`] CMC_ELD_LIM) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[LIM_CONST] THEN CONJ_TAC THENL
         [USE_THEN "L0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          USE_THEN "L1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
        REWRITE_TAC[TENDSTO_REAL; o_DEF]]];
    ALL_TAC] THEN
  (* The limit of the sums. *)
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
  EXISTS_TAC
   `\j. sum(1..2) (\i. drop(integral t
          (\x. lift(hmrm_eld S G ((v:num->real^2->real^K) j x) (wan_wd t i (v j) x)
                             ((phi:real^2->real^K) x) (partial_derivative i phi x)))))` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUM_2] THEN MATCH_MP_TAC REALLIM_ADD THEN
    REWRITE_TAC[TENDSTO_REAL; o_DEF; LIFT_DROP] THEN CONJ_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    ASM_REWRITE_TAC[REALLIM_CONST]]);;

(* ------------------------------------------------------------------------- *)
(* The local theorem (CM Lemma B.23 on one ball): if the energies on         *)
(* ball(a,R) stay below e0, a subsequence converges in L^2 with the weak     *)
(* partials on ball(a,R/32) to a smooth harmonic map.                        *)
(* ------------------------------------------------------------------------- *)

(* The replacements of the whole sequence on ball(a,R/8).                    *)

let CMC_REP_SEQ = prove
 (`!S (G:real^K->real^K^K) d eL (C:num->real) e0 (w:num->real^2->real^K) eta a R.
     cm_target S G d /\ &0 < eL /\ (!k. &0 < C k) /\
     (!(a:real^2) r (u:real^2->real^K) l x.
         &0 < r /\ cm_harmonic S G (ball(a,r)) u /\ wan_w12 (ball(a,r)) u /\
         wan_gdir (ball(a,r)) G u <= eL /\
         ALL (\i. 1 <= i /\ i <= 2) l /\ ~(l = []) /\ x IN ball(a,r / &2)
         ==> r pow (LENGTH l) * norm(iterated_partial l u x)
             <= C (LENGTH l) * sqrt(wan_gdir (ball(a,r)) G u)) /\
     (!(a:real^2) r (u:real^2->real^K).
         &0 < r /\ cm_cmap S (ball(a,r)) u /\ wan_gdir (ball(a,r)) G u <= eL
         ==> ?w. cm_minimizer S G (ball(a,r)) w /\
                 wan_w120 (ball(a,r)) (\x. w x - u x) /\
                 cm_cmap S (ball(a,r)) w /\ cm_harmonic S G (ball(a,r)) w /\
                 (!x. x IN sphere(a,r) ==> w x = u x)) /\
     &0 < e0 /\ e0 <= eL /\
     (!j. cmc_pmap S (w j) /\ cmc_ah S G e0 (eta j) (w j)) /\
     &0 < R /\ (!j. wan_gdir (ball(a,R)) G (w j) < e0)
     ==> ?v. !j. cm_harmonic S G (ball(a,R / &8)) (v j) /\
                 wan_w12 (ball(a,R / &8)) (v j) /\
                 wan_w120 (ball(a,R / &8)) (\x. v j x - w j x) /\
                 wan_dir (ball(a,R / &8)) (\x. w j x - v j x) <= eta j /\
                 (!l x. ALL (\i. 1 <= i /\ i <= 2) l /\ ~(l = []) /\
                        x IN ball(a,R / &16)
                        ==> norm(iterated_partial l (v j) x)
                            <= (C (LENGTH l) * sqrt e0) / (R / &8) pow (LENGTH l))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "EPS")
    (CONJUNCTS_THEN2 (LABEL_TAC "REP") STRIP_ASSUME_TAC))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_target]) THEN
  REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `j:num` THEN
  SUBGOAL_THEN `&0 < R / &8` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `wan_gdir (ball(a:real^2,R / &8)) G ((w:num->real^2->real^K) j) <
                wan_gdir (ball(a,R)) G (w j) \/
                wan_gdir (ball(a:real^2,R / &8)) G ((w:num->real^2->real^K) j) =
                wan_gdir (ball(a,R)) G (w j)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_LE_LT] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                   `(w:num->real^2->real^K) j`] CMC_GDIR_PEN) THEN
    ASM_SIMP_TAC[OPEN_BALL] THEN DISCH_THEN(K ALL_TAC) THEN
    MATCH_MP_TAC CMC_PEN_MONO THEN MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; OPEN_BALL] THEN
    MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_gdir (ball(a:real^2,R / &8)) G ((w:num->real^2->real^K) j) < e0`
  ASSUME_TAC THENL
   [MP_TAC(SPEC `j:num` (ASSUME `!j. wan_gdir (ball(a:real^2,R)) G
                                          ((w:num->real^2->real^K) j) < e0`)) THEN
    UNDISCH_TAC `wan_gdir (ball(a:real^2,R / &8)) G ((w:num->real^2->real^K) j) <
                 wan_gdir (ball(a,R)) G (w j) \/
                 wan_gdir (ball(a:real^2,R / &8)) G ((w:num->real^2->real^K) j) =
                 wan_gdir (ball(a,R)) G (w j)` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `eL:real`;
                 `C:num->real`; `(w:num->real^2->real^K) j`; `a:real^2`; `R / &8`]
                CMC_REP_ONE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`wan_gdir (ball(a:real^2,R / &8)) G ((w:num->real^2->real^K) j) < e0`;
      `e0:real <= eL`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^2->real^K` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [(* property (B) for one ball *)
    MP_TAC(SPEC `j:num` (ASSUME `!j. cmc_pmap S ((w:num->real^2->real^K) j) /\
                                    cmc_ah S G e0 (eta j) (w j)`)) THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[cmc_ah] THEN
    DISCH_THEN(MP_TAC o SPECL [`1`; `\k:num. (a:real^2)`; `\k:num. (R:real)`;
                               `\k:num. (u:real^2->real^K)`]) THEN
    REWRITE_TAC[SUM_SING_NUMSEG] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MESON_TAC[ARITH_RULE `~(1 <= k /\ k < l /\ l <= 1)`];
      SIMP_TAC[]];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (R / &8) pow (LENGTH (l:(num)list))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(C:num->real) (LENGTH (l:(num)list)) *
              sqrt(wan_gdir (ball(a:real^2,R / &8)) G ((w:num->real^2->real^K) j))` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `R / &8 / &2 = R / &16` (fun th -> ASM_REWRITE_TAC[th]) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [ASM_MESON_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  MATCH_MP_TAC SQRT_MONO_LE THEN ASM_MESON_TAC[REAL_LT_IMP_LE]);;

let CMC_LENGTH_SING = prove
 (`!i:num. LENGTH [i] = 1`,
  REWRITE_TAC[LENGTH; ONE]);;

(* The local theorem.                                                         *)

let CMC_LOCAL = prove
 (`!S (G:real^K->real^K^K) d eL (C:num->real) e0 (w:num->real^2->real^K) eta a R.
     cm_target S G d /\ &0 < eL /\ (!k. &0 < C k) /\
     (!(a:real^2) r (u:real^2->real^K) l x.
         &0 < r /\ cm_harmonic S G (ball(a,r)) u /\ wan_w12 (ball(a,r)) u /\
         wan_gdir (ball(a,r)) G u <= eL /\
         ALL (\i. 1 <= i /\ i <= 2) l /\ ~(l = []) /\ x IN ball(a,r / &2)
         ==> r pow (LENGTH l) * norm(iterated_partial l u x)
             <= C (LENGTH l) * sqrt(wan_gdir (ball(a,r)) G u)) /\
     (!(a:real^2) r (u:real^2->real^K).
         &0 < r /\ cm_cmap S (ball(a,r)) u /\ wan_gdir (ball(a,r)) G u <= eL
         ==> ?w. cm_minimizer S G (ball(a,r)) w /\
                 wan_w120 (ball(a,r)) (\x. w x - u x) /\
                 cm_cmap S (ball(a,r)) w /\ cm_harmonic S G (ball(a,r)) w /\
                 (!x. x IN sphere(a,r) ==> w x = u x)) /\
     &0 < e0 /\ e0 <= eL /\ (eta ---> &0) sequentially /\
     (!j. cmc_pmap S (w j) /\ cmc_ah S G e0 (eta j) (w j)) /\
     &0 < R /\ (!j. wan_gdir (ball(a,R)) G (w j) < e0)
     ==> ?(t:num->num) u.
           (!m n. m < n ==> t m < t n) /\
           smooth_map_on (ball(a,R / &32)) u /\
           cm_harmonic S G (ball(a,R / &32)) u /\
           (!j. (\x. w (t j) x - u x) IN lspace (ball(a,R / &32)) (&2)) /\
           ((\j. lnorm (ball(a,R / &32)) (&2) (\x. w (t j) x - u x)) ---> &0)
           sequentially /\
           (!i. 1 <= i /\ i <= 2
                ==> (!j. (\x. wan_wd (:real^2) i (w (t j)) x - partial_derivative i u x)
                         IN lspace (ball(a,R / &32)) (&2)) /\
                    ((\j. lnorm (ball(a,R / &32)) (&2)
                            (\x. wan_wd (:real^2) i (w (t j)) x -
                                 partial_derivative i u x)) ---> &0) sequentially)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `eL:real`;
                 `C:num->real`; `e0:real`; `w:num->real^2->real^K`; `eta:num->real`;
                 `a:real^2`; `R:real`] CMC_REP_SEQ) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:num->real^2->real^K` (LABEL_TAC "V")) THEN
  SUBGOAL_THEN `?MS. &0 < MS /\ !z:real^K. z IN S ==> norm z <= MS` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPACT_IMP_BOUNDED; BOUNDED_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `ball(a:real^2,R / &32) SUBSET ball(a,R / &16) /\
                ball(a:real^2,R / &16) SUBSET ball(a,R / &8)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?B:num->real. !n. B n = if n = 0 then MS
                                        else ((C:num->real) n * sqrt e0) / (R / &8) pow n`
  (X_CHOOSE_THEN `B:num->real` (LABEL_TAC "BDEF")) THENL
   [EXISTS_TAC `\n. if n = 0 then MS else ((C:num->real) n * sqrt e0) / (R / &8) pow n` THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!l j x. ALL (\i. 1 <= i /\ i <= 2) l /\ x IN ball(a:real^2,R / &16)
            ==> norm(iterated_partial l ((v:num->real^2->real^K) j) x) <=
                (B:num->real) (LENGTH l)`
  (LABEL_TAC "VB") THENL
   [MAP_EVERY X_GEN_TAC [`l:(num)list`; `j:num`; `x:real^2`] THEN STRIP_TAC THEN
    USE_THEN "BDEF" (fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `l:(num)list = []` THENL
     [ASM_REWRITE_TAC[LENGTH; iterated_partial] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      USE_THEN "V" (MP_TAC o SPEC `j:num`) THEN REWRITE_TAC[cm_harmonic] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT1) THEN ASM SET_TAC[];
      ASM_REWRITE_TAC[LENGTH_EQ_NIL] THEN
      USE_THEN "V" (MP_TAC o SPEC `j:num`) THEN
      DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REMOVE_THEN "BDEF" (fun th -> ASSUME_TAC(REWRITE_RULE[] (SPEC `0` th))) THEN
  MP_TAC(ISPECL [`v:num->real^2->real^K`; `a:real^2`; `R / &32`; `B:num->real`]
                CMC_CINF_COMPACT) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&2 * R / &32 = R / &16` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN GEN_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(a:real^2,R / &8)` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "V" (MP_TAC o SPEC `j:num`) THEN
    SIMP_TAC[cm_harmonic];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:num->num` (X_CHOOSE_THEN `u:real^2->real^K`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CV"))))) THEN
  (* Orders zero and one. *)
  SUBGOAL_THEN
   `(!x. x IN ball(a:real^2,R / &32) ==> norm((u:real^2->real^K) x) <= MS) /\
    (!e. &0 < e ==> ?N. !n x. N <= n /\ x IN ball(a,R / &32)
                              ==> norm((v:num->real^2->real^K) ((t:num->num) n) x - u x) < e)`
  (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "U0")) THENL
   [USE_THEN "CV" (MP_TAC o SPEC `[]:(num)list`) THEN
    REWRITE_TAC[ALL; LENGTH; iterated_partial] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> (!x. x IN ball(a:real^2,R / &32)
                 ==> norm(partial_derivative i (u:real^2->real^K) x) <= (B:num->real) 1) /\
            (!e. &0 < e
                 ==> ?N. !n x. N <= n /\ x IN ball(a,R / &32)
                               ==> norm(partial_derivative i
                                          ((v:num->real^2->real^K) ((t:num->num) n)) x -
                                        partial_derivative i u x) < e)`
  (LABEL_TAC "U1") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "CV" (MP_TAC o SPEC `[i:num]`) THEN
    REWRITE_TAC[ALL; CMC_LENGTH_SING; iterated_partial] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `t:num->num` THEN EXISTS_TAC `u:real^2->real^K` THEN ASM_REWRITE_TAC[] THEN
  (* Harmonicity of the limit. *)
  SUBGOAL_THEN `cm_harmonic S G (ball(a:real^2,R / &32)) (u:real^2->real^K)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMC_HARMONIC_LIMIT THEN
    MAP_EVERY EXISTS_TAC [`d:real`; `\j. (v:num->real^2->real^K) ((t:num->num) j)`;
                          `(B:num->real) 1`] THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN REPEAT CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC HMC_HARMONIC_SUBSET THEN
      EXISTS_TAC `ball(a:real^2,R / &8)` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ASM SET_TAC[]];
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      MATCH_MP_TAC(ISPEC `sequentially` LIM_IN_CLOSED_SET) THEN
      EXISTS_TAC `\j. (v:num->real^2->real^K) ((t:num->num) j) x` THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED; TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
       [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `j:num` THEN REWRITE_TAC[] THEN
        USE_THEN "V" (MP_TAC o SPEC `(t:num->num) j`) THEN REWRITE_TAC[cm_harmonic] THEN
        DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT1) THEN ASM SET_TAC[];
        REWRITE_TAC[LIM_SEQUENTIALLY; dist] THEN ASM_MESON_TAC[LE_REFL]];
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      REWRITE_TAC[LIM_SEQUENTIALLY; dist] THEN ASM_MESON_TAC[LE_REFL];
      MAP_EVERY X_GEN_TAC [`i:num`; `x:real^2`] THEN STRIP_TAC THEN
      REWRITE_TAC[LIM_SEQUENTIALLY; dist] THEN
      USE_THEN "U1" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN ASM_MESON_TAC[LE_REFL];
      MAP_EVERY X_GEN_TAC [`j:num`; `i:num`; `x:real^2`] THEN STRIP_TAC THEN
      USE_THEN "VB" (MP_TAC o SPECL [`[i:num]`; `(t:num->num) j`; `x:real^2`]) THEN
      REWRITE_TAC[ALL; CMC_LENGTH_SING; iterated_partial] THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; SIMP_TAC[]]];
    ASM_REWRITE_TAC[]] THEN
  (* The L^2 convergence. *)
  MP_TAC(ISPECL [`S:real^K->bool`; `\j. (w:num->real^2->real^K) ((t:num->num) j)`;
                 `\j. (v:num->real^2->real^K) ((t:num->num) j)`; `u:real^2->real^K`;
                 `\j. (eta:num->real) ((t:num->num) j)`; `a:real^2`; `R / &8`; `R / &32`]
                CMC_LOCAL_CONV) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    UNDISCH_TAC `&0 < R` THEN REAL_ARITH_TAC;
    UNDISCH_TAC `&0 < R` THEN REAL_ARITH_TAC;
    MATCH_MP_TAC HMD_REALLIM_SUBSEQ THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[];
    GEN_TAC THEN USE_THEN "V" (MP_TAC o SPEC `(t:num->num) j`) THEN
    SIMP_TAC[cm_harmonic];
    ASM_REWRITE_TAC[];
    EXISTS_TAC `&2 * max MS ((B:num->real) 1)` THEN
    MAP_EVERY X_GEN_TAC [`j:num`; `x:real^2`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^2) IN ball(a,R / &16)` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(NORM_ARITH
       `norm(x:real^K) <= m /\ norm(y:real^K) <= m ==> norm(x - y) <= &2 * m`) THEN
      CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `MS:real` THEN
      REWRITE_TAC[REAL_ARITH `m <= max m b`] THENL
       [USE_THEN "VB" (MP_TAC o SPECL [`[]:(num)list`; `(t:num->num) j`; `x:real^2`]) THEN
        REWRITE_TAC[ALL; LENGTH; iterated_partial] THEN ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[]];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      MATCH_MP_TAC(NORM_ARITH
       `norm(x:real^K) <= m /\ norm(y:real^K) <= m ==> norm(x - y) <= &2 * m`) THEN
      CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(B:num->real) 1` THEN
      REWRITE_TAC[REAL_ARITH `b <= max m b`] THENL
       [USE_THEN "VB" (MP_TAC o SPECL [`[i:num]`; `(t:num->num) j`; `x:real^2`]) THEN
        REWRITE_TAC[ALL; CMC_LENGTH_SING; iterated_partial] THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
        USE_THEN "U1" (MP_TAC o SPEC `i:num`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[]]];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "U0" (MP_TAC o SPEC `e:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN
    SUBGOAL_THEN
     `!i. ?N. 1 <= i /\ i <= 2
              ==> !n x. N <= n /\ x IN ball(a:real^2,R / &32)
                        ==> norm(partial_derivative i
                                   ((v:num->real^2->real^K) ((t:num->num) n)) x -
                                 partial_derivative i (u:real^2->real^K) x) < e`
     MP_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN
      USE_THEN "U1" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `e:real` o CONJUNCT2) THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `NN:num->num`)] THEN
    EXISTS_TAC `(N0:num) + (NN:num->num) 1 + NN 2` THEN MAP_EVERY X_GEN_TAC [`j:num`; `x:real^2`] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `i = 1 \/ i = 2` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]]);;


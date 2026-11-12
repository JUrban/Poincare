(* ========================================================================= *)
(* pc_pde_rdt_coef: the Ricci-DeTurck existence, part 3.  Uniform tame       *)
(* bounds, in one chart, for the coefficients of the frozen operator         *)
(* tr_G Hess_H in pde_lop0 form (pde_mlbb, pde_mlcc of pc_pde_mlop) and for  *)
(* the Ricci-DeTurck remainder (pde_rdt_sym of pc_pde_rdt_symbol): each is a *)
(* fixed smooth map of the point (vec G, its first partials, the Christoffel *)
(* symbols of H and their first partials), so RDT_COMPOSE_TAME gives bounds  *)
(* that depend only on bounds of G and of the jets of H at the point.        *)
(* ========================================================================= *)

needs "src/pc_pde_rdt_tame.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Jets of maps of the form vectorize(lambda c. G c z), jets of              *)
(* pastecart, and the boundedness of the jets of a smooth map on a compact   *)
(* subset of its open domain.                                                *)
(* ------------------------------------------------------------------------- *)

let RDT_JETN_COMPONENTS = prove
 (`!m s (Fv:real^N->real^P) y.
     open s /\ smooth_map_on s Fv /\ y IN s
     ==> pde_jetn m Fv y <= sum(1..dimindex(:P)) (\k. pde_jetn m (\z. lift(Fv z$k)) y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `Fv = (\z. vsum(1..dimindex(:P)) (\k. drop(lift((Fv:real^N->real^P) z$k)) %
                                                       basis k))`
  (fun th -> GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RAND_CONV) [th]) THENL
   [REWRITE_TAC[FUN_EQ_THM; LIFT_DROP; BASIS_EXPANSION]; ALL_TAC] THEN
  SUBGOAL_THEN `!k. smooth_map_on s (\z. lift((Fv:real^N->real^P) z$k))` ASSUME_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN `?k'. 1 <= k' /\ k' <= dimindex(:P) /\ !x:real^P. x$k = x$k'`
    STRIP_ASSUME_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `smooth_map_on s (Fv:real^N->real^P)` THEN
    GEN_REWRITE_TAC LAND_CONV
     [MATCH_MP (INST_TYPE [`:P`,`:N`; `:N`,`:M`] SMOOTH_MAP_ON_COMPONENTWISE)
               (ASSUME `open (s:real^N->bool)`)] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:P))
                (\k. pde_jetn m (\z. drop(lift((Fv:real^N->real^P) z$k)) % basis k:real^P) y)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`m:num`; `s:real^N->bool`; `1..dimindex(:P)`;
                   `\k z. drop(lift((Fv:real^N->real^P) z$k)) % basis k:real^P`; `y:real^N`]
      P2CT_JETN_VSUM) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `\z. lift((Fv:real^N->real^P) z$k)`;
                   `\a:real^1. drop a % basis k:real^P`] SMOOTH_MAP_ON_LINEAR_O) THEN
    ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`m:num`; `\a:real^1. drop a % basis k:real^P`; `&1`; `s:real^N->bool`;
                 `\z. lift((Fv:real^N->real^P) z$k)`; `y:real^N`] P2CT_JETN_LINEAR) THEN
  ASM_REWRITE_TAC[REAL_MUL_LID] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
    GEN_TAC THEN ASM_SIMP_TAC[NORM_MUL; NORM_BASIS; ABS_DROP; REAL_MUL_RID; REAL_LE_REFL]]);;

let RDT_SMOOTH_VLAMBDA = prove
 (`!s (G:num->real^N->real^K).
     open s /\ (!c. 1 <= c /\ c <= dimindex(:M) ==> smooth_map_on s (G c))
     ==> smooth_map_on s (\z. vectorize((lambda c. G c z):real^K^M))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I
   [MATCH_MP (INST_TYPE [`:(M,K)finite_prod`,`:N`; `:N`,`:M`] SMOOTH_MAP_ON_COMPONENTWISE)
             (ASSUME `open (s:real^N->bool)`)] THEN
  X_GEN_TAC `k:num` THEN REWRITE_TAC[DIMINDEX_FINITE_PROD] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[VECTORIZE_COMPONENT] THEN
  SUBGOAL_THEN `1 <= 1 + (k - 1) DIV dimindex(:K) /\ 1 + (k - 1) DIV dimindex(:K) <= dimindex(:M) /\
                1 <= 1 + (k - 1) MOD dimindex(:K) /\ 1 + (k - 1) MOD dimindex(:K) <= dimindex(:K)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`dimindex(:M)`; `dimindex(:K)`; `k:num`] RDT_INDEX_SPLIT) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[LAMBDA_BETA] THEN
  SUBGOAL_THEN `smooth_map_on s ((G:num->real^N->real^K) (1 + (k - 1) DIV dimindex(:K)))`
  MP_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV
   [MATCH_MP (INST_TYPE [`:K`,`:N`; `:N`,`:M`] SMOOTH_MAP_ON_COMPONENTWISE)
             (ASSUME `open (s:real^N->bool)`)] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let RDT_JETN_VLAMBDA_BOUND = prove
 (`!m s (G:num->real^N->real^K) y Bd.
     open s /\ (!c. 1 <= c /\ c <= dimindex(:M) ==> smooth_map_on s (G c)) /\ y IN s /\
     (!c. 1 <= c /\ c <= dimindex(:M) ==> pde_jetn m (G c) y <= Bd)
     ==> pde_jetn m (\z. vectorize((lambda c. G c z):real^K^M)) y <=
         &(dimindex(:M) * dimindex(:K)) * Bd`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:num`; `s:real^N->bool`;
                 `\z. vectorize((lambda c. (G:num->real^N->real^K) c z):real^K^M)`; `y:real^N`]
    RDT_JETN_COMPONENTS) THEN
  ASM_SIMP_TAC[RDT_SMOOTH_VLAMBDA] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  REWRITE_TAC[DIMINDEX_FINITE_PROD] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:M) * dimindex(:K)) (\k:num. Bd)` THEN CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_LE_REFL]] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `1 <= 1 + (k - 1) DIV dimindex(:K) /\ 1 + (k - 1) DIV dimindex(:K) <= dimindex(:M) /\
                1 <= 1 + (k - 1) MOD dimindex(:K) /\ 1 + (k - 1) MOD dimindex(:K) <= dimindex(:K)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`dimindex(:M)`; `dimindex(:K)`; `k:num`] RDT_INDEX_SPLIT) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. lift(vectorize((lambda c. (G:num->real^N->real^K) c z):real^K^M)$k)) =
    (\z. lift(G (1 + (k - 1) DIV dimindex(:K)) z$(1 + (k - 1) MOD dimindex(:K))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN ASM_SIMP_TAC[VECTORIZE_COMPONENT; DIMINDEX_FINITE_PROD; LAMBDA_BETA];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `pde_jetn m ((G:num->real^N->real^K) (1 + (k - 1) DIV dimindex(:K))) y` THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC P2CT_JETN_LIFT_COMPONENT THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[]);;

let RDT_JETN_PASTECART = prove
 (`!m s (f:real^N->real^P) (g:real^N->real^Q) y.
     open s /\ smooth_map_on s f /\ smooth_map_on s g /\ y IN s
     ==> pde_jetn m (\z. pastecart (f z) (g z)) y <= pde_jetn m f y + pde_jetn m g y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z. pastecart ((f:real^N->real^P) z) ((g:real^N->real^Q) z)) =
                (\z. pastecart (f z) (vec 0) + pastecart (vec 0) (g z))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; PASTECART_ADD; VECTOR_ADD_LID; VECTOR_ADD_RID]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on s (\z. pastecart ((f:real^N->real^P) z) (vec 0:real^Q)) /\
                smooth_map_on s (\z. pastecart (vec 0:real^P) ((g:real^N->real^Q) z))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`s:real^N->bool`; `f:real^N->real^P`;
                     `\a:real^P. pastecart a (vec 0:real^Q)`] SMOOTH_MAP_ON_LINEAR_O);
      MP_TAC(ISPECL [`s:real^N->bool`; `g:real^N->real^Q`;
                     `\a:real^Q. pastecart (vec 0:real^P) a`] SMOOTH_MAP_ON_LINEAR_O)] THEN
    ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[linear; PASTECART_ADD; GSYM PASTECART_CMUL; VECTOR_ADD_LID; VECTOR_MUL_RZERO];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:num`; `s:real^N->bool`;
                 `\z. pastecart ((f:real^N->real^P) z) (vec 0:real^Q)`;
                 `\z. pastecart (vec 0:real^P) ((g:real^N->real^Q) z)`; `y:real^N`]
    P2CT_JETN_ADD) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH `a <= c /\ b <= d ==> x <= a + b ==> x <= c + d`) THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`m:num`; `\a:real^P. pastecart a (vec 0:real^Q)`; `&1`; `s:real^N->bool`;
                   `f:real^N->real^P`; `y:real^N`] P2CT_JETN_LINEAR);
    MP_TAC(ISPECL [`m:num`; `\a:real^Q. pastecart (vec 0:real^P) a`; `&1`; `s:real^N->bool`;
                   `g:real^N->real^Q`; `y:real^N`] P2CT_JETN_LINEAR)] THEN
  ASM_REWRITE_TAC[REAL_MUL_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[linear; PASTECART_ADD; GSYM PASTECART_CMUL; VECTOR_ADD_LID; VECTOR_MUL_RZERO;
              NORM_PASTECART_0; REAL_LE_REFL]);;

let RDT_JETS_BOUNDED_COMPACT = prove
 (`!W S (Phi:real^M->real^P) n.
     open W /\ smooth_map_on W Phi /\ compact S /\ S SUBSET W
     ==> ?C. &0 <= C /\ !x. x IN S ==> pde_jetn n Phi x <= C`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`W:real^M->bool`; `S:real^M->bool`; `n:num`; `Phi:real^M->real^P`]
    RDT_JETN_CONT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\x. lift(pde_jetn n (Phi:real^M->real^P) x)`; `S:real^M->bool`]
    COMPACT_CONTINUOUS_IMAGE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; NORM_LIFT] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `B:real` THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Encodings.  rdt_gv H y and rdt_gdv H y collect the                        *)
(* Christoffel symbols of H at y and their first partials as vectors,        *)
(* rdt_dgv G y the first partials of vec G; the decoders rdt_dec3, rdt_dec4, *)
(* rdt_dd1 give back exactly the jet arrays pde_jhc, pde_jhdc, pde_jd1 of    *)
(* pc_pde_rdt_symbol (out of range they are 0, as are the arrays).           *)
(* ------------------------------------------------------------------------- *)

let rdt_gv = new_definition
 `rdt_gv (H:real^N->real^N^N) (y:real^N) =
    (vectorize:real^(N,N)finite_prod^N->real^(N,(N,N)finite_prod)finite_prod)
    (lambda a. (vectorize:real^N^N->real^(N,N)finite_prod)
                 (lambda b. christoffel H y (basis a) (basis b)))`;;

let rdt_gdv = new_definition
 `rdt_gdv (H:real^N->real^N^N) (y:real^N) =
    (vectorize:real^(N,(N,N)finite_prod)finite_prod^N
               ->real^(N,(N,(N,N)finite_prod)finite_prod)finite_prod)
    (lambda c. (vectorize:real^(N,N)finite_prod^N->real^(N,(N,N)finite_prod)finite_prod)
       (lambda a. (vectorize:real^N^N->real^(N,N)finite_prod)
          (lambda b. partial_derivative c (\z. christoffel H z (basis a) (basis b)) y)))`;;

let rdt_dgv = new_definition
 `rdt_dgv (G:real^N->real^N^N) (y:real^N) =
    (vectorize:real^(N,N)finite_prod^N->real^(N,(N,N)finite_prod)finite_prod)
    (lambda c. partial_derivative c ((vectorize:real^N^N->real^(N,N)finite_prod) o G) y)`;;

let rdt_dec3 = new_definition
 `rdt_dec3 (v:real^(N,(N,N)finite_prod)finite_prod) m a b =
    if 1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)
    then (((matrify:real^(N,N)finite_prod->real^N^N)
            (((matrify:real^(N,(N,N)finite_prod)finite_prod->real^(N,N)finite_prod^N) v)$a))$b)$m
    else &0`;;

let rdt_dec4 = new_definition
 `rdt_dec4 (v:real^(N,(N,(N,N)finite_prod)finite_prod)finite_prod) c m a b =
    if 1 <= c /\ c <= dimindex(:N) /\ 1 <= a /\ a <= dimindex(:N) /\
       1 <= b /\ b <= dimindex(:N)
    then (((matrify:real^(N,N)finite_prod->real^N^N)
            (((matrify:real^(N,(N,N)finite_prod)finite_prod->real^(N,N)finite_prod^N)
              (((matrify:real^(N,(N,(N,N)finite_prod)finite_prod)finite_prod
                         ->real^(N,(N,N)finite_prod)finite_prod^N) v)$c))$a))$b)$m
    else &0`;;

let rdt_dd1 = new_definition
 `rdt_dd1 (v:real^(N,(N,N)finite_prod)finite_prod) c i j =
    if 1 <= c /\ c <= dimindex(:N)
    then ((matrify:real^(N,N)finite_prod->real^N^N)
            (((matrify:real^(N,(N,N)finite_prod)finite_prod->real^(N,N)finite_prod^N) v)$c))$i$j
    else &0`;;

let RDT_DEC3_GV = prove
 (`!U (H:real^N->real^N^N) y.
     metric_field U H /\ y IN U ==> rdt_dec3 (rdt_gv H y) = pde_jhc H y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM; rdt_dec3; rdt_gv; pde_jhc] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `a:num`; `b:num`] THEN COND_CASES_TAC THENL
   [ASM_SIMP_TAC[MATRIFY_VECTORIZE; LAMBDA_BETA]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `H:real^N->real^N^N`; `y:real^N`] CHRISTOFFEL_BILINEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `basis a:real^N = vec 0 \/ basis b:real^N = vec 0` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[BASIS_EQ_0; IN_NUMSEG] THEN ASM_ARITH_TAC;
    MP_TAC(ISPECL [`christoffel (H:real^N->real^N^N) y`; `basis b:real^N`] BILINEAR_LZERO);
    MP_TAC(ISPECL [`christoffel (H:real^N->real^N^N) y`; `basis a:real^N`] BILINEAR_RZERO)] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VEC_COMPONENT]);;

let RDT_DD1_DGV = prove
 (`!U (G:real^N->real^N^N) y.
     metric_field U G /\ y IN U ==> rdt_dd1 (rdt_dgv G y) = pde_jd1 G y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM; rdt_dd1; rdt_dgv; pde_jd1; mderiv] THEN
  MAP_EVERY X_GEN_TAC [`c:num`; `i:num`; `j:num`] THEN COND_CASES_TAC THENL
   [ASM_SIMP_TAC[MATRIFY_VECTORIZE; LAMBDA_BETA; partial_derivative]; ALL_TAC] THEN
  SUBGOAL_THEN `basis c:real^N = vec 0` SUBST1_TAC THENL
   [REWRITE_TAC[BASIS_EQ_0; IN_NUMSEG] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_METRIC_FIELD_DIFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  DISCH_THEN(MP_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP LINEAR_0) THEN
  REWRITE_TAC[MATRIFY_0; MAT_0_COMPONENT]);;

let RDT_DEC4_GDV = prove
 (`!U (H:real^N->real^N^N) y.
     metric_field U H /\ y IN U ==> rdt_dec4 (rdt_gdv H y) = pde_jhdc H y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM; rdt_dec4; rdt_gdv; pde_jhdc] THEN
  MAP_EVERY X_GEN_TAC [`c:num`; `m:num`; `a:num`; `b:num`] THEN COND_CASES_TAC THENL
   [ASM_SIMP_TAC[MATRIFY_VECTORIZE; LAMBDA_BETA; partial_derivative]; ALL_TAC] THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  ASM_CASES_TAC `1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)` THENL
   [SUBGOAL_THEN `basis c:real^N = vec 0` SUBST1_TAC THENL
     [REWRITE_TAC[BASIS_EQ_0; IN_NUMSEG] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(\z. christoffel (H:real^N->real^N^N) z (basis a) (basis b))
                  differentiable at y` MP_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `H:real^N->real^N^N`; `basis a:real^N`;
                     `\y:real^N. basis b:real^N`] LRG_CHRISTOFFEL_SMOOTH_ARG) THEN
      ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP LINEAR_0) THEN REWRITE_TAC[VEC_COMPONENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `basis a:real^N = vec 0 \/ basis b:real^N = vec 0` ASSUME_TAC THENL
   [REWRITE_TAC[BASIS_EQ_0; IN_NUMSEG] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`[c:num]`; `U:real^N->bool`;
                 `\z. christoffel (H:real^N->real^N^N) z (basis a) (basis b)`; `y:real^N`]
    TEXT_ITERATED_PARTIAL_ZERO_OPEN) THEN
  ASM_REWRITE_TAC[iterated_partial; partial_derivative] THEN
  ANTS_TAC THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `H:real^N->real^N^N`; `z:real^N`] CHRISTOFFEL_BILINEAR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THENL
     [MP_TAC(ISPECL [`christoffel (H:real^N->real^N^N) z`; `basis b:real^N`] BILINEAR_LZERO);
      MP_TAC(ISPECL [`christoffel (H:real^N->real^N^N) z`; `basis a:real^N`] BILINEAR_RZERO)] THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VEC_COMPONENT]]);;

(* Jets of the encodings.                                                    *)

let RDT_GV_FUN = prove
 (`!(H:real^N->real^N^N).
     rdt_gv H = (\z. (vectorize:real^(N,N)finite_prod^N->real^(N,(N,N)finite_prod)finite_prod)
                       (lambda a. (vectorize:real^N^N->real^(N,N)finite_prod)
                                    (lambda b. christoffel H z (basis a) (basis b))))`,
  REWRITE_TAC[FUN_EQ_THM; rdt_gv]);;

let RDT_GDV_FUN = prove
 (`!(H:real^N->real^N^N).
     rdt_gdv H =
     (\y. (vectorize:real^(N,(N,N)finite_prod)finite_prod^N
                     ->real^(N,(N,(N,N)finite_prod)finite_prod)finite_prod)
          (lambda c. (vectorize:real^(N,N)finite_prod^N->real^(N,(N,N)finite_prod)finite_prod)
             (lambda a. (vectorize:real^N^N->real^(N,N)finite_prod)
                (lambda b. partial_derivative c (\z. christoffel H z (basis a) (basis b)) y))))`,
  REWRITE_TAC[FUN_EQ_THM; rdt_gdv]);;

let RDT_DGV_FUN = prove
 (`!(G:real^N->real^N^N).
     rdt_dgv G =
     (\y. (vectorize:real^(N,N)finite_prod^N->real^(N,(N,N)finite_prod)finite_prod)
          (lambda c. partial_derivative c ((vectorize:real^N^N->real^(N,N)finite_prod) o G) y))`,
  REWRITE_TAC[FUN_EQ_THM; rdt_dgv]);;

let RDT_GV_JETN = prove
 (`!n B L. ?C. &0 <= C /\
     !s (H:real^N->real^N^N) y.
       open s /\ smooth_map_on s (vectorize o H) /\ (!z. z IN s ==> ~(det(H z) = &0)) /\
       y IN s /\ pde_jetn (SUC n) (vectorize o H) y <= B /\
       norm(vectorize(matrix_inv(H y))) <= L
       ==> smooth_map_on s (rdt_gv H) /\ pde_jetn n (rdt_gv H) y <= C`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`n:num`; `B:real`; `L:real`] (INST_TYPE [`:N`,`:N`] P2CT_CHRISTOFFEL_JET)) THEN
  DISCH_THEN(X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "chr"))) THEN
  EXISTS_TAC `&(dimindex(:N) * dimindex(:(N,N)finite_prod)) *
              (&(dimindex(:N) * dimindex(:N)) * C0)` THEN
  CONJ_TAC THENL [RDT_NN_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!a b. 1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)
          ==> smooth_map_on s (\z. christoffel (H:real^N->real^N^N) z (basis a) (basis b)) /\
              pde_jetn n (\z. christoffel H z (basis a) (basis b)) y <= C0`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN USE_THEN "chr" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a. 1 <= a /\ a <= dimindex(:N)
        ==> smooth_map_on s
              (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                     (lambda b. christoffel (H:real^N->real^N^N) z (basis a) (basis b))) /\
            pde_jetn n
              (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                     (lambda b. christoffel H z (basis a) (basis b))) y <=
            &(dimindex(:N) * dimindex(:N)) * C0`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:num` THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC RDT_SMOOTH_VLAMBDA THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC RDT_JETN_VLAMBDA_BOUND THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[RDT_GV_FUN] THEN CONJ_TAC THENL
   [MATCH_MP_TAC RDT_SMOOTH_VLAMBDA THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC RDT_JETN_VLAMBDA_BOUND THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_SIMP_TAC[]]);;

let RDT_GDV_JETN = prove
 (`!n B L. ?C. &0 <= C /\
     !s (H:real^N->real^N^N) y.
       open s /\ smooth_map_on s (vectorize o H) /\ (!z. z IN s ==> ~(det(H z) = &0)) /\
       y IN s /\ pde_jetn (SUC(SUC n)) (vectorize o H) y <= B /\
       norm(vectorize(matrix_inv(H y))) <= L
       ==> smooth_map_on s (rdt_gdv H) /\ pde_jetn n (rdt_gdv H) y <= C`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`SUC n`; `B:real`; `L:real`] (INST_TYPE [`:N`,`:N`] P2CT_CHRISTOFFEL_JET)) THEN
  DISCH_THEN(X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "chr"))) THEN
  EXISTS_TAC `&(dimindex(:N) * dimindex(:(N,(N,N)finite_prod)finite_prod)) *
              (&(dimindex(:N) * dimindex(:(N,N)finite_prod)) *
               (&(dimindex(:N) * dimindex(:N)) * C0))` THEN
  CONJ_TAC THENL [RDT_NN_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!c a b. 1 <= c /\ c <= dimindex(:N) /\ 1 <= a /\ a <= dimindex(:N) /\
            1 <= b /\ b <= dimindex(:N)
            ==> smooth_map_on s (partial_derivative c
                   (\z. christoffel (H:real^N->real^N^N) z (basis a) (basis b))) /\
                pde_jetn n (partial_derivative c
                   (\z. christoffel H z (basis a) (basis b))) y <= C0`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "chr" (MP_TAC o SPECL [`s:real^N->bool`; `H:real^N->real^N^N`; `y:real^N`;
                                    `a:num`; `b:num`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `pde_jetn (SUC n) (\z. christoffel (H:real^N->real^N^N) z (basis a) (basis b)) y` THEN
      ASM_SIMP_TAC[PDE_JETN_PARTIAL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c a. 1 <= c /\ c <= dimindex(:N) /\ 1 <= a /\ a <= dimindex(:N)
          ==> smooth_map_on s
                (\y. (vectorize:real^N^N->real^(N,N)finite_prod)
                       (lambda b. partial_derivative c
                          (\z. christoffel (H:real^N->real^N^N) z (basis a) (basis b)) y)) /\
              pde_jetn n
                (\y. (vectorize:real^N^N->real^(N,N)finite_prod)
                       (lambda b. partial_derivative c
                          (\z. christoffel H z (basis a) (basis b)) y)) y <=
              &(dimindex(:N) * dimindex(:N)) * C0`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC RDT_SMOOTH_VLAMBDA THEN ASM_SIMP_TAC[ETA_AX];
      MATCH_MP_TAC RDT_JETN_VLAMBDA_BOUND THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_SIMP_TAC[ETA_AX]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c. 1 <= c /\ c <= dimindex(:N)
        ==> smooth_map_on s
              (\y. (vectorize:real^(N,N)finite_prod^N->real^(N,(N,N)finite_prod)finite_prod)
                     (lambda a. (vectorize:real^N^N->real^(N,N)finite_prod)
                        (lambda b. partial_derivative c
                           (\z. christoffel (H:real^N->real^N^N) z (basis a) (basis b)) y))) /\
            pde_jetn n
              (\y. (vectorize:real^(N,N)finite_prod^N->real^(N,(N,N)finite_prod)finite_prod)
                     (lambda a. (vectorize:real^N^N->real^(N,N)finite_prod)
                        (lambda b. partial_derivative c
                           (\z. christoffel H z (basis a) (basis b)) y))) y <=
            &(dimindex(:N) * dimindex(:(N,N)finite_prod)) *
            (&(dimindex(:N) * dimindex(:N)) * C0)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC RDT_SMOOTH_VLAMBDA THEN ASM_SIMP_TAC[ETA_AX];
      MATCH_MP_TAC RDT_JETN_VLAMBDA_BOUND THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_SIMP_TAC[ETA_AX]];
    ALL_TAC] THEN
  REWRITE_TAC[RDT_GDV_FUN] THEN CONJ_TAC THENL
   [MATCH_MP_TAC RDT_SMOOTH_VLAMBDA THEN ASM_SIMP_TAC[ETA_AX];
    MATCH_MP_TAC RDT_JETN_VLAMBDA_BOUND THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_SIMP_TAC[ETA_AX]]);;

let RDT_DGV_JETN = prove
 (`!n s (G:real^N->real^N^N) y.
     open s /\ smooth_map_on s (vectorize o G) /\ y IN s
     ==> smooth_map_on s (rdt_dgv G) /\
         pde_jetn n (rdt_dgv G) y <=
         &(dimindex(:N) * dimindex(:(N,N)finite_prod)) *
         pde_jetn (SUC n) ((vectorize:real^N^N->real^(N,N)finite_prod) o G) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[RDT_DGV_FUN] THEN CONJ_TAC THENL
   [MATCH_MP_TAC RDT_SMOOTH_VLAMBDA THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; ETA_AX];
    MATCH_MP_TAC RDT_JETN_VLAMBDA_BOUND THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; PDE_JETN_PARTIAL; ETA_AX]]);;

(* ------------------------------------------------------------------------- *)
(* Smoothness of the atoms of the coefficient maps: entries of               *)
(* a matrix, of its inverse, and of the decoders, after a linear projection  *)
(* prj of the argument.                                                       *)
(* ------------------------------------------------------------------------- *)

let RDT_ROW_ADD = prove
 (`!(A:real^K^M) B a. (A + B)$a = A$a + B$a`,
  SIMP_TAC[CART_EQ; MATRIX_ADD_COMPONENT; VECTOR_ADD_COMPONENT]);;

let RDT_ROW_CMUL = prove
 (`!(A:real^K^M) c a. (c %% A)$a = c % A$a`,
  SIMP_TAC[CART_EQ; MATRIX_CMUL_COMPONENT; VECTOR_MUL_COMPONENT]);;

let RDT_LINEAR_DEC3_ENTRY = prove
 (`!a b m. linear (\v:real^(N,(N,N)finite_prod)finite_prod.
                     lift((((matrify:real^(N,N)finite_prod->real^N^N)
                             (((matrify:real^(N,(N,N)finite_prod)finite_prod
                                        ->real^(N,N)finite_prod^N) v)$a))$b)$m))`,
  REWRITE_TAC[linear; MATRIFY_ADD; MATRIFY_CMUL; RDT_ROW_ADD; RDT_ROW_CMUL;
              MATRIX_ADD_COMPONENT; MATRIX_CMUL_COMPONENT; RDT_ROW_ADD; RDT_ROW_CMUL;
              VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; LIFT_ADD; LIFT_CMUL]);;

let RDT_LINEAR_DEC4_ENTRY = prove
 (`!c a b m.
     linear (\v:real^(N,(N,(N,N)finite_prod)finite_prod)finite_prod.
               lift((((matrify:real^(N,N)finite_prod->real^N^N)
                       (((matrify:real^(N,(N,N)finite_prod)finite_prod->real^(N,N)finite_prod^N)
                         (((matrify:real^(N,(N,(N,N)finite_prod)finite_prod)finite_prod
                                    ->real^(N,(N,N)finite_prod)finite_prod^N) v)$c))$a))$b)$m))`,
  REWRITE_TAC[linear; MATRIFY_ADD; MATRIFY_CMUL; RDT_ROW_ADD; RDT_ROW_CMUL] THEN
  REWRITE_TAC[MATRIFY_ADD; MATRIFY_CMUL; RDT_ROW_ADD; RDT_ROW_CMUL] THEN
  REWRITE_TAC[MATRIFY_ADD; MATRIFY_CMUL; MATRIX_ADD_COMPONENT; MATRIX_CMUL_COMPONENT;
              RDT_ROW_ADD; RDT_ROW_CMUL; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
              LIFT_ADD; LIFT_CMUL]);;

let RDT_LINEAR_DD1_ENTRY = prove
 (`!c i j. linear (\v:real^(N,(N,N)finite_prod)finite_prod.
                     lift(((matrify:real^(N,N)finite_prod->real^N^N)
                            (((matrify:real^(N,(N,N)finite_prod)finite_prod
                                       ->real^(N,N)finite_prod^N) v)$c))$i$j))`,
  REWRITE_TAC[linear; MATRIFY_ADD; MATRIFY_CMUL; RDT_ROW_ADD; RDT_ROW_CMUL;
              MATRIX_ADD_COMPONENT; MATRIX_CMUL_COMPONENT; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT; LIFT_ADD; LIFT_CMUL]);;

let RDT_SMOOTH_LINEAR_O = prove
 (`!S (L:real^P->real^Q) (prj:real^M->real^P).
     open S /\ linear L /\ linear prj ==> smooth_map_on S (\x. L(prj x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[smooth_map_on] THEN GEN_TAC THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\x. (L:real^P->real^Q) ((prj:real^M->real^P) x)) = L o prj` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ASM_SIMP_TAC[LINEAR_COMPOSE]]);;

let RDT_SMOOTH_DEC3 = prove
 (`!S (prj:real^M->real^(N,(N,N)finite_prod)finite_prod) m a b.
     open S /\ linear prj ==> smooth_map_on S (\x. lift(rdt_dec3 (prj x) m a b))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rdt_dec3] THEN
  ASM_CASES_TAC `1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)` THEN
  ASM_REWRITE_TAC[LIFT_NUM; SMOOTH_MAP_ON_CONST] THEN
  MP_TAC(ISPECL [`S:real^M->bool`;
    `\v:real^(N,(N,N)finite_prod)finite_prod.
        lift((((matrify:real^(N,N)finite_prod->real^N^N)
               (((matrify:real^(N,(N,N)finite_prod)finite_prod->real^(N,N)finite_prod^N) v)$a))$b)$m)`;
    `prj:real^M->real^(N,(N,N)finite_prod)finite_prod`] RDT_SMOOTH_LINEAR_O) THEN
  ASM_REWRITE_TAC[RDT_LINEAR_DEC3_ENTRY]);;

let RDT_SMOOTH_DEC4 = prove
 (`!S (prj:real^M->real^(N,(N,(N,N)finite_prod)finite_prod)finite_prod) c m a b.
     open S /\ linear prj ==> smooth_map_on S (\x. lift(rdt_dec4 (prj x) c m a b))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rdt_dec4] THEN
  ASM_CASES_TAC `1 <= c /\ c <= dimindex(:N) /\ 1 <= a /\ a <= dimindex(:N) /\
                 1 <= b /\ b <= dimindex(:N)` THEN
  ASM_REWRITE_TAC[LIFT_NUM; SMOOTH_MAP_ON_CONST] THEN
  MP_TAC(ISPECL [`S:real^M->bool`;
    `\v:real^(N,(N,(N,N)finite_prod)finite_prod)finite_prod.
        lift((((matrify:real^(N,N)finite_prod->real^N^N)
               (((matrify:real^(N,(N,N)finite_prod)finite_prod->real^(N,N)finite_prod^N)
                 (((matrify:real^(N,(N,(N,N)finite_prod)finite_prod)finite_prod
                            ->real^(N,(N,N)finite_prod)finite_prod^N) v)$c))$a))$b)$m)`;
    `prj:real^M->real^(N,(N,(N,N)finite_prod)finite_prod)finite_prod`] RDT_SMOOTH_LINEAR_O) THEN
  ASM_REWRITE_TAC[RDT_LINEAR_DEC4_ENTRY]);;

let RDT_SMOOTH_DD1 = prove
 (`!S (prj:real^M->real^(N,(N,N)finite_prod)finite_prod) c i j.
     open S /\ linear prj ==> smooth_map_on S (\x. lift(rdt_dd1 (prj x) c i j))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rdt_dd1] THEN
  ASM_CASES_TAC `1 <= c /\ c <= dimindex(:N)` THEN
  ASM_REWRITE_TAC[LIFT_NUM; SMOOTH_MAP_ON_CONST] THEN
  MP_TAC(ISPECL [`S:real^M->bool`;
    `\v:real^(N,(N,N)finite_prod)finite_prod.
        lift(((matrify:real^(N,N)finite_prod->real^N^N)
              (((matrify:real^(N,(N,N)finite_prod)finite_prod->real^(N,N)finite_prod^N) v)$c))$i$j)`;
    `prj:real^M->real^(N,(N,N)finite_prod)finite_prod`] RDT_SMOOTH_LINEAR_O) THEN
  ASM_REWRITE_TAC[RDT_LINEAR_DD1_ENTRY]);;

let RDT_SMOOTH_PENTRY = prove
 (`!S (prj:real^M->real^(N,N)finite_prod) i j.
     open S /\ linear prj ==> smooth_map_on S (\x. lift((matrify(prj x):real^N^N)$i$j))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^M->bool`;
                 `\v:real^(N,N)finite_prod. lift((matrify v:real^N^N)$i$j)`;
                 `prj:real^M->real^(N,N)finite_prod`] RDT_SMOOTH_LINEAR_O) THEN
  ASM_REWRITE_TAC[LRG_LINEAR_MATRIFY_ENTRY]);;

let RDT_SMOOTH_GI = prove
 (`!S (prj:real^M->real^(N,N)finite_prod) i j.
     open S /\ linear prj /\ (!x. x IN S ==> ~(det(matrify(prj x):real^N^N) = &0))
     ==> smooth_map_on S (\x. lift(matrix_inv(matrify(prj x):real^N^N)$i$j))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. lift(matrix_inv(matrify((prj:real^M->real^(N,N)finite_prod) x):real^N^N)$i$j)) =
    (\v:real^(N,N)finite_prod. lift((matrify v:real^N^N)$i$j)) o
    ((vectorize:real^N^N->real^(N,N)finite_prod) o
     (\x. matrix_inv(matrify(prj x):real^N^N)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; MATRIFY_VECTORIZE]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[LRG_LINEAR_MATRIFY_ENTRY] THEN
  MATCH_MP_TAC LRG_SMOOTH_MATRIX_INV THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[o_DEF; VECTORIZE_MATRIFY] THEN
  MP_TAC(ISPECL [`S:real^M->bool`; `\v:real^(N,N)finite_prod. v`;
                 `prj:real^M->real^(N,N)finite_prod`] RDT_SMOOTH_LINEAR_O) THEN
  ASM_REWRITE_TAC[LINEAR_ID; ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* The inner maps rdt_kc (coefficients) and rdt_kf (remainder),              *)
(* the fixed outer maps rdt_phia, rdt_phib c, rdt_phic, rdt_psi, their       *)
(* smoothness on the invertible set, and the identities with the lop0        *)
(* coefficients (pde_mlbb, pde_mlcc) and the symbol pde_rdt_sym.             *)
(* ------------------------------------------------------------------------- *)

let rdt_kc = new_definition
 `rdt_kc (G:real^N->real^N^N) (H:real^N->real^N^N) (y:real^N) =
    pastecart ((vectorize:real^N^N->real^(N,N)finite_prod) (G y))
              (pastecart (rdt_gv H y) (rdt_gdv H y))`;;

let rdt_kf = new_definition
 `rdt_kf (G:real^N->real^N^N) (H:real^N->real^N^N) (y:real^N) =
    pastecart ((vectorize:real^N^N->real^(N,N)finite_prod) (G y))
              (pastecart (rdt_dgv G y) (pastecart (rdt_gv H y) (rdt_gdv H y)))`;;

let rdt_phia = new_definition
 `rdt_phia (x:real^((N,N)finite_prod,((N,(N,N)finite_prod)finite_prod,
                                       (N,(N,(N,N)finite_prod)finite_prod)finite_prod)
                                      finite_sum)finite_sum) =
    (vectorize:real^N^N->real^(N,N)finite_prod)
      (transp(matrix_inv((matrify:real^(N,N)finite_prod->real^N^N) (fstcart x))))`;;

let rdt_phib = new_definition
 `rdt_phib (c:num)
           (x:real^((N,N)finite_prod,((N,(N,N)finite_prod)finite_prod,
                                       (N,(N,(N,N)finite_prod)finite_prod)finite_prod)
                                      finite_sum)finite_sum) =
    (vectorize:real^(N,N)finite_prod^(N,N)finite_prod
               ->real^((N,N)finite_prod,(N,N)finite_prod)finite_prod)
    (matrix (\w:real^(N,N)finite_prod. (vectorize:real^N^N->real^(N,N)finite_prod)
       ((lambda a b. pde_jtrhess (dimindex(:N)) (\i j. &0)
                       (\i j. matrix_inv((matrify:real^(N,N)finite_prod->real^N^N)
                                           (fstcart x))$i$j)
                       (\e i j. if e = c then (matrify w:real^N^N)$i$j else &0)
                       (\p q i j. &0) (rdt_dec3 (fstcart(sndcart x)))
                       (rdt_dec4 (sndcart(sndcart x))) a b):real^N^N)))`;;

let rdt_phic = new_definition
 `rdt_phic (x:real^((N,N)finite_prod,((N,(N,N)finite_prod)finite_prod,
                                       (N,(N,(N,N)finite_prod)finite_prod)finite_prod)
                                      finite_sum)finite_sum) =
    (vectorize:real^(N,N)finite_prod^(N,N)finite_prod
               ->real^((N,N)finite_prod,(N,N)finite_prod)finite_prod)
    (matrix (\w:real^(N,N)finite_prod. (vectorize:real^N^N->real^(N,N)finite_prod)
       ((lambda a b. pde_jtrhess (dimindex(:N)) (\i j. (matrify w:real^N^N)$i$j)
                       (\i j. matrix_inv((matrify:real^(N,N)finite_prod->real^N^N)
                                           (fstcart x))$i$j)
                       (\c i j. &0) (\p q i j. &0) (rdt_dec3 (fstcart(sndcart x)))
                       (rdt_dec4 (sndcart(sndcart x))) a b):real^N^N)))`;;

let rdt_psi = new_definition
 `rdt_psi (x:real^((N,N)finite_prod,((N,(N,N)finite_prod)finite_prod,
                     ((N,(N,N)finite_prod)finite_prod,
                      (N,(N,(N,N)finite_prod)finite_prod)finite_prod)finite_sum)
                    finite_sum)finite_sum) =
    (vectorize:real^N^N->real^(N,N)finite_prod)
    ((lambda a b. pde_jdj (dimindex(:N))
        (\i j. ((matrify:real^(N,N)finite_prod->real^N^N) (fstcart x))$i$j)
        (\i j. matrix_inv((matrify:real^(N,N)finite_prod->real^N^N) (fstcart x))$i$j)
        (rdt_dd1 (fstcart(sndcart x))) (\c e i j. &0)
        (rdt_dec3 (fstcart(sndcart(sndcart x))))
        (rdt_dec4 (sndcart(sndcart(sndcart x)))) a b):real^N^N)`;;

(* The identities.                                                          *)

let RDT_PHIA_KC = prove
 (`!(G:real^N->real^N^N) H y.
     rdt_phia (rdt_kc G H y) = vectorize(transp(matrix_inv(G y)))`,
  REWRITE_TAC[rdt_phia; rdt_kc; FSTCART_PASTECART; MATRIFY_VECTORIZE]);;

let RDT_PHIB_KC = prove
 (`!U (G:real^N->real^N^N) H y c.
     metric_field U H /\ y IN U ==> rdt_phib c (rdt_kc G H y) = vectorize(pde_mlbb G H y c)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `rdt_dec3 (rdt_gv (H:real^N->real^N^N) y) = pde_jhc H y /\
                rdt_dec4 (rdt_gdv H y) = pde_jhdc H y` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RDT_DEC3_GV; RDT_DEC4_GDV]; ALL_TAC] THEN
  ASM_REWRITE_TAC[rdt_phib; rdt_kc; pde_mlbb; FSTCART_PASTECART; SNDCART_PASTECART;
                  MATRIFY_VECTORIZE; pde_jgi]);;

let RDT_PHIC_KC = prove
 (`!U (G:real^N->real^N^N) H y.
     metric_field U H /\ y IN U ==> rdt_phic (rdt_kc G H y) = vectorize(pde_mlcc G H y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `rdt_dec3 (rdt_gv (H:real^N->real^N^N) y) = pde_jhc H y /\
                rdt_dec4 (rdt_gdv H y) = pde_jhdc H y` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RDT_DEC3_GV; RDT_DEC4_GDV]; ALL_TAC] THEN
  ASM_REWRITE_TAC[rdt_phic; rdt_kc; pde_mlcc; FSTCART_PASTECART; SNDCART_PASTECART;
                  MATRIFY_VECTORIZE; pde_jgi]);;

let RDT_PSI_KF = prove
 (`!U (G:real^N->real^N^N) H y.
     metric_field U G /\ metric_field U H /\ y IN U
     ==> rdt_psi (rdt_kf G H y) =
         pde_rdt_sym H
           (pastecart y
             (pastecart ((vectorize:real^N^N->real^(N,N)finite_prod) (G y))
               ((vectorize:real^N^(N,N)finite_prod->real^((N,N)finite_prod,N)finite_prod)
                (matrix(frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o G)
                                           (at y))))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!v. matrix(frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                   (G:real^N->real^N^N)) (at y)) ** v =
        frechet_derivative (vectorize o G) (at y) v`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MATRIX_WORKS THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    ASM_MESON_TAC[LRG_METRIC_FIELD_DIFF];
    ALL_TAC] THEN
  SUBGOAL_THEN `rdt_dec3 (rdt_gv (H:real^N->real^N^N) y) = pde_jhc H y /\
                rdt_dec4 (rdt_gdv H y) = pde_jhdc H y /\
                rdt_dd1 (rdt_dgv (G:real^N->real^N^N) y) = pde_jd1 G y` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RDT_DEC3_GV; RDT_DEC4_GDV; RDT_DD1_DGV]; ALL_TAC] THEN
  ASM_REWRITE_TAC[rdt_psi; rdt_kf; pde_rdt_sym; FSTCART_PASTECART; SNDCART_PASTECART;
                  MATRIFY_VECTORIZE] THEN
  REWRITE_TAC[pde_jd1; mderiv]);;

(* ------------------------------------------------------------------------- *)
(* Smoothness of the outer maps on the invertible set.                       *)
(* ------------------------------------------------------------------------- *)

let RDT_OPEN_INV = prove
 (`!(f:real^M->real^(N,N)finite_prod).
     linear f ==> open {x | ~(det((matrify:real^(N,N)finite_prod->real^N^N) (f x)) = &0)}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^M)`; `f:real^M->real^(N,N)finite_prod`]
    (INST_TYPE [`:N`,`:N`] PDE_OPEN_INVERTIBLE_SET)) THEN
  ASM_SIMP_TAC[OPEN_UNIV; LINEAR_CONTINUOUS_ON; IN_UNIV; INVERTIBLE_DET_NZ]);;

let RDT_LINEAR_FS = prove
 (`linear (\x:real^(M,(P,Q)finite_sum)finite_sum. fstcart(sndcart x)) /\
   linear (\x:real^(M,(P,Q)finite_sum)finite_sum. sndcart(sndcart x)) /\
   linear (\x:real^(M,P)finite_sum. fstcart x)`,
  REWRITE_TAC[linear; FSTCART_ADD; SNDCART_ADD; FSTCART_CMUL; SNDCART_CMUL]);;

let RDT_LINEAR_FSS = prove
 (`linear (\x:real^(M,(P,(Q,R)finite_sum)finite_sum)finite_sum. fstcart(sndcart(sndcart x))) /\
   linear (\x:real^(M,(P,(Q,R)finite_sum)finite_sum)finite_sum. sndcart(sndcart(sndcart x)))`,
  REWRITE_TAC[linear; FSTCART_ADD; SNDCART_ADD; FSTCART_CMUL; SNDCART_CMUL]);;

let RDT_VEC_MATRIX_COMPONENT = prove
 (`!(f:real^M->real^N) k.
     1 <= k /\ k <= dimindex(:N) * dimindex(:M)
     ==> (vectorize(matrix f))$k =
         (f (basis (1 + (k - 1) MOD dimindex(:M))))$(1 + (k - 1) DIV dimindex(:M))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[VECTORIZE_COMPONENT] THEN
  MP_TAC(ISPECL [`dimindex(:N)`; `dimindex(:M)`; `k:num`] RDT_INDEX_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[matrix; LAMBDA_BETA] THEN REWRITE_TAC[ADD_SYM]);;

let RDT_VEC_LAMBDA2_COMPONENT = prove
 (`!(Tf:num->num->real) r.
     1 <= r /\ r <= dimindex(:N) * dimindex(:N)
     ==> (vectorize((lambda a b. Tf a b):real^N^N))$r =
         Tf (1 + (r - 1) DIV dimindex(:N)) (1 + (r - 1) MOD dimindex(:N))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[VECTORIZE_COMPONENT] THEN
  MP_TAC(ISPECL [`dimindex(:N)`; `dimindex(:N)`; `r:num`] RDT_INDEX_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN REWRITE_TAC[ADD_SYM]);;

let RDT_PHIA_SMOOTH = prove
 (`smooth_map_on {x | ~(det((matrify:real^(N,N)finite_prod->real^N^N) (fstcart x)) = &0)}
                 rdt_phia`,
  SUBGOAL_THEN
   `open {x:real^((N,N)finite_prod,((N,(N,N)finite_prod)finite_prod,
                   (N,(N,(N,N)finite_prod)finite_prod)finite_prod)finite_sum)finite_sum |
          ~(det((matrify:real^(N,N)finite_prod->real^N^N) (fstcart x)) = &0)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RDT_OPEN_INV THEN REWRITE_TAC[RDT_LINEAR_FS; LINEAR_FSTCART]; ALL_TAC] THEN
  SUBGOAL_THEN
   `rdt_phia =
    (\v:real^(N,N)finite_prod. (vectorize:real^N^N->real^(N,N)finite_prod)
                                 (transp((matrify:real^(N,N)finite_prod->real^N^N) v))) o
    ((vectorize:real^N^N->real^(N,N)finite_prod) o
     (\x:real^((N,N)finite_prod,((N,(N,N)finite_prod)finite_prod,
                 (N,(N,(N,N)finite_prod)finite_prod)finite_prod)finite_sum)finite_sum.
        matrix_inv((matrify:real^(N,N)finite_prod->real^N^N) (fstcart x))))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; rdt_phia; MATRIFY_VECTORIZE]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[linear; MATRIFY_ADD; MATRIFY_CMUL; TRANSP_MATRIX_ADD; TRANSP_MATRIX_CMUL;
                VECTORIZE_ADD; VECTORIZE_CMUL];
    ALL_TAC] THEN
  MATCH_MP_TAC LRG_SMOOTH_MATRIX_INV THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  REWRITE_TAC[o_DEF; VECTORIZE_MATRIFY] THEN
  MP_TAC(ISPECL [`{x:real^((N,N)finite_prod,((N,(N,N)finite_prod)finite_prod,
                     (N,(N,(N,N)finite_prod)finite_prod)finite_prod)finite_sum)finite_sum |
                   ~(det((matrify:real^(N,N)finite_prod->real^N^N) (fstcart x)) = &0)}`;
                 `\v:real^(N,N)finite_prod. v`;
                 `\x:real^((N,N)finite_prod,((N,(N,N)finite_prod)finite_prod,
                     (N,(N,(N,N)finite_prod)finite_prod)finite_prod)finite_sum)finite_sum.
                    fstcart x`] RDT_SMOOTH_LINEAR_O) THEN
  ASM_REWRITE_TAC[LINEAR_ID; RDT_LINEAR_FS; ETA_AX]);;

(* The atoms of the coefficient maps as smooth functions of x.              *)

let RDT_COEF_ATOMS = prove
 (`!S. S = {x | ~(det((matrify:real^(N,N)finite_prod->real^N^N) (fstcart x)) = &0)}
       ==> open S /\
           (!i j. smooth_map_on S
                    (\x:real^((N,N)finite_prod,((N,(N,N)finite_prod)finite_prod,
                               (N,(N,(N,N)finite_prod)finite_prod)finite_prod)finite_sum)
                              finite_sum.
                       lift(matrix_inv((matrify:real^(N,N)finite_prod->real^N^N)
                                         (fstcart x))$i$j))) /\
           (!i j. smooth_map_on S (\x. lift(((matrify:real^(N,N)finite_prod->real^N^N)
                                              (fstcart x))$i$j))) /\
           (!m a b. smooth_map_on S (\x. lift(rdt_dec3 (fstcart(sndcart x)) m a b))) /\
           (!c m a b. smooth_map_on S (\x. lift(rdt_dec4 (sndcart(sndcart x)) c m a b)))`,
  GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `open {x:real^((N,N)finite_prod,((N,(N,N)finite_prod)finite_prod,
                   (N,(N,(N,N)finite_prod)finite_prod)finite_prod)finite_sum)finite_sum |
          ~(det((matrify:real^(N,N)finite_prod->real^N^N) (fstcart x)) = &0)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RDT_OPEN_INV THEN REWRITE_TAC[RDT_LINEAR_FS; LINEAR_FSTCART]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [MATCH_MP_TAC RDT_SMOOTH_GI THEN ASM_REWRITE_TAC[RDT_LINEAR_FS; LINEAR_FSTCART; IN_ELIM_THM];
    MATCH_MP_TAC RDT_SMOOTH_PENTRY THEN ASM_REWRITE_TAC[RDT_LINEAR_FS; LINEAR_FSTCART];
    MATCH_MP_TAC RDT_SMOOTH_DEC3 THEN ASM_REWRITE_TAC[RDT_LINEAR_FS];
    MATCH_MP_TAC RDT_SMOOTH_DEC4 THEN ASM_REWRITE_TAC[RDT_LINEAR_FS]]);;

let RDT_PHIB_SMOOTH = prove
 (`!c. smooth_map_on
         {x | ~(det((matrify:real^(N,N)finite_prod->real^N^N) (fstcart x)) = &0)}
         (rdt_phib c)`,
  GEN_TAC THEN
  MP_TAC(ISPEC
   `{x:real^((N,N)finite_prod,((N,(N,N)finite_prod)finite_prod,
              (N,(N,(N,N)finite_prod)finite_prod)finite_prod)finite_sum)finite_sum |
     ~(det((matrify:real^(N,N)finite_prod->real^N^N) (fstcart x)) = &0)}` RDT_COEF_ATOMS) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC I
   [MATCH_MP (INST_TYPE [`:((N,N)finite_prod,(N,N)finite_prod)finite_prod`,`:N`;
                         `:((N,N)finite_prod,((N,(N,N)finite_prod)finite_prod,
                             (N,(N,(N,N)finite_prod)finite_prod)finite_prod)finite_sum)
                            finite_sum`,`:M`] SMOOTH_MAP_ON_COMPONENTWISE) th]) THEN
  X_GEN_TAC `k:num` THEN REWRITE_TAC[DIMINDEX_FINITE_PROD] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[rdt_phib; RDT_VEC_MATRIX_COMPONENT; DIMINDEX_FINITE_PROD] THEN
  SUBGOAL_THEN `1 <= 1 + (k - 1) DIV (dimindex(:N) * dimindex(:N)) /\
                1 + (k - 1) DIV (dimindex(:N) * dimindex(:N)) <= dimindex(:N) * dimindex(:N)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`dimindex(:N) * dimindex(:N)`; `dimindex(:N) * dimindex(:N)`; `k:num`]
      RDT_INDEX_SPLIT) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[RDT_VEC_LAMBDA2_COMPONENT] THEN
  MATCH_MP_TAC PDE_SM_JTRHESS THEN ASM_REWRITE_TAC[LIFT_NUM; SMOOTH_MAP_ON_CONST] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[LIFT_NUM; SMOOTH_MAP_ON_CONST]);;

let RDT_PHIC_SMOOTH = prove
 (`smooth_map_on
     {x | ~(det((matrify:real^(N,N)finite_prod->real^N^N) (fstcart x)) = &0)} rdt_phic`,
  MP_TAC(ISPEC
   `{x:real^((N,N)finite_prod,((N,(N,N)finite_prod)finite_prod,
              (N,(N,(N,N)finite_prod)finite_prod)finite_prod)finite_sum)finite_sum |
     ~(det((matrify:real^(N,N)finite_prod->real^N^N) (fstcart x)) = &0)}` RDT_COEF_ATOMS) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC I
   [MATCH_MP (INST_TYPE [`:((N,N)finite_prod,(N,N)finite_prod)finite_prod`,`:N`;
                         `:((N,N)finite_prod,((N,(N,N)finite_prod)finite_prod,
                             (N,(N,(N,N)finite_prod)finite_prod)finite_prod)finite_sum)
                            finite_sum`,`:M`] SMOOTH_MAP_ON_COMPONENTWISE) th]) THEN
  X_GEN_TAC `k:num` THEN REWRITE_TAC[DIMINDEX_FINITE_PROD] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[rdt_phic; RDT_VEC_MATRIX_COMPONENT; DIMINDEX_FINITE_PROD] THEN
  SUBGOAL_THEN `1 <= 1 + (k - 1) DIV (dimindex(:N) * dimindex(:N)) /\
                1 + (k - 1) DIV (dimindex(:N) * dimindex(:N)) <= dimindex(:N) * dimindex(:N)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`dimindex(:N) * dimindex(:N)`; `dimindex(:N) * dimindex(:N)`; `k:num`]
      RDT_INDEX_SPLIT) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[RDT_VEC_LAMBDA2_COMPONENT] THEN
  MATCH_MP_TAC PDE_SM_JTRHESS THEN ASM_REWRITE_TAC[LIFT_NUM; SMOOTH_MAP_ON_CONST]);;

let RDT_PSI_SMOOTH = prove
 (`smooth_map_on
     {x | ~(det((matrify:real^(N,N)finite_prod->real^N^N) (fstcart x)) = &0)} rdt_psi`,
  SUBGOAL_THEN
   `open {x:real^((N,N)finite_prod,((N,(N,N)finite_prod)finite_prod,
                   ((N,(N,N)finite_prod)finite_prod,
                    (N,(N,(N,N)finite_prod)finite_prod)finite_prod)finite_sum)finite_sum)
                  finite_sum |
          ~(det((matrify:real^(N,N)finite_prod->real^N^N) (fstcart x)) = &0)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RDT_OPEN_INV THEN REWRITE_TAC[LINEAR_FSTCART]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC I
   [MATCH_MP (INST_TYPE [`:(N,N)finite_prod`,`:N`;
                         `:((N,N)finite_prod,((N,(N,N)finite_prod)finite_prod,
                            ((N,(N,N)finite_prod)finite_prod,
                             (N,(N,(N,N)finite_prod)finite_prod)finite_prod)finite_sum)
                           finite_sum)finite_sum`,`:M`] SMOOTH_MAP_ON_COMPONENTWISE) th]) THEN
  X_GEN_TAC `k:num` THEN REWRITE_TAC[DIMINDEX_FINITE_PROD] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[rdt_psi; RDT_VEC_LAMBDA2_COMPONENT] THEN
  MATCH_MP_TAC PDE_SM_JDJ THEN ASM_REWRITE_TAC[LIFT_NUM; SMOOTH_MAP_ON_CONST] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  FIRST (map (fun th -> MATCH_MP_TAC th THEN
                        ASM_REWRITE_TAC[LINEAR_FSTCART; RDT_LINEAR_FS; RDT_LINEAR_FSS;
                                        IN_ELIM_THM])
             [RDT_SMOOTH_PENTRY; RDT_SMOOTH_GI; RDT_SMOOTH_DD1; RDT_SMOOTH_DEC3;
              RDT_SMOOTH_DEC4]));;

(* ------------------------------------------------------------------------- *)
(* The tame jet bound of a fixed smooth outer map composed with              *)
(* an inner map whose value lies in a compact subset of the domain, and the  *)
(* compact sets of arguments (positive definite part with bounds).           *)
(* ------------------------------------------------------------------------- *)

let RDT_COMPOSE_JETN = prove
 (`!m (Phi:real^M->real^P) W S Mlow.
     open W /\ smooth_map_on W Phi /\ compact S /\ S SUBSET W /\ &0 <= Mlow
     ==> ?C. &0 <= C /\
             !U (Kf:real^N->real^M) y.
               open U /\ smooth_map_on U Kf /\ IMAGE Kf U SUBSET W /\ y IN U /\ Kf y IN S /\
               pde_jetn (m DIV 2 + 1) Kf y <= Mlow
               ==> pde_jetn m (\z. Phi(Kf z)) y <= C * (&1 + pde_jetn m Kf y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`W:real^M->bool`; `S:real^M->bool`; `Phi:real^M->real^P`; `m:num`]
    RDT_JETS_BOUNDED_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `MP:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(INST_TYPE [`:M`,`:M`; `:P`,`:P`; `:N`,`:N`] RDT_COMPOSE_TAME) THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `cc:num->real` (LABEL_TAC "ct")) THEN
  SUBGOAL_THEN `!k. &0 <= (cc:num->real) k` ASSUME_TAC THENL
   [GEN_TAC THEN USE_THEN "ct" (MP_TAC o SPEC `k:num`) THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sum(0..m) (cc:num->real)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `&(CARD(pde_index_lists m (:N))) *
              (sum(0..m) cc * MP * (&1 + Mlow) pow m)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [pde_jetn] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (pde_index_lists m (:N))
                (\l:num list. (sum(0..m) cc * MP * (&1 + Mlow) pow m) *
                              (&1 + pde_jetn m (Kf:real^N->real^M) y))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    SIMP_TAC[SUM_CONST; PDE_INDEX_LISTS_FINITE] THEN REWRITE_TAC[REAL_MUL_ASSOC; REAL_LE_REFL]] THEN
  MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
  X_GEN_TAC `l:num list` THEN REWRITE_TAC[pde_index_lists; IN_ELIM_THM] THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  REMOVE_THEN "ct" (MP_TAC o SPEC `LENGTH(l:num list)`) THEN
  DISCH_THEN(MP_TAC o SPECL [`Phi:real^M->real^P`; `Kf:real^N->real^M`; `U:real^N->bool`;
                             `W:real^M->bool`; `y:real^N`; `l:num list`] o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  ABBREV_TAC `n = LENGTH(l:num list)` THEN
  SUBGOAL_THEN `n DIV 2 + 1 <= m DIV 2 + 1` ASSUME_TAC THENL
   [REWRITE_TAC[LE_ADD_RCANCEL] THEN MATCH_MP_TAC DIV_MONO THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC RDT_PROD4_LE THEN
  SIMP_TAC[PDE_JETN_POS; REAL_POW_LE; REAL_ARITH `&0 <= x ==> &0 <= &1 + x`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`{n:num}`; `0..m`; `cc:num->real`] SUM_SUBSET_SIMPLE) THEN
    REWRITE_TAC[SUM_SING; FINITE_NUMSEG; SING_SUBSET; IN_NUMSEG] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `pde_jetn m (Phi:real^M->real^P) ((Kf:real^N->real^M) y)` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC PDE_JETN_MONO THEN ASM_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 + Mlow) pow n` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN
      SIMP_TAC[PDE_JETN_POS; REAL_ARITH `&0 <= x ==> &0 <= &1 + x`] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= y ==> &1 + x <= &1 + y`) THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `pde_jetn (m DIV 2 + 1) (Kf:real^N->real^M) y` THEN
      ASM_SIMP_TAC[PDE_JETN_MONO];
      MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> &1 + x <= &1 + y`) THEN
    MATCH_MP_TAC PDE_JETN_MONO THEN ASM_ARITH_TAC]);;

(* Compact sets of arguments: bounded matrices with a uniform lower bound.   *)

let RDT_POSB_INV = prove
 (`!K1 (P:real^(N,N)finite_prod).
     (!v:real^N. norm v pow 2 <= K1 * (v dot ((matrify P:real^N^N) ** v)))
     ==> ~(det(matrify P:real^N^N) = &0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM HOMOGENEOUS_LINEAR_EQUATIONS_DET] THEN
  DISCH_TAC THEN DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N`) THEN
  ASM_REWRITE_TAC[DOT_RZERO; REAL_MUL_RZERO] THEN
  ASM_SIMP_TAC[REAL_POW_LE; NORM_POS_LE; REAL_ARITH `&0 <= x ==> (x <= &0 <=> x = &0)`] THEN
  ASM_REWRITE_TAC[REAL_POW_EQ_0; NORM_EQ_0; ARITH_EQ]);;

let RDT_POSB_CLOSED = prove
 (`!K1. closed {P:real^(N,N)finite_prod |
                !v:real^N. norm v pow 2 <= K1 * (v dot ((matrify P:real^N^N) ** v))}`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `{P:real^(N,N)finite_prod |
     !v:real^N. norm v pow 2 <= K1 * (v dot ((matrify P:real^N^N) ** v))} =
    INTERS {{P | lift(K1 * (v dot ((matrify P:real^N^N) ** v))) IN
                 {y:real^1 | y$1 >= norm v pow 2}} | v IN (:real^N)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; INTERS_GSPEC; IN_ELIM_THM; IN_UNIV; LIFT_COMPONENT; real_ge];
    ALL_TAC] THEN
  MATCH_MP_TAC CLOSED_INTERS THEN REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV] THEN
  X_GEN_TAC `v:real^N` THEN MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE_UNIV THEN
  REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_GE] THEN GEN_TAC THEN
  MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
  REWRITE_TAC[linear; MATRIFY_ADD; MATRIFY_CMUL; MATRIX_VECTOR_MUL_ADD_RDISTRIB;
              MATRIX_VECTOR_LMUL; DOT_RADD; DOT_RMUL; LIFT_ADD; LIFT_CMUL] THEN
  REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC);;

let rdt_sk = new_definition
 `rdt_sk (K1:real) (R:real) =
    {x:real^((N,N)finite_prod,Q)finite_sum |
       norm(fstcart x) <= K1 /\
       (!v:real^N. norm v pow 2 <= K1 * (v dot ((matrify(fstcart x):real^N^N) ** v))) /\
       norm(sndcart x) <= R}`;;

let RDT_SK_COMPACT = prove
 (`!K1 R. compact(rdt_sk K1 R:real^((N,N)finite_prod,Q)finite_sum->bool)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
   [REWRITE_TAC[bounded; rdt_sk; IN_ELIM_THM] THEN EXISTS_TAC `K1 + R:real` THEN
    X_GEN_TAC `x:real^((N,N)finite_prod,Q)finite_sum` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`fstcart(x:real^((N,N)finite_prod,Q)finite_sum)`;
                   `sndcart(x:real^((N,N)finite_prod,Q)finite_sum)`] NORM_PASTECART_LE) THEN
    REWRITE_TAC[PASTECART_FST_SND] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `rdt_sk K1 R:real^((N,N)finite_prod,Q)finite_sum->bool =
    {x | fstcart x IN {P:real^(N,N)finite_prod | norm P <= K1} INTER
                      {P | !v:real^N. norm v pow 2 <= K1 * (v dot ((matrify P:real^N^N) ** v))}} INTER
    {x | sndcart x IN cball(vec 0:real^Q,R)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[rdt_sk; EXTENSION; IN_INTER; IN_ELIM_THM; IN_CBALL_0] THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CLOSED_INTER THEN CONJ_TAC THEN
  MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE_UNIV THEN
  SIMP_TAC[LINEAR_CONTINUOUS_AT; LINEAR_FSTCART; LINEAR_SNDCART; CLOSED_CBALL] THEN
  MATCH_MP_TAC CLOSED_INTER THEN REWRITE_TAC[RDT_POSB_CLOSED] THEN
  SUBGOAL_THEN `{P:real^(N,N)finite_prod | norm P <= K1} = cball(vec 0,K1)` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_CBALL_0]; REWRITE_TAC[CLOSED_CBALL]]);;

let RDT_SK_SUBSET = prove
 (`!K1 R. rdt_sk K1 R SUBSET
          {x:real^((N,N)finite_prod,Q)finite_sum |
             ~(det((matrify:real^(N,N)finite_prod->real^N^N) (fstcart x)) = &0)}`,
  REWRITE_TAC[rdt_sk; SUBSET; IN_ELIM_THM] THEN MESON_TAC[RDT_POSB_INV]);;

(* ------------------------------------------------------------------------- *)
(* Smoothness and jets of the inner map rdt_kc, the composition              *)
(* bound on the invertible set, and the tame bound of the jet sum of the     *)
(* lop0 coefficients of tr_G Hess_H (RDT_COEF_CJET).                         *)
(* ------------------------------------------------------------------------- *)

let RDT_GV_SMOOTH = prove
 (`!U (H:real^N->real^N^N). metric_field U H ==> smooth_map_on U (rdt_gv H)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  REWRITE_TAC[RDT_GV_FUN] THEN MATCH_MP_TAC RDT_SMOOTH_VLAMBDA THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `a:num` THEN DISCH_TAC THEN MATCH_MP_TAC RDT_SMOOTH_VLAMBDA THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `b:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `H:real^N->real^N^N`; `basis a:real^N`;
                 `\y:real^N. basis b:real^N`] LRG_CHRISTOFFEL_SMOOTH_ARG) THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST]);;

let RDT_GDV_SMOOTH = prove
 (`!U (H:real^N->real^N^N). metric_field U H ==> smooth_map_on U (rdt_gdv H)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  REWRITE_TAC[RDT_GDV_FUN] THEN MATCH_MP_TAC RDT_SMOOTH_VLAMBDA THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `c:num` THEN DISCH_TAC THEN MATCH_MP_TAC RDT_SMOOTH_VLAMBDA THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `a:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC RDT_SMOOTH_VLAMBDA THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `b:num` THEN DISCH_TAC THEN REWRITE_TAC[ETA_AX] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `H:real^N->real^N^N`; `basis a:real^N`;
                 `\y:real^N. basis b:real^N`] LRG_CHRISTOFFEL_SMOOTH_ARG) THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST]);;

let RDT_KC_FUN = prove
 (`!(G:real^N->real^N^N) H.
     rdt_kc G H =
     (\z. pastecart ((vectorize:real^N^N->real^(N,N)finite_prod) (G z))
                    (pastecart (rdt_gv H z) (rdt_gdv H z)))`,
  REWRITE_TAC[FUN_EQ_THM; rdt_kc]);;

let RDT_KC_SMOOTH_JETN = prove
 (`!U (G:real^N->real^N^N) H y k.
     metric_field U G /\ metric_field U H /\ y IN U
     ==> smooth_map_on U (rdt_kc G H) /\
         pde_jetn k (rdt_kc G H) y <=
         pde_jetn k ((vectorize:real^N^N->real^(N,N)finite_prod) o G) y +
         pde_jetn k (rdt_gv H) y + pde_jetn k (rdt_gdv H) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool) /\
                smooth_map_on U (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                                       ((G:real^N->real^N^N) z)) /\
                smooth_map_on U (rdt_gv (H:real^N->real^N^N)) /\
                smooth_map_on U (rdt_gdv H)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN CONJ_TAC THENL
     [UNDISCH_TAC `metric_field U (G:real^N->real^N^N)` THEN SIMP_TAC[metric_field; o_DEF];
      ASM_MESON_TAC[RDT_GV_SMOOTH; RDT_GDV_SMOOTH]];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on U (\z. pastecart (rdt_gv (H:real^N->real^N^N) z) (rdt_gdv H z))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  REWRITE_TAC[RDT_KC_FUN; o_DEF] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`;
                 `\z. (vectorize:real^N^N->real^(N,N)finite_prod) ((G:real^N->real^N^N) z)`;
                 `\z. pastecart (rdt_gv (H:real^N->real^N^N) z) (rdt_gdv H z)`; `y:real^N`]
    RDT_JETN_PASTECART) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> x <= a + b ==> x <= a + c`) THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `rdt_gv (H:real^N->real^N^N)`;
                 `rdt_gdv (H:real^N->real^N^N)`; `y:real^N`] RDT_JETN_PASTECART) THEN
  ASM_REWRITE_TAC[ETA_AX]);;

(* The composition bound on the invertible set with values in rdt_sk.       *)

let RDT_COMPOSE_INV = prove
 (`!(Phi:real^((N,N)finite_prod,Q)finite_sum->real^P).
     smooth_map_on {x | ~(det((matrify:real^(N,N)finite_prod->real^N^N) (fstcart x)) = &0)} Phi
     ==> !m K1 R Mlow. &0 <= Mlow
         ==> ?C. &0 <= C /\
                 !U (Kf:real^K->real^((N,N)finite_prod,Q)finite_sum) y.
                   open U /\ smooth_map_on U Kf /\
                   (!z. z IN U ==> ~(det((matrify:real^(N,N)finite_prod->real^N^N)
                                           (fstcart(Kf z))) = &0)) /\
                   y IN U /\ Kf y IN rdt_sk K1 R /\
                   pde_jetn (m DIV 2 + 1) Kf y <= Mlow
                   ==> pde_jetn m (\z. Phi(Kf z)) y <= C * (&1 + pde_jetn m Kf y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:num`; `Phi:real^((N,N)finite_prod,Q)finite_sum->real^P`;
                 `{x:real^((N,N)finite_prod,Q)finite_sum |
                     ~(det((matrify:real^(N,N)finite_prod->real^N^N) (fstcart x)) = &0)}`;
                 `rdt_sk K1 R:real^((N,N)finite_prod,Q)finite_sum->bool`; `Mlow:real`]
    (INST_TYPE [`:K`,`:N`] RDT_COMPOSE_JETN)) THEN
  ASM_REWRITE_TAC[RDT_SK_COMPACT; RDT_SK_SUBSET] THEN ANTS_TAC THENL
   [MATCH_MP_TAC RDT_OPEN_INV THEN REWRITE_TAC[LINEAR_FSTCART]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) THEN EXISTS_TAC `C:real` THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `U:real^K->bool` THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM]);;

(* The tame bound of the coefficient jets of tr_G Hess_H in pde_lop0 form.  *)

let RDT_COEF_CJET = prove
 (`!m K1 MG BH LH.
     &0 <= MG
     ==> ?C. &0 <= C /\
             !U (G:real^N->real^N^N) H y.
               metric_field U G /\ metric_field U H /\ y IN U /\
               norm(vectorize(G y)) <= K1 /\
               (!v. norm v pow 2 <= K1 * (v dot (G y ** v))) /\
               pde_jetn (m DIV 2 + 1) (vectorize o G) y <= MG /\
               pde_jetn (m + 3) (vectorize o H) y <= BH /\
               norm(vectorize(matrix_inv(H y))) <= LH
               ==> rdt_cjet m (\y. transp(matrix_inv(G y))) (\y c. pde_mlbb G H y c)
                              (\y. pde_mlcc G H y) y
                   <= C * (&1 + pde_jetn m (vectorize o G) y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`m + 1`; `BH:real`; `LH:real`] (INST_TYPE [`:N`,`:N`] RDT_GV_JETN)) THEN
  DISCH_THEN(X_CHOOSE_THEN `Cg:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gv"))) THEN
  MP_TAC(ISPECL [`m + 1`; `BH:real`; `LH:real`] (INST_TYPE [`:N`,`:N`] RDT_GDV_JETN)) THEN
  DISCH_THEN(X_CHOOSE_THEN `Cd:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gdv"))) THEN
  SUBGOAL_THEN `&0 <= MG + Cg + Cd` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(INST_TYPE [`:N`,`:K`] (SPECL [`m:num`; `K1:real`; `Cg + Cd:real`; `MG + Cg + Cd:real`]
           (MATCH_MP RDT_COMPOSE_INV RDT_PHIA_SMOOTH))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `CA:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ca"))) THEN
  MP_TAC(INST_TYPE [`:N`,`:K`] (SPECL [`m:num`; `K1:real`; `Cg + Cd:real`; `MG + Cg + Cd:real`]
           (MATCH_MP RDT_COMPOSE_INV RDT_PHIC_SMOOTH))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `CC:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cc"))) THEN
  MP_TAC(INST_TYPE [`:N`,`:K`] (GEN `c:num` (SPECL [`m:num`; `K1:real`; `Cg + Cd:real`; `MG + Cg + Cd:real`]
           (MATCH_MP RDT_COMPOSE_INV (SPEC `c:num` RDT_PHIB_SMOOTH))))) THEN
  ASM_REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `CB:num->real` (LABEL_TAC "cb")) THEN
  SUBGOAL_THEN `!c. &0 <= (CB:num->real) c` ASSUME_TAC THENL
   [GEN_TAC THEN USE_THEN "cb" (MP_TAC o SPEC `c:num`) THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sum(1..dimindex(:N)) (CB:num->real)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `(CA + sum(1..dimindex(:N)) CB + CC) * (&1 + Cg + Cd)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool) /\
                smooth_map_on U ((vectorize:real^N^N->real^(N,N)finite_prod) o H) /\
                (!z. z IN U ==> ~(det((H:real^N->real^N^N) z) = &0)) /\
                (!z. z IN U ==> ~(det((G:real^N->real^N^N) z) = &0))`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field; LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  SUBGOAL_THEN `pde_jetn (m + 1) (rdt_gv (H:real^N->real^N^N)) y <= Cg /\
                pde_jetn (m + 1) (rdt_gdv H) y <= Cd`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "gv" (MP_TAC o SPECL [`U:real^N->bool`; `H:real^N->real^N^N`; `y:real^N`]);
      USE_THEN "gdv" (MP_TAC o SPECL [`U:real^N->bool`; `H:real^N->real^N^N`; `y:real^N`])] THEN
    (ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]]) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `SUC(SUC(m + 1)) = m + 3`] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `pde_jetn (m + 3) ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                  (H:real^N->real^N^N)) y` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PDE_JETN_MONO THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. k <= m + 1
                    ==> pde_jetn k (rdt_gv (H:real^N->real^N^N)) y <= Cg /\
                        pde_jetn k (rdt_gdv H) y <= Cd`
  (LABEL_TAC "lowj") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `pde_jetn (m + 1) (rdt_gv (H:real^N->real^N^N)) y`;
      EXISTS_TAC `pde_jetn (m + 1) (rdt_gdv (H:real^N->real^N^N)) y`] THEN
    ASM_SIMP_TAC[PDE_JETN_MONO];
    ALL_TAC] THEN
  (* the inner map *)
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `H:real^N->real^N^N`; `y:real^N`]
    RDT_KC_SMOOTH_JETN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "kc") THEN
  SUBGOAL_THEN
   `smooth_map_on U (rdt_kc (G:real^N->real^N^N) H) /\
    (!z. z IN U ==> ~(det((matrify:real^(N,N)finite_prod->real^N^N)
                            (fstcart(rdt_kc G H z))) = &0)) /\
    rdt_kc G H y IN rdt_sk K1 (Cg + Cd) /\
    pde_jetn (m DIV 2 + 1) (rdt_kc G H) y <= MG + Cg + Cd /\
    pde_jetn m (rdt_kc G H) y <=
    pde_jetn m ((vectorize:real^N^N->real^(N,N)finite_prod) o G) y + Cg + Cd`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "kc" (MP_TAC o SPEC `0`) THEN SIMP_TAC[];
      ASM_SIMP_TAC[rdt_kc; FSTCART_PASTECART; MATRIFY_VECTORIZE];
      REWRITE_TAC[rdt_sk; IN_ELIM_THM; rdt_kc; FSTCART_PASTECART; SNDCART_PASTECART;
                  MATRIFY_VECTORIZE] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm(rdt_gv (H:real^N->real^N^N) y) + norm(rdt_gdv H y)` THEN
      REWRITE_TAC[NORM_PASTECART_LE] THEN
      USE_THEN "lowj" (MP_TAC o SPEC `0`) THEN REWRITE_TAC[RDT_JETN_0; LE_0] THEN
      REAL_ARITH_TAC;
      USE_THEN "kc" (MP_TAC o SPEC `m DIV 2 + 1`) THEN
      MATCH_MP_TAC(REAL_ARITH `a <= a' /\ b <= b' /\ c <= c' ==>
                               (s /\ x <= a + b + c) ==> x <= a' + b' + c'`) THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
      (USE_THEN "lowj" (MP_TAC o SPEC `m DIV 2 + 1`) THEN ANTS_TAC THENL
        [MP_TAC(SPECL [`m:num`; `2`] DIVISION) THEN ARITH_TAC; SIMP_TAC[]]);
      USE_THEN "kc" (MP_TAC o SPEC `m:num`) THEN
      MATCH_MP_TAC(REAL_ARITH `b <= b' /\ c <= c' ==>
                               (s /\ x <= a + b + c) ==> x <= a + b' + c'`) THEN
      USE_THEN "lowj" (MP_TAC o SPEC `m:num`) THEN ANTS_TAC THENL [ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  ABBREV_TAC `J = pde_jetn m ((vectorize:real^N^N->real^(N,N)finite_prod) o
                              (G:real^N->real^N^N)) y` THEN
  SUBGOAL_THEN `&0 <= J` ASSUME_TAC THENL [EXPAND_TAC "J" THEN REWRITE_TAC[PDE_JETN_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `!X. &0 <= X ==> X * (&1 + pde_jetn m (rdt_kc (G:real^N->real^N^N) H) y) <=
                                 X * (&1 + Cg + Cd) * (&1 + J)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `X * (&1 + J + Cg + Cd)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ARITH `X * (&1 + J + a + b) = X * (&1 + J) + X * (a + b)`;
                  REAL_ARITH `X * (&1 + a + b) * (&1 + J) =
                              X * (&1 + J) + X * (a + b) + X * ((a + b) * J)`] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= z ==> x + y <= x + y + z`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[rdt_cjet] THEN
  SUBGOAL_THEN
   `pde_jetn m (\x. (vectorize:real^N^N->real^(N,N)finite_prod)
                      (transp(matrix_inv((G:real^N->real^N^N) x)))) y <=
    CA * (&1 + Cg + Cd) * (&1 + J) /\
    sum(1..dimindex(:N))
      (\i. pde_jetn m (\x. (vectorize:real^(N,N)finite_prod^(N,N)finite_prod
                                      ->real^((N,N)finite_prod,(N,N)finite_prod)finite_prod)
                             (pde_mlbb G H x i)) y) <=
    sum(1..dimindex(:N)) CB * (&1 + Cg + Cd) * (&1 + J) /\
    pde_jetn m (\x. (vectorize:real^(N,N)finite_prod^(N,N)finite_prod
                               ->real^((N,N)finite_prod,(N,N)finite_prod)finite_prod)
                      (pde_mlcc G H x)) y <=
    CC * (&1 + Cg + Cd) * (&1 + J)`
  MP_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`m:num`; `U:real^N->bool`;
        `\x. (vectorize:real^N^N->real^(N,N)finite_prod) (transp(matrix_inv((G:real^N->real^N^N) x)))`;
        `\z. rdt_phia(rdt_kc (G:real^N->real^N^N) H z)`; `y:real^N`] P2CT_JETN_LOCAL) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[RDT_PHIA_KC]; DISCH_THEN SUBST1_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `CA * (&1 + pde_jetn m (rdt_kc (G:real^N->real^N^N) H) y)` THEN
      ASM_SIMP_TAC[] THEN USE_THEN "ca" MATCH_MP_TAC THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM SUM_RMUL; GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
      X_GEN_TAC `c:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`m:num`; `U:real^N->bool`;
        `\x. (vectorize:real^(N,N)finite_prod^(N,N)finite_prod
                        ->real^((N,N)finite_prod,(N,N)finite_prod)finite_prod)
               (pde_mlbb (G:real^N->real^N^N) H x c)`;
        `\z. rdt_phib c (rdt_kc (G:real^N->real^N^N) H z)`; `y:real^N`] P2CT_JETN_LOCAL) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[RDT_PHIB_KC]; DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(CB:num->real) c * (&1 + pde_jetn m (rdt_kc (G:real^N->real^N^N) H) y)` THEN
      CONJ_TAC THENL
       [USE_THEN "cb" (MP_TAC o SPEC `c:num`) THEN
        DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN EXISTS_TAC `U:real^N->bool` THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN ASM_SIMP_TAC[]];
      MP_TAC(ISPECL [`m:num`; `U:real^N->bool`;
        `\x. (vectorize:real^(N,N)finite_prod^(N,N)finite_prod
                        ->real^((N,N)finite_prod,(N,N)finite_prod)finite_prod)
               (pde_mlcc (G:real^N->real^N^N) H x)`;
        `\z. rdt_phic (rdt_kc (G:real^N->real^N^N) H z)`; `y:real^N`] P2CT_JETN_LOCAL) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[RDT_PHIC_KC]; DISCH_THEN SUBST1_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `CC * (&1 + pde_jetn m (rdt_kc (G:real^N->real^N^N) H) y)` THEN
      ASM_SIMP_TAC[] THEN USE_THEN "cc" MATCH_MP_TAC THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The inner map rdt_kf of the remainder and the tame bound of               *)
(* the jets of the Ricci-DeTurck remainder pde_rdt_sym H (y, G, DG).         *)
(* ------------------------------------------------------------------------- *)

let RDT_KF_FUN = prove
 (`!(G:real^N->real^N^N) H.
     rdt_kf G H =
     (\z. pastecart ((vectorize:real^N^N->real^(N,N)finite_prod) (G z))
                    (pastecart (rdt_dgv G z) (pastecart (rdt_gv H z) (rdt_gdv H z))))`,
  REWRITE_TAC[FUN_EQ_THM; rdt_kf]);;

let RDT_KF_SMOOTH_JETN = prove
 (`!U (G:real^N->real^N^N) H y k.
     metric_field U G /\ metric_field U H /\ y IN U
     ==> smooth_map_on U (rdt_kf G H) /\
         pde_jetn k (rdt_kf G H) y <=
         pde_jetn k ((vectorize:real^N^N->real^(N,N)finite_prod) o G) y +
         pde_jetn k (rdt_dgv G) y + pde_jetn k (rdt_gv H) y + pde_jetn k (rdt_gdv H) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool) /\
                smooth_map_on U ((vectorize:real^N^N->real^(N,N)finite_prod) o G) /\
                smooth_map_on U (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                                       ((G:real^N->real^N^N) z)) /\
                smooth_map_on U (rdt_gv (H:real^N->real^N^N)) /\
                smooth_map_on U (rdt_gdv H)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN CONJ_TAC THENL
     [UNDISCH_TAC `metric_field U (G:real^N->real^N^N)` THEN SIMP_TAC[metric_field; o_DEF];
      ASM_MESON_TAC[RDT_GV_SMOOTH; RDT_GDV_SMOOTH]];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on U (rdt_dgv (G:real^N->real^N^N))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`0`; `U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] RDT_DGV_JETN) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on U (\z. pastecart (rdt_gv (H:real^N->real^N^N) z) (rdt_gdv H z))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on U (\z. pastecart (rdt_dgv (G:real^N->real^N^N) z)
                                               (pastecart (rdt_gv (H:real^N->real^N^N) z)
                                                          (rdt_gdv H z)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  REWRITE_TAC[RDT_KF_FUN; o_DEF] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`;
                 `\z. (vectorize:real^N^N->real^(N,N)finite_prod) ((G:real^N->real^N^N) z)`;
                 `\z. pastecart (rdt_dgv (G:real^N->real^N^N) z)
                                (pastecart (rdt_gv (H:real^N->real^N^N) z) (rdt_gdv H z))`;
                 `y:real^N`] RDT_JETN_PASTECART) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> x <= a + b ==> x <= a + c`) THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `rdt_dgv (G:real^N->real^N^N)`;
                 `\z. pastecart (rdt_gv (H:real^N->real^N^N) z) (rdt_gdv H z)`; `y:real^N`]
    RDT_JETN_PASTECART) THEN
  ASM_REWRITE_TAC[ETA_AX] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> x <= a + b ==> x <= a + c`) THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `rdt_gv (H:real^N->real^N^N)`;
                 `rdt_gdv (H:real^N->real^N^N)`; `y:real^N`] RDT_JETN_PASTECART) THEN
  ASM_REWRITE_TAC[ETA_AX]);;

let RDT_REM_JETN = prove
 (`!m K1 MG BH LH.
     &0 <= MG
     ==> ?C. &0 <= C /\
             !U (G:real^N->real^N^N) H y.
               metric_field U G /\ metric_field U H /\ y IN U /\
               norm(vectorize(G y)) <= K1 /\
               (!v. norm v pow 2 <= K1 * (v dot (G y ** v))) /\
               pde_jetn (m DIV 2 + 2) (vectorize o G) y <= MG /\
               pde_jetn (m + 3) (vectorize o H) y <= BH /\
               norm(vectorize(matrix_inv(H y))) <= LH
               ==> pde_jetn m (\z. rdt_psi (rdt_kf G H z)) y <=
                   C * (&1 + pde_jetn (m + 1) (vectorize o G) y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`m + 1`; `BH:real`; `LH:real`] (INST_TYPE [`:N`,`:N`] RDT_GV_JETN)) THEN
  DISCH_THEN(X_CHOOSE_THEN `Cg:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gv"))) THEN
  MP_TAC(ISPECL [`m + 1`; `BH:real`; `LH:real`] (INST_TYPE [`:N`,`:N`] RDT_GDV_JETN)) THEN
  DISCH_THEN(X_CHOOSE_THEN `Cd:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gdv"))) THEN
  ABBREV_TAC `NN = &(dimindex(:N) * dimindex(:(N,N)finite_prod))` THEN
  SUBGOAL_THEN `&0 <= NN` ASSUME_TAC THENL [EXPAND_TAC "NN" THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= MG + NN * MG + Cg + Cd /\ &0 <= NN * MG` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= NN * MG` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(INST_TYPE [`:N`,`:K`]
    (SPECL [`m:num`; `K1:real`; `NN * MG + Cg + Cd:real`; `MG + NN * MG + Cg + Cd:real`]
           (MATCH_MP RDT_COMPOSE_INV RDT_PSI_SMOOTH))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `CP:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cp"))) THEN
  EXISTS_TAC `CP * (&1 + NN + Cg + Cd)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool) /\
                smooth_map_on U ((vectorize:real^N^N->real^(N,N)finite_prod) o H) /\
                smooth_map_on U ((vectorize:real^N^N->real^(N,N)finite_prod) o G) /\
                (!z. z IN U ==> ~(det((H:real^N->real^N^N) z) = &0)) /\
                (!z. z IN U ==> ~(det((G:real^N->real^N^N) z) = &0))`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field; LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  SUBGOAL_THEN `pde_jetn (m + 1) (rdt_gv (H:real^N->real^N^N)) y <= Cg /\
                pde_jetn (m + 1) (rdt_gdv H) y <= Cd`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "gv" (MP_TAC o SPECL [`U:real^N->bool`; `H:real^N->real^N^N`; `y:real^N`]);
      USE_THEN "gdv" (MP_TAC o SPECL [`U:real^N->bool`; `H:real^N->real^N^N`; `y:real^N`])] THEN
    (ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]]) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `SUC(SUC(m + 1)) = m + 3`] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `pde_jetn (m + 3) ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                  (H:real^N->real^N^N)) y` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PDE_JETN_MONO THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. k <= m + 1
                    ==> pde_jetn k (rdt_gv (H:real^N->real^N^N)) y <= Cg /\
                        pde_jetn k (rdt_gdv H) y <= Cd`
  (LABEL_TAC "lowj") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `pde_jetn (m + 1) (rdt_gv (H:real^N->real^N^N)) y`;
      EXISTS_TAC `pde_jetn (m + 1) (rdt_gdv (H:real^N->real^N^N)) y`] THEN
    ASM_SIMP_TAC[PDE_JETN_MONO];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. pde_jetn k (rdt_dgv (G:real^N->real^N^N)) y <=
                    NN * pde_jetn (SUC k) ((vectorize:real^N^N->real^(N,N)finite_prod) o G) y`
  (LABEL_TAC "dgvj") THENL
   [GEN_TAC THEN EXPAND_TAC "NN" THEN
    MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] RDT_DGV_JETN) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `H:real^N->real^N^N`; `y:real^N`]
    RDT_KF_SMOOTH_JETN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "kf") THEN
  ABBREV_TAC `J1 = pde_jetn (m + 1) ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                     (G:real^N->real^N^N)) y` THEN
  SUBGOAL_THEN `&0 <= J1` ASSUME_TAC THENL [EXPAND_TAC "J1" THEN REWRITE_TAC[PDE_JETN_POS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on U (rdt_kf (G:real^N->real^N^N) H) /\
    (!z. z IN U ==> ~(det((matrify:real^(N,N)finite_prod->real^N^N)
                            (fstcart(rdt_kf G H z))) = &0)) /\
    rdt_kf G H y IN rdt_sk K1 (NN * MG + Cg + Cd) /\
    pde_jetn (m DIV 2 + 1) (rdt_kf G H) y <= MG + NN * MG + Cg + Cd /\
    pde_jetn m (rdt_kf G H) y <= (&1 + NN) * J1 + Cg + Cd`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "kf" (MP_TAC o SPEC `0`) THEN SIMP_TAC[];
      ASM_SIMP_TAC[rdt_kf; FSTCART_PASTECART; MATRIFY_VECTORIZE];
      REWRITE_TAC[rdt_sk; IN_ELIM_THM; rdt_kf; FSTCART_PASTECART; SNDCART_PASTECART;
                  MATRIFY_VECTORIZE] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm(rdt_dgv (G:real^N->real^N^N) y) +
                  norm(rdt_gv (H:real^N->real^N^N) y) + norm(rdt_gdv H y)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `norm(rdt_dgv (G:real^N->real^N^N) y) +
                    norm(pastecart (rdt_gv (H:real^N->real^N^N) y) (rdt_gdv H y))` THEN
        REWRITE_TAC[NORM_PASTECART_LE] THEN
        MP_TAC(ISPECL [`rdt_gv (H:real^N->real^N^N) y`; `rdt_gdv (H:real^N->real^N^N) y`]
          NORM_PASTECART_LE) THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      USE_THEN "lowj" (MP_TAC o SPEC `0`) THEN REWRITE_TAC[RDT_JETN_0; LE_0] THEN
      USE_THEN "dgvj" (MP_TAC o SPEC `0`) THEN REWRITE_TAC[RDT_JETN_0] THEN
      SUBGOAL_THEN `NN * pde_jetn (SUC 0) ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                           (G:real^N->real^N^N)) y <= NN * MG`
      MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `pde_jetn (m DIV 2 + 2) ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                            (G:real^N->real^N^N)) y` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PDE_JETN_MONO THEN ARITH_TAC;
        REAL_ARITH_TAC];
      USE_THEN "kf" (MP_TAC o SPEC `m DIV 2 + 1`) THEN
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN
      MATCH_MP_TAC(REAL_ARITH `a <= a' /\ b <= b' /\ c <= c' /\ d <= d' ==>
                               x <= a + b + c + d ==> x <= a' + b' + c' + d'`) THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `pde_jetn (m DIV 2 + 2) ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                            (G:real^N->real^N^N)) y` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PDE_JETN_MONO THEN ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `NN * pde_jetn (SUC(m DIV 2 + 1))
                              ((vectorize:real^N^N->real^(N,N)finite_prod) o
                               (G:real^N->real^N^N)) y` THEN
        ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[ARITH_RULE `SUC(m DIV 2 + 1) = m DIV 2 + 2`] THEN ASM_REWRITE_TAC[];
        USE_THEN "lowj" (MP_TAC o SPEC `m DIV 2 + 1`) THEN ANTS_TAC THENL
         [MP_TAC(SPECL [`m:num`; `2`] DIVISION) THEN ARITH_TAC; SIMP_TAC[]];
        USE_THEN "lowj" (MP_TAC o SPEC `m DIV 2 + 1`) THEN ANTS_TAC THENL
         [MP_TAC(SPECL [`m:num`; `2`] DIVISION) THEN ARITH_TAC; SIMP_TAC[]]];
      SUBGOAL_THEN `pde_jetn m (rdt_dgv (G:real^N->real^N^N)) y <= NN * J1` ASSUME_TAC THENL
       [USE_THEN "dgvj" (MP_TAC o SPEC `m:num`) THEN REWRITE_TAC[ADD1] THEN
        EXPAND_TAC "J1" THEN SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `pde_jetn m (rdt_gv (H:real^N->real^N^N)) y <= Cg /\
                    pde_jetn m (rdt_gdv H) y <= Cd` STRIP_ASSUME_TAC THENL
       [USE_THEN "lowj" MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `pde_jetn m ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                (G:real^N->real^N^N)) y <= J1` ASSUME_TAC THENL
       [EXPAND_TAC "J1" THEN MATCH_MP_TAC PDE_JETN_MONO THEN ARITH_TAC; ALL_TAC] THEN
      USE_THEN "kf" (MP_TAC o CONJUNCT2 o SPEC `m:num`) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `CP * (&1 + pde_jetn m (rdt_kf (G:real^N->real^N^N) H) y)` THEN CONJ_TAC THENL
   [USE_THEN "cp" MATCH_MP_TAC THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 + (&1 + NN) * J1 + Cg + Cd` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (Cg + Cd) * J1` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

(* The symbol identity for the witness pde_rdt_sym H of PDE_LRDT_SYMBOL.     *)

let RDT_SYM_ID = prove
 (`!U (H:real^N->real^N^N) G y.
     metric_field U H /\ metric_field U G /\ y IN U
     ==> pde_lrdt H G y =
         pde_ltrhess G H G y +
         (matrify:real^(N,N)finite_prod->real^N^N)
         (pde_rdt_sym H
           (pastecart y
             (pastecart ((vectorize:real^N^N->real^(N,N)finite_prod) (G y))
               ((vectorize:real^N^(N,N)finite_prod->real^((N,N)finite_prod,N)finite_prod)
                (matrix(frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o G)
                                           (at y)))))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!v. matrix(frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                   (G:real^N->real^N^N)) (at y)) ** v =
        frechet_derivative (vectorize o G) (at y) v`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MATRIX_WORKS THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    ASM_MESON_TAC[LRG_METRIC_FIELD_DIFF];
    ALL_TAC] THEN
  REWRITE_TAC[CART_EQ] THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
  REWRITE_TAC[CART_EQ] THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN
  REWRITE_TAC[MATRIX_ADD_COMPONENT] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `x = y + z <=> x - y = z`] THEN
  REWRITE_TAC[GSYM MATRIX_SUB_COMPONENT] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `H:real^N->real^N^N`; `G:real^N->real^N^N`; `y:real^N`;
                 `a:num`; `b:num`] PDE_LRDT_ENTRY_D2FREE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[pde_rdt_sym; MATRIFY_VECTORIZE; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ASM_SIMP_TAC[LAMBDA_BETA] THEN
  REWRITE_TAC[pde_jg; pde_jgi; pde_jd1; mderiv]);;


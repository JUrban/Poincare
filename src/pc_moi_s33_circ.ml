(* ========================================================================= *)
(* pc_moi_s33_circ: orientation of PL circles and the collar adjustment,    *)
(* for Moise 33.1 Lemma 13 (used in pc_moi_s33_sorient and                  *)
(* pc_moi_s33_match).  General results:                                     *)
(*   O1  the cyclic order of rf std_triangle given by the parameter          *)
(*       moi_lsp_tau of std_triangle_loop (pc_moi_lt_sphere): every         *)
(*       homeomorphism of rf std_triangle preserves or reverses it          *)
(*       (MOI_S3CI_ORIENT), and one preserved triple decides               *)
(*       (MOI_S3CI_LOCAL);                                                  *)
(*   O2  an orientation-preserving PL self-homeomorphism of one end of a PL  *)
(*       annulus extends to a PL self-homeomorphism of the annulus that is  *)
(*       the identity on the other end (MOI_S3CI_COLLAR).                   *)
(* The statement terms below use only existing constants (CYC written out   *)
(* through moi_lsp_tau, std_triangle_loop of pc_moi_lt_sphere); the proofs  *)
(* use MOI_S5W_DICHOTOMY of pc_moi_s35_ext2t.                               *)
(* ========================================================================= *)

needs "src/pc_moi_lt_sphere.ml";;
needs "src/pc_moi_s35_ext2t.ml";;

prioritize_real();;
type_invention_error := true;;

(* In the terms, CYC a b c abbreviates the cyclic order of the parameters:  *)
(*   moi_lsp_tau a < moi_lsp_tau b /\ moi_lsp_tau b < moi_lsp_tau c \/      *)
(*   moi_lsp_tau b < moi_lsp_tau c /\ moi_lsp_tau c < moi_lsp_tau a \/      *)
(*   moi_lsp_tau c < moi_lsp_tau a /\ moi_lsp_tau a < moi_lsp_tau b         *)
(* (it is written out in full).                                             *)

let MOI_S3CI_ORIENT_TERM =
 `!q:real^2->real^2.
   q continuous_on relative_frontier std_triangle /\
   IMAGE q (relative_frontier std_triangle) = relative_frontier std_triangle /\
   (!x y. x IN relative_frontier std_triangle /\ y IN relative_frontier std_triangle /\ q x = q y ==> x = y)
   ==> (!a b c. a IN relative_frontier std_triangle /\ b IN relative_frontier std_triangle /\ c IN relative_frontier std_triangle /\
               (moi_lsp_tau a < moi_lsp_tau b /\ moi_lsp_tau b < moi_lsp_tau c \/
                moi_lsp_tau b < moi_lsp_tau c /\ moi_lsp_tau c < moi_lsp_tau a \/
                moi_lsp_tau c < moi_lsp_tau a /\ moi_lsp_tau a < moi_lsp_tau b)
               ==> (moi_lsp_tau (q a) < moi_lsp_tau (q b) /\ moi_lsp_tau (q b) < moi_lsp_tau (q c) \/
                    moi_lsp_tau (q b) < moi_lsp_tau (q c) /\ moi_lsp_tau (q c) < moi_lsp_tau (q a) \/
                    moi_lsp_tau (q c) < moi_lsp_tau (q a) /\ moi_lsp_tau (q a) < moi_lsp_tau (q b))) \/
       (!a b c. a IN relative_frontier std_triangle /\ b IN relative_frontier std_triangle /\ c IN relative_frontier std_triangle /\
               (moi_lsp_tau a < moi_lsp_tau b /\ moi_lsp_tau b < moi_lsp_tau c \/
                moi_lsp_tau b < moi_lsp_tau c /\ moi_lsp_tau c < moi_lsp_tau a \/
                moi_lsp_tau c < moi_lsp_tau a /\ moi_lsp_tau a < moi_lsp_tau b)
               ==> (moi_lsp_tau (q c) < moi_lsp_tau (q b) /\ moi_lsp_tau (q b) < moi_lsp_tau (q a) \/
                    moi_lsp_tau (q b) < moi_lsp_tau (q a) /\ moi_lsp_tau (q a) < moi_lsp_tau (q c) \/
                    moi_lsp_tau (q a) < moi_lsp_tau (q c) /\ moi_lsp_tau (q c) < moi_lsp_tau (q b)))`;;

let MOI_S3CI_LOCAL_TERM =
 `!(q:real^2->real^2) a0 b0 c0.
   q continuous_on relative_frontier std_triangle /\
   IMAGE q (relative_frontier std_triangle) = relative_frontier std_triangle /\
   (!x y. x IN relative_frontier std_triangle /\ y IN relative_frontier std_triangle /\ q x = q y ==> x = y) /\
   a0 IN relative_frontier std_triangle /\ b0 IN relative_frontier std_triangle /\ c0 IN relative_frontier std_triangle /\
   (moi_lsp_tau a0 < moi_lsp_tau b0 /\ moi_lsp_tau b0 < moi_lsp_tau c0 \/
    moi_lsp_tau b0 < moi_lsp_tau c0 /\ moi_lsp_tau c0 < moi_lsp_tau a0 \/
    moi_lsp_tau c0 < moi_lsp_tau a0 /\ moi_lsp_tau a0 < moi_lsp_tau b0) /\
   (moi_lsp_tau (q a0) < moi_lsp_tau (q b0) /\ moi_lsp_tau (q b0) < moi_lsp_tau (q c0) \/
    moi_lsp_tau (q b0) < moi_lsp_tau (q c0) /\ moi_lsp_tau (q c0) < moi_lsp_tau (q a0) \/
    moi_lsp_tau (q c0) < moi_lsp_tau (q a0) /\ moi_lsp_tau (q a0) < moi_lsp_tau (q b0))
   ==> (!a b c. a IN relative_frontier std_triangle /\ b IN relative_frontier std_triangle /\ c IN relative_frontier std_triangle /\
               (moi_lsp_tau a < moi_lsp_tau b /\ moi_lsp_tau b < moi_lsp_tau c \/
                moi_lsp_tau b < moi_lsp_tau c /\ moi_lsp_tau c < moi_lsp_tau a \/
                moi_lsp_tau c < moi_lsp_tau a /\ moi_lsp_tau a < moi_lsp_tau b)
               ==> (moi_lsp_tau (q a) < moi_lsp_tau (q b) /\ moi_lsp_tau (q b) < moi_lsp_tau (q c) \/
                    moi_lsp_tau (q b) < moi_lsp_tau (q c) /\ moi_lsp_tau (q c) < moi_lsp_tau (q a) \/
                    moi_lsp_tau (q c) < moi_lsp_tau (q a) /\ moi_lsp_tau (q a) < moi_lsp_tau (q b)))`;;

let MOI_S3CI_COLLAR_TERM =
 `!(k:real^N->bool) (j0:real^N->bool) (j1:real^N->bool)
 (p:real^2->real^N) (p':real^N->real^2) (phi:real^N->real^N) (phi':real^N->real^N).
   pl_annulus_with_ends k j0 j1 /\
   pl_homeomorphism (relative_frontier std_triangle,j0) (p,p') /\
   pl_homeomorphism (j0,j0) (phi,phi') /\
   (!a b c. a IN relative_frontier std_triangle /\ b IN relative_frontier std_triangle /\ c IN relative_frontier std_triangle /\
           (moi_lsp_tau a < moi_lsp_tau b /\ moi_lsp_tau b < moi_lsp_tau c \/
            moi_lsp_tau b < moi_lsp_tau c /\ moi_lsp_tau c < moi_lsp_tau a \/
            moi_lsp_tau c < moi_lsp_tau a /\ moi_lsp_tau a < moi_lsp_tau b)
           ==> (moi_lsp_tau ((p' o phi o p) a) < moi_lsp_tau ((p' o phi o p) b) /\ moi_lsp_tau ((p' o phi o p) b) < moi_lsp_tau ((p' o phi o p) c) \/
                moi_lsp_tau ((p' o phi o p) b) < moi_lsp_tau ((p' o phi o p) c) /\ moi_lsp_tau ((p' o phi o p) c) < moi_lsp_tau ((p' o phi o p) a) \/
                moi_lsp_tau ((p' o phi o p) c) < moi_lsp_tau ((p' o phi o p) a) /\ moi_lsp_tau ((p' o phi o p) a) < moi_lsp_tau ((p' o phi o p) b)))
   ==> ?(g:real^N->real^N) (g':real^N->real^N).
         pl_homeomorphism (k,k) (g,g') /\
         (!x. x IN j0 ==> g x = phi x) /\ (!x. x IN j1 ==> g x = x)`;;

(* ------------------------------------------------------------------------- *)
(* O1: the cyclic order of rf std_triangle (by the parameter moi_lsp_tau of *)
(* std_triangle_loop) and the dichotomy: a homeomorphism of rf std_triangle *)
(* preserves or reverses it.                                                 *)
(* ------------------------------------------------------------------------- *)

let moi_s3ci_cyc3 = new_definition
 `moi_s3ci_cyc3 (x:real) y z <=> x < y /\ y < z \/ y < z /\ z < x \/ z < x /\ x < y`;;

let moi_s3ci_cyc = new_definition
 `moi_s3ci_cyc (a:real^2) (b:real^2) (c:real^2) <=>
    moi_s3ci_cyc3 (moi_lsp_tau a) (moi_lsp_tau b) (moi_lsp_tau c)`;;

let moi_s3ci_cycpres = new_definition
 `moi_s3ci_cycpres (q:real^2->real^2) <=>
    !a b c. a IN relative_frontier std_triangle /\ b IN relative_frontier std_triangle /\
            c IN relative_frontier std_triangle /\ moi_s3ci_cyc a b c
            ==> moi_s3ci_cyc (q a) (q b) (q c)`;;

let moi_s3ci_cycrev = new_definition
 `moi_s3ci_cycrev (q:real^2->real^2) <=>
    !a b c. a IN relative_frontier std_triangle /\ b IN relative_frontier std_triangle /\
            c IN relative_frontier std_triangle /\ moi_s3ci_cyc a b c
            ==> moi_s3ci_cyc (q c) (q b) (q a)`;;

(* The shift of a parameter in [0,1) by c in [0,1), modulo 1. *)
let moi_s3ci_sh = new_definition
 `moi_s3ci_sh (c:real) (w:real) = if c <= w then w - c else w - c + &1`;;

let MOI_S3CI_SH = prove
 (`!c w. &0 <= c /\ c < &1 /\ &0 <= w /\ w < &1
         ==> &0 <= moi_s3ci_sh c w /\ moi_s3ci_sh c w < &1 /\
             (moi_s3ci_sh c w = &0 <=> w = c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s3ci_sh] THEN COND_CASES_TAC THEN
  ASM_REAL_ARITH_TAC);;

let MOI_S3CI_CYC3_SH = prove
 (`!c x y z. &0 <= c /\ c < &1 /\ &0 <= x /\ x < &1 /\ &0 <= y /\ y < &1 /\
             &0 <= z /\ z < &1
             ==> (moi_s3ci_cyc3 (moi_s3ci_sh c x) (moi_s3ci_sh c y) (moi_s3ci_sh c z) <=>
                  moi_s3ci_cyc3 x y z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_s3ci_cyc3; moi_s3ci_sh] THEN
  REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;

let MOI_S3CI_CYC3_ROT = prove
 (`!x y z. moi_s3ci_cyc3 x y z <=> moi_s3ci_cyc3 y z x`,
  REWRITE_TAC[moi_s3ci_cyc3] THEN REAL_ARITH_TAC);;

let MOI_S3CI_CYC3_NOT_BOTH = prove
 (`!x y z. ~(moi_s3ci_cyc3 x y z /\ moi_s3ci_cyc3 z y x)`,
  REWRITE_TAC[moi_s3ci_cyc3] THEN REAL_ARITH_TAC);;

let MOI_S3CI_CYC3_CASES = prove
 (`!x y z. ~(x = y) /\ ~(y = z) /\ ~(x = z)
           ==> moi_s3ci_cyc3 x y z \/ moi_s3ci_cyc3 z y x`,
  REWRITE_TAC[moi_s3ci_cyc3] THEN REAL_ARITH_TAC);;

(* A strictly increasing map of [0,1) preserves cyclic order; a map fixing 0 *)
(* and strictly decreasing on (0,1) into (0,1) reverses it.                  *)
let MOI_S3CI_CYC3_INC = prove
 (`!g x y z. (!u v. &0 <= u /\ u < &1 /\ &0 <= v /\ v < &1 /\ u < v ==> g u < g v) /\
             &0 <= x /\ x < &1 /\ &0 <= y /\ y < &1 /\ &0 <= z /\ z < &1 /\
             moi_s3ci_cyc3 x y z
             ==> moi_s3ci_cyc3 (g x) (g y) (g z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s3ci_cyc3] THEN STRIP_TAC THEN
  ASM_MESON_TAC[]);;

let MOI_S3CI_CYC3_DEC = prove
 (`!g x y z. g(&0) = &0 /\
             (!u. &0 < u /\ u < &1 ==> &0 < g u /\ g u < &1) /\
             (!u v. &0 < u /\ u < &1 /\ &0 < v /\ v < &1 /\ u < v ==> g v < g u) /\
             &0 <= x /\ x < &1 /\ &0 <= y /\ y < &1 /\ &0 <= z /\ z < &1 /\
             moi_s3ci_cyc3 x y z
             ==> moi_s3ci_cyc3 (g z) (g y) (g x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `x = &0` THEN ASM_CASES_TAC `y = &0` THEN ASM_CASES_TAC `z = &0` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `moi_s3ci_cyc3`)) (concl th))) THEN
  ASM_REWRITE_TAC[moi_s3ci_cyc3] THEN
  (REPEAT STRIP_TAC THEN TRY ASM_REAL_ARITH_TAC) THEN
  ASM_MESON_TAC[REAL_LT_TRANS; REAL_LET_TRANS; REAL_LT_IMP_LE; REAL_LE_REFL;
                REAL_ARITH `&0 <= u /\ ~(u = &0) ==> &0 < u`]);;

(* ------------------------------------------------------------------------- *)
(* The parameter moi_lsp_tau on rf std_triangle.                             *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CI_TAU_FACTS = prove
 (`(!x. x IN relative_frontier std_triangle
        ==> &0 <= moi_lsp_tau x /\ moi_lsp_tau x < &1 /\
            std_triangle_loop(lift(moi_lsp_tau x)) = x) /\
   (!s. &0 <= s /\ s < &1
        ==> std_triangle_loop(lift s) IN relative_frontier std_triangle /\
            moi_lsp_tau(std_triangle_loop(lift s)) = s)`,
  CONJ_TAC THENL [REWRITE_TAC[MOI_LSP_TAU_RF]; ALL_TAC] THEN
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[GSYM(CONJUNCT2(CONJUNCT2(CONJUNCT2 MOI_LTD_STD_TRIANGLE_LOOP)));
                path_image] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
    ASM_REAL_ARITH_TAC;
    MP_TAC(SPEC `lift s` MOI_LSP_TAU_STL) THEN
    REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

let MOI_S3CI_TAU_INJ = prove
 (`!x y. x IN relative_frontier std_triangle /\ y IN relative_frontier std_triangle /\
         moi_lsp_tau x = moi_lsp_tau y ==> x = y`,
  MESON_TAC[MOI_S3CI_TAU_FACTS]);;

let MOI_S3CI_TAU_ZERO = prove
 (`vec 0 IN relative_frontier std_triangle /\ moi_lsp_tau(vec 0:real^2) = &0 /\
   (!x. x IN relative_frontier std_triangle /\ moi_lsp_tau x = &0 ==> x = vec 0)`,
  SUBGOAL_THEN `moi_lsp_tau(vec 0:real^2) = &0` ASSUME_TAC THENL
   [REWRITE_TAC[moi_lsp_tau; VEC_COMPONENT] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[CONJUNCT1(CONJUNCT2(CONJUNCT2 MOI_LTD_FRONTIER_SUBSET_TRIANGLE))] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S3CI_TAU_INJ THEN
  ASM_REWRITE_TAC[CONJUNCT1(CONJUNCT2(CONJUNCT2 MOI_LTD_FRONTIER_SUBSET_TRIANGLE))]);;

let MOI_S3CI_AFF_CONT = prove
 (`!a b c. (\x:real^2. lift(a * x$1 + b * x$2 + c)) continuous_on (:real^2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN
  MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_CMUL;
    MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_CMUL; REWRITE_TAC[CONTINUOUS_ON_CONST]]] THEN
  SIMP_TAC[CONTINUOUS_ON_LIFT_COMPONENT; DIMINDEX_2; ARITH]);;

let MOI_S3CI_EDGES_TAC =
  REPEAT(FIRST_X_ASSUM(fun th -> FIRST (map (fun e g -> STRIP_ASSUME_TAC (MATCH_MP e th) g)
    [CONJUNCT1 MOI_LSP_STD_EDGES; CONJUNCT1(CONJUNCT2 MOI_LSP_STD_EDGES);
     CONJUNCT2(CONJUNCT2 MOI_LSP_STD_EDGES)])));;

let MOI_S3CI_STD_SEGS = prove
 (`segment[vec 0,basis 1] INTER segment[basis 1,basis 2] = {basis 1:real^2} /\
   segment[basis 1,basis 2] INTER segment[basis 2,vec 0] = {basis 2:real^2} /\
   segment[vec 0,basis 1] INTER segment[basis 2,vec 0] = {vec 0:real^2} /\
   ~(vec 0 IN segment[basis 1:real^2,basis 2]) /\
   ~(basis 1:real^2 = vec 0) /\ ~(basis 2:real^2 = vec 0)`,
  SIMP_TAC[BASIS_NONZERO; DIMINDEX_2; ARITH] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_SING] THEN REPEAT CONJ_TAC THEN
  TRY(X_GEN_TAC `x:real^2` THEN EQ_TAC THENL
       [STRIP_TAC THEN MOI_S3CI_EDGES_TAC THEN
        ASM_REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; MOI_LSP_BASIS2; VEC_COMPONENT] THEN
        ASM_REAL_ARITH_TAC;
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ENDS_IN_SEGMENT]]) THEN
  DISCH_TAC THEN MOI_S3CI_EDGES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VEC_COMPONENT]) THEN ASM_REAL_ARITH_TAC);;

let MOI_S3CI_TAU_CONT = prove
 (`(lift o moi_lsp_tau) continuous_on (relative_frontier std_triangle DIFF {vec 0})`,
  REWRITE_TAC[MOI_LTD_STD_TRIANGLE_FRONTIER] THEN
  MP_TAC MOI_S3CI_STD_SEGS THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`vec 0:real^2`; `basis 1:real^2`] ENDS_IN_SEGMENT) THEN
  MP_TAC(ISPECL [`basis 1:real^2`; `basis 2:real^2`] ENDS_IN_SEGMENT) THEN
  MP_TAC(ISPECL [`basis 2:real^2`; `vec 0:real^2`] ENDS_IN_SEGMENT) THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(segment[vec 0,basis 1] UNION segment[basis 1,basis 2] UNION segment[basis 2,vec 0])
    DIFF {vec 0:real^2} =
    (segment[vec 0,basis 1] DIFF {vec 0}) UNION
    (segment[basis 1,basis 2] UNION (segment[basis 2,vec 0] DIFF {vec 0}))`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(lift o moi_lsp_tau) continuous_on (segment[vec 0,basis 1] DIFF {vec 0:real^2}) /\
    (lift o moi_lsp_tau) continuous_on segment[basis 1,basis 2:real^2] /\
    (lift o moi_lsp_tau) continuous_on (segment[basis 2,vec 0] DIFF {vec 0:real^2})`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THENL
     [EXISTS_TAC `\x:real^2. lift(&1 / &2 * x$1 + &0 * x$2 + &0)`;
      EXISTS_TAC `\x:real^2. lift(&0 * x$1 + &1 / &4 * x$2 + &1 / &2)`;
      EXISTS_TAC `\x:real^2. lift(&0 * x$1 + -- (&1 / &4) * x$2 + &1)`] THEN
    (CONJ_TAC THENL
      [X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_DIFF; IN_SING; o_THM] THEN STRIP_TAC THEN
       MOI_S3CI_EDGES_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[moi_lsp_tau] THEN
       REPEAT COND_CASES_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
       UNDISCH_TAC `~(x:real^2 = vec 0)` THEN
       ASM_REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VEC_COMPONENT] THEN
       ASM_REAL_ARITH_TAC;
       MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
       REWRITE_TAC[SUBSET_UNIV; MOI_S3CI_AFF_CONT]]);
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_UNION_LOCAL THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[CLOSED_IN_CLOSED] THEN EXISTS_TAC `segment[vec 0,basis 1:real^2]` THEN
    REWRITE_TAC[CLOSED_SEGMENT] THEN ASM SET_TAC[];
    REWRITE_TAC[CLOSED_IN_CLOSED] THEN
    EXISTS_TAC `segment[basis 1,basis 2] UNION segment[basis 2,vec 0:real^2]` THEN
    SIMP_TAC[CLOSED_UNION; CLOSED_SEGMENT] THEN ASM SET_TAC[];
    MATCH_MP_TAC CONTINUOUS_ON_UNION_LOCAL THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN REWRITE_TAC[CLOSED_IN_CLOSED] THENL
     [EXISTS_TAC `segment[basis 1,basis 2:real^2]`;
      EXISTS_TAC `segment[basis 2,vec 0:real^2]`] THEN
    REWRITE_TAC[CLOSED_SEGMENT] THEN ASM SET_TAC[]]);;

(* Adding c modulo 1, the inverse of the shift. *)
let moi_s3ci_ad = new_definition
 `moi_s3ci_ad (c:real) (s:real) = if c + s < &1 then c + s else c + s - &1`;;

let MOI_S3CI_AD_SH = prove
 (`!c w. &0 <= c /\ c < &1 /\ &0 <= w /\ w < &1
         ==> moi_s3ci_ad c (moi_s3ci_sh c w) = w /\ moi_s3ci_sh c (moi_s3ci_ad c w) = w /\
             &0 <= moi_s3ci_ad c w /\ moi_s3ci_ad c w < &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s3ci_ad; moi_s3ci_sh] THEN STRIP_TAC THEN
  REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;

(* The loop started at the point of parameter c. *)
let MOI_S3CI_SHIFT = prove
 (`!c. &0 <= c /\ c < &1
       ==> path (shiftpath (lift c) std_triangle_loop) /\
           (!s. &0 <= s /\ s < &1
                ==> shiftpath (lift c) std_triangle_loop (lift s) IN
                    relative_frontier std_triangle /\
                    moi_lsp_tau(shiftpath (lift c) std_triangle_loop (lift s)) =
                    moi_s3ci_ad c s) /\
           (!w. &0 <= w /\ w < &1
                ==> shiftpath (lift c) std_triangle_loop (lift(moi_s3ci_sh c w)) =
                    std_triangle_loop(lift w))`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!s. &0 <= s /\ s < &1
        ==> shiftpath (lift c) std_triangle_loop (lift s) =
            std_triangle_loop(lift(moi_s3ci_ad c s))`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    REWRITE_TAC[shiftpath; moi_s3ci_ad; DROP_ADD; LIFT_DROP] THEN
    ASM_CASES_TAC `c + s < &1` THEN ASM_REWRITE_TAC[] THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_LE; GSYM LIFT_ADD]; ALL_TAC] THEN
    ASM_CASES_TAC `c + s = &1` THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL; GSYM LIFT_ADD; LIFT_NUM] THEN
      SUBGOAL_THEN `c + s - &1 = &0` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[LIFT_NUM] THEN
      REWRITE_TAC[REWRITE_RULE[pathfinish; pathstart] (CONJ
        (CONJUNCT1(CONJUNCT2(CONJUNCT2 MOI_LTD_STD_TRIANGLE_LOOP)))
        (CONJUNCT1(CONJUNCT2 MOI_LTD_STD_TRIANGLE_LOOP)))];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(c + s <= &1)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM DROP_EQ; DROP_ADD; DROP_SUB; LIFT_DROP; DROP_VEC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PATH_SHIFTPATH THEN
    REWRITE_TAC[MOI_LTD_STD_TRIANGLE_LOOP; IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC(CONJUNCT2 MOI_S3CI_TAU_FACTS) THEN ASM_MESON_TAC[MOI_S3CI_AD_SH];
    X_GEN_TAC `w:real` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`c:real`; `w:real`] MOI_S3CI_SH) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[MOI_S3CI_AD_SH]]);;

(* In the proof of MOI_S3CI_DICHOT: the facts G1 at the three points x, y, *)
(* w and the cyclic order of their shifted parameters.                      *)
let MOI_S3CI_G_TAC =
  USE_THEN "G1" (fun th -> MAP_EVERY (fun t -> STRIP_ASSUME_TAC(MP (SPEC t th)
    (ASSUME (mk_comb(mk_comb(`(IN):real^2->(real^2->bool)->bool`,t),
                     `relative_frontier std_triangle`)))))
    [`x:real^2`; `y:real^2`; `w:real^2`]) THEN
  SUBGOAL_THEN `moi_s3ci_cyc3 (moi_s3ci_sh c (moi_lsp_tau (x:real^2)))
                  (moi_s3ci_sh c (moi_lsp_tau (y:real^2))) (moi_s3ci_sh c (moi_lsp_tau (w:real^2)))`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`c:real`; `moi_lsp_tau(x:real^2)`; `moi_lsp_tau(y:real^2)`;
                  `moi_lsp_tau(w:real^2)`] MOI_S3CI_CYC3_SH) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC];;

(* O1 main: a homeomorphism of rf std_triangle preserves or reverses the     *)
(* cyclic order.                                                             *)
let MOI_S3CI_DICHOT = prove
 (`!q:real^2->real^2.
     q continuous_on relative_frontier std_triangle /\
     IMAGE q (relative_frontier std_triangle) = relative_frontier std_triangle /\
     (!x y. x IN relative_frontier std_triangle /\ y IN relative_frontier std_triangle /\
            q x = q y ==> x = y)
     ==> moi_s3ci_cycpres q \/ moi_s3ci_cycrev q`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?p0:real^2. p0 IN relative_frontier std_triangle /\
                            (q:real^2->real^2) p0 = vec 0`
  STRIP_ASSUME_TAC THENL
   [MP_TAC MOI_S3CI_TAU_ZERO THEN ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `c = moi_lsp_tau(p0:real^2)` THEN
  SUBGOAL_THEN `&0 <= c /\ c < &1` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S3CI_TAU_FACTS]; ALL_TAC] THEN
  MP_TAC(SPEC `c:real` MOI_S3CI_SHIFT) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `z = shiftpath (lift c) std_triangle_loop` THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s. &0 < s /\ s < &1 ==> ~((q:real^2->real^2)(z(lift s)) = vec 0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^1->real^2)(lift s) = p0` MP_TAC THENL
     [FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
        can (find_term ((=) `q:real^2->real^2`)) (concl th) then MATCH_MP_TAC th
        else NO_TAC) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      DISCH_TAC THEN
      MP_TAC(SPECL [`c:real`; `s:real`] MOI_S3CI_AD_SH) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `moi_s3ci_ad`)) (concl th))) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      REWRITE_TAC[moi_s3ci_ad; moi_s3ci_sh] THEN
      REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^1. x IN interval(vec 0,vec 1)
      ==> (z:real^1->real^2) x IN relative_frontier std_triangle /\
          moi_lsp_tau (z x) = moi_s3ci_ad c (drop x) /\
          (q:real^2->real^2) (z x) IN relative_frontier std_triangle /\
          ~(q (z x) = vec 0)`
  (LABEL_TAC "zx") THENL
   [X_GEN_TAC `x:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= drop(x:real^1)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o REWRITE_RULE[LIFT_DROP] o SPEC `drop(x:real^1)` o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `moi_s3ci_ad`)) (concl th))) THEN
    FIRST_ASSUM(MP_TAC o REWRITE_RULE[LIFT_DROP] o SPEC `drop(x:real^1)` o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `vec 0:real^2`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (q:real^2->real^2) (relative_frontier std_triangle) =
                 relative_frontier std_triangle` THEN
    UNDISCH_TAC `(z:real^1->real^2) x IN relative_frontier std_triangle` THEN SET_TAC[];
    ALL_TAC] THEN
  (* the parameter of the image, measured on the open arc *)
  SUBGOAL_THEN
   `(lift o moi_lsp_tau o (q:real^2->real^2) o (z:real^1->real^2)) continuous_on
    interval(vec 0,vec 1)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(lift o moi_lsp_tau o (q:real^2->real^2) o (z:real^1->real^2)) =
                  (lift o moi_lsp_tau) o (q o z)` SUBST1_TAC THENL
     [REWRITE_TAC[o_ASSOC]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
        REWRITE_TAC[INTERVAL_OPEN_SUBSET_CLOSED] THEN
        ASM_MESON_TAC[path];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `relative_frontier std_triangle:real^2->bool` THEN
        ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[]];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `relative_frontier std_triangle DIFF {vec 0:real^2}` THEN
      REWRITE_TAC[MOI_S3CI_TAU_CONT] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM; IN_DIFF; IN_SING] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  (* it is injective, hence strictly monotone *)
  SUBGOAL_THEN
   `(!x y. x IN interval(vec 0,vec 1) /\ y IN interval(vec 0,vec 1) /\ drop x < drop y
           ==> drop((lift o moi_lsp_tau o (q:real^2->real^2) o (z:real^1->real^2)) x) <
               drop((lift o moi_lsp_tau o q o z) y)) \/
    (!x y. x IN interval(vec 0,vec 1) /\ y IN interval(vec 0,vec 1) /\ drop x < drop y
           ==> drop((lift o moi_lsp_tau o q o z) y) < drop((lift o moi_lsp_tau o q o z) x))`
  MP_TAC THENL
   [MP_TAC(ISPECL [`lift o moi_lsp_tau o (q:real^2->real^2) o (z:real^1->real^2)`;
                   `interval(vec 0:real^1,vec 1)`] CONTINUOUS_INJECTIVE_IFF_MONOTONIC) THEN
    ASM_REWRITE_TAC[IS_INTERVAL_INTERVAL] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^1`] THEN
    REWRITE_TAC[o_THM; LIFT_EQ] THEN STRIP_TAC THEN
    USE_THEN "zx" (fun th -> STRIP_ASSUME_TAC (MP (SPEC `x:real^1` th)
      (ASSUME `(x:real^1) IN interval(vec 0,vec 1)`))) THEN
    USE_THEN "zx" (fun th -> STRIP_ASSUME_TAC (MP (SPEC `y:real^1` th)
      (ASSUME `(y:real^1) IN interval(vec 0,vec 1)`))) THEN
    SUBGOAL_THEN `(q:real^2->real^2) ((z:real^1->real^2) x) = q (z y)` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_S3CI_TAU_INJ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^1->real^2) x = z y` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `q:real^2->real^2`)) (concl th) &&
        not (can (find_term ((=) `vec 0:real^2`)) (concl th)) &&
        not (can (find_term ((=) `z:real^1->real^2`)) (concl th)))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `moi_s3ci_ad c (drop(x:real^1)) = moi_s3ci_ad c (drop(y:real^1))` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(x:real^1) IN interval(vec 0,vec 1)` THEN
    UNDISCH_TAC `(y:real^1) IN interval(vec 0,vec 1)` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; GSYM DROP_EQ] THEN REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`c:real`; `drop(x:real^1)`] MOI_S3CI_AD_SH) THEN
    MP_TAC(SPECL [`c:real`; `drop(y:real^1)`] MOI_S3CI_AD_SH) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  (* G u = moi_lsp_tau(q(z(lift u))) on [0,1) represents q in the parameter *)
  SUBGOAL_THEN
   `!x. x IN relative_frontier std_triangle
        ==> &0 <= moi_lsp_tau x /\ moi_lsp_tau x < &1 /\
            &0 <= moi_s3ci_sh c (moi_lsp_tau x) /\ moi_s3ci_sh c (moi_lsp_tau x) < &1 /\
            moi_lsp_tau ((q:real^2->real^2) x) =
            moi_lsp_tau (q ((z:real^1->real^2) (lift (moi_s3ci_sh c (moi_lsp_tau x)))))`
  (LABEL_TAC "G1") THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    MP_TAC(SPEC `x:real^2` (CONJUNCT1 MOI_S3CI_TAU_FACTS)) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    MP_TAC(SPECL [`c:real`; `moi_lsp_tau(x:real^2)`] MOI_S3CI_SH) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `moi_s3ci_sh`)) (concl th)
      then MP_TAC(MP (SPEC `moi_lsp_tau(x:real^2)` th)
             (CONJ (ASSUME `&0 <= moi_lsp_tau(x:real^2)`) (ASSUME `moi_lsp_tau(x:real^2) < &1`)))
      else NO_TAC) THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. &0 < u /\ u < &1
        ==> &0 < moi_lsp_tau((q:real^2->real^2)((z:real^1->real^2)(lift u))) /\
            moi_lsp_tau(q(z(lift u))) < &1`
  (LABEL_TAC "G2") THENL
   [X_GEN_TAC `u:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `lift u IN interval(vec 0,vec 1)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC]; ALL_TAC] THEN
    USE_THEN "zx" (fun th -> STRIP_ASSUME_TAC (MP (SPEC `lift u` th)
      (ASSUME `lift u IN interval(vec 0,vec 1)`))) THEN
    MP_TAC(MP (SPEC `(q:real^2->real^2)((z:real^1->real^2)(lift u))` (CONJUNCT1 MOI_S3CI_TAU_FACTS))
      (ASSUME `(q:real^2->real^2)((z:real^1->real^2)(lift u)) IN relative_frontier std_triangle`)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= t /\ ~(t = &0) ==> &0 < t`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    UNDISCH_TAC `~((q:real^2->real^2)((z:real^1->real^2)(lift u)) = vec 0)` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC(CONJUNCT2(CONJUNCT2 MOI_S3CI_TAU_ZERO)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_lsp_tau((q:real^2->real^2)((z:real^1->real^2)(lift(&0)))) = &0`
  (LABEL_TAC "G0") THENL
   [MP_TAC(SPECL [`c:real`; `c:real`] MOI_S3CI_SH) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `moi_s3ci_sh`)) (concl th)
      then MP_TAC(MP (SPEC `c:real` th) (CONJ (ASSUME `&0 <= c`) (ASSUME `c < &1`)))
      else NO_TAC) THEN
    FIRST_ASSUM(fun th -> if concl th = `moi_s3ci_sh c c = &0` then REWRITE_TAC[th] else NO_TAC) THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC(MP (SPEC `p0:real^2` (CONJUNCT1 MOI_S3CI_TAU_FACTS))
      (ASSUME `(p0:real^2) IN relative_frontier std_triangle`)) THEN
    FIRST_ASSUM(fun th -> if concl th = `moi_lsp_tau (p0:real^2) = c` then REWRITE_TAC[th] else NO_TAC) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[MOI_S3CI_TAU_ZERO];
    ALL_TAC] THEN
  (* increasing: q preserves the cyclic order; decreasing: q reverses it *)
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [DISJ1_TAC THEN REWRITE_TAC[moi_s3ci_cycpres; moi_s3ci_cyc] THEN
    MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`; `w:real^2`] THEN STRIP_TAC THEN
    MOI_S3CI_G_TAC THEN
    MP_TAC(BETA_RULE(ISPECL [`\u. moi_lsp_tau((q:real^2->real^2)((z:real^1->real^2)(lift u)))`;
      `moi_s3ci_sh c (moi_lsp_tau (x:real^2))`; `moi_s3ci_sh c (moi_lsp_tau (y:real^2))`;
      `moi_s3ci_sh c (moi_lsp_tau (w:real^2))`] MOI_S3CI_CYC3_INC)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`u:real`; `v:real`] THEN STRIP_TAC THEN
      ASM_CASES_TAC `u = &0` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN USE_THEN "G0" SUBST1_TAC THEN
        USE_THEN "G2" (MP_TAC o SPEC `v:real`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        FIRST_ASSUM(MP_TAC o SPECL [`lift u`; `lift v`] o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `interval(vec 0:real^1,vec 1)`)) (concl th) &&
          not (can (find_term ((=) `relative_frontier std_triangle`)) (concl th)))) THEN
        REWRITE_TAC[o_THM; LIFT_DROP; IN_INTERVAL_1; DROP_VEC] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      ASM_REWRITE_TAC[]];
    DISJ2_TAC THEN REWRITE_TAC[moi_s3ci_cycrev; moi_s3ci_cyc] THEN
    MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`; `w:real^2`] THEN STRIP_TAC THEN
    MOI_S3CI_G_TAC THEN
    MP_TAC(BETA_RULE(ISPECL [`\u. moi_lsp_tau((q:real^2->real^2)((z:real^1->real^2)(lift u)))`;
      `moi_s3ci_sh c (moi_lsp_tau (x:real^2))`; `moi_s3ci_sh c (moi_lsp_tau (y:real^2))`;
      `moi_s3ci_sh c (moi_lsp_tau (w:real^2))`] MOI_S3CI_CYC3_DEC)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN TRY(CONJ_TAC THENL [USE_THEN "G2" ACCEPT_TAC; ALL_TAC]) THEN
      MAP_EVERY X_GEN_TAC [`u:real`; `v:real`] THEN STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o SPECL [`lift u`; `lift v`] o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `interval(vec 0:real^1,vec 1)`)) (concl th) &&
        not (can (find_term ((=) `relative_frontier std_triangle`)) (concl th)))) THEN
      REWRITE_TAC[o_THM; LIFT_DROP; IN_INTERVAL_1; DROP_VEC] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* O1 algebra: a cyclic triple, exclusivity, composition and inverses, and   *)
(* the headline forms MOI_S3CI_ORIENT and MOI_S3CI_LOCAL of the dichotomy.   *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CI_TRIPLE = prove
 (`vec 0 IN relative_frontier std_triangle /\
   basis 1 IN relative_frontier std_triangle /\
   basis 2 IN relative_frontier std_triangle /\
   moi_s3ci_cyc (vec 0) (basis 1:real^2) (basis 2)`,
  REWRITE_TAC[MOI_LTD_STD_TRIANGLE_FRONTIER; IN_UNION; ENDS_IN_SEGMENT] THEN
  REWRITE_TAC[moi_s3ci_cyc; moi_s3ci_cyc3; moi_lsp_tau] THEN
  SIMP_TAC[VEC_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let MOI_S3CI_EXCL = prove
 (`!q:real^2->real^2. ~(moi_s3ci_cycpres q /\ moi_s3ci_cycrev q)`,
  GEN_TAC THEN REWRITE_TAC[moi_s3ci_cycpres; moi_s3ci_cycrev] THEN
  DISCH_THEN(CONJUNCTS_THEN (MP_TAC o SPECL [`vec 0:real^2`; `basis 1:real^2`;
                                              `basis 2:real^2`])) THEN
  REWRITE_TAC[MOI_S3CI_TRIPLE; moi_s3ci_cyc] THEN
  MESON_TAC[MOI_S3CI_CYC3_NOT_BOTH]);;

let MOI_S3CI_CYC_DISTINCT = prove
 (`!a b c:real^2.
     moi_s3ci_cyc a b c
     ==> ~(moi_lsp_tau a = moi_lsp_tau b) /\ ~(moi_lsp_tau b = moi_lsp_tau c) /\
         ~(moi_lsp_tau a = moi_lsp_tau c) /\ ~(a = b) /\ ~(b = c) /\ ~(a = c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s3ci_cyc; moi_s3ci_cyc3] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THEN
  TRY(DISCH_THEN SUBST_ALL_TAC) THEN ASM_REAL_ARITH_TAC);;

let MOI_S3CI_COMPOSE = prove
 (`!q1 q2:real^2->real^2.
     (!x. x IN relative_frontier std_triangle ==> q1 x IN relative_frontier std_triangle)
     ==> (moi_s3ci_cycpres q1 /\ moi_s3ci_cycpres q2 ==> moi_s3ci_cycpres (q2 o q1)) /\
         (moi_s3ci_cycpres q1 /\ moi_s3ci_cycrev q2 ==> moi_s3ci_cycrev (q2 o q1)) /\
         (moi_s3ci_cycrev q1 /\ moi_s3ci_cycpres q2 ==> moi_s3ci_cycrev (q2 o q1)) /\
         (moi_s3ci_cycrev q1 /\ moi_s3ci_cycrev q2 ==> moi_s3ci_cycpres (q2 o q1))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[moi_s3ci_cycpres; moi_s3ci_cycrev; o_THM] THEN
  REPEAT CONJ_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:real^2`; `b:real^2`; `c:real^2`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]);;

let MOI_S3CI_INVERSE = prove
 (`!q q':real^2->real^2.
     (!x. x IN relative_frontier std_triangle
          ==> q x IN relative_frontier std_triangle /\
              q' x IN relative_frontier std_triangle /\ q (q' x) = x /\ q' (q x) = x)
     ==> (moi_s3ci_cycpres q ==> moi_s3ci_cycpres q') /\
         (moi_s3ci_cycrev q ==> moi_s3ci_cycrev q')`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!a b c. a IN relative_frontier std_triangle /\ b IN relative_frontier std_triangle /\
            c IN relative_frontier std_triangle /\ moi_s3ci_cyc a b c
            ==> (moi_s3ci_cyc ((q':real^2->real^2) a) (q' b) (q' c) \/
                 moi_s3ci_cyc (q' c) (q' b) (q' a)) /\
                (q':real^2->real^2) a IN relative_frontier std_triangle /\
                q' b IN relative_frontier std_triangle /\
                q' c IN relative_frontier std_triangle /\
                (q:real^2->real^2) (q' a) = a /\ q (q' b) = b /\ q (q' c) = c`
  (LABEL_TAC "cases") THENL
   [MAP_EVERY X_GEN_TAC [`a:real^2`; `b:real^2`; `c:real^2`] THEN STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3CI_CYC_DISTINCT) THEN
    SUBGOAL_THEN
     `(q':real^2->real^2) a IN relative_frontier std_triangle /\
      q' b IN relative_frontier std_triangle /\ q' c IN relative_frontier std_triangle /\
      (q:real^2->real^2) (q' a) = a /\ q (q' b) = b /\ q (q' c) = c`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[moi_s3ci_cyc] THEN MATCH_MP_TAC MOI_S3CI_CYC3_CASES THEN
    REPEAT CONJ_TAC THEN DISCH_TAC THENL
     [UNDISCH_TAC `~(a:real^2 = b)`; UNDISCH_TAC `~(b:real^2 = c)`;
      UNDISCH_TAC `~(a:real^2 = c)`] THEN
    REWRITE_TAC[] THEN ASM_MESON_TAC[MOI_S3CI_TAU_INJ];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s3ci_cycpres; moi_s3ci_cycrev] THEN CONJ_TAC THEN
  (DISCH_THEN(LABEL_TAC "q") THEN
   MAP_EVERY X_GEN_TAC [`a:real^2`; `b:real^2`; `c:real^2`] THEN STRIP_TAC THEN
   USE_THEN "cases" (MP_TAC o SPECL [`a:real^2`; `b:real^2`; `c:real^2`]) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN(CONJUNCTS_THEN2 DISJ_CASES_TAC STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
   FIRST_ASSUM(fun th ->
     match strip_comb(concl th) with
       (h,[x;y;z]) when h = `moi_s3ci_cyc` && is_comb x &&
                        rator x = `q':real^2->real^2` ->
         USE_THEN "q" (MP_TAC o SPECL [x;y;z])
     | _ -> NO_TAC) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
   UNDISCH_TAC `moi_s3ci_cyc a b (c:real^2)` THEN REWRITE_TAC[moi_s3ci_cyc] THEN
   MESON_TAC[MOI_S3CI_CYC3_NOT_BOTH]));;

let MOI_S3CI_LOCAL_DEF = prove
 (`!q:real^2->real^2 a0 b0 c0.
     q continuous_on relative_frontier std_triangle /\
     IMAGE q (relative_frontier std_triangle) = relative_frontier std_triangle /\
     (!x y. x IN relative_frontier std_triangle /\ y IN relative_frontier std_triangle /\
            q x = q y ==> x = y) /\
     a0 IN relative_frontier std_triangle /\ b0 IN relative_frontier std_triangle /\
     c0 IN relative_frontier std_triangle /\
     moi_s3ci_cyc a0 b0 c0 /\ moi_s3ci_cyc (q a0) (q b0) (q c0)
     ==> moi_s3ci_cycpres q`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `q:real^2->real^2` MOI_S3CI_DICHOT) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a0:real^2`; `b0:real^2`; `c0:real^2`] o
    REWRITE_RULE[moi_s3ci_cycrev] o check (fun th ->
      can (find_term ((=) `moi_s3ci_cycrev`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `moi_s3ci_cyc ((q:real^2->real^2) a0) (q b0) (q c0)` THEN
  REWRITE_TAC[moi_s3ci_cyc] THEN MESON_TAC[MOI_S3CI_CYC3_NOT_BOTH]);;

let MOI_S3CI_ORIENT = prove
 (MOI_S3CI_ORIENT_TERM,
  MP_TAC MOI_S3CI_DICHOT THEN
  REWRITE_TAC[moi_s3ci_cycpres; moi_s3ci_cycrev; moi_s3ci_cyc; moi_s3ci_cyc3]);;

let MOI_S3CI_LOCAL = prove
 (MOI_S3CI_LOCAL_TERM,
  MP_TAC MOI_S3CI_LOCAL_DEF THEN
  REWRITE_TAC[moi_s3ci_cycpres; moi_s3ci_cyc; moi_s3ci_cyc3]);;

(* ------------------------------------------------------------------------- *)
(* Orientation and loops: a homeomorphism of rf std_triangle that reverses   *)
(* the cyclic order carries std_triangle_loop to a loop homotopic to its     *)
(* reverse.  The image loop is split at its midpoint into two paths, each    *)
(* inside an arc of the triangle (simply connected), and compared with the  *)
(* two pieces of the reversed loop.                                          *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CI_STL_ENDS = prove
 (`std_triangle_loop(vec 0) = vec 0 /\ std_triangle_loop(vec 1) = vec 0`,
  MP_TAC MOI_LTD_STD_TRIANGLE_LOOP THEN REWRITE_TAC[pathstart; pathfinish] THEN
  SIMP_TAC[]);;

let MOI_S3CI_STL_INJ = prove
 (`!s t. &0 <= s /\ s <= &1 /\ &0 <= t /\ t <= &1 /\
         std_triangle_loop(lift s) = std_triangle_loop(lift t)
         ==> s = t \/ (s = &0 /\ t = &1) \/ (s = &1 /\ t = &0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!r. &0 <= r /\ r < &1
                    ==> moi_lsp_tau(std_triangle_loop(lift r)) = r` ASSUME_TAC THENL
   [MESON_TAC[MOI_S3CI_TAU_FACTS]; ALL_TAC] THEN
  ASM_CASES_TAC `s = &1` THEN ASM_CASES_TAC `t = &1` THEN ASM_REWRITE_TAC[] THENL
   [UNDISCH_TAC `std_triangle_loop(lift s) = std_triangle_loop(lift t)` THEN
    ASM_REWRITE_TAC[LIFT_NUM; MOI_S3CI_STL_ENDS] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[SYM th]) THEN
    REWRITE_TAC[MOI_S3CI_TAU_ZERO] THEN REAL_ARITH_TAC;
    UNDISCH_TAC `std_triangle_loop(lift s) = std_triangle_loop(lift t)` THEN
    ASM_REWRITE_TAC[LIFT_NUM; MOI_S3CI_STL_ENDS] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[MOI_S3CI_TAU_ZERO] THEN REAL_ARITH_TAC;
    FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `s:real` th) THEN MP_TAC(SPEC `t:real` th)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
    ASM_MESON_TAC[]]);;

let MOI_S3CI_STL_ARCS = prove
 (`!a. &0 < a /\ a < &1
       ==> simply_connected (IMAGE std_triangle_loop (interval[vec 0,lift a])) /\
           simply_connected (IMAGE std_triangle_loop (interval[lift a,vec 1])) /\
           IMAGE std_triangle_loop (interval[vec 0,lift a]) SUBSET
           relative_frontier std_triangle /\
           IMAGE std_triangle_loop (interval[lift a,vec 1]) SUBSET
           relative_frontier std_triangle`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `interval[vec 0,lift a] SUBSET interval[vec 0,vec 1] /\
                interval[lift a,vec 1] SUBSET interval[vec 0,vec 1]` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `std_triangle_loop continuous_on interval[vec 0,vec 1]` ASSUME_TAC THENL
   [MP_TAC MOI_LTD_STD_TRIANGLE_LOOP THEN SIMP_TAC[path]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(MESON[HOMEOMORPHIC_SIMPLY_CONNECTED_EQ; CONVEX_IMP_SIMPLY_CONNECTED;
                       CONVEX_INTERVAL]
      `interval[vec 0:real^1,lift a] homeomorphic (t:real^2->bool) ==> simply_connected t`) THEN
    REWRITE_TAC[homeomorphic] THEN EXISTS_TAC `std_triangle_loop` THEN
    MATCH_MP_TAC HOMEOMORPHISM_COMPACT THEN
    REWRITE_TAC[COMPACT_INTERVAL] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
    REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `t:real`] THEN STRIP_TAC THEN REWRITE_TAC[LIFT_EQ] THEN
    MP_TAC(SPECL [`s:real`; `t:real`] MOI_S3CI_STL_INJ) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(MESON[HOMEOMORPHIC_SIMPLY_CONNECTED_EQ; CONVEX_IMP_SIMPLY_CONNECTED;
                       CONVEX_INTERVAL]
      `interval[lift a,vec 1:real^1] homeomorphic (t:real^2->bool) ==> simply_connected t`) THEN
    REWRITE_TAC[homeomorphic] THEN EXISTS_TAC `std_triangle_loop` THEN
    MATCH_MP_TAC HOMEOMORPHISM_COMPACT THEN
    REWRITE_TAC[COMPACT_INTERVAL] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
    REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `t:real`] THEN STRIP_TAC THEN REWRITE_TAC[LIFT_EQ] THEN
    MP_TAC(SPECL [`s:real`; `t:real`] MOI_S3CI_STL_INJ) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    MP_TAC MOI_LTD_STD_TRIANGLE_LOOP THEN REWRITE_TAC[path_image] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM SET_TAC[];
    MP_TAC MOI_LTD_STD_TRIANGLE_LOOP THEN REWRITE_TAC[path_image] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM SET_TAC[]]);;

(* A loop at vec 0 whose first half runs in the arc of parameters [a,1] and *)
(* whose second half runs in the arc [0,a] is homotopic to the reverse of   *)
(* std_triangle_loop.                                                        *)
let MOI_S3CI_SPLIT_REV = prove
 (`!(P:real^1->real^2) a.
     &0 < a /\ a < &1 /\ path P /\
     (!u. &0 <= u /\ u <= &1 / &2
          ==> P(lift u) IN IMAGE std_triangle_loop (interval[lift a,vec 1])) /\
     (!u. &1 / &2 <= u /\ u <= &1
          ==> P(lift u) IN IMAGE std_triangle_loop (interval[vec 0,lift a])) /\
     P(vec 0) = vec 0 /\ P(vec 1) = vec 0 /\
     P(lift(&1 / &2)) = std_triangle_loop(lift a)
     ==> homotopic_paths (relative_frontier std_triangle) P
           (reversepath std_triangle_loop)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `a:real` MOI_S3CI_STL_ARCS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `A1 = IMAGE std_triangle_loop (interval[vec 0,lift a])` THEN
  ABBREV_TAC `A2 = IMAGE std_triangle_loop (interval[lift a,vec 1])` THEN
  MP_TAC MOI_LTD_STD_TRIANGLE_LOOP THEN STRIP_TAC THEN
  SUBGOAL_THEN `lift(&1 / &2) IN interval[vec 0,vec 1] /\
                lift(&1 - a) IN interval[vec 0,vec 1] /\
                vec 0 IN interval[vec 0:real^1,vec 1] /\ vec 1 IN interval[vec 0:real^1,vec 1] /\
                vec 1 - lift(&1 - a) = lift a`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC; GSYM DROP_EQ; DROP_SUB] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `path_image (P:real^1->real^2) SUBSET relative_frontier std_triangle`
  ASSUME_TAC THENL
   [REWRITE_TAC[path_image; SUBSET; FORALL_IN_IMAGE; FORALL_LIFT; IN_INTERVAL_1;
                LIFT_DROP; DROP_VEC] THEN
    X_GEN_TAC `u:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `u <= &1 / &2` THENL
     [SUBGOAL_THEN `(P:real^1->real^2)(lift u) IN A2` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        ASM SET_TAC[]];
      SUBGOAL_THEN `(P:real^1->real^2)(lift u) IN A1` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        ASM SET_TAC[]]];
    ALL_TAC] THEN
  (* the two halves of P and of the reversed loop *)
  SUBGOAL_THEN
   `homotopic_paths A2 (subpath (vec 0) (lift(&1 / &2)) P)
      (subpath (vec 0) (lift(&1 - a)) (reversepath std_triangle_loop)) /\
    homotopic_paths A1 (subpath (lift(&1 / &2)) (vec 1) P)
      (subpath (lift(&1 - a)) (vec 1) (reversepath std_triangle_loop))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(REWRITE_RULE[SIMPLY_CONNECTED_EQ_HOMOTOPIC_PATHS]
        (ASSUME `simply_connected (A2:real^2->bool)`));
      MP_TAC(REWRITE_RULE[SIMPLY_CONNECTED_EQ_HOMOTOPIC_PATHS]
        (ASSUME `simply_connected (A1:real^2->bool)`))] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    ASM_SIMP_TAC[PATH_SUBPATH; PATH_REVERSEPATH; PATHSTART_SUBPATH; PATHFINISH_SUBPATH] THEN
    REWRITE_TAC[reversepath; VECTOR_SUB_RZERO; VECTOR_SUB_REFL] THEN
    ASM_REWRITE_TAC[MOI_S3CI_STL_ENDS] THEN
    SIMP_TAC[PATH_IMAGE_SUBPATH; LIFT_DROP; DROP_VEC; REAL_ARITH `&0 <= &1 / &2`;
             REAL_ARITH `&1 / &2 <= &1`] THEN
    (CONJ_TAC THENL
      [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP;
                   DROP_VEC] THEN
       X_GEN_TAC `u:real` THEN STRIP_TAC THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
       ALL_TAC]) THEN
    (SUBGOAL_THEN `drop(vec 0) <= drop(lift(&1 - a)) /\ drop(lift(&1 - a)) <= drop(vec 1)`
     STRIP_ASSUME_TAC THENL
      [REWRITE_TAC[LIFT_DROP; DROP_VEC] THEN ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    ASM_SIMP_TAC[PATH_IMAGE_SUBPATH] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP;
                DROP_VEC] THEN
    X_GEN_TAC `u:real` THEN STRIP_TAC THEN
    MAP_EVERY EXPAND_TAC ["A1"; "A2"] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_SUB; LIFT_DROP; DROP_VEC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* join the halves *)
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
  EXISTS_TAC `subpath (vec 0) (lift(&1 / &2)) P ++
              subpath (lift(&1 / &2)) (vec 1) (P:real^1->real^2)` THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM SUBPATH_TRIVIAL] THEN
    MATCH_MP_TAC HOMOTOPIC_JOIN_SUBPATHS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
  EXISTS_TAC `subpath (vec 0) (lift(&1 - a)) (reversepath std_triangle_loop) ++
              subpath (lift(&1 - a)) (vec 1) (reversepath std_triangle_loop)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
    REWRITE_TAC[PATHFINISH_SUBPATH; PATHSTART_SUBPATH] THEN
    CONJ_TAC THEN MATCH_MP_TAC HOMOTOPIC_PATHS_SUBSET THENL
     [EXISTS_TAC `A2:real^2->bool`; EXISTS_TAC `A1:real^2->bool`] THEN
    ASM_REWRITE_TAC[];
    GEN_REWRITE_TAC RAND_CONV [GSYM SUBPATH_TRIVIAL] THEN
    MATCH_MP_TAC HOMOTOPIC_JOIN_SUBPATHS THEN
    ASM_REWRITE_TAC[PATH_REVERSEPATH; PATH_IMAGE_REVERSEPATH; SUBSET_REFL]]);;

let MOI_S3CI_REV_LOOP = prove
 (`!K:real^2->real^2.
     K continuous_on relative_frontier std_triangle /\
     IMAGE K (relative_frontier std_triangle) = relative_frontier std_triangle /\
     (!x y. x IN relative_frontier std_triangle /\ y IN relative_frontier std_triangle /\
            K x = K y ==> x = y) /\
     moi_s3ci_cycrev K
     ==> homotopic_loops (relative_frontier std_triangle) (K o std_triangle_loop)
           (reversepath std_triangle_loop)`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC MOI_LTD_STD_TRIANGLE_LOOP THEN STRIP_TAC THEN
  SUBGOAL_THEN `?p0:real^2. p0 IN relative_frontier std_triangle /\
                            (K:real^2->real^2) p0 = vec 0`
  STRIP_ASSUME_TAC THENL
   [MP_TAC MOI_S3CI_TAU_ZERO THEN ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `c = moi_lsp_tau(p0:real^2)` THEN
  SUBGOAL_THEN `&0 <= c /\ c < &1 /\ std_triangle_loop(lift c) = p0` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S3CI_TAU_FACTS]; ALL_TAC] THEN
  MP_TAC(SPEC `c:real` MOI_S3CI_SHIFT) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `z = shiftpath (lift c) std_triangle_loop` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z:real^1->real^2)(vec 0) = p0 /\ z(vec 1) = p0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN REWRITE_TAC[shiftpath; VECTOR_ADD_RID; DROP_ADD; LIFT_DROP; DROP_VEC] THEN
    CONJ_TAC THENL
     [COND_CASES_TAC THENL [ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
      COND_CASES_TAC THENL
       [SUBGOAL_THEN `c = &0` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[LIFT_NUM; VECTOR_ADD_LID] THEN
        ASM_MESON_TAC[MOI_S3CI_STL_ENDS; LIFT_NUM];
        REWRITE_TAC[VECTOR_SUB_REFL; VECTOR_ADD_RID] THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  (* the parameter of the image *)
  SUBGOAL_THEN
   `!u. &0 < u /\ u < &1
        ==> (K:real^2->real^2) ((z:real^1->real^2) (lift u)) IN relative_frontier std_triangle /\
            &0 < moi_lsp_tau (K (z (lift u))) /\ moi_lsp_tau (K (z (lift u))) < &1 /\
            std_triangle_loop (lift (moi_lsp_tau (K (z (lift u))))) = K (z (lift u))`
  (LABEL_TAC "G1") THENL
   [X_GEN_TAC `u:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
      can (find_term ((=) `moi_s3ci_ad`)) (concl th)
      then MP_TAC(SPEC `u:real` th) else NO_TAC) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `(K:real^2->real^2) ((z:real^1->real^2) (lift u)) IN
                  relative_frontier std_triangle` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(MP (SPEC `(K:real^2->real^2) ((z:real^1->real^2) (lift u))`
      (CONJUNCT1 MOI_S3CI_TAU_FACTS)) (ASSUME `(K:real^2->real^2) ((z:real^1->real^2) (lift u)) IN
                  relative_frontier std_triangle`)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= t /\ ~(t = &0) ==> &0 < t`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(K:real^2->real^2) ((z:real^1->real^2) (lift u)) = K p0` MP_TAC THENL
     [ASM_MESON_TAC[MOI_S3CI_TAU_ZERO]; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^1->real^2) (lift u) = p0` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `K:real^2->real^2`)) (concl th) &&
        not (can (find_term ((=) `vec 0:real^2`)) (concl th)))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN
    UNDISCH_TAC `moi_lsp_tau ((z:real^1->real^2) (lift u)) = moi_s3ci_ad c u` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`c:real`; `u:real`] MOI_S3CI_AD_SH) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[moi_s3ci_ad; moi_s3ci_sh] THEN
    REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* reversal: the parameter of the image decreases on (0,1) *)
  SUBGOAL_THEN
   `!u v. &0 < u /\ u < v /\ v < &1
          ==> moi_lsp_tau((K:real^2->real^2)((z:real^1->real^2)(lift v))) <
              moi_lsp_tau(K(z(lift u)))`
  (LABEL_TAC "G2") THENL
   [MAP_EVERY X_GEN_TAC [`u:real`; `v:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= u /\ u < &1 /\ &0 <= v /\ &0 < v` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `(z:real^1->real^2)(lift u) IN relative_frontier std_triangle /\
      moi_lsp_tau (z (lift u)) = moi_s3ci_ad c u /\
      z (lift v) IN relative_frontier std_triangle /\
      moi_lsp_tau (z (lift v)) = moi_s3ci_ad c v`
    STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> if is_forall(concl th) &&
        can (find_term ((=) `moi_s3ci_ad`)) (concl th)
        then MP_TAC(SPEC `u:real` th) THEN MP_TAC(SPEC `v:real` th) else NO_TAC) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `moi_s3ci_cyc p0 ((z:real^1->real^2)(lift u)) (z(lift v))` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[moi_s3ci_cyc] THEN
      MP_TAC(SPECL [`c:real`; `c:real`; `moi_s3ci_ad c u`; `moi_s3ci_ad c v`]
        MOI_S3CI_CYC3_SH) THEN
      MP_TAC(SPECL [`c:real`; `u:real`] MOI_S3CI_AD_SH) THEN
      MP_TAC(SPECL [`c:real`; `v:real`] MOI_S3CI_AD_SH) THEN
      MP_TAC(SPECL [`c:real`; `c:real`] MOI_S3CI_SH) THEN
      ASM_SIMP_TAC[REAL_LE_REFL] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[moi_s3ci_cyc3] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`p0:real^2`; `(z:real^1->real^2)(lift u)`;
                                 `(z:real^1->real^2)(lift v)`] o
      REWRITE_RULE[moi_s3ci_cycrev] o
      check (fun th -> concl th = `moi_s3ci_cycrev (K:real^2->real^2)`)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[moi_s3ci_cyc; moi_s3ci_cyc3; CONJUNCT1(CONJUNCT2 MOI_S3CI_TAU_ZERO)] THEN
    SUBGOAL_THEN `&0 < moi_lsp_tau((K:real^2->real^2)((z:real^1->real^2)(lift u)))` MP_TAC THENL
     [USE_THEN "G1" (MP_TAC o SPEC `u:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the midpoint parameter a and the split *)
  ABBREV_TAC `a = moi_lsp_tau((K:real^2->real^2)((z:real^1->real^2)(lift(&1 / &2))))` THEN
  SUBGOAL_THEN `&0 < a /\ a < &1 /\
                std_triangle_loop(lift a) = (K:real^2->real^2)((z:real^1->real^2)(lift(&1 / &2)))`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "G1" (MP_TAC o SPEC `&1 / &2`) THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> if concl th = `moi_lsp_tau((K:real^2->real^2)((z:real^1->real^2)(lift(&1 / &2)))) = a`
      then REWRITE_TAC[th] else NO_TAC) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. &0 < u /\ u < &1
        ==> (K:real^2->real^2)((z:real^1->real^2)(lift u)) =
            std_triangle_loop(lift(moi_lsp_tau(K(z(lift u))))) /\
            &0 < moi_lsp_tau(K(z(lift u))) /\ moi_lsp_tau(K(z(lift u))) < &1`
  (LABEL_TAC "G3") THENL
   [X_GEN_TAC `u:real` THEN DISCH_TAC THEN
    USE_THEN "G1" (MP_TAC o SPEC `u:real`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
  EXISTS_TAC `(K:real^2->real^2) o (z:real^1->real^2)` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(K:real^2->real^2) o (z:real^1->real^2) =
                  shiftpath (lift c) (K o std_triangle_loop)` SUBST1_TAC THENL
     [EXPAND_TAC "z" THEN REWRITE_TAC[FUN_EQ_THM; o_THM; shiftpath] THEN
      GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_SHIFTPATH_SELF THEN
    ASM_REWRITE_TAC[PATH_IMAGE_COMPOSE; PATHSTART_COMPOSE; PATHFINISH_COMPOSE; SUBSET_REFL;
                    IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
    CONJ_TAC THENL [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[];
                    ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_IMP_HOMOTOPIC_LOOPS THEN
  REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATHFINISH_REVERSEPATH] THEN
  ASM_REWRITE_TAC[pathstart; pathfinish] THEN
  MATCH_MP_TAC MOI_S3CI_SPLIT_REV THEN EXISTS_TAC `a:real` THEN
  ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `relative_frontier std_triangle:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "z" THEN
    W(fun (_,w) -> MP_TAC(ISPECL [`lift c`; `std_triangle_loop`] PATH_IMAGE_SHIFTPATH)) THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[SUBSET_REFL]];
    ALL_TAC] THEN
  CONJ_TAC THEN X_GEN_TAC `u:real` THEN STRIP_TAC THENL
   [ASM_CASES_TAC `u = &0` THENL
     [ASM_REWRITE_TAC[LIFT_NUM; IN_IMAGE] THEN EXISTS_TAC `vec 1:real^1` THEN
      REWRITE_TAC[MOI_S3CI_STL_ENDS; IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
      ASM_REAL_ARITH_TAC;
      USE_THEN "G3" (MP_TAC o SPEC `u:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      SUBGOAL_THEN `a <= moi_lsp_tau((K:real^2->real^2)((z:real^1->real^2)(lift u)))`
      ASSUME_TAC THENL
       [ASM_CASES_TAC `u = &1 / &2` THENL
         [EXPAND_TAC "a" THEN ASM_REWRITE_TAC[REAL_LE_REFL];
          MATCH_MP_TAC REAL_LT_IMP_LE THEN EXPAND_TAC "a" THEN
          USE_THEN "G2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      FIRST_X_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) =
        `(K:real^2->real^2)((z:real^1->real^2)(lift u))` then SUBST1_TAC th else NO_TAC) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN
      REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN ASM_REAL_ARITH_TAC];
    ASM_CASES_TAC `u = &1` THENL
     [ASM_REWRITE_TAC[LIFT_NUM; IN_IMAGE] THEN EXISTS_TAC `vec 0:real^1` THEN
      REWRITE_TAC[MOI_S3CI_STL_ENDS; IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
      ASM_REAL_ARITH_TAC;
      USE_THEN "G3" (MP_TAC o SPEC `u:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      SUBGOAL_THEN `moi_lsp_tau((K:real^2->real^2)((z:real^1->real^2)(lift u))) <= a`
      ASSUME_TAC THENL
       [ASM_CASES_TAC `u = &1 / &2` THENL
         [EXPAND_TAC "a" THEN ASM_REWRITE_TAC[REAL_LE_REFL];
          MATCH_MP_TAC REAL_LT_IMP_LE THEN EXPAND_TAC "a" THEN
          USE_THEN "G2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      FIRST_X_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) =
        `(K:real^2->real^2)((z:real^1->real^2)(lift u))` then SUBST1_TAC th else NO_TAC) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN
      REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN ASM_REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* The square annulus M = [-2,2]^2 minus (-1,1)^2 of pl_annulus_with_ends:   *)
(* a homeomorphism of M fixing the outer square pointwise preserves the      *)
(* cyclic order on the inner square (in any parametrization from            *)
(* rf std_triangle).  Winding numbers about vec 0: the inner loop and its    *)
(* image are homotopic in M (radial homotopy to the outer square, where the *)
(* map is the identity), while a reversing map gives the reversed loop.     *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CI_STL_SIMPLE = prove
 (`simple_path std_triangle_loop`,
  REWRITE_TAC[simple_path; MOI_LTD_STD_TRIANGLE_LOOP] THEN
  REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `t:real`] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP; DROP_VEC] THEN
  MATCH_MP_TAC MOI_S3CI_STL_INJ THEN ASM_REWRITE_TAC[]);;

let MOI_S3CI_SQ1 = prove
 (`inside(relative_frontier(interval[--vector[&1;&1],vector[&1;&1]]:real^2->bool)) =
   interval(--vector[&1;&1],vector[&1;&1]) /\
   (vec 0:real^2) IN interval(--vector[&1;&1],vector[&1;&1]) /\
   ~((vec 0:real^2) IN relative_frontier(interval[--vector[&1;&1],vector[&1;&1]])) /\
   ~((vec 0:real^2) IN interval[--vector[&2;&2],vector[&2;&2]] DIFF
                      interval(--vector[&1;&1],vector[&1;&1]))`,
  REWRITE_TAC[MOI_S5C_IN_SQO; MOI_S5C_IN_RF1; MOI_S5C_IN_SQANN; VEC_COMPONENT] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MP_TAC(SPEC `&1` MOI_S5C_SQ_INTERIOR) THEN REWRITE_TAC[REAL_LT_01] THEN
  SIMP_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR] THEN DISCH_TAC THEN
  SIMP_TAC[INSIDE_FRONTIER_EQ_INTERIOR; BOUNDED_INTERVAL; CONVEX_INTERVAL;
           INTERIOR_CLOSED_INTERVAL]);;

let MOI_S3CI_SQ_WN = prove
 (`!g:real^1->real^2.
     simple_path g /\
     path_image g = relative_frontier(interval[--vector[&1;&1],vector[&1;&1]])
     ==> winding_number(g,vec 0) = Cx(&1) \/ winding_number(g,vec 0) = --Cx(&1)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SIMPLE_CLOSED_PATH_WINDING_NUMBER_INSIDE) THEN
  ASM_REWRITE_TAC[MOI_S3CI_SQ1] THEN MESON_TAC[MOI_S3CI_SQ1]);;

let MOI_S3CI_RADIAL = prove
 (`!x:real^2.
     x IN relative_frontier(interval[--vector[&1;&1],vector[&1;&1]])
     ==> segment[x,&2 % x] SUBSET
         interval[--vector[&2;&2],vector[&2;&2]] DIFF
         interval(--vector[&1;&1],vector[&1;&1]) /\
         &2 % x IN relative_frontier(interval[--vector[&2;&2],vector[&2;&2]])`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!c. &1 <= c /\ c <= &2
        ==> c % (x:real^2) IN relative_frontier(interval[--vector[c;c],vector[c;c]])`
  ASSUME_TAC THENL
   [X_GEN_TAC `c:real` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`&1`; `c:real`] MOI_S5C_SQ_RF_SCALE) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_RID; pl_homeomorphism; homeomorphism] THEN
    STRIP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_SEGMENT] THEN X_GEN_TAC `y:real^2` THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&1 + s`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `y = (&1 + s) % (x:real^2)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`&1 + s`; `(&1 + s) % (x:real^2)`] MOI_S5C_SQ_RF) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MOI_S5C_IN_SQANN] THEN
    ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `&2`) THEN REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]]);;

let MOI_S3CI_ANN_FIX = prove
 (`!(h:real^2->real^2) h' (b:real^2->real^2) b'.
     homeomorphism
       (interval[--vector[&2;&2],vector[&2;&2]] DIFF interval(--vector[&1;&1],vector[&1;&1]),
        interval[--vector[&2;&2],vector[&2;&2]] DIFF interval(--vector[&1;&1],vector[&1;&1]))
       (h,h') /\
     (!x. x IN relative_frontier(interval[--vector[&2;&2],vector[&2;&2]]) ==> h x = x) /\
     IMAGE h (relative_frontier(interval[--vector[&1;&1],vector[&1;&1]])) =
     relative_frontier(interval[--vector[&1;&1],vector[&1;&1]]) /\
     homeomorphism (relative_frontier std_triangle,
                    relative_frontier(interval[--vector[&1;&1],vector[&1;&1]])) (b,b')
     ==> moi_s3ci_cycpres (b' o h o b)`,
  REPEAT GEN_TAC THEN
  MP_TAC MOI_S3CI_SQ1 THEN
  MP_TAC MOI_S3CI_RADIAL THEN
  SUBGOAL_THEN
   `relative_frontier(interval[--vector[&1;&1],vector[&1;&1]]) SUBSET
    interval[--vector[&2;&2],vector[&2;&2]] DIFF interval(--vector[&1;&1],vector[&1;&1]) /\
    relative_frontier(interval[--vector[&2;&2],vector[&2;&2]]) SUBSET
    interval[--vector[&2;&2],vector[&2;&2]] DIFF
    interval(--vector[&1;&1],vector[&1;&1]):real^2->bool`
  MP_TAC THENL
   [REWRITE_TAC[SUBSET; MOI_S5C_IN_RF1; MOI_S5C_IN_RF2; MOI_S5C_IN_SQANN] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `M = interval[--vector[&2;&2],vector[&2;&2]] DIFF
                  interval(--vector[&1;&1],vector[&1;&1]):real^2->bool` THEN
  ABBREV_TAC `C1 = relative_frontier(interval[--vector[&1;&1],vector[&1;&1]]):real^2->bool` THEN
  ABBREV_TAC `C2 = relative_frontier(interval[--vector[&2;&2],vector[&2;&2]]):real^2->bool` THEN
  REPEAT DISCH_TAC THEN FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  SUBGOAL_THEN
   `(h:real^2->real^2) continuous_on M /\ IMAGE h M = M /\
    (!x. x IN M ==> h' (h x) = x) /\
    (b:real^2->real^2) continuous_on relative_frontier std_triangle /\
    IMAGE b (relative_frontier std_triangle) = C1 /\
    (b':real^2->real^2) continuous_on C1 /\ IMAGE b' C1 = relative_frontier std_triangle /\
    (!x. x IN relative_frontier std_triangle ==> b' (b x) = x) /\
    (!y. y IN C1 ==> b (b' y) = y)`
  STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism]) THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  (* the circle map is a homeomorphism of rf std_triangle *)
  ABBREV_TAC `K = (b':real^2->real^2) o (h:real^2->real^2) o (b:real^2->real^2)` THEN
  SUBGOAL_THEN
   `(K:real^2->real^2) continuous_on relative_frontier std_triangle /\
    IMAGE K (relative_frontier std_triangle) = relative_frontier std_triangle /\
    (!x y. x IN relative_frontier std_triangle /\ y IN relative_frontier std_triangle /\
           K x = K y ==> x = y)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
        ASM_REWRITE_TAC[IMAGE_o]];
      ASM_REWRITE_TAC[IMAGE_o];
      REWRITE_TAC[o_THM] THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `(b:real^2->real^2) x IN C1 /\ b y IN C1` STRIP_ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(h:real^2->real^2) ((b:real^2->real^2) x) IN C1 /\ h (b y) IN C1`
      STRIP_ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(h:real^2->real^2) ((b:real^2->real^2) x) = h (b y)` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(b:real^2->real^2) x = b y` ASSUME_TAC THENL
       [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPEC `K:real^2->real^2` MOI_S3CI_DICHOT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN2 ACCEPT_TAC ASSUME_TAC) THEN
  (* reversing case: contradiction by winding numbers *)
  MP_TAC(SPEC `K:real^2->real^2` MOI_S3CI_REV_LOOP) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC MOI_LTD_STD_TRIANGLE_LOOP THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `path ((b:real^2->real^2) o std_triangle_loop) /\ path_image (b o std_triangle_loop) = C1 /\
    pathfinish (b o std_triangle_loop) = pathstart (b o std_triangle_loop) /\
    simple_path (b o std_triangle_loop)`
  MP_TAC THENL
   [ASM_REWRITE_TAC[PATH_IMAGE_COMPOSE; PATHSTART_COMPOSE; PATHFINISH_COMPOSE] THEN
    CONJ_TAC THENL [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SIMPLE_PATH_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[MOI_S3CI_STL_SIMPLE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `ell = (b:real^2->real^2) o std_triangle_loop` THEN STRIP_TAC THEN
  SUBGOAL_THEN `homotopic_loops C1 ((h:real^2->real^2) o (ell:real^1->real^2)) (reversepath ell)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
    EXISTS_TAC `(b:real^2->real^2) o (K:real^2->real^2) o std_triangle_loop` THEN CONJ_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_LOOPS_EQ THEN
      REWRITE_TAC[PATH_IMAGE_COMPOSE; PATHSTART_COMPOSE; PATHFINISH_COMPOSE] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
        ASM_REWRITE_TAC[SUBSET_REFL];
        X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
        EXPAND_TAC "ell" THEN EXPAND_TAC "K" THEN REWRITE_TAC[o_THM] THEN
        SUBGOAL_THEN `std_triangle_loop t IN relative_frontier std_triangle` ASSUME_TAC THENL
         [UNDISCH_TAC `path_image std_triangle_loop = relative_frontier std_triangle` THEN
          REWRITE_TAC[path_image] THEN ASM SET_TAC[];
          ALL_TAC] THEN
        SUBGOAL_THEN `(h:real^2->real^2) ((b:real^2->real^2) (std_triangle_loop t)) IN C1`
        ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        CONV_TAC SYM_CONV THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          is_forall(concl th) && can (find_term ((=) `b':real^2->real^2`)) (concl th) &&
          can (find_term ((=) `C1:real^2->bool`)) (concl th))) THEN
        ASM_REWRITE_TAC[]];
      SUBGOAL_THEN `reversepath (ell:real^1->real^2) =
                    (b:real^2->real^2) o reversepath std_triangle_loop` SUBST1_TAC THENL
       [EXPAND_TAC "ell" THEN REWRITE_TAC[FUN_EQ_THM; reversepath; o_THM]; ALL_TAC] THEN
      REWRITE_TAC[GSYM o_ASSOC] THEN
      MATCH_MP_TAC HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE THEN
      EXISTS_TAC `relative_frontier std_triangle:real^2->bool` THEN
      ASM_REWRITE_TAC[SUBSET_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `homotopic_loops M ((h:real^2->real^2) o (ell:real^1->real^2)) ell`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `!t. t IN interval[vec 0,vec 1] ==> (ell:real^1->real^2) t IN C1`
    ASSUME_TAC THENL
     [UNDISCH_TAC `path_image (ell:real^1->real^2) = C1` THEN
      REWRITE_TAC[path_image] THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `path ((\x:real^2. &2 % x) o (ell:real^1->real^2)) /\
                  pathfinish ((\x:real^2. &2 % x) o ell) =
                  pathstart ((\x:real^2. &2 % x) o ell)`
    STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE] THEN
      MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN
      ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SCALING];
      ALL_TAC] THEN
    SUBGOAL_THEN `homotopic_loops M (ell:real^1->real^2) ((\x:real^2. &2 % x) o ell)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_LOOPS_LINEAR THEN ASM_REWRITE_TAC[o_THM] THEN
      REPEAT STRIP_TAC THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
    EXISTS_TAC `(h:real^2->real^2) o (\x:real^2. &2 % x) o (ell:real^1->real^2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE THEN EXISTS_TAC `M:real^2->bool` THEN
      ASM_REWRITE_TAC[SUBSET_REFL];
      ALL_TAC] THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
    EXISTS_TAC `(\x:real^2. &2 % x) o (ell:real^1->real^2)` THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[HOMOTOPIC_LOOPS_SYM] THEN MATCH_MP_TAC HOMOTOPIC_LOOPS_EQ THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [FIRST_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_SUBSET o check (fun th ->
          can (find_term ((=) `M:real^2->bool`)) (concl th) &&
          can (find_term ((=) `ell:real^1->real^2`)) (concl th))) THEN SIMP_TAC[];
        X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
        CONV_TAC SYM_CONV THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          is_forall(concl th) && can (find_term ((=) `C2:real^2->bool`)) (concl th) &&
          not (can (find_term ((=) `C1:real^2->bool`)) (concl th)))) THEN
        ASM_MESON_TAC[]];
      ONCE_REWRITE_TAC[HOMOTOPIC_LOOPS_SYM] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `winding_number((h:real^2->real^2) o (ell:real^1->real^2),vec 0) =
    winding_number(ell,vec 0) /\
    winding_number(h o ell,vec 0) = winding_number(reversepath ell,vec 0)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC WINDING_NUMBER_HOMOTOPIC_LOOPS THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_SUBSET THENL
     [EXISTS_TAC `M:real^2->bool`; EXISTS_TAC `C1:real^2->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ell:real^1->real^2`; `vec 0:real^2`] WINDING_NUMBER_REVERSEPATH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `winding_number(ell:real^1->real^2,vec 0) = --winding_number(ell,vec 0)`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `ell:real^1->real^2` MOI_S3CI_SQ_WN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THEN
  UNDISCH_TAC `winding_number(ell:real^1->real^2,vec 0) = --winding_number(ell,vec 0)` THEN
  ASM_REWRITE_TAC[COMPLEX_NEG_NEG; GSYM CX_NEG; CX_INJ] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* The diagonal reflection (x1,x2) to (x2,x1) of the inner square reverses   *)
(* the cyclic order in every parametrization.  An explicit one,             *)
(* x |-> moi_s3ci_sq(moi_lsp_tau x), with moi_s3ci_sq the constant-speed     *)
(* loop around the square from (-1,-1); the reflection reverses its         *)
(* parameter.  Conjugation then transfers this to any parametrization.      *)
(* ------------------------------------------------------------------------- *)

let moi_s3ci_sq = new_definition
 `moi_s3ci_sq (s:real) =
    if s <= &1 / &4 then vector[&8 * s - &1; -- &1]:real^2
    else if s <= &1 / &2 then vector[&1; &8 * s - &3]
    else if s <= &3 / &4 then vector[&5 - &8 * s; &1]
    else vector[-- &1; &7 - &8 * s]`;;

let MOI_S3CI_SQ_C1 = prove
 (`!s. &0 <= s /\ s <= &1
       ==> moi_s3ci_sq s IN relative_frontier(interval[--vector[&1;&1],vector[&1;&1]])`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_s3ci_sq] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[MOI_S5C_IN_RF1; VECTOR_2] THEN
  REWRITE_TAC[real_max] THEN REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;

let MOI_S3CI_SQ_INJ = prove
 (`!s t. &0 <= s /\ s < &1 /\ &0 <= t /\ t < &1 /\ moi_s3ci_sq s = moi_s3ci_sq t
         ==> s = t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s3ci_sq] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN ASM_REAL_ARITH_TAC);;

let MOI_S3CI_SQ_ONTO = prove
 (`!y:real^2. y IN relative_frontier(interval[--vector[&1;&1],vector[&1;&1]])
              ==> ?s. &0 <= s /\ s < &1 /\ moi_s3ci_sq s = y`,
  GEN_TAC THEN REWRITE_TAC[MOI_S5C_IN_RF1] THEN DISCH_TAC THEN
  SUBGOAL_THEN `abs((y:real^2)$1) <= &1 /\ abs(y$2) <= &1 /\ (abs(y$1) = &1 \/ abs(y$2) = &1)`
  ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `(y:real^2)$2 = -- &1 /\ y$1 < &1` THENL
   [EXISTS_TAC `((y:real^2)$1 + &1) / &8`;
    ASM_CASES_TAC `(y:real^2)$1 = &1 /\ y$2 < &1` THENL
     [EXISTS_TAC `((y:real^2)$2 + &3) / &8`;
      ASM_CASES_TAC `(y:real^2)$2 = &1 /\ -- &1 < y$1` THENL
       [EXISTS_TAC `(&5 - (y:real^2)$1) / &8`; EXISTS_TAC `(&7 - (y:real^2)$2) / &8`]]] THEN
  REWRITE_TAC[moi_s3ci_sq; CART_EQ; DIMINDEX_2; FORALL_2] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[VECTOR_2] THEN ASM_REAL_ARITH_TAC);;

let MOI_S3CI_SQ_SWAP = prove
 (`!s. &0 < s /\ s < &1
       ==> vector[(moi_s3ci_sq s)$2; (moi_s3ci_sq s)$1] = moi_s3ci_sq(&1 - s)`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_s3ci_sq] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN ASM_REAL_ARITH_TAC);;

let MOI_S3CI_SQ_ENDS = prove
 (`moi_s3ci_sq(&0) = vector[-- &1; -- &1] /\ moi_s3ci_sq(&1) = vector[-- &1; -- &1]`,
  REWRITE_TAC[moi_s3ci_sq] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]);;

let MOI_S3CI_V1_CONT_TAC =
  GEN_REWRITE_TAC I [CONTINUOUS_ON_COMPONENTWISE_LIFT] THEN
  REWRITE_TAC[DIMINDEX_2; FORALL_2; VECTOR_2;
              LIFT_ADD; LIFT_SUB; LIFT_CMUL; LIFT_NEG; LIFT_DROP] THEN
  SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_SUB; CONTINUOUS_ON_CMUL; CONTINUOUS_ON_ID;
           CONTINUOUS_ON_CONST; CONTINUOUS_ON_NEG];;

let MOI_S3CI_SQ_CONT = prove
 (`(\t:real^1. moi_s3ci_sq (drop t)) continuous_on (:real^1)`,
  REWRITE_TAC[moi_s3ci_sq] THEN
  MATCH_MP_TAC CONTINUOUS_ON_CASES_1 THEN REPEAT CONJ_TAC THENL
   [MOI_S3CI_V1_CONT_TAC;
    MATCH_MP_TAC CONTINUOUS_ON_CASES_1 THEN REPEAT CONJ_TAC THENL
     [MOI_S3CI_V1_CONT_TAC;
      MATCH_MP_TAC CONTINUOUS_ON_CASES_1 THEN REPEAT CONJ_TAC THENL
       [MOI_S3CI_V1_CONT_TAC; MOI_S3CI_V1_CONT_TAC; ALL_TAC];
      ALL_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_UNIV; LIFT_DROP] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

(* The explicit parametrization x |-> moi_s3ci_sq(moi_lsp_tau x) of the     *)
(* inner square: on each edge of the triangle it is moi_s3ci_sq of an      *)
(* affine function (on the closed third edge as well, since the square     *)
(* loop is closed).                                                         *)
let MOI_S3CI_SQAFF_CONT = prove
 (`!a b c (s:real^2->bool).
     (\x:real^2. moi_s3ci_sq(a * x$1 + b * x$2 + c)) continuous_on s`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `(\x:real^2. moi_s3ci_sq(a * x$1 + b * x$2 + c)) =
                (\t:real^1. moi_s3ci_sq(drop t)) o (\x:real^2. lift(a * x$1 + b * x$2 + c))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    REWRITE_TAC[SUBSET_UNIV; MOI_S3CI_AFF_CONT];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
    REWRITE_TAC[SUBSET_UNIV; MOI_S3CI_SQ_CONT]]);;

let MOI_S3CI_B1_CONT = prove
 (`(\x:real^2. moi_s3ci_sq(moi_lsp_tau x)) continuous_on relative_frontier std_triangle`,
  REWRITE_TAC[MOI_LTD_STD_TRIANGLE_FRONTIER] THEN
  MP_TAC MOI_S3CI_STD_SEGS THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`vec 0:real^2`; `basis 1:real^2`] ENDS_IN_SEGMENT) THEN
  MP_TAC(ISPECL [`basis 1:real^2`; `basis 2:real^2`] ENDS_IN_SEGMENT) THEN
  MP_TAC(ISPECL [`basis 2:real^2`; `vec 0:real^2`] ENDS_IN_SEGMENT) THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x:real^2. moi_s3ci_sq(moi_lsp_tau x)) continuous_on segment[vec 0,basis 1] /\
    (\x:real^2. moi_s3ci_sq(moi_lsp_tau x)) continuous_on segment[basis 1,basis 2] /\
    (\x:real^2. moi_s3ci_sq(moi_lsp_tau x)) continuous_on segment[basis 2,vec 0]`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THENL
     [EXISTS_TAC `\x:real^2. moi_s3ci_sq(&1 / &2 * x$1 + &0 * x$2 + &0)`;
      EXISTS_TAC `\x:real^2. moi_s3ci_sq(&0 * x$1 + &1 / &4 * x$2 + &1 / &2)`;
      EXISTS_TAC `\x:real^2. moi_s3ci_sq(&0 * x$1 + --(&1 / &4) * x$2 + &1)`] THEN
    REWRITE_TAC[MOI_S3CI_SQAFF_CONT] THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN MOI_S3CI_EDGES_TAC THEN
    REWRITE_TAC[moi_lsp_tau] THEN
    REPEAT COND_CASES_TAC THEN TRY(AP_TERM_TAC THEN ASM_REAL_ARITH_TAC) THEN
    REWRITE_TAC[MOI_S3CI_SQ_ENDS] THEN
    TRY(MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_REAL_ARITH_TAC) THEN
    SUBGOAL_THEN `&0 * (x:real^2)$1 + --(&1 / &4) * x$2 + &1 = &1` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; REWRITE_TAC[MOI_S3CI_SQ_ENDS]] THEN
    SUBGOAL_THEN `(x:real^2)$1 / &2 = &0` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; REWRITE_TAC[MOI_S3CI_SQ_ENDS]];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_UNION_LOCAL THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[CLOSED_IN_CLOSED] THEN EXISTS_TAC `segment[vec 0,basis 1:real^2]` THEN
    REWRITE_TAC[CLOSED_SEGMENT] THEN ASM SET_TAC[];
    REWRITE_TAC[CLOSED_IN_CLOSED] THEN
    EXISTS_TAC `segment[basis 1,basis 2] UNION segment[basis 2,vec 0:real^2]` THEN
    SIMP_TAC[CLOSED_UNION; CLOSED_SEGMENT] THEN ASM SET_TAC[];
    MATCH_MP_TAC CONTINUOUS_ON_UNION_LOCAL THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN REWRITE_TAC[CLOSED_IN_CLOSED] THENL
     [EXISTS_TAC `segment[basis 1,basis 2:real^2]`;
      EXISTS_TAC `segment[basis 2,vec 0:real^2]`] THEN
    REWRITE_TAC[CLOSED_SEGMENT] THEN ASM SET_TAC[]]);;

let MOI_S3CI_B1 = prove
 (`?b1'. homeomorphism (relative_frontier std_triangle,
                        relative_frontier(interval[--vector[&1;&1],vector[&1;&1]]))
                       ((\x:real^2. moi_s3ci_sq(moi_lsp_tau x)),b1')`,
  MATCH_MP_TAC HOMEOMORPHISM_COMPACT THEN REWRITE_TAC[MOI_S3CI_B1_CONT] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MOI_LTD_FRONTIER_SUBSET_TRIANGLE];
    REWRITE_TAC[EXTENSION; IN_IMAGE] THEN X_GEN_TAC `y:real^2` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_S3CI_SQ_C1 THEN ASM_MESON_TAC[MOI_S3CI_TAU_FACTS; REAL_LT_IMP_LE];
      DISCH_THEN(MP_TAC o MATCH_MP MOI_S3CI_SQ_ONTO) THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `std_triangle_loop(lift s)` THEN
      MP_TAC(SPEC `s:real` (CONJUNCT2 MOI_S3CI_TAU_FACTS)) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[]];
    MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_S3CI_TAU_INJ THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S3CI_SQ_INJ THEN ASM_MESON_TAC[MOI_S3CI_TAU_FACTS]]);;

let MOI_S3CI_PTWISE = prove
 (`!q1 q2:real^2->real^2.
     (!x. x IN relative_frontier std_triangle ==> q1 x = q2 x)
     ==> (moi_s3ci_cycpres q1 <=> moi_s3ci_cycpres q2) /\
         (moi_s3ci_cycrev q1 <=> moi_s3ci_cycrev q2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s3ci_cycpres; moi_s3ci_cycrev] THEN
  EQ_TAC THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:real^2`; `b:real^2`; `c:real^2`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^2`; `b:real^2`; `c:real^2`]) THEN
  ASM_SIMP_TAC[]);;

let MOI_S3CI_CONJ = prove
 (`!(q:real^2->real^2) h h'.
     homeomorphism (relative_frontier std_triangle,relative_frontier std_triangle) (h,h') /\
     (!x. x IN relative_frontier std_triangle ==> q x IN relative_frontier std_triangle)
     ==> (moi_s3ci_cycpres q ==> moi_s3ci_cycpres (h' o q o h)) /\
         (moi_s3ci_cycrev q ==> moi_s3ci_cycrev (h' o q o h))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[homeomorphism] th))
    ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_s3ci_cycpres (h:real^2->real^2) \/ moi_s3ci_cycrev h` MP_TAC THENL
   [MATCH_MP_TAC MOI_S3CI_DICHOT THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`h:real^2->real^2`; `h':real^2->real^2`] MOI_S3CI_INVERSE) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(!x. x IN relative_frontier std_triangle ==> (h:real^2->real^2) x IN
                                                relative_frontier std_triangle) /\
    (!x. x IN relative_frontier std_triangle ==> ((q:real^2->real^2) o h) x IN
                                                relative_frontier std_triangle)`
  STRIP_ASSUME_TAC THENL [REWRITE_TAC[o_THM] THEN ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`h:real^2->real^2`; `q:real^2->real^2`] MOI_S3CI_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`(q:real^2->real^2) o (h:real^2->real^2)`; `h':real^2->real^2`] MOI_S3CI_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  DISCH_THEN(DISJ_CASES_TAC) THEN CONJ_TAC THEN DISCH_TAC THEN ASM_MESON_TAC[]);;

let MOI_S3CI_T1_REV = prove
 (`!b1':real^2->real^2.
     homeomorphism (relative_frontier std_triangle,
                    relative_frontier(interval[--vector[&1;&1],vector[&1;&1]]))
                   ((\x:real^2. moi_s3ci_sq(moi_lsp_tau x)),b1')
     ==> moi_s3ci_cycrev (b1' o (\x:real^2. vector[x$2; x$1]) o
                          (\x:real^2. moi_s3ci_sq(moi_lsp_tau x)))`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism]) THEN
  SUBGOAL_THEN
   `!x. x IN relative_frontier std_triangle
        ==> ((b1':real^2->real^2) o (\x:real^2. vector[x$2; x$1]) o
             (\x:real^2. moi_s3ci_sq(moi_lsp_tau x))) x IN relative_frontier std_triangle /\
            moi_lsp_tau(((b1':real^2->real^2) o (\x:real^2. vector[x$2; x$1]) o
                         (\x:real^2. moi_s3ci_sq(moi_lsp_tau x))) x) =
            (if moi_lsp_tau x = &0 then &0 else &1 - moi_lsp_tau x)`
  (LABEL_TAC "T1") THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    MP_TAC(MP (SPEC `x:real^2` (CONJUNCT1 MOI_S3CI_TAU_FACTS))
      (ASSUME `(x:real^2) IN relative_frontier std_triangle`)) THEN STRIP_TAC THEN
    COND_CASES_TAC THENL
     [ASM_REWRITE_TAC[MOI_S3CI_SQ_ENDS; VECTOR_2] THEN
      SUBGOAL_THEN `(b1':real^2->real^2) (vector[-- &1; -- &1]) = vec 0` SUBST1_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `vec 0:real^2` o check (fun th -> is_forall(concl th) &&
          (let b = snd(strip_forall(concl th)) in
           is_imp b && is_eq(rand b) && is_comb(lhs(rand b)) &&
           rator(lhs(rand b)) = `b1':real^2->real^2`))) THEN
        REWRITE_TAC[MOI_S3CI_TAU_ZERO; MOI_S3CI_SQ_ENDS];
        REWRITE_TAC[MOI_S3CI_TAU_ZERO]];
      SUBGOAL_THEN `&0 < moi_lsp_tau(x:real^2)` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPEC `&1 - moi_lsp_tau(x:real^2)` (CONJUNCT2 MOI_S3CI_TAU_FACTS)) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      MP_TAC(SPEC `moi_lsp_tau(x:real^2)` MOI_S3CI_SQ_SWAP) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      FIRST_X_ASSUM(fun th -> if concl th =
        `moi_lsp_tau (std_triangle_loop (lift (&1 - moi_lsp_tau (x:real^2)))) =
         &1 - moi_lsp_tau x` then SUBST1_TAC(SYM th) THEN ASSUME_TAC th else NO_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `std_triangle_loop (lift (&1 - moi_lsp_tau (x:real^2)))` o
        check (fun th -> is_forall(concl th) &&
          (let b = snd(strip_forall(concl th)) in
           is_imp b && is_eq(rand b) && is_comb(lhs(rand b)) &&
           rator(lhs(rand b)) = `b1':real^2->real^2`))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s3ci_cycrev; moi_s3ci_cyc] THEN
  MAP_EVERY X_GEN_TAC [`a:real^2`; `b:real^2`; `c:real^2`] THEN STRIP_TAC THEN
  USE_THEN "T1" (fun th -> MAP_EVERY (fun t -> STRIP_ASSUME_TAC(MP (SPEC t th)
    (ASSUME (mk_comb(mk_comb(`(IN):real^2->(real^2->bool)->bool`,t),
                     `relative_frontier std_triangle`)))))
    [`a:real^2`; `b:real^2`; `c:real^2`]) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(BETA_RULE(ISPECL [`\s. if s = &0 then &0 else &1 - s`;
    `moi_lsp_tau(a:real^2)`; `moi_lsp_tau(b:real^2)`; `moi_lsp_tau(c:real^2)`]
    MOI_S3CI_CYC3_DEC)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
      ASM_MESON_TAC[MOI_S3CI_TAU_FACTS];
      ASM_MESON_TAC[MOI_S3CI_TAU_FACTS];
      ASM_MESON_TAC[MOI_S3CI_TAU_FACTS];
      ASM_MESON_TAC[MOI_S3CI_TAU_FACTS];
      ASM_MESON_TAC[MOI_S3CI_TAU_FACTS];
      ASM_MESON_TAC[MOI_S3CI_TAU_FACTS]];
    REWRITE_TAC[]]);;

let MOI_S3CI_SQ_LOCPOLY = prove
 (`locally_polyhedral
     (relative_frontier(interval[--vector[&1;&1],vector[&1;&1]]):real^2->bool) /\
   relative_frontier(interval[--vector[&1;&1],vector[&1;&1]]) SUBSET
   interval[--vector[&2;&2],vector[&2;&2]] DIFF
   interval(--vector[&1;&1],vector[&1;&1]):real^2->bool /\
   relative_frontier(interval[--vector[&2;&2],vector[&2;&2]]) SUBSET
   interval[--vector[&2;&2],vector[&2;&2]] DIFF
   interval(--vector[&1;&1],vector[&1;&1]):real^2->bool /\
   IMAGE (\x:real^2. vector[x$2; x$1])
     (relative_frontier(interval[--vector[&1;&1],vector[&1;&1]])) =
   relative_frontier(interval[--vector[&1;&1],vector[&1;&1]])`,
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    MP_TAC(SPEC `&1` MOI_S5C_SQ_RF_POLYHEDRON) THEN REWRITE_TAC[REAL_LT_01];
    REWRITE_TAC[SUBSET; MOI_S5C_IN_RF1; MOI_S5C_IN_SQANN] THEN REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; MOI_S5C_IN_RF2; MOI_S5C_IN_SQANN] THEN REAL_ARITH_TAC;
    REWRITE_TAC[EXTENSION; IN_IMAGE; MOI_S5C_IN_RF1] THEN X_GEN_TAC `y:real^2` THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[VECTOR_2] THEN ASM_REAL_ARITH_TAC;
      DISCH_TAC THEN EXISTS_TAC `vector[(y:real^2)$2; y$1]:real^2` THEN
      REWRITE_TAC[VECTOR_2; CART_EQ; DIMINDEX_2; FORALL_2] THEN ASM_REAL_ARITH_TAC]]);;

let MOI_S3CI_SWAP_REV = prove
 (`!(b:real^2->real^2) b'.
     homeomorphism (relative_frontier std_triangle,
                    relative_frontier(interval[--vector[&1;&1],vector[&1;&1]])) (b,b')
     ==> moi_s3ci_cycrev (b' o (\x:real^2. vector[x$2; x$1]) o b)`,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_TAC `b1':real^2->real^2` MOI_S3CI_B1 THEN
  MP_TAC(SPEC `b1':real^2->real^2` MOI_S3CI_T1_REV) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC MOI_S3CI_SQ_LOCPOLY THEN STRIP_TAC THEN
  ABBREV_TAC `C1 = relative_frontier(interval[--vector[&1;&1],vector[&1;&1]]):real^2->bool` THEN
  ABBREV_TAC `b1 = \x:real^2. moi_s3ci_sq(moi_lsp_tau x)` THEN
  ABBREV_TAC `sw = \x:real^2. vector[x$2; x$1]:real^2` THEN
  SUBGOAL_THEN
   `homeomorphism (relative_frontier std_triangle,relative_frontier std_triangle)
      ((b1':real^2->real^2) o (b:real^2->real^2),(b':real^2->real^2) o (b1:real^2->real^2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `C1:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[HOMEOMORPHISM_SYM];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism]) THEN
  MP_TAC(SPECL [`(b1':real^2->real^2) o (sw:real^2->real^2) o (b1:real^2->real^2)`;
                `(b1':real^2->real^2) o (b:real^2->real^2)`;
                `(b':real^2->real^2) o (b1:real^2->real^2)`] MOI_S3CI_CONJ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[homeomorphism] THEN REWRITE_TAC[o_THM] THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(sw:real^2->real^2) ((b1:real^2->real^2) x) IN C1` MP_TAC THENL
     [ASM SET_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(p <=> q) ==> p ==> q`) THEN
  MATCH_MP_TAC(MESON[MOI_S3CI_PTWISE]
   `!q1 q2:real^2->real^2.
      (!x. x IN relative_frontier std_triangle ==> q1 x = q2 x)
      ==> (moi_s3ci_cycrev q1 <=> moi_s3ci_cycrev q2)`) THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
  SUBGOAL_THEN `(b:real^2->real^2) x IN C1` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(sw:real^2->real^2) ((b:real^2->real^2) x) IN C1` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* O2: collar adjustment.  An orientation-preserving PL self-homeomorphism   *)
(* phi of the end j0 of a PL annulus extends to a PL self-homeomorphism of  *)
(* the annulus that is the identity on the other end.  Transport to the     *)
(* square model; MOI_S5W_DICHOTOMY (pc_moi_s35_ext2t) extends the model map *)
(* or its composite with the diagonal reflection; the second case would     *)
(* make the reflection orientation-preserving (MOI_S3CI_ANN_FIX), against   *)
(* MOI_S3CI_SWAP_REV.                                                        *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CI_IMAGE_EQ = prove
 (`!s f g. (!x:real^2. x IN s ==> (f:real^2->real^2) x = g x) ==> IMAGE f s = IMAGE g s`,
  SET_TAC[]);;

let MOI_S3CI_COLLAR_DEF = prove
 (`!(k:real^N->bool) (j0:real^N->bool) (j1:real^N->bool)
    (p:real^2->real^N) (p':real^N->real^2) (phi:real^N->real^N) (phi':real^N->real^N).
     pl_annulus_with_ends k j0 j1 /\
     pl_homeomorphism (relative_frontier std_triangle,j0) (p,p') /\
     pl_homeomorphism (j0,j0) (phi,phi') /\
     moi_s3ci_cycpres (p' o phi o p)
     ==> ?(g:real^N->real^N) (g':real^N->real^N).
           pl_homeomorphism (k,k) (g,g') /\
           (!x. x IN j0 ==> g x = phi x) /\ (!x. x IN j1 ==> g x = x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_annulus_with_ends] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `f:real^2->real^N` (X_CHOOSE_THEN
    `g:real^N->real^2` STRIP_ASSUME_TAC)) STRIP_ASSUME_TAC) THEN
  MP_TAC MOI_S3CI_SQ_LOCPOLY THEN
  ABBREV_TAC `M = interval[--vector[&2;&2],vector[&2;&2]] DIFF
                  interval(--vector[&1;&1],vector[&1;&1]):real^2->bool` THEN
  ABBREV_TAC `C1 = relative_frontier(interval[--vector[&1;&1],vector[&1;&1]]):real^2->bool` THEN
  ABBREV_TAC `C2 = relative_frontier(interval[--vector[&2;&2],vector[&2;&2]]):real^2->bool` THEN
  STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    (lhs(concl th) = `j0:real^N->bool` || lhs(concl th) = `j1:real^N->bool`)))) THEN
  (* the model circle map g0 = g o phi o f on C1 *)
  SUBGOAL_THEN `pl_homeomorphism (C1,IMAGE (f:real^2->real^N) C1) (f,g)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_CEL_PLH_RESTRICT THEN EXISTS_TAC `M:real^2->bool` THEN
    EXISTS_TAC `k:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_homeomorphism (C1,C1) ((g:real^N->real^2) o (phi:real^N->real^N) o (f:real^2->real^N),
                              (g o phi') o f)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `IMAGE (f:real^2->real^N) C1` THEN CONJ_TAC THENL
     [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
      EXISTS_TAC `IMAGE (f:real^2->real^N) C1` THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[PL_HOMEOMORPHISM_SYM]];
    ALL_TAC] THEN
  (* the square model dichotomy *)
  MP_TAC(ISPECL [`(g:real^N->real^2) o (phi:real^N->real^N) o (f:real^2->real^N)`;
                 `((g:real^N->real^2) o (phi':real^N->real^N)) o (f:real^2->real^N)`]
         MOI_S5W_DICHOTOMY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism; homeomorphism] o
    check (fun th -> concl th = `pl_homeomorphism (M,k) (f:real^2->real^N,g)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism; homeomorphism] o
    check (fun th -> concl th =
      `pl_homeomorphism (IMAGE (f:real^2->real^N) C1,IMAGE f C1) (phi,phi')`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism; homeomorphism] o
    check (fun th -> concl th =
      `pl_homeomorphism (C1,C1) ((g:real^N->real^2) o (phi:real^N->real^N) o (f:real^2->real^N),
                                 (g o phi') o f)`)) THEN
  SUBGOAL_THEN
   `(!y:real^2. y IN C1 ==> y IN M) /\ (!y:real^2. y IN C2 ==> y IN M) /\
    (!y. y IN IMAGE (f:real^2->real^N) C1 ==> (phi:real^N->real^N) y IN IMAGE f C1) /\
    (!y. y IN IMAGE (f:real^2->real^N) C1 ==> (phi:real^N->real^N) y IN k)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `a /\ b /\ c /\ (a /\ c ==> d) ==> a /\ b /\ c /\ d`) THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `C1 SUBSET (M:real^2->bool)` THEN SET_TAC[];
      UNDISCH_TAC `C2 SUBSET (M:real^2->bool)` THEN SET_TAC[];
      UNDISCH_TAC `IMAGE (phi:real^N->real^N) (IMAGE (f:real^2->real^N) C1) = IMAGE f C1` THEN
      SET_TAC[];
      UNDISCH_TAC `IMAGE (f:real^2->real^N) M = k` THEN SET_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN (X_CHOOSE_THEN `H:real^2->real^2`
    (X_CHOOSE_THEN `H':real^2->real^2` STRIP_ASSUME_TAC)) o check (is_disj o concl)) THENL
   [(* the model map extends: transport back *)
    MAP_EVERY EXISTS_TAC
     [`((f:real^2->real^N) o (H:real^2->real^2)) o (g:real^N->real^2)`;
      `(f:real^2->real^N) o ((H':real^2->real^2) o (g:real^N->real^2))`] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `M:real^2->bool` THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC[PL_HOMEOMORPHISM_SYM];
        MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `M:real^2->bool` THEN
        ASM_REWRITE_TAC[]];
      REWRITE_TAC[FORALL_IN_IMAGE; o_THM] THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(y:real^2) IN M /\ (phi:real^N->real^N) ((f:real^2->real^N) y) IN k`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `k:real^N->bool`)) (concl th) &&
          can (find_term ((=) `phi:real^N->real^N`)) (concl th))) THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_SIMP_TAC[o_THM];
      REWRITE_TAC[FORALL_IN_IMAGE; o_THM] THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(y:real^2) IN M` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[]];
    (* the reflected case is impossible *)
    MATCH_MP_TAC(TAUT `F ==> p`) THEN
    SUBGOAL_THEN
     `homeomorphism (relative_frontier std_triangle,C1)
        ((g:real^N->real^2) o (p:real^2->real^N),(p':real^N->real^2) o (f:real^2->real^N))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `IMAGE (f:real^2->real^N) C1` THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC[pl_homeomorphism];
        ASM_MESON_TAC[pl_homeomorphism; HOMEOMORPHISM_SYM]];
      ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (H:real^2->real^2) C1 = C1` ASSUME_TAC THENL
     [SUBGOAL_THEN `IMAGE (H:real^2->real^2) C1 =
                    IMAGE (((g:real^N->real^2) o (phi:real^N->real^N) o (f:real^2->real^N)) o
                           (\x:real^2. vector[x$2; x$1])) C1` SUBST1_TAC THENL
       [MATCH_MP_TAC MOI_S3CI_IMAGE_EQ THEN REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[o_THM];
        ALL_TAC] THEN
      GEN_REWRITE_TAC LAND_CONV [IMAGE_o] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`H:real^2->real^2`; `H':real^2->real^2`;
                   `(g:real^N->real^2) o (p:real^2->real^N)`;
                   `(p':real^N->real^2) o (f:real^2->real^N)`] MOI_S3CI_ANN_FIX) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[pl_homeomorphism]; DISCH_TAC] THEN
    MP_TAC(ISPECL [`(g:real^N->real^2) o (p:real^2->real^N)`;
                   `(p':real^N->real^2) o (f:real^2->real^N)`] MOI_S3CI_SWAP_REV) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o
      check (fun th -> concl th = `homeomorphism (relative_frontier std_triangle,C1)
        ((g:real^N->real^2) o (p:real^2->real^N),(p':real^N->real^2) o (f:real^2->real^N))`)) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism; homeomorphism] o
      check (fun th -> concl th = `pl_homeomorphism (relative_frontier std_triangle,
        IMAGE (f:real^2->real^N) C1) (p,p')`)) THEN
    SUBGOAL_THEN
     `!x. x IN relative_frontier std_triangle
          ==> (g:real^N->real^2) ((p:real^2->real^N) x) IN C1`
    ASSUME_TAC THENL
     [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      UNDISCH_TAC `IMAGE ((g:real^N->real^2) o (p:real^2->real^N))
                     (relative_frontier std_triangle) = C1` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE; o_THM] THEN
      EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `!y:real^2. y IN C1 ==> (vector[y$2; y$1]:real^2) IN C1` ASSUME_TAC THENL
     [UNDISCH_TAC `IMAGE (\x:real^2. vector [x$2; x$1]) C1 = C1` THEN
      REWRITE_TAC[EXTENSION; IN_IMAGE] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!y. y IN C1 ==> ((p':real^N->real^2) o (f:real^2->real^N)) y IN
                      relative_frontier std_triangle`
    ASSUME_TAC THENL
     [X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
      UNDISCH_TAC `IMAGE ((p':real^N->real^2) o (f:real^2->real^N)) C1 =
                   relative_frontier std_triangle` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPECL [`((p':real^N->real^2) o (f:real^2->real^N)) o (\x:real^2. vector[x$2; x$1]) o
                   (g:real^N->real^2) o (p:real^2->real^N)`;
                  `(p':real^N->real^2) o (phi:real^N->real^N) o (p:real^2->real^N)`]
      MOI_S3CI_COMPOSE) THEN
    ANTS_TAC THENL
     [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      ONCE_REWRITE_TAC[o_THM] THEN FIRST_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL
     [`((p':real^N->real^2) o (phi:real^N->real^N) o (p:real^2->real^N)) o
       ((p':real^N->real^2) o (f:real^2->real^N)) o (\x:real^2. vector[x$2; x$1]) o
       (g:real^N->real^2) o (p:real^2->real^N)`;
      `((p':real^N->real^2) o (f:real^2->real^N)) o (H:real^2->real^2) o
       (g:real^N->real^2) o (p:real^2->real^N)`] MOI_S3CI_PTWISE) THEN
    ANTS_TAC THENL
     [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
      SUBGOAL_THEN `(g:real^N->real^2) ((p:real^2->real^N) x) IN C1` ASSUME_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      ABBREV_TAC `w = vector[((g:real^N->real^2) ((p:real^2->real^N) x))$2;
                             (g (p x))$1]:real^2` THEN
      SUBGOAL_THEN `(w:real^2) IN C1` ASSUME_TAC THENL
       [EXPAND_TAC "w" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(f:real^2->real^N) w IN IMAGE f C1` ASSUME_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(phi:real^N->real^N) ((f:real^2->real^N) w) IN k` ASSUME_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(H:real^2->real^2) ((g:real^N->real^2) ((p:real^2->real^N) x)) =
                    g ((phi:real^N->real^N) ((f:real^2->real^N) w))` SUBST1_TAC THENL
       [EXPAND_TAC "w" THEN ASM_SIMP_TAC[o_THM]; ALL_TAC] THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THEN
    MP_TAC(ISPEC `((p':real^N->real^2) o (f:real^2->real^N)) o (H:real^2->real^2) o
                  (g:real^N->real^2) o (p:real^2->real^N)` MOI_S3CI_EXCL) THEN
    FIRST_X_ASSUM(fun th -> if is_iff(concl th) &&
        can (find_term (fun u -> is_const u && fst(dest_const u) = "moi_s3ci_cycrev")) (concl th)
      then MP_TAC th else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[]]);;

let MOI_S3CI_COLLAR = prove
 (MOI_S3CI_COLLAR_TERM,
  MP_TAC MOI_S3CI_COLLAR_DEF THEN
  REWRITE_TAC[moi_s3ci_cycpres; moi_s3ci_cyc; moi_s3ci_cyc3]);;


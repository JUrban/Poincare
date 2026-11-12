needs "src/pc_moi_s32_chart.ml";;
needs "src/pc_moi_s31_rev.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* pc_moi_s32_tower: Moise GTM 47, Sec 32 (p.224), the tower of solid tori   *)
(* for the model data (main theorem TOWER : |- MOI_S32_TOWER of              *)
(* pc_moi_s3032_stmt).  Route:                                               *)
(*   1. radii r_i in (0,1) increasing from 0 to 1 over the integers, with   *)
(*      margins e_i a quarter of the smallest neighbouring gap;              *)
(*   2. stadium disks: rectangles around the segments in the half plane,    *)
(*      thin enough for their revolutions to lie in v; they are disks with  *)
(*      boundary (theta of pc_moi_s32_chart and an affine map) and meet     *)
(*      only consecutive ones;                                               *)
(*   3. local finiteness at the centre and at the rim;                       *)
(*   4. a PL solid torus for every index from 31.1 applied to the triple;   *)
(*   5. the even ones moved by the RECROSS consequent to cross their odd    *)
(*      neighbours (both orders), and the tower clauses checked.            *)
(* The antecedent PL_SOLID_TORUS_BASIC of the statement is not used.         *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Radii and margins over the integers.                                      *)
(* ------------------------------------------------------------------------- *)

let moi_s3tw_f = new_definition
 `moi_s3tw_f (x:real) = x / (&1 + abs x)`;;

let moi_s3tw_r = new_definition
 `moi_s3tw_r (i:int) = (&1 + moi_s3tw_f (real_of_int i)) / &2`;;

let MOI_S3TW_DIV_LT = prove
 (`!a b x y. &0 < a /\ &0 < b ==> (x / a < y / b <=> x * b < y * a)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
  SUBGOAL_THEN `y / b * a = (y * a) / b` SUBST1_TAC THENL
   [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ]);;

let MOI_S3TW_F_BOUND = prove
 (`!x. abs(moi_s3tw_f x) < &1`,
  GEN_TAC THEN REWRITE_TAC[moi_s3tw_f; REAL_ABS_DIV] THEN
  SUBGOAL_THEN `&0 < &1 + abs x` ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < y ==> abs y = y`; REAL_LT_LDIV_EQ] THEN REAL_ARITH_TAC);;

let MOI_S3TW_F_MONO = prove
 (`!x y. x < y ==> moi_s3tw_f x < moi_s3tw_f y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s3tw_f] THEN
  ASM_SIMP_TAC[MOI_S3TW_DIV_LT; REAL_ARITH `!x. &0 < &1 + abs x`] THEN
  ASM_CASES_TAC `&0 <= x` THENL
   [SUBGOAL_THEN `abs x = x /\ abs y = y` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= y` THENL
   [SUBGOAL_THEN `abs x = --x /\ abs y = y` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`--x:real`; `y:real`] REAL_LE_MUL) THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `abs x = --x /\ abs y = --y` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]]);;

let MOI_S3TW_F_NUM = prove
 (`!n. moi_s3tw_f (&n) = &n / (&1 + &n) /\
       moi_s3tw_f (--(&n)) = --(&n / (&1 + &n))`,
  GEN_TAC THEN REWRITE_TAC[moi_s3tw_f; REAL_ABS_NUM; REAL_ABS_NEG; real_div] THEN
  REAL_ARITH_TAC);;

let MOI_S3TW_R = prove
 (`(!i. &0 < moi_s3tw_r i /\ moi_s3tw_r i < &1) /\
   (!i j. i < j ==> moi_s3tw_r i < moi_s3tw_r j) /\
   (!i j. i <= j ==> moi_s3tw_r i <= moi_s3tw_r j) /\
   (!e. &0 < e ==> (?i. moi_s3tw_r i < e) /\ (?i. &1 - e < moi_s3tw_r i))`,
  SUBGOAL_THEN `!i j. i < j ==> moi_s3tw_r i < moi_s3tw_r j` ASSUME_TAC THENL
   [REWRITE_TAC[int_lt; moi_s3tw_r] THEN REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`real_of_int i`; `real_of_int j`] MOI_S3TW_F_MONO) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[moi_s3tw_r] THEN
    MP_TAC(SPEC `real_of_int i` MOI_S3TW_F_BOUND) THEN REAL_ARITH_TAC;
    REPEAT GEN_TAC THEN REWRITE_TAC[INT_LE_LT] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(SPEC `inv e` REAL_ARCH_SIMPLE) THEN
    DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
    SUBGOAL_THEN `&1 <= e * &n` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e * inv e` THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_LE_REFL];
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&1 / (&2 * (&1 + &n)) < e` ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 < &2 * (&1 + &n)` ASSUME_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `~(&1 + &n = &0)` ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [EXISTS_TAC `--(&n:int)` THEN
      REWRITE_TAC[moi_s3tw_r; int_neg_th; int_of_num_th; MOI_S3TW_F_NUM] THEN
      SUBGOAL_THEN `(&1 + --(&n / (&1 + &n))) / &2 = &1 / (&2 * (&1 + &n))` SUBST1_TAC THENL
       [UNDISCH_TAC `~(&1 + &n = &0)` THEN CONV_TAC REAL_FIELD; ASM_REWRITE_TAC[]];
      EXISTS_TAC `&n:int` THEN
      REWRITE_TAC[moi_s3tw_r; int_of_num_th; MOI_S3TW_F_NUM] THEN
      SUBGOAL_THEN `(&1 + &n / (&1 + &n)) / &2 = &1 - &1 / (&2 * (&1 + &n))` SUBST1_TAC THENL
       [UNDISCH_TAC `~(&1 + &n = &0)` THEN CONV_TAC REAL_FIELD; ASM_REAL_ARITH_TAC]]]);;

let moi_s3tw_e = new_definition
 `moi_s3tw_e (i:int) =
    min (min (moi_s3tw_r i - moi_s3tw_r (i - &1)) (moi_s3tw_r (i + &1) - moi_s3tw_r i))
        (moi_s3tw_r (i + &2) - moi_s3tw_r (i + &1)) / &4`;;

let MOI_S3TW_E = prove
 (`!i. &0 < moi_s3tw_e i /\
       &0 < moi_s3tw_r i - moi_s3tw_e i /\
       moi_s3tw_r i - moi_s3tw_e i < moi_s3tw_r i /\
       moi_s3tw_r i < moi_s3tw_r (i + &1) /\
       moi_s3tw_r (i + &1) < moi_s3tw_r (i + &1) + moi_s3tw_e i /\
       moi_s3tw_r (i + &1) + moi_s3tw_e i < &1 /\
       moi_s3tw_e i <= (moi_s3tw_r (i + &1) - moi_s3tw_r i) / &4 /\
       moi_s3tw_e i <= (moi_s3tw_r i - moi_s3tw_r (i - &1)) / &4 /\
       moi_s3tw_e i <= (moi_s3tw_r (i + &2) - moi_s3tw_r (i + &1)) / &4`,
  GEN_TAC THEN REWRITE_TAC[moi_s3tw_e] THEN
  MP_TAC(SPECL [`i - &1:int`; `i:int`] (CONJUNCT1(CONJUNCT2 MOI_S3TW_R))) THEN
  MP_TAC(SPECL [`i:int`; `i + &1:int`] (CONJUNCT1(CONJUNCT2 MOI_S3TW_R))) THEN
  MP_TAC(SPECL [`i + &1:int`; `i + &2:int`] (CONJUNCT1(CONJUNCT2 MOI_S3TW_R))) THEN
  MP_TAC(SPEC `i - &1:int` (CONJUNCT1 MOI_S3TW_R)) THEN
  MP_TAC(SPEC `i + &2:int` (CONJUNCT1 MOI_S3TW_R)) THEN
  REWRITE_TAC[INT_ARITH `i - &1 < i /\ i < i + &1 /\ i + &1 < i + &2:int`] THEN
  REAL_ARITH_TAC);;

(* The separation of non-consecutive stadium disks (used both for the       *)
(* crossing set-up and for local finiteness).                                *)

let MOI_S3TW_E_SEP = prove
 (`!i k. i + &2 <= k
         ==> moi_s3tw_r (i + &1) + moi_s3tw_e i < moi_s3tw_r k - moi_s3tw_e k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(CONJUNCT2(CONJUNCT2(SPEC `i:int` MOI_S3TW_E))) THEN
  MP_TAC(CONJUNCT2(CONJUNCT2(SPEC `k:int` MOI_S3TW_E))) THEN
  MP_TAC(SPECL [`i + &2:int`; `k:int`] (CONJUNCT1(CONJUNCT2(CONJUNCT2 MOI_S3TW_R)))) THEN
  MP_TAC(SPECL [`i + &1:int`; `k - &1:int`] (CONJUNCT1(CONJUNCT2(CONJUNCT2 MOI_S3TW_R)))) THEN
  MP_TAC(SPECL [`i + &1:int`; `i + &2:int`] (CONJUNCT1(CONJUNCT2 MOI_S3TW_R))) THEN
  ASM_REWRITE_TAC[INT_ARITH `i + &1 < i + &2:int`] THEN
  SUBGOAL_THEN `i + &1 <= k - &1:int` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Rectangles in the half plane: they are disks with their relative         *)
(* frontier as boundary (theta o emb of pc_moi_s32_chart maps the unit disk *)
(* onto the model square, then an affine map).                              *)
(* ------------------------------------------------------------------------- *)

let moi_s3tw_rect = new_definition
 `moi_s3tw_rect a b c =
    {x:real^3 | x$3 = &0 /\ a <= x$1 /\ x$1 <= b /\ abs(x$2) <= c}`;;

let moi_s3tw_aff = new_definition
 `moi_s3tw_aff a b c (y:real^3) =
    vector[(a + b) / &2 + (b - a) / &2 * y$1; c * y$3; &0]:real^3`;;

let moi_s3tw_pl = new_definition
 `moi_s3tw_pl (z:real^2) = vector[z$1; z$2; &0]:real^3`;;

let MOI_S3TW_EMB_DISK = prove
 (`IMAGE moi_s3ch_emb (cball(vec 0:real^2,&1)) = moi_s32_disk /\
   IMAGE moi_s3ch_emb (sphere(vec 0:real^2,&1)) = moi_s32_rim`,
  REWRITE_TAC[MOI_S3CH_EMB; MOI_S3CH_CYL_SETS; IN_CBALL_0; IN_SPHERE_0; EXTENSION;
              IN_ELIM_THM; moi_s3ch_rad; vector_norm; dot; DIMINDEX_2; SUM_2; VECTOR_2;
              BETA_THM; GSYM REAL_POW_2] THEN
  MESON_TAC[]);;

let MOI_S3TW_DISK_Q = prove
 (`?f g. homeomorphism (cball(vec 0:real^2,&1),moi_s3ch_q) (f,g) /\
         IMAGE f (sphere(vec 0:real^2,&1)) = moi_s3ch_rq`,
  MP_TAC(ISPECL [`cball(vec 0:real^2,&1)`; `moi_s3ch_theta o moi_s3ch_emb`;
                 `moi_s3ch_q`] HOMEOMORPHISM_COMPACT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COMPACT_CBALL; IMAGE_o; MOI_S3TW_EMB_DISK; MOI_S3CH_IMAGES] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[MOI_S3CH_EMB];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
        REWRITE_TAC[MOI_S3CH_THETA_CONT; SUBSET_UNIV]];
      REWRITE_TAC[o_THM] THEN MESON_TAC[MOI_S3CH_THETA_INJ; MOI_S3CH_EMB]];
    DISCH_THEN(X_CHOOSE_TAC `g:real^3->real^2`) THEN
    MAP_EVERY EXISTS_TAC [`moi_s3ch_theta o moi_s3ch_emb`; `g:real^3->real^2`] THEN
    ASM_REWRITE_TAC[IMAGE_o; MOI_S3TW_EMB_DISK; MOI_S3CH_IMAGES]]);;

let MOI_S3TW_PL = prove
 (`linear moi_s3tw_pl /\
   (!x y. moi_s3tw_pl x = moi_s3tw_pl y ==> x = y) /\
   (!s. IMAGE moi_s3tw_pl s = {y:real^3 | y$3 = &0 /\ (vector[y$1; y$2]:real^2) IN s}) /\
   (!s. relative_interior (IMAGE moi_s3tw_pl s) =
        IMAGE moi_s3tw_pl (relative_interior s))`,
  SUBGOAL_THEN `linear moi_s3tw_pl /\
                (!x y. moi_s3tw_pl x = moi_s3tw_pl y ==> x = y)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[linear; moi_s3tw_pl; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
                  VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC;
      REWRITE_TAC[moi_s3tw_pl; CART_EQ; DIMINDEX_3; DIMINDEX_2; FORALL_3; FORALL_2;
                  VECTOR_3] THEN MESON_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; moi_s3tw_pl] THEN
    X_GEN_TAC `s:real^2->bool` THEN X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[VECTOR_3] THEN
      SUBGOAL_THEN `vector[(z:real^2)$1; z$2]:real^2 = z` (fun th -> ASM_REWRITE_TAC[th]) THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2];
      STRIP_TAC THEN EXISTS_TAC `vector[(y:real^3)$1; y$2]:real^2` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_2] THEN
      ASM_REWRITE_TAC[]];
    GEN_TAC THEN MATCH_MP_TAC RELATIVE_INTERIOR_INJECTIVE_LINEAR_IMAGE THEN
    ASM_REWRITE_TAC[]]);;

let MOI_S3TW_RECT_FACTS = prove
 (`!a b c.
     a < b /\ &0 < c
     ==> moi_s3tw_rect a b c =
           IMAGE moi_s3tw_pl (interval[vector[a; --c],vector[b; c]]) /\
         relative_interior (moi_s3tw_rect a b c) =
           {x:real^3 | x$3 = &0 /\ a < x$1 /\ x$1 < b /\ abs(x$2) < c} /\
         compact (moi_s3tw_rect a b c) /\ convex (moi_s3tw_rect a b c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_s3tw_rect a b c =
                IMAGE moi_s3tw_pl (interval[vector[a; --c],vector[b; c]])` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S3TW_PL; moi_s3tw_rect; EXTENSION; IN_ELIM_THM; IN_INTERVAL;
                DIMINDEX_2; FORALL_2; VECTOR_2] THEN
    GEN_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MOI_S3TW_PL] THEN
    SUBGOAL_THEN `~(interior(interval[vector[a; --c],vector[b; c]]):real^2->bool = {})`
    ASSUME_TAC THENL
     [REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; INTERVAL_NE_EMPTY; DIMINDEX_2; FORALL_2;
                  VECTOR_2] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[RELATIVE_INTERIOR_NONEMPTY_INTERIOR; INTERIOR_CLOSED_INTERVAL] THEN
    REWRITE_TAC[MOI_S3TW_PL; EXTENSION; IN_ELIM_THM; IN_INTERVAL; DIMINDEX_2; FORALL_2;
                VECTOR_2] THEN
    GEN_TAC THEN REAL_ARITH_TAC;
    MATCH_MP_TAC COMPACT_LINEAR_IMAGE THEN REWRITE_TAC[MOI_S3TW_PL; COMPACT_INTERVAL];
    MATCH_MP_TAC CONVEX_LINEAR_IMAGE THEN REWRITE_TAC[MOI_S3TW_PL; CONVEX_INTERVAL]]);;

let MOI_S3TW_ABS_SCALE = prove
 (`!h t. &0 < h
         ==> (abs t <= &1 <=> abs(h * t) <= h) /\ (abs t < &1 <=> abs(h * t) < h) /\
             (abs t = &1 <=> abs(h * t) = h)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < h ==> abs h = h`] THEN
  MP_TAC(SPECL [`abs t`; `&1`; `h:real`] REAL_LE_LMUL_EQ) THEN
  MP_TAC(SPECL [`abs t`; `&1`; `h:real`] REAL_LT_LMUL_EQ) THEN
  MP_TAC(SPECL [`h:real`; `abs t`; `&1`] REAL_EQ_MUL_LCANCEL) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NZ; REAL_MUL_RID]);;

let MOI_S3TW_AFF = prove
 (`!a b c.
     a < b /\ &0 < c
     ==> IMAGE (moi_s3tw_aff a b c) moi_s3ch_q = moi_s3tw_rect a b c /\
         IMAGE (moi_s3tw_aff a b c) moi_s3ch_rq =
           moi_s3tw_rect a b c DIFF
           {x:real^3 | x$3 = &0 /\ a < x$1 /\ x$1 < b /\ abs(x$2) < c} /\
         (!x y. x IN moi_s3ch_q /\ y IN moi_s3ch_q /\
                moi_s3tw_aff a b c x = moi_s3tw_aff a b c y ==> x = y) /\
         moi_s3tw_aff a b c continuous_on (:real^3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `h = (b - a) / &2` THEN
  SUBGOAL_THEN `&0 < h /\ (a + b) / &2 - h = a /\ (a + b) / &2 + h = b` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^3. y$2 = &0
     ==> (moi_s3tw_aff a b c y IN moi_s3tw_rect a b c <=> moi_s3ch_sq y <= &1) /\
         (moi_s3tw_aff a b c y IN
            moi_s3tw_rect a b c DIFF
            {x:real^3 | x$3 = &0 /\ a < x$1 /\ x$1 < b /\ abs(x$2) < c} <=>
          moi_s3ch_sq y = &1)`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    REWRITE_TAC[moi_s3tw_aff; moi_s3tw_rect; moi_s3ch_sq; IN_DIFF; IN_ELIM_THM; VECTOR_3] THEN
    ASM_REWRITE_TAC[CONJ_ASSOC] THEN
    SUBGOAL_THEN `(a <= (a + b) / &2 + h * (y:real^3)$1 /\ (a + b) / &2 + h * y$1 <= b <=>
                   abs(h * y$1) <= h) /\
                  (a < (a + b) / &2 + h * (y:real^3)$1 /\ (a + b) / &2 + h * y$1 < b <=>
                   abs(h * y$1) < h)` (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `(a + b) / &2 - h = a` THEN UNDISCH_TAC `(a + b) / &2 + h = b` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`h:real`; `(y:real^3)$1`] MOI_S3TW_ABS_SCALE) THEN
    MP_TAC(SPECL [`c:real`; `(y:real^3)$3`] MOI_S3TW_ABS_SCALE) THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(DISCH_THEN(fun th -> REWRITE_TAC[GSYM th])) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^3. x IN moi_s3tw_rect a b c
     ==> ?y. y$2 = &0 /\ moi_s3tw_aff a b c y = x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN REWRITE_TAC[moi_s3tw_rect; IN_ELIM_THM] THEN STRIP_TAC THEN
    EXISTS_TAC `vector[((x:real^3)$1 - (a + b) / &2) / h; &0; (x:real^3)$2 / c]:real^3` THEN
    ASM_REWRITE_TAC[moi_s3tw_aff; VECTOR_3; CART_EQ; DIMINDEX_3; FORALL_3] THEN
    UNDISCH_TAC `&0 < h` THEN UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `(y:real^3) IN moi_s3ch_q` THEN
      REWRITE_TAC[moi_s3ch_q; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
      DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN EXISTS_TAC `y:real^3` THEN
      ASM_REWRITE_TAC[moi_s3ch_q; IN_ELIM_THM] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN ASM_SIMP_TAC[]];
    REWRITE_TAC[EXTENSION; IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `(y:real^3) IN moi_s3ch_rq` THEN
      REWRITE_TAC[moi_s3ch_rq; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
      DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3`) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN EXISTS_TAC `y:real^3` THEN
      ASM_REWRITE_TAC[moi_s3ch_rq; IN_ELIM_THM] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN ASM_SIMP_TAC[]];
    REWRITE_TAC[moi_s3ch_q; IN_ELIM_THM; moi_s3tw_aff; CART_EQ; DIMINDEX_3; FORALL_3;
                VECTOR_3] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~((b - a) / &2 = &0) /\ ~(c = &0)` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_EQ_ADD_LCANCEL; REAL_EQ_MUL_LCANCEL]) THEN
    ASM_MESON_TAC[];
    MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[CONTINUOUS_COMPONENTWISE_LIFT] THEN
    REWRITE_TAC[DIMINDEX_3; FORALL_3; moi_s3tw_aff; VECTOR_3; LIFT_ADD; LIFT_CMUL] THEN
    REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC CONTINUOUS_ADD THEN REWRITE_TAC[CONTINUOUS_CONST]) THEN
    TRY(MATCH_MP_TAC CONTINUOUS_CMUL) THEN
    REWRITE_TAC[CONTINUOUS_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_AT_LIFT_COMPONENT THEN REWRITE_TAC[DIMINDEX_3] THEN ARITH_TAC]);;

let MOI_S3TW_RECT_DISK = prove
 (`!a b c. a < b /\ &0 < c
           ==> disk_with_boundary (moi_s3tw_rect a b c)
                 (moi_s3tw_rect a b c DIFF relative_interior (moi_s3tw_rect a b c))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `relative_interior (moi_s3tw_rect a b c) =
                {x:real^3 | x$3 = &0 /\ a < x$1 /\ x$1 < b /\ abs(x$2) < c}`
  SUBST1_TAC THENL [ASM_MESON_TAC[MOI_S3TW_RECT_FACTS]; ALL_TAC] THEN
  MP_TAC(SPECL [`a:real`; `b:real`; `c:real`] MOI_S3TW_AFF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  X_CHOOSE_THEN `f0:real^2->real^3` (X_CHOOSE_THEN `g0:real^3->real^2` STRIP_ASSUME_TAC)
    MOI_S3TW_DISK_Q THEN
  SUBGOAL_THEN `?g1. homeomorphism (moi_s3ch_q,moi_s3tw_rect a b c)
                                   (moi_s3tw_aff a b c,g1)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPACT THEN ASM_REWRITE_TAC[MOI_S3CH_Q_FACTS] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[disk_with_boundary] THEN
  MAP_EVERY EXISTS_TAC [`moi_s3tw_aff a b c o (f0:real^2->real^3)`;
                        `(g0:real^3->real^2) o (g1:real^3->real^3)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `moi_s3ch_q` THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[IMAGE_o]]);;

(* ------------------------------------------------------------------------- *)
(* Revolution facts: intersections, compactness, the revolved rectangles,  *)
(* margins inside an open set, and the positive distance of a compact set  *)
(* missing the centre and the rim.                                           *)
(* ------------------------------------------------------------------------- *)

let MOI_S3TW_REV_INTER = prove
 (`!x y:real^3->bool. revolution x INTER revolution y = revolution (x INTER y)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER; revolution; IN_ELIM_THM] THEN
    X_GEN_TAC `p:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `q':real^3` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `q:real^3` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `q':real^3 = q` (fun th -> ASM_MESON_TAC[th]) THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_EQ THEN EXISTS_TAC `2` THEN ASM_REWRITE_TAC[ARITH];
    REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THEN MATCH_MP_TAC MOI_S3RV_REV_MONO THEN
    SET_TAC[]]);;

let MOI_S3TW_REV_COMPACT = prove
 (`!x:real^3->bool.
     compact x /\ x SUBSET {q:real^3 | q$3 = &0 /\ &0 < q$1}
     ==> compact (revolution x)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MOI_S3RV_REV_IMAGE] THEN
  MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
  ASM_SIMP_TAC[MOI_S3RV_ROT_CONTINUOUS; COMPACT_PCROSS; COMPACT_SPHERE]);;

let MOI_S3TW_REV_RECT = prove
 (`!a b c (p:real^3).
     &0 <= a
     ==> (p IN revolution (moi_s3tw_rect a b c) <=>
          a <= moi_s3ch_rad p /\ moi_s3ch_rad p <= b /\ abs(p$2) <= c)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[revolution; moi_s3tw_rect; IN_ELIM_THM] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(q:real^3)$1 = moi_s3ch_rad p` (fun th -> ASM_MESON_TAC[th]) THEN
    REWRITE_TAC[moi_s3ch_rad] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      try fst(dest_eq(concl th)) = `(q:real^3)$1 pow 2` with Failure _ -> false)) THEN
    ASM_SIMP_TAC[POW_2_SQRT];
    STRIP_TAC THEN EXISTS_TAC `vector[moi_s3ch_rad p; (p:real^3)$2; &0]:real^3` THEN
    ASM_REWRITE_TAC[VECTOR_3] THEN
    REWRITE_TAC[moi_s3ch_rad] THEN
    SIMP_TAC[SQRT_POS_LE; REAL_LE_ADD; REAL_LE_POW_2; SQRT_POW_2]]);;

(* The revolved rectangles are inside an open set containing the punctured *)
(* open disk, if they are thin enough.                                      *)

let MOI_S3TW_MARGIN = prove
 (`!v a b.
     open v /\ moi_s32_disk DIFF (vec 0 INSERT moi_s32_rim) SUBSET v /\
     &0 < a /\ a <= b /\ b < &1
     ==> ?d. &0 < d /\ !c. c <= d ==> revolution (moi_s3tw_rect a b c) SUBSET v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `compact (revolution (moi_s3tw_rect a b (&0)))` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3TW_REV_COMPACT THEN CONJ_TAC THENL
     [REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
       [REWRITE_TAC[BOUNDED_POS; moi_s3tw_rect; IN_ELIM_THM] THEN
        EXISTS_TAC `abs a + abs b + &1` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `sum(1..dimindex(:3)) (\i. abs((x:real^3)$i))` THEN
        REWRITE_TAC[NORM_LE_L1; DIMINDEX_3; SUM_3] THEN ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `moi_s3tw_rect a b (&0) =
                      {x:real^3 | x$3 = &0} INTER {x | a <= x$1} INTER {x | x$1 <= b} INTER
                      {x | x$2 = &0}` SUBST1_TAC THENL
         [REWRITE_TAC[moi_s3tw_rect; EXTENSION; IN_INTER; IN_ELIM_THM] THEN REAL_ARITH_TAC;
          ALL_TAC] THEN
        REPEAT(MATCH_MP_TAC CLOSED_INTER THEN CONJ_TAC) THEN
        REWRITE_TAC[CLOSED_STANDARD_HYPERPLANE; CLOSED_HALFSPACE_COMPONENT_LE;
                    CLOSED_HALFSPACE_COMPONENT_GE] THEN
        REWRITE_TAC[GSYM real_ge; CLOSED_HALFSPACE_COMPONENT_GE]];
      REWRITE_TAC[moi_s3tw_rect; SUBSET; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `revolution (moi_s3tw_rect a b (&0)) SUBSET (v:real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `p:real^3` THEN
    ASM_SIMP_TAC[MOI_S3TW_REV_RECT; REAL_LT_IMP_LE] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[MOI_S3CH_PDISK] THEN
    SUBGOAL_THEN `(p:real^3)$2 = &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM(CONJUNCT1(SPEC `p:real^3` MOI_S3CH_RAD_1))] THEN
      SUBGOAL_THEN `~(moi_s3ch_rad p = &1)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[MOI_S3CH_RAD_1] THEN
      MP_TAC(CONJUNCT1(SPEC `p:real^3` MOI_S3CH_RAD_1)) THEN
      SUBGOAL_THEN `moi_s3ch_rad p <= &1` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      DISCH_TAC THEN UNDISCH_TAC `a <= moi_s3ch_rad p` THEN
      ASM_REWRITE_TAC[moi_s3ch_rad; VEC_COMPONENT] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[SQRT_0] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`revolution (moi_s3tw_rect a b (&0))`; `(:real^3) DIFF v`]
    SEPARATE_COMPACT_CLOSED) THEN
  ASM_REWRITE_TAC[GSYM OPEN_CLOSED] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  X_GEN_TAC `c:real` THEN DISCH_TAC THEN REWRITE_TAC[SUBSET] THEN X_GEN_TAC `p:real^3` THEN
  ASM_SIMP_TAC[MOI_S3TW_REV_RECT; REAL_LT_IMP_LE] THEN STRIP_TAC THEN
  ABBREV_TAC `p' = vector[(p:real^3)$1; &0; p$3]:real^3` THEN
  SUBGOAL_THEN `(p':real^3) IN revolution (moi_s3tw_rect a b (&0)) /\
                dist(p',p) <= abs((p:real^3)$2)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_SIMP_TAC[MOI_S3TW_REV_RECT; REAL_LT_IMP_LE] THEN EXPAND_TAC "p'" THEN
      REWRITE_TAC[moi_s3ch_rad; VECTOR_3; REAL_ABS_NUM; REAL_LE_REFL] THEN
      REWRITE_TAC[GSYM moi_s3ch_rad] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "p'" THEN
    REWRITE_TAC[dist; vector_norm; dot; DIMINDEX_3; SUM_3; VECTOR_SUB_COMPONENT; VECTOR_3;
                BETA_THM] THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_LZERO; REAL_ADD_LID; REAL_ADD_RID; REAL_SUB_LZERO] THEN
    REWRITE_TAC[REAL_ARITH `--x * --x = x * x`; GSYM REAL_POW_2; POW_2_SQRT_ABS; REAL_LE_REFL];
    ALL_TAC] THEN
  ASM_CASES_TAC `(p:real^3) IN v` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p':real^3`; `p:real^3`]) THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
  UNDISCH_TAC `dist(p':real^3,p) <= abs((p:real^3)$2)` THEN
  UNDISCH_TAC `abs((p:real^3)$2) <= c` THEN UNDISCH_TAC `c <= d / &2` THEN
  UNDISCH_TAC `&0 < d` THEN REAL_ARITH_TAC);;

(* A compact set missing the centre and the rim stays a positive distance  *)
(* away from both, measured by rad + abs x2 and abs(1 - rad) + abs x2.      *)

let MOI_S3TW_AWAY = prove
 (`!c:real^3->bool.
     compact c /\ DISJOINT c (vec 0 INSERT moi_s32_rim)
     ==> ?m. &0 < m /\
             !p. p IN c ==> m <= moi_s3ch_rad p + abs(p$2) /\
                            m <= abs(&1 - moi_s3ch_rad p) + abs(p$2)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `c:real^3->bool = {}` THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(lift o (\p:real^3. moi_s3ch_rad p + abs(p$2))) continuous_on c /\
    (lift o (\p:real^3. abs(&1 - moi_s3ch_rad p) + abs(p$2))) continuous_on c`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MOI_S3CH_LIP_CONT THEN EXISTS_TAC `&2` THEN REWRITE_TAC[] THEN
    (CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC]) THEN
    MAP_EVERY X_GEN_TAC [`u:real^3`; `w:real^3`] THEN
    MP_TAC(SPECL [`u:real^3`; `w:real^3`] MOI_S3CH_RAD_LIP) THEN
    MP_TAC(ISPECL [`u - w:real^3`; `2`] COMPONENT_LE_NORM) THEN
    REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\p:real^3. moi_s3ch_rad p + abs(p$2)`; `c:real^3->bool`]
    CONTINUOUS_ATTAINS_INF) THEN
  ASM_REWRITE_TAC[BETA_THM] THEN DISCH_THEN(X_CHOOSE_THEN `x0:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`\p:real^3. abs(&1 - moi_s3ch_rad p) + abs(p$2)`; `c:real^3->bool`]
    CONTINUOUS_ATTAINS_INF) THEN
  ASM_REWRITE_TAC[BETA_THM] THEN DISCH_THEN(X_CHOOSE_THEN `x1:real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min (moi_s3ch_rad x0 + abs((x0:real^3)$2))
                  (abs(&1 - moi_s3ch_rad x1) + abs((x1:real^3)$2))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `~(moi_s3ch_rad x0 = &0 /\ (x0:real^3)$2 = &0)` MP_TAC THENL
       [STRIP_TAC THEN
        SUBGOAL_THEN `x0:real^3 = vec 0` ASSUME_TAC THENL
         [REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VEC_COMPONENT] THEN
          ASM_MESON_TAC[MOI_S3CH_RAD_SQ];
          ASM SET_TAC[]];
        MP_TAC(SPEC `x0:real^3` MOI_S3CH_RAD_SQ) THEN REAL_ARITH_TAC];
      SUBGOAL_THEN `~(moi_s3ch_rad x1 = &1 /\ (x1:real^3)$2 = &0)` MP_TAC THENL
       [STRIP_TAC THEN SUBGOAL_THEN `(x1:real^3) IN moi_s32_rim` ASSUME_TAC THENL
         [REWRITE_TAC[MOI_S3CH_CYL_SETS; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
          ASM SET_TAC[]];
        REAL_ARITH_TAC]];
    X_GEN_TAC `p:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:real^3`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:real^3`) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The stadium disks dd d i (rectangles around the segments [pp i,pp(i+1)]) *)
(* for a thickness function d with 0 < d i <= e i.                          *)
(* ------------------------------------------------------------------------- *)

let moi_s3tw_pp = new_definition
 `moi_s3tw_pp (i:int) = moi_s3tw_r i % basis 1:real^3`;;

let moi_s3tw_dd = new_definition
 `moi_s3tw_dd (d:int->real) (i:int) =
    moi_s3tw_rect (moi_s3tw_r i - moi_s3tw_e i) (moi_s3tw_r (i + &1) + moi_s3tw_e i) (d i)`;;

let MOI_S3TW_RECT_INTER = prove
 (`!a b c a' b' c'.
     moi_s3tw_rect a b c INTER moi_s3tw_rect a' b' c' =
     moi_s3tw_rect (max a a') (min b b') (min c c')`,
  REWRITE_TAC[moi_s3tw_rect; EXTENSION; IN_INTER; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

let MOI_S3TW_STADIUM = prove
 (`!v:real^3->bool.
     open v /\ moi_s32_disk DIFF (vec 0 INSERT moi_s32_rim) SUBSET v
     ==> ?d. !i. &0 < d i /\ d i <= moi_s3tw_e i /\ revolution (moi_s3tw_dd d i) SUBSET v`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_s3tw_dd] THEN
  REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `i:int` THEN
  MP_TAC(SPECL [`v:real^3->bool`; `moi_s3tw_r i - moi_s3tw_e i`;
                `moi_s3tw_r (i + &1) + moi_s3tw_e i`] MOI_S3TW_MARGIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `i:int` MOI_S3TW_E) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d0 (moi_s3tw_e i)` THEN
  ASM_SIMP_TAC[REAL_LT_MIN; MOI_S3TW_E; REAL_ARITH `min x y <= x /\ min x y <= y`]);;

let MOI_S3TW_DD_FACTS = prove
 (`!d. (!i. &0 < d i /\ d i <= moi_s3tw_e i)
       ==> (!i. moi_s3tw_dd d i SUBSET {q:real^3 | q$3 = &0 /\ &0 < q$1}) /\
           (!i. disk_with_boundary (moi_s3tw_dd d i)
                  (moi_s3tw_dd d i DIFF relative_interior (moi_s3tw_dd d i))) /\
           (!i. ~(moi_s3tw_pp i = moi_s3tw_pp (i + &1))) /\
           (!i. segment[moi_s3tw_pp i,moi_s3tw_pp (i + &1)] SUBSET
                relative_interior (moi_s3tw_dd d i)) /\
           (!i. ?jj. disk_with_boundary (moi_s3tw_dd d i INTER moi_s3tw_dd d (i + &1)) jj) /\
           (!i k. i + &2 <= k ==> DISJOINT (moi_s3tw_dd d i) (moi_s3tw_dd d k)) /\
           (!i. compact (moi_s3tw_dd d i))`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!i. moi_s3tw_r i - moi_s3tw_e i < moi_s3tw_r (i + &1) + moi_s3tw_e i`
  ASSUME_TAC THENL
   [GEN_TAC THEN MP_TAC(SPEC `i:int` MOI_S3TW_E) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[moi_s3tw_dd; moi_s3tw_rect; SUBSET; IN_ELIM_THM] THEN
    MP_TAC(SPEC `i:int` MOI_S3TW_E) THEN REAL_ARITH_TAC;
    GEN_TAC THEN REWRITE_TAC[moi_s3tw_dd] THEN MATCH_MP_TAC MOI_S3TW_RECT_DISK THEN
    ASM_REWRITE_TAC[];
    GEN_TAC THEN REWRITE_TAC[moi_s3tw_pp; VECTOR_MUL_RCANCEL] THEN
    SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH] THEN
    MP_TAC(SPEC `i:int` MOI_S3TW_E) THEN REAL_ARITH_TAC;
    GEN_TAC THEN REWRITE_TAC[moi_s3tw_dd] THEN
    MP_TAC(SPECL [`moi_s3tw_r i - moi_s3tw_e i`; `moi_s3tw_r (i + &1) + moi_s3tw_e i`;
                  `(d:int->real) i`] MOI_S3TW_RECT_FACTS) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[SUBSET; IN_SEGMENT; IN_ELIM_THM; moi_s3tw_pp] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID; REAL_MUL_RID; REAL_ABS_NUM] THEN
    MP_TAC(SPEC `i:int` MOI_S3TW_E) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:int` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `d:int->real`)) (concl th))) THEN
    MP_TAC(SPECL [`u:real`; `moi_s3tw_r (i + &1) - moi_s3tw_r i`] REAL_LE_MUL) THEN
    MP_TAC(SPECL [`&1 - u:real`; `moi_s3tw_r (i + &1) - moi_s3tw_r i`] REAL_LE_MUL) THEN
    ASM_REAL_ARITH_TAC;
    GEN_TAC THEN REWRITE_TAC[moi_s3tw_dd; MOI_S3TW_RECT_INTER] THEN
    EXISTS_TAC `moi_s3tw_rect
                 (max (moi_s3tw_r i - moi_s3tw_e i)
                      (moi_s3tw_r (i + &1) - moi_s3tw_e (i + &1)))
                 (min (moi_s3tw_r (i + &1) + moi_s3tw_e i)
                      (moi_s3tw_r ((i + &1) + &1) + moi_s3tw_e (i + &1)))
                 (min ((d:int->real) i) (d (i + &1))) DIFF
               relative_interior
                (moi_s3tw_rect
                 (max (moi_s3tw_r i - moi_s3tw_e i)
                      (moi_s3tw_r (i + &1) - moi_s3tw_e (i + &1)))
                 (min (moi_s3tw_r (i + &1) + moi_s3tw_e i)
                      (moi_s3tw_r ((i + &1) + &1) + moi_s3tw_e (i + &1)))
                 (min (d i) (d (i + &1))))` THEN
    MATCH_MP_TAC MOI_S3TW_RECT_DISK THEN
    MP_TAC(SPEC `i:int` MOI_S3TW_E) THEN MP_TAC(SPEC `i + &1:int` MOI_S3TW_E) THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:int` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `d:int->real`)) (concl th))) THEN
    FIRST_ASSUM(MP_TAC o SPEC `i + &1:int` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `d:int->real`)) (concl th))) THEN
    REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s3tw_dd; MOI_S3TW_RECT_INTER] THEN
    REWRITE_TAC[DISJOINT; EXTENSION; NOT_IN_EMPTY; moi_s3tw_rect; IN_ELIM_THM; IN_INTER] THEN
    MP_TAC(SPECL [`i:int`; `k:int`] MOI_S3TW_E_SEP) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    GEN_TAC THEN REWRITE_TAC[moi_s3tw_dd] THEN
    MP_TAC(SPECL [`moi_s3tw_r i - moi_s3tw_e i`; `moi_s3tw_r (i + &1) + moi_s3tw_e i`;
                  `(d:int->real) i`] MOI_S3TW_RECT_FACTS) THEN
    ASM_SIMP_TAC[]]);;

(* Local finiteness: a compact set missing the centre and the rim meets     *)
(* only finitely many revolved stadium disks.                                *)

let MOI_S3TW_LOCFIN = prove
 (`!d c. (!i. &0 < d i /\ d i <= moi_s3tw_e i) /\
         compact c /\ DISJOINT c (vec 0 INSERT moi_s32_rim)
         ==> FINITE {i:int | ~(revolution (moi_s3tw_dd d i) INTER c = {})}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `c:real^3->bool` MOI_S3TW_AWAY) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `m:real` (CONJUNCT2(CONJUNCT2(CONJUNCT2 MOI_S3TW_R)))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `n1:int`) (X_CHOOSE_TAC `n2:int`)) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{i:int | n1 - &2 < i /\ i < n2 + &2}` THEN
  REWRITE_TAC[FINITE_INT_SEG] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  X_GEN_TAC `i:int` THEN DISCH_THEN(X_CHOOSE_THEN `p:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_s3tw_r i - moi_s3tw_e i <= moi_s3ch_rad p /\
                moi_s3ch_rad p <= moi_s3tw_r (i + &1) + moi_s3tw_e i /\
                abs((p:real^3)$2) <= moi_s3tw_e i` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(p:real^3) IN revolution (moi_s3tw_dd d i)` THEN
    REWRITE_TAC[moi_s3tw_dd] THEN
    MP_TAC(SPEC `i:int` MOI_S3TW_E) THEN STRIP_TAC THEN
    ASM_SIMP_TAC[MOI_S3TW_REV_RECT; REAL_LT_IMP_LE] THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:int` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `d:int->real`)) (concl th))) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p:real^3` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `m:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `i:int` MOI_S3TW_E) THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM INT_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`i + &2:int`; `n1:int`] (CONJUNCT1(CONJUNCT2(CONJUNCT2 MOI_S3TW_R)))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[GSYM INT_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`n2:int`; `i - &1:int`] (CONJUNCT1(CONJUNCT2(CONJUNCT2 MOI_S3TW_R)))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* A PL solid torus for every index, from 31.1 applied to the triple         *)
(* (dd i, dd (i+1), dd (i+2)) (its first torus).                             *)
(* ------------------------------------------------------------------------- *)

let MOI_S3TW_MODEL_SUB = prove
 (`!(g:real^3->real^3) v s.
     moi_s32_model g v /\ s SUBSET v
     ==> g continuous_on s /\ (!x y. x IN s /\ y IN s /\ g x = g y ==> x = y) /\
         s SUBSET moi_s32_cyl`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s32_model] THEN STRIP_TAC THEN
  SUBGOAL_THEN `s SUBSET moi_s32_cyl` ASSUME_TAC THENL
   [MP_TAC(ISPEC `moi_s32_cyl` INTERIOR_SUBSET) THEN ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s32_cyl` THEN ASM_REWRITE_TAC[];
    ASM SET_TAC[]]);;

let MOI_S3TW_TRIPLE = prove
 (`!(g:real^3->real^3) v d i.
     moi_s32_model g v /\ (!i. &0 < d i /\ d i <= moi_s3tw_e i) /\
     (!i. revolution (moi_s3tw_dd d i) SUBSET v)
     ==> planar_cell_chain (\k. moi_s3tw_pp (i + &k)) (\k. moi_s3tw_dd d (i + &k)) /\
         g continuous_on UNIONS {revolution ((\k. moi_s3tw_dd d (i + &k)) j) | j < 3} /\
         (!x y. x IN UNIONS {revolution ((\k. moi_s3tw_dd d (i + &k)) j) | j < 3} /\
                y IN UNIONS {revolution ((\k. moi_s3tw_dd d (i + &k)) j) | j < 3} /\
                g x = g y ==> x = y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `d:int->real` MOI_S3TW_DD_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `UNIONS {revolution ((\k. moi_s3tw_dd d (i + &k)) j) | j < 3} SUBSET
                (v:real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`;
                 `UNIONS {revolution ((\k. moi_s3tw_dd d (i + &k)) j) | j < 3}`]
    MOI_S3TW_MODEL_SUB) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[planar_cell_chain; GSYM INT_OF_NUM_ADD; INT_ADD_ASSOC] THEN
  ASM_REWRITE_TAC[INT_ADD_RID] THEN
  MP_TAC(SPECL [`i:int`; `i + &2:int`] (ASSUME
   `!i k. i + &2 <= k ==> DISJOINT (moi_s3tw_dd d i) (moi_s3tw_dd d k)`)) THEN
  REWRITE_TAC[INT_LE_REFL; DISJOINT]);;

let MOI_S3TW_TORI = prove
 (mk_imp(`MOISE_311_STATEMENT`,
  `!(g:real^3->real^3) v d.
     moi_s32_model g v /\ (!i. &0 < d i /\ d i <= moi_s3tw_e i) /\
     (!i. revolution (moi_s3tw_dd d i) SUBSET v)
     ==> ?S. !i. pl_solid_torus (S i) /\
                 IMAGE g (revolution (segment[moi_s3tw_pp i,moi_s3tw_pp (i + &1)]))
                 SUBSET interior (S i) /\
                 S i SUBSET interior (IMAGE g (revolution (moi_s3tw_dd d i)))`),
  REWRITE_TAC[MOISE_311_STATEMENT] THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `i:int` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`\k:num. moi_s3tw_pp (i + &k)`;
                                `\k:num. moi_s3tw_dd d (i + &k)`; `g:real^3->real^3`]) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC MOI_S3TW_TRIPLE THEN EXISTS_TAC `v:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:num->real^3->bool` MP_TAC) THEN
  REWRITE_TAC[canonical_configuration] THEN
  DISCH_THEN(MP_TAC o SPEC `0` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[INT_ADD_RID] THEN
  DISCH_TAC THEN EXISTS_TAC `(s2:num->real^3->bool) 0` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The even tori are moved by the RECROSS consequent so that their          *)
(* boundaries cross those of their odd neighbours (both orders).           *)
(* ------------------------------------------------------------------------- *)

let MOI_S3TW_PARITY = prove
 (`!m:int. &2 divides (m + &1) <=> ~(&2 divides m)`,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(&2:int) divides &1` MP_TAC THENL
     [UNDISCH_TAC `(&2:int) divides m` THEN UNDISCH_TAC `(&2:int) divides (m + &1)` THEN
      REWRITE_TAC[int_divides] THEN
      DISCH_THEN(X_CHOOSE_TAC `x:int`) THEN DISCH_THEN(X_CHOOSE_TAC `y:int`) THEN
      EXISTS_TAC `x - y:int` THEN ASM_ARITH_TAC;
      DISCH_THEN(MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN INT_ARITH_TAC];
    REWRITE_TAC[GSYM(CONJUNCT2 INT_REM_2_DIVIDES)] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`m:int`; `&2:int`] INT_DIVISION) THEN
    ASM_REWRITE_TAC[INT_OF_NUM_EQ; ARITH_EQ] THEN STRIP_TAC THEN
    REWRITE_TAC[int_divides] THEN EXISTS_TAC `m div &2 + &1` THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [ASSUME `m = m div &2 * &2 + &1`] THEN
    INT_ARITH_TAC]);;

let MOI_S3TW_FR_SUBSET = prove
 (`!(g:real^3->real^3) v s x.
     moi_s32_model g v /\ x SUBSET v /\ compact x /\
     s SUBSET interior (IMAGE g x)
     ==> frontier s SUBSET IMAGE g x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `closed (IMAGE (g:real^3->real^3) x)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_MESON_TAC[MOI_S3TW_MODEL_SUB];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `closure (s:real^3->bool)` THEN
  REWRITE_TAC[frontier; SUBSET_DIFF] THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
  ASM_REWRITE_TAC[] THEN MP_TAC(ISPEC `IMAGE (g:real^3->real^3) x` INTERIOR_SUBSET) THEN
  ASM SET_TAC[]);;

let MOI_S3TW_CROSSED = prove
 (mk_imp(moi_std_csq MOI_S31_RECROSS,
  `!(g:real^3->real^3) v d S.
     moi_s32_model g v /\ (!i. &0 < d i /\ d i <= moi_s3tw_e i) /\
     (!i. revolution (moi_s3tw_dd d i) SUBSET v) /\
     (!i. pl_solid_torus (S i) /\
          IMAGE g (revolution (segment[moi_s3tw_pp i,moi_s3tw_pp (i + &1)]))
          SUBSET interior (S i) /\
          S i SUBSET interior (IMAGE g (revolution (moi_s3tw_dd d i))))
     ==> ?s2. (!i. pl_solid_torus (s2 i) /\
                   IMAGE g (revolution (segment[moi_s3tw_pp i,moi_s3tw_pp (i + &1)]))
                   SUBSET interior (s2 i) /\
                   s2 i SUBSET interior (IMAGE g (revolution (moi_s3tw_dd d i)))) /\
              (!i x. x IN frontier (s2 i) INTER frontier (s2 (i + &1))
                     ==> pl_crossing_at (frontier (s2 i)) (frontier (s2 (i + &1))) x)`),
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `d:int->real` MOI_S3TW_DD_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. compact (revolution (moi_s3tw_dd d i)) /\
        compact (IMAGE (g:real^3->real^3) (revolution (moi_s3tw_dd d i))) /\
        compact (IMAGE g (revolution (segment[moi_s3tw_pp i,moi_s3tw_pp (i + &1)])))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN `compact (revolution (moi_s3tw_dd d i))` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_S3TW_REV_COMPACT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THENL
     [ASM_MESON_TAC[MOI_S3TW_MODEL_SUB]; ALL_TAC] THEN
    SUBGOAL_THEN `segment[moi_s3tw_pp i,moi_s3tw_pp (i + &1)] SUBSET moi_s3tw_dd d i`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `relative_interior (moi_s3tw_dd d i)` THEN
      ASM_REWRITE_TAC[RELATIVE_INTERIOR_SUBSET];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `revolution (moi_s3tw_dd d i)` THEN
      ASM_SIMP_TAC[MOI_S3RV_REV_MONO] THEN ASM_MESON_TAC[MOI_S3TW_MODEL_SUB];
      MATCH_MP_TAC MOI_S3TW_REV_COMPACT THEN REWRITE_TAC[COMPACT_SEGMENT] THEN
      ASM_MESON_TAC[SUBSET_TRANS]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. ?t. pl_solid_torus t /\
            IMAGE (g:real^3->real^3)
              (revolution (segment[moi_s3tw_pp m,moi_s3tw_pp (m + &1)]))
            SUBSET interior t /\
            t SUBSET interior (IMAGE g (revolution (moi_s3tw_dd d m))) /\
            (!u x. u IN {frontier (S (m - &1)),frontier (S (m + &1))} /\
                   x IN frontier t INTER u
                   ==> pl_crossing_at (frontier t) u x /\ pl_crossing_at u (frontier t) x)`
  MP_TAC THENL
   [X_GEN_TAC `m:int` THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `(S:int->real^3->bool) m` THEN ASM_REWRITE_TAC[OPEN_INTERIOR] THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
    REPEAT CONJ_TAC THENL
     [EXISTS_TAC `(S:int->real^3->bool) (m - &1)` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `(S:int->real^3->bool) (m + &1)` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[PAIRWISE_INSERT; PAIRWISE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
      SUBGOAL_THEN `DISJOINT (frontier ((S:int->real^3->bool) (m - &1)))
                             (frontier (S (m + &1)))` MP_TAC THENL
       [MATCH_MP_TAC(SET_RULE `!(a:real^3->bool) b c d.
           a SUBSET c /\ b SUBSET d /\ DISJOINT c d ==> DISJOINT a b`) THEN
        MAP_EVERY EXISTS_TAC
         [`IMAGE (g:real^3->real^3) (revolution (moi_s3tw_dd d (m - &1)))`;
          `IMAGE (g:real^3->real^3) (revolution (moi_s3tw_dd d (m + &1)))`] THEN
        REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC MOI_S3TW_FR_SUBSET THEN EXISTS_TAC `v:real^3->bool` THEN
          ASM_REWRITE_TAC[];
          MATCH_MP_TAC MOI_S3TW_FR_SUBSET THEN EXISTS_TAC `v:real^3->bool` THEN
          ASM_REWRITE_TAC[];
          MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`;
            `revolution (moi_s3tw_dd d (m - &1)) UNION revolution (moi_s3tw_dd d (m + &1))`]
            MOI_S3TW_MODEL_SUB) THEN
          ASM_REWRITE_TAC[UNION_SUBSET] THEN STRIP_TAC THEN
          SUBGOAL_THEN `revolution (moi_s3tw_dd d (m - &1)) INTER
                        revolution (moi_s3tw_dd d (m + &1)) = {}` MP_TAC THENL
           [REWRITE_TAC[MOI_S3TW_REV_INTER] THEN
            SUBGOAL_THEN `moi_s3tw_dd d (m - &1) INTER moi_s3tw_dd d (m + &1) = {}`
            SUBST1_TAC THENL
             [REWRITE_TAC[GSYM DISJOINT] THEN FIRST_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
              REWRITE_TAC[revolution; NOT_IN_EMPTY; EMPTY_GSPEC]];
            ALL_TAC] THEN
          UNDISCH_TAC `!x y. x IN revolution (moi_s3tw_dd d (m - &1)) UNION
                             revolution (moi_s3tw_dd d (m + &1)) /\
                             y IN revolution (moi_s3tw_dd d (m - &1)) UNION
                             revolution (moi_s3tw_dd d (m + &1)) /\
                             (g:real^3->real^3) x = g y ==> x = y` THEN
          SET_TAC[]];
        SET_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `tt:int->real^3->bool`) THEN
  EXISTS_TAC `\m. if &2 divides m then (tt:int->real^3->bool) m else S m` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:int`; `x:real^3`] THEN
  REWRITE_TAC[MOI_S3TW_PARITY] THEN ASM_CASES_TAC `(&2:int) divides i` THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[IN_INTER]) THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `i:int` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `tt:int->real^3->bool`)) (concl th))) THEN
    DISCH_THEN(MP_TAC o SPECL [`frontier ((S:int->real^3->bool) (i + &1))`; `x:real^3`] o
               CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[IN_INSERT; IN_INTER] THEN SIMP_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `i + &1:int` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `tt:int->real^3->bool`)) (concl th))) THEN
    DISCH_THEN(MP_TAC o SPECL [`frontier ((S:int->real^3->bool) i)`; `x:real^3`] o
               CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[INT_ARITH `(i + &1) - &1 = i:int`; IN_INSERT] THEN
    ASM_REWRITE_TAC[IN_INTER] THEN SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The theorem TOWER.                                                         *)
(* ------------------------------------------------------------------------- *)

let TOWER = prove
 (MOI_S32_TOWER,
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `open (v:real^3->bool) /\
                moi_s32_disk DIFF (vec 0 INSERT moi_s32_rim) SUBSET v`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[moi_s32_model]; ALL_TAC] THEN
  MP_TAC(SPEC `v:real^3->bool` MOI_S3TW_STADIUM) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `d:int->real`) THEN
  SUBGOAL_THEN `(!i. &0 < d i /\ d i <= moi_s3tw_e i) /\
                (!i. revolution (moi_s3tw_dd d i) SUBSET (v:real^3->bool))`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`g:real^3->real^3`; `v:real^3->bool`; `d:int->real`]
    (UNDISCH MOI_S3TW_TORI)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `S:int->real^3->bool`) THEN
  MP_TAC(SPECL [`g:real^3->real^3`; `v:real^3->bool`; `d:int->real`;
                `S:int->real^3->bool`] (UNDISCH MOI_S3TW_CROSSED)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:int->real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `d:int->real` MOI_S3TW_DD_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`moi_s3tw_pp`; `moi_s3tw_dd d`; `s2:int->real^3->bool`] THEN
  REWRITE_TAC[moi_s32_tower] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i:int` THEN
    MP_TAC(SPECL [`g:real^3->real^3`; `v:real^3->bool`; `d:int->real`; `i:int`]
      MOI_S3TW_TRIPLE) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[canonical_configuration; BETA_THM] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_ADD; INT_ADD_ASSOC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
    X_GEN_TAC `i:int` THEN EXISTS_TAC `moi_s3tw_r i` THEN
    REWRITE_TAC[moi_s3tw_pp; MOI_S3TW_R];
    X_GEN_TAC `i:int` THEN REWRITE_TAC[moi_s3tw_pp; VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
    MATCH_MP_TAC(CONJUNCT1(CONJUNCT2 MOI_S3TW_R)) THEN INT_ARITH_TAC;
    REWRITE_TAC[moi_s3tw_pp; VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
    REWRITE_TAC[MOI_S3TW_R];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S3TW_LOCFIN THEN ASM_REWRITE_TAC[]]);;


needs "src/pc_moi_loop_stmt.ml";;
needs "src/pc_moi_fnd_m3b.ml";;
needs "src/pc_moi_fnd_collar.ml";;
needs "src/pc_moi_fnd_sapprox.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* pc_moi_lt_fill: Moise GTM 47 p.183 (Theorem 2 from Theorem 1) and p.187: *)
(* a null-homotopic loop in a boundary component b of a finite combinatorial *)
(* 3-manifold with boundary c is homotopic in b to the boundary loop of a    *)
(* proper simplicial map of a triangulation of std_triangle into sd(c)       *)
(* (the statement MOI_LT_FILL of pc_moi_loop_stmt).                          *)
(* Route:                                                                   *)
(*   A. the domain: the frontier polygon, the cone from the barycentre, and *)
(*      each sector split into an inner triangle and two ring triangles;    *)
(*      the ring map is simplicial, the inner triangle carries a filling   *)
(*      off the boundary; a mixed simplicial approximation (vertex choices *)
(*      from the ring map near the frontier, Lebesgue choices elsewhere)    *)
(*      is proper;                                                          *)
(*   B. collar data: a simplicial approximation of the loop in the boundary *)
(*      surface, moved onto the dual graph (vertex links are circles) and  *)
(*      pushed inwards across the books of the boundary edges (arcs);       *)
(*   C. loops off the boundary that are null-homotopic in |c| are null-     *)
(*      homotopic off the boundary (collar push), and fill by Borsuk.      *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* 1. The boundary loop of std_triangle: explicit pieces, simple path, and   *)
(* its 4m equally spaced parameter points.                                   *)
(* ------------------------------------------------------------------------- *)

let MOI_LFI_LOOP_FORMULA = prove
 (`!t. std_triangle_loop t =
       if drop t <= &1 / &2 then (&2 * drop t) % basis 1:real^2
       else if drop t <= &3 / &4
            then (&3 - &4 * drop t) % basis 1 + (&4 * drop t - &2) % basis 2
       else (&4 - &4 * drop t) % basis 2`,
  GEN_TAC THEN REWRITE_TAC[std_triangle_loop; joinpaths; linepath] THEN
  BETA_TAC THEN REWRITE_TAC[DROP_SUB; DROP_CMUL; DROP_VEC] THEN
  ASM_CASES_TAC `drop t <= &1 / &2` THEN ASM_REWRITE_TAC[] THENL
   [VECTOR_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `drop t <= &3 / &4` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `&2 * drop t - &1 <= &1 / &2` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC];
    SUBGOAL_THEN `~(&2 * drop t - &1 <= &1 / &2)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC]]);;

let MOI_LFI_LOOP_PIECE1 = prove
 (`!t. &0 <= drop t /\ drop t <= &1 / &2
       ==> std_triangle_loop t = (&2 * drop t) % basis 1:real^2`,
  SIMP_TAC[MOI_LFI_LOOP_FORMULA]);;

let MOI_LFI_LOOP_PIECE2 = prove
 (`!t. &1 / &2 <= drop t /\ drop t <= &3 / &4
       ==> std_triangle_loop t =
           (&3 - &4 * drop t) % basis 1 + (&4 * drop t - &2) % basis 2:real^2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MOI_LFI_LOOP_FORMULA] THEN
  ASM_CASES_TAC `drop t <= &1 / &2` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `drop t = &1 / &2` SUBST1_TAC THENL
   [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC]);;

let MOI_LFI_LOOP_PIECE3 = prove
 (`!t. &3 / &4 <= drop t
       ==> std_triangle_loop t = (&4 - &4 * drop t) % basis 2:real^2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MOI_LFI_LOOP_FORMULA] THEN
  SUBGOAL_THEN `~(drop t <= &1 / &2)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `drop t <= &3 / &4` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `drop t = &3 / &4` SUBST1_TAC THENL
   [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC]);;

let MOI_LFI_SIDE1 = prove
 (`segment[vec 0:real^2,basis 1] = {x | x$2 = &0 /\ &0 <= x$1 /\ x$1 <= &1}`,
  REWRITE_TAC[EXTENSION; IN_SEGMENT; IN_ELIM_THM] THEN X_GEN_TAC `x:real^2` THEN
  SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT;
           VECTOR_MUL_COMPONENT; VEC_COMPONENT; BASIS_COMPONENT; ARITH] THEN
  EQ_TAC THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC THEN EXISTS_TAC `(x:real^2)$1` THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC]);;

let MOI_LFI_SIDE2 = prove
 (`segment[basis 1:real^2,basis 2] =
   {x | x$1 + x$2 = &1 /\ &0 <= x$1 /\ &0 <= x$2}`,
  REWRITE_TAC[EXTENSION; IN_SEGMENT; IN_ELIM_THM] THEN X_GEN_TAC `x:real^2` THEN
  SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT;
           VECTOR_MUL_COMPONENT; VEC_COMPONENT; BASIS_COMPONENT; ARITH] THEN
  EQ_TAC THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC THEN EXISTS_TAC `(x:real^2)$2` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

let MOI_LFI_SIDE3 = prove
 (`segment[basis 2:real^2,vec 0] = {x | x$1 = &0 /\ &0 <= x$2 /\ x$2 <= &1}`,
  REWRITE_TAC[EXTENSION; IN_SEGMENT; IN_ELIM_THM] THEN X_GEN_TAC `x:real^2` THEN
  SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT;
           VECTOR_MUL_COMPONENT; VEC_COMPONENT; BASIS_COMPONENT; ARITH] THEN
  EQ_TAC THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC THEN EXISTS_TAC `&1 - (x:real^2)$2` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

let MOI_LFI_BASIS_DISTINCT = prove
 (`~(vec 0:real^2 = basis 1) /\ ~(basis 1:real^2 = basis 2) /\
   ~(basis 2:real^2 = vec 0)`,
  SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VEC_COMPONENT; BASIS_COMPONENT;
           ARITH] THEN REAL_ARITH_TAC);;

let MOI_LFI_LOOP_SIMPLE = prove
 (`simple_path std_triangle_loop`,
  REWRITE_TAC[std_triangle_loop] THEN MATCH_MP_TAC SIMPLE_PATH_JOIN_LOOP THEN
  SIMP_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH;
           PATHFINISH_LINEPATH; PATH_IMAGE_JOIN; PATH_IMAGE_LINEPATH] THEN
  REWRITE_TAC[ARC_LINEPATH_EQ; MOI_LFI_BASIS_DISTINCT] THEN CONJ_TAC THENL
   [MATCH_MP_TAC ARC_JOIN THEN
    REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH; PATH_IMAGE_LINEPATH;
                ARC_LINEPATH_EQ; MOI_LFI_BASIS_DISTINCT] THEN
    REWRITE_TAC[MOI_LFI_SIDE2; MOI_LFI_SIDE3; SUBSET; IN_INTER; IN_ELIM_THM;
                IN_SING] THEN
    X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
    SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; BASIS_COMPONENT; ARITH] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[MOI_LFI_SIDE1; MOI_LFI_SIDE2; MOI_LFI_SIDE3; SUBSET; IN_INTER;
                IN_UNION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    X_GEN_TAC `x:real^2` THEN STRIP_TAC THENL
     [DISJ2_TAC; DISJ1_TAC] THEN
    SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; BASIS_COMPONENT; VEC_COMPONENT;
             ARITH] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 2. The frontier vertices x_j = loop(j / 4m) and the loop between them.    *)
(* ------------------------------------------------------------------------- *)

let moi_lfi_x = new_definition
 `moi_lfi_x m j = std_triangle_loop(lift(&(j MOD (4 * m)) / &(4 * m)))`;;

let MOI_LFI_AFFINE_ON_INTERVAL = prove
 (`!(f:real->real^2) c v a b t.
     (!r. a <= r /\ r <= b ==> f r = c + r % v) /\ a < b /\ a <= t /\ t <= b
     ==> f t = (&1 - (t - a) / (b - a)) % f a + ((t - a) / (b - a)) % f b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(f:real->real^2) t = c + t % v /\ f a = c + a % v /\
                f b = c + b % v` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VECTOR_ARITH
   `(&1 - s) % (c + a % v) + s % (c + b % v) = c + ((&1 - s) * a + s * b) % v`] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `a < b` THEN CONV_TAC REAL_FIELD);;

let MOI_LFI_LOOP_LIFT_PIECES = prove
 (`(!r. &0 <= r /\ r <= &1 / &2
        ==> std_triangle_loop(lift r) = vec 0 + r % (&2 % basis 1:real^2)) /\
   (!r. &1 / &2 <= r /\ r <= &3 / &4
        ==> std_triangle_loop(lift r) =
            (&3 % basis 1 - &2 % basis 2) + r % (&4 % basis 2 - &4 % basis 1:real^2)) /\
   (!r. &3 / &4 <= r /\ r <= &1
        ==> std_triangle_loop(lift r) = &4 % basis 2 + r % (-- &4 % basis 2:real^2))`,
  REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [MP_TAC(SPEC `lift r` MOI_LFI_LOOP_PIECE1);
    MP_TAC(SPEC `lift r` MOI_LFI_LOOP_PIECE2);
    MP_TAC(SPEC `lift r` MOI_LFI_LOOP_PIECE3)] THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC);;

let MOI_LFI_X_LOOP = prove
 (`!m j. 1 <= m /\ j <= 4 * m
         ==> moi_lfi_x m j = std_triangle_loop(lift(&j / &(4 * m)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_lfi_x] THEN
  ASM_CASES_TAC `j = 4 * m` THENL
   [SUBGOAL_THEN `~(4 * m = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[MOD_REFL] THEN
    SUBGOAL_THEN `&0 / &(4 * m) = &0 /\ &(4 * m) / &(4 * m) = &1`
      (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THENL [REWRITE_TAC[real_div; REAL_MUL_LZERO]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_DIV_REFL THEN ASM_REWRITE_TAC[REAL_OF_NUM_EQ];
      ALL_TAC] THEN
    MP_TAC(SPEC `lift(&0)` MOI_LFI_LOOP_PIECE1) THEN
    MP_TAC(SPEC `lift(&1)` MOI_LFI_LOOP_PIECE3) THEN
    REWRITE_TAC[LIFT_DROP] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REPEAT(DISCH_THEN SUBST1_TAC) THEN VECTOR_ARITH_TAC;
    SUBGOAL_THEN `j MOD (4 * m) = j` (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC]);;

let MOI_LFI_LOOP_AFFINE = prove
 (`!m j t. 1 <= m /\ j < 4 * m /\
           &j / &(4 * m) <= drop t /\ drop t <= &(j + 1) / &(4 * m)
           ==> std_triangle_loop t =
               (&1 - (&(4 * m) * drop t - &j)) % moi_lfi_x m j +
               (&(4 * m) * drop t - &j) % moi_lfi_x m (j + 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &(4 * m)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_LFI_X_LOOP; LT_IMP_LE; ARITH_RULE `j < n ==> j + 1 <= n`] THEN
  SUBGOAL_THEN
   `&(4 * m) * drop t - &j =
    (drop t - &j / &(4 * m)) / (&(j + 1) / &(4 * m) - &j / &(4 * m))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    UNDISCH_TAC `&0 < &(4 * m)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM(CONJUNCT1 LIFT_DROP)] THEN
  MATCH_MP_TAC(BETA_RULE(ISPEC `\r. std_triangle_loop(lift r)`
    MOI_LFI_AFFINE_ON_INTERVAL)) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&j / &(4 * m) < &(j + 1) / &(4 * m)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV2_EQ; REAL_OF_NUM_LT] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= &j / &(4 * m) /\ &(j + 1) / &(4 * m) <= &1`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LE_LDIV_EQ; REAL_MUL_LID;
                 REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!a b. &a / &(4 * m) <= &b / &4 <=> &4 * &a <= &b * &(4 * m)) /\
    (!a b. &b / &4 <= &a / &(4 * m) <=> &b * &(4 * m) <= &4 * &a)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT GEN_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LDIV_EQ]; ASM_SIMP_TAC[REAL_LE_RDIV_EQ]] THEN
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `j + 1 <= 2 * m` THENL
   [MAP_EVERY EXISTS_TAC [`vec 0:real^2`; `&2 % basis 1:real^2`] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(CONJUNCT1 MOI_LFI_LOOP_LIFT_PIECES) THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&(j + 1) / &(4 * m)` THEN
    ASM_REWRITE_TAC[REAL_ARITH `&1 / &2 = &2 / &4`] THEN
    UNDISCH_TAC `j + 1 <= 2 * m` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_ADD;
                GSYM REAL_OF_NUM_MUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `j + 1 <= 3 * m` THENL
   [MAP_EVERY EXISTS_TAC [`&3 % basis 1 - &2 % basis 2:real^2`;
                          `&4 % basis 2 - &4 % basis 1:real^2`] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(CONJUNCT1(CONJUNCT2 MOI_LFI_LOOP_LIFT_PIECES)) THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `&j / &(4 * m)` THEN
      ASM_REWRITE_TAC[REAL_ARITH `&1 / &2 = &2 / &4`] THEN
      SUBGOAL_THEN `2 * m <= j` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC];
      EXISTS_TAC `&(j + 1) / &(4 * m)` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `j + 1 <= 3 * m`] THEN
    REWRITE_TAC[NOT_LE; GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_LT;
                GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`&4 % basis 2:real^2`; `-- &4 % basis 2:real^2`] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(CONJUNCT2(CONJUNCT2 MOI_LFI_LOOP_LIFT_PIECES)) THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&j / &(4 * m)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `3 * m <= j` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[NOT_LE; GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_LT;
              GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 3. The frontier polygon complex with 4m edges.                            *)
(* ------------------------------------------------------------------------- *)

let MOI_LFI_X_PERIODIC = prove
 (`!m j. moi_lfi_x m (j + 4 * m) = moi_lfi_x m j`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lfi_x] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  REWRITE_TAC[ARITH_RULE `4 * m + j = 1 * (4 * m) + j`; MOD_MULT_ADD]);;

let MOI_LFI_X_ZERO = prove
 (`!m. 1 <= m ==> moi_lfi_x m 0 = vec 0 /\ moi_lfi_x m (4 * m) = vec 0`,
  GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[MOI_LFI_X_LOOP; LE_0; LE_REFL] THEN
  SUBGOAL_THEN `~(&(4 * m) = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 / &(4 * m) = &0 /\ &(4 * m) / &(4 * m) = &1`
    (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THENL [REWRITE_TAC[real_div; REAL_MUL_LZERO]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_DIV_REFL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `lift(&0)` MOI_LFI_LOOP_PIECE1) THEN
  MP_TAC(SPEC `lift(&1)` MOI_LFI_LOOP_PIECE3) THEN
  REWRITE_TAC[LIFT_DROP] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN VECTOR_ARITH_TAC);;

let MOI_LFI_X_IN_FRONTIER = prove
 (`!m j. 1 <= m ==> moi_lfi_x m j IN relative_frontier std_triangle`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_lfi_x] THEN
  REWRITE_TAC[GSYM MOI_LTD_STD_TRIANGLE_LOOP; path_image] THEN
  MATCH_MP_TAC FUN_IN_IMAGE THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
  SUBGOAL_THEN `&0 < &(4 * m)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LE_LDIV_EQ; REAL_MUL_LID;
               REAL_OF_NUM_LE] THEN
  MATCH_MP_TAC LT_IMP_LE THEN REWRITE_TAC[MOD_LT_EQ] THEN
  ASM_ARITH_TAC);;

let MOI_LFI_X_INJ = prove
 (`!m i j. 1 <= m /\ i < 4 * m /\ j < 4 * m /\ moi_lfi_x m i = moi_lfi_x m j
           ==> i = j`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &(4 * m)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `moi_lfi_x m i = moi_lfi_x m j` THEN
  ASM_SIMP_TAC[MOI_LFI_X_LOOP; LT_IMP_LE] THEN DISCH_TAC THEN
  MP_TAC MOI_LFI_LOOP_SIMPLE THEN REWRITE_TAC[simple_path] THEN
  DISCH_THEN(MP_TAC o SPECL [`lift(&i / &(4 * m))`; `lift(&j / &(4 * m))`] o
    CONJUNCT2) THEN
  ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP; GSYM DROP_EQ] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LE_LDIV_EQ; REAL_MUL_LID;
                 REAL_OF_NUM_LE; LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!a. &a / &(4 * m) = &1 <=> a = 4 * m) /\
                (!a. &a / &(4 * m) = &0 <=> a = 0) /\
                (!a b. &a / &(4 * m) = &b / &(4 * m) <=> a = b)`
   (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
    UNDISCH_TAC `&0 < &(4 * m)` THEN CONV_TAC REAL_FIELD;
    ASM_ARITH_TAC]);;

let MOI_LFI_X_SEGMENT = prove
 (`!m j. 1 <= m /\ j < 4 * m
         ==> segment[moi_lfi_x m j,moi_lfi_x m (j + 1)] =
             IMAGE std_triangle_loop
               (interval[lift(&j / &(4 * m)),lift(&(j + 1) / &(4 * m))])`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &(4 * m)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^2` THEN
  REWRITE_TAC[IN_SEGMENT; IN_IMAGE; IN_INTERVAL_1; LIFT_DROP] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `lift((&j + s) / &(4 * m))` THEN
    SUBGOAL_THEN `&j / &(4 * m) <= (&j + s) / &(4 * m) /\
                  (&j + s) / &(4 * m) <= &(j + 1) / &(4 * m)`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_DIV2_EQ; GSYM REAL_OF_NUM_ADD] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN
    MP_TAC(ISPECL [`m:num`; `j:num`; `lift((&j + s) / &(4 * m))`]
      MOI_LFI_LOOP_AFFINE) THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `&(4 * m) * (&j + s) / &(4 * m) - &j = s` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < &(4 * m)` THEN CONV_TAC REAL_FIELD; ASM_REWRITE_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `&(4 * m) * drop t - &j` THEN
    UNDISCH_TAC `y = std_triangle_loop t` THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`m:num`; `j:num`; `t:real^1`] MOI_LFI_LOOP_AFFINE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN
    SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; GSYM REAL_OF_NUM_ADD] THEN
    REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC]);;

let MOI_LFI_PARAM_EQ = prove
 (`!m j t. 1 <= m /\ j <= 4 * m /\ drop t = &j / &(4 * m)
           ==> std_triangle_loop t = moi_lfi_x m j`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MOI_LFI_X_LOOP] THEN AP_TERM_TAC THEN
  ASM_REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP]);;

let MOI_LFI_PARAM_RANGE = prove
 (`!m i t. 1 <= m /\ &i / &(4 * m) <= drop t /\ drop t <= &(i + 1) / &(4 * m)
           ==> &i <= &(4 * m) * drop t /\ &(4 * m) * drop t <= &i + &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &(4 * m)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `&i / &(4 * m) <= drop t` THEN
  UNDISCH_TAC `drop t <= &(i + 1) / &(4 * m)` THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; GSYM REAL_OF_NUM_ADD] THEN
  REAL_ARITH_TAC);;

let MOI_LFI_SEG_PARAM = prove
 (`!m i y. 1 <= m /\ i < 4 * m /\
           y IN segment[moi_lfi_x m i,moi_lfi_x m (i + 1)]
           ==> ?t. y = std_triangle_loop t /\ &0 <= drop t /\ drop t <= &1 /\
                   &i <= &(4 * m) * drop t /\ &(4 * m) * drop t <= &i + &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `y IN segment[moi_lfi_x m i,moi_lfi_x m (i + 1)]` THEN
  ASM_SIMP_TAC[MOI_LFI_X_SEGMENT; IN_IMAGE; IN_INTERVAL_1; LIFT_DROP] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:real^1` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`m:num`; `i:num`; `t:real^1`] MOI_LFI_PARAM_RANGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < &(4 * m) /\ &i + &1 <= &(4 * m)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN EXISTS_TAC `&(4 * m)` THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `&(4 * m)` THEN
    ASM_REAL_ARITH_TAC]);;

let MOI_LFI_SEG_INTER = prove
 (`!m i j y. 1 <= m /\ i < 4 * m /\ j < 4 * m /\ ~(i = j) /\
             y IN segment[moi_lfi_x m i,moi_lfi_x m (i + 1)] /\
             y IN segment[moi_lfi_x m j,moi_lfi_x m (j + 1)]
             ==> (y = moi_lfi_x m i \/ y = moi_lfi_x m (i + 1)) /\
                 (y = moi_lfi_x m j \/ y = moi_lfi_x m (j + 1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &(4 * m)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`m:num`; `i:num`; `y:real^2`] MOI_LFI_SEG_PARAM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`m:num`; `j:num`; `y:real^2`] MOI_LFI_SEG_PARAM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t':real^1` STRIP_ASSUME_TAC) THEN
  MP_TAC MOI_LFI_LOOP_SIMPLE THEN REWRITE_TAC[simple_path] THEN
  DISCH_THEN(MP_TAC o SPECL [`t:real^1`; `t':real^1`] o CONJUNCT2) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM DROP_EQ; DROP_VEC] THEN
  SUBGOAL_THEN `moi_lfi_x m 0 = vec 0 /\ moi_lfi_x m (4 * m) = vec 0`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[MOI_LFI_X_ZERO]; ALL_TAC] THEN
  SUBGOAL_THEN `(drop t = &0 ==> std_triangle_loop t = vec 0) /\
                (drop t' = &0 ==> std_triangle_loop t' = vec 0)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THENL
     [MP_TAC(SPEC `t:real^1` MOI_LFI_LOOP_PIECE1);
      MP_TAC(SPEC `t':real^1` MOI_LFI_LOOP_PIECE1)] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[VECTOR_MUL_LZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `std_triangle_loop t = std_triangle_loop t'` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THENL
   [SUBGOAL_THEN `&j <= &(4 * m) * drop t /\ &(4 * m) * drop t <= &j + &1`
    STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `j <= i + 1 /\ i <= j + 1` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_ADD] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `j = i + 1 \/ i = j + 1` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THENL
     [SUBGOAL_THEN `&(4 * m) * drop t = &j` ASSUME_TAC THENL
       [UNDISCH_TAC `&j <= &(4 * m) * drop t` THEN
        UNDISCH_TAC `&(4 * m) * drop t <= &i + &1` THEN
        REWRITE_TAC[ASSUME `j = i + 1`; GSYM REAL_OF_NUM_ADD] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `std_triangle_loop t = moi_lfi_x m j` ASSUME_TAC THENL
       [MATCH_MP_TAC MOI_LFI_PARAM_EQ THEN
        CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `&(4 * m) * drop t = &j` THEN
        UNDISCH_TAC `&0 < &(4 * m)` THEN CONV_TAC REAL_FIELD;
        ASM_MESON_TAC[]];
      SUBGOAL_THEN `&(4 * m) * drop t = &i` ASSUME_TAC THENL
       [UNDISCH_TAC `&i <= &(4 * m) * drop t` THEN
        UNDISCH_TAC `&(4 * m) * drop t <= &j + &1` THEN
        REWRITE_TAC[ASSUME `i = j + 1`; GSYM REAL_OF_NUM_ADD] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `std_triangle_loop t = moi_lfi_x m i` ASSUME_TAC THENL
       [MATCH_MP_TAC MOI_LFI_PARAM_EQ THEN
        CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `&(4 * m) * drop t = &i` THEN
        UNDISCH_TAC `&0 < &(4 * m)` THEN CONV_TAC REAL_FIELD;
        ASM_MESON_TAC[]]];
    SUBGOAL_THEN `i = 0 /\ j + 1 = 4 * m` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [SUBGOAL_THEN `&i <= &0` MP_TAC THENL
         [ASM_MESON_TAC[REAL_MUL_RZERO]; REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC];
        SUBGOAL_THEN `&(4 * m) <= &j + &1` MP_TAC THENL
         [ASM_MESON_TAC[REAL_MUL_RID];
          REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC]];
      ALL_TAC] THEN
    SUBGOAL_THEN `std_triangle_loop t = vec 0` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    SUBGOAL_THEN `j = 0 /\ i + 1 = 4 * m` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [SUBGOAL_THEN `&j <= &0` MP_TAC THENL
         [ASM_MESON_TAC[REAL_MUL_RZERO]; REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC];
        SUBGOAL_THEN `&(4 * m) <= &i + &1` MP_TAC THENL
         [ASM_MESON_TAC[REAL_MUL_RID];
          REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC]];
      ALL_TAC] THEN
    SUBGOAL_THEN `std_triangle_loop t = vec 0` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 4. Simplicial complexes from vertex sets, and the frontier polygon.       *)
(* ------------------------------------------------------------------------- *)

(* A finite family of affinely independent vertex sets, closed under subsets, *)
(* whose distinct hulls meet only in common vertices, spans a simplicial      *)
(* complex.                                                                  *)

let MOI_LFI_HULLS_COMPLEX = prove
 (`!ww:(real^N->bool)->bool.
     FINITE ww /\ (!w. w IN ww ==> ~affine_dependent w) /\
     (!w w'. w IN ww /\ w' SUBSET w ==> w' IN ww) /\
     (!w w'. w IN ww /\ w' IN ww /\ ~(convex hull w = convex hull w')
             ==> (convex hull w) INTER (convex hull w') SUBSET w INTER w')
     ==> simplicial_complex {convex hull w | w IN ww}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[simplicial_complex] THEN
  ASM_SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE] THEN REWRITE_TAC[IN_IMAGE] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `&(CARD(w:real^N->bool)) - &1:int` THEN
    MATCH_MP_TAC SIMPLEX_CONVEX_HULL THEN ASM_SIMP_TAC[] THEN INT_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`f:real^N->bool`; `s:real^N->bool`] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    MP_TAC(ISPECL [`w:real^N->bool`; `f:real^N->bool`]
      FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
    ASM_SIMP_TAC[] THEN UNDISCH_TAC `(f:real^N->bool) face_of s` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `w':real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `w':real^N->bool` THEN ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `s':real^N->bool`] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `w':real^N->bool` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `convex hull w:real^N->bool = convex hull w'` THENL
     [ASM_REWRITE_TAC[INTER_IDEMPOT] THEN
      SIMP_TAC[FACE_OF_REFL; CONVEX_CONVEX_HULL];
      ALL_TAC] THEN
    SUBGOAL_THEN `(convex hull w) INTER (convex hull w') =
                  convex hull ((w:real^N->bool) INTER w')` SUBST1_TAC THENL
     [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `(w:real^N->bool) INTER w'` THEN
        ASM_SIMP_TAC[HULL_SUBSET];
        REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THEN MATCH_MP_TAC HULL_MONO THEN
        SET_TAC[]];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`w:real^N->bool`; `convex hull (w INTER w'):real^N->bool`]
        FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT);
      MP_TAC(ISPECL [`w':real^N->bool`; `convex hull (w INTER w'):real^N->bool`]
        FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT)] THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
    EXISTS_TAC `(w:real^N->bool) INTER w'` THEN SET_TAC[]]);;

let MOI_LFI_NUM_COVER = prove
 (`!n x. 1 <= n /\ &0 <= x /\ x <= &n ==> ?j. j < n /\ &j <= x /\ x <= &j + &1`,
  INDUCT_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  ASM_CASES_TAC `n = 0` THENL
   [EXISTS_TAC `0` THEN UNDISCH_TAC `x <= &(SUC n)` THEN
    ASM_REWRITE_TAC[ARITH] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `x <= &n` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[] THEN ARITH_TAC];
    EXISTS_TAC `n:num` THEN
    UNDISCH_TAC `x <= &(SUC n)` THEN UNDISCH_TAC `~(x <= &n)` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN REPEAT DISCH_TAC THEN
    CONJ_TAC THENL [ARITH_TAC; ASM_REAL_ARITH_TAC]]);;

let MOI_LFI_PARAM_COVER = prove
 (`!m t. 1 <= m /\ &0 <= drop t /\ drop t <= &1
         ==> ?j. j < 4 * m /\ &j / &(4 * m) <= drop t /\
                 drop t <= &(j + 1) / &(4 * m)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &(4 * m)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`4 * m`; `&(4 * m) * drop t`] MOI_LFI_NUM_COVER) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; GSYM REAL_OF_NUM_ADD] THEN
  ASM_REAL_ARITH_TAC);;

let MOI_LFI_X_MOD = prove
 (`!m j. moi_lfi_x m j = moi_lfi_x m (j MOD (4 * m)) /\
         (1 <= m ==> j MOD (4 * m) < 4 * m)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lfi_x; MOD_MOD_REFL] THEN
  REWRITE_TAC[MOD_LT_EQ] THEN ARITH_TAC);;

let moi_lfi_vs = new_definition
 `moi_lfi_vs (m:num) =
    {{moi_lfi_x m j, moi_lfi_x m (j + 1)} | j | j < 4 * m} UNION
    {{moi_lfi_x m j} | j | j < 4 * m} UNION {{}:real^2->bool}`;;

let moi_lfi_pcx = new_definition
 `moi_lfi_pcx (m:num) = {convex hull w | (w:real^2->bool) IN moi_lfi_vs m}`;;

let MOI_LFI_VERTEX_IN_SEG = prove
 (`!m i k. 1 <= m /\ i < 4 * m /\ k < 4 * m /\
           moi_lfi_x m k IN segment[moi_lfi_x m i,moi_lfi_x m (i + 1)]
           ==> moi_lfi_x m k = moi_lfi_x m i \/
               moi_lfi_x m k = moi_lfi_x m (i + 1)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `k:num = i` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`m:num`; `i:num`; `k:num`; `moi_lfi_x m k`] MOI_LFI_SEG_INTER) THEN
  ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN ASM_MESON_TAC[]);;

let MOI_LFI_IN_VS = prove
 (`!m w. w IN moi_lfi_vs m <=>
         (?j. j < 4 * m /\ w = {moi_lfi_x m j, moi_lfi_x m (j + 1)}) \/
         (?j. j < 4 * m /\ w = {moi_lfi_x m j}) \/ w = {}`,
  REWRITE_TAC[moi_lfi_vs; IN_UNION; IN_ELIM_THM; IN_SING]);;

let MOI_LFI_VS_FINITE = prove
 (`!m. FINITE (moi_lfi_vs m)`,
  GEN_TAC THEN REWRITE_TAC[moi_lfi_vs; FINITE_UNION; FINITE_SING] THEN
  CONJ_TAC THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  MATCH_MP_TAC FINITE_IMAGE THEN REWRITE_TAC[FINITE_NUMSEG_LT]);;

let MOI_LFI_VS_SUBSET = prove
 (`!m w w'. 1 <= m /\ w IN moi_lfi_vs m /\ w' SUBSET w ==> w' IN moi_lfi_vs m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN UNDISCH_TAC `(w':real^2->bool) SUBSET w` THEN
  UNDISCH_TAC `(w:real^2->bool) IN moi_lfi_vs m` THEN
  REWRITE_TAC[MOI_LFI_IN_VS] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[SET_RULE
     `(s:real^2->bool) SUBSET {a,b} <=>
      s = {} \/ s = {a} \/ s = {b} \/ s = {a,b}`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [DISJ2_TAC THEN DISJ1_TAC THEN EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN DISJ1_TAC THEN EXISTS_TAC `(j + 1) MOD (4 * m)` THEN
      ASM_MESON_TAC[MOI_LFI_X_MOD];
      DISJ1_TAC THEN EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[SET_RULE `(s:real^2->bool) SUBSET {a} <=> s = {} \/ s = {a}`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISJ2_TAC THEN DISJ1_TAC THEN EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET_EMPTY] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]]);;

let MOI_LFI_VS_INTER = prove
 (`!m w w'. 1 <= m /\ w IN moi_lfi_vs m /\ w' IN moi_lfi_vs m /\
            ~(convex hull w = convex hull w')
            ==> (convex hull w) INTER (convex hull w') SUBSET w INTER w'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `~(convex hull w:real^2->bool = convex hull w')` THEN
  UNDISCH_TAC `(w':real^2->bool) IN moi_lfi_vs m` THEN
  UNDISCH_TAC `(w:real^2->bool) IN moi_lfi_vs m` THEN
  REWRITE_TAC[MOI_LFI_IN_VS] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[CONVEX_HULL_EMPTY; CONVEX_HULL_SING; GSYM SEGMENT_CONVEX_HULL;
                  INTER_EMPTY; EMPTY_SUBSET] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_INSERT; NOT_IN_EMPTY] THEN
  X_GEN_TAC `y:real^2` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC MOI_LFI_SEG_INTER THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN UNDISCH_TAC `~(convex hull w:real^2->bool = convex hull w')` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_LFI_VERTEX_IN_SEG THEN ASM_MESON_TAC[];
    MATCH_MP_TAC MOI_LFI_VERTEX_IN_SEG THEN ASM_MESON_TAC[]]);;

let MOI_LFI_FRONTIER_IMAGE = prove
 (`relative_frontier std_triangle =
   IMAGE std_triangle_loop (interval[vec 0,vec 1])`,
  REWRITE_TAC[GSYM path_image; MOI_LTD_STD_TRIANGLE_LOOP]);;

let MOI_LFI_PCX_COMPLEX = prove
 (`!m. 1 <= m
       ==> simplicial_complex (moi_lfi_pcx m) /\
           UNIONS (moi_lfi_pcx m) = relative_frontier std_triangle`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[moi_lfi_pcx] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_LFI_HULLS_COMPLEX THEN
    REWRITE_TAC[MOI_LFI_VS_FINITE] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[MOI_LFI_IN_VS] THEN GEN_TAC THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[AFFINE_INDEPENDENT_2; AFFINE_INDEPENDENT_1;
                      AFFINE_INDEPENDENT_EMPTY];
      ASM_MESON_TAC[MOI_LFI_VS_SUBSET];
      ASM_MESON_TAC[MOI_LFI_VS_INTER]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &(4 * m)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^2` THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; MOI_LFI_IN_VS] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `s:real^2->bool` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^2->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(y:real^2) IN s` THEN
    ASM_REWRITE_TAC[CONVEX_HULL_EMPTY; CONVEX_HULL_SING; NOT_IN_EMPTY;
                    GSYM SEGMENT_CONVEX_HULL; IN_SING] THENL
     [ASM_SIMP_TAC[MOI_LFI_X_SEGMENT] THEN REWRITE_TAC[MOI_LFI_FRONTIER_IMAGE] THEN
      MATCH_MP_TAC(SET_RULE
       `s SUBSET t ==> (y:real^2) IN IMAGE (f:real^1->real^2) s ==> y IN IMAGE f t`) THEN
      REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
      DISJ2_TAC THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS];
        ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_OF_NUM_LE] THEN ARITH_TAC;
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LID; REAL_OF_NUM_LE] THEN
        ASM_ARITH_TAC];
      DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[MOI_LFI_X_IN_FRONTIER]];
    REWRITE_TAC[MOI_LFI_FRONTIER_IMAGE; IN_IMAGE; IN_INTERVAL_1; DROP_VEC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPECL [`m:num`; `t:real^1`] MOI_LFI_PARAM_COVER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `segment[moi_lfi_x m j,moi_lfi_x m (j + 1)]` THEN CONJ_TAC THENL
     [EXISTS_TAC `{moi_lfi_x m j,moi_lfi_x m (j + 1)}` THEN
      REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN DISJ1_TAC THEN
      EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[MOI_LFI_X_SEGMENT] THEN REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `t:real^1` THEN ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP]]]);;

(* ------------------------------------------------------------------------- *)
(* 5. General hull lemmas: complexes from vertex-set families whose hulls    *)
(* meet in the hulls of the common vertices; hulls of subsets of an         *)
(* affinely independent set; hulls meeting a face; maximal vertex sets.      *)
(* ------------------------------------------------------------------------- *)

let MOI_LFI_HULLS_COMPLEX_GEN = prove
 (`!ww:(real^N->bool)->bool.
     FINITE ww /\ (!w. w IN ww ==> ~affine_dependent w) /\
     (!w w'. w IN ww /\ w' SUBSET w ==> w' IN ww) /\
     (!w w'. w IN ww /\ w' IN ww
             ==> (convex hull w) INTER (convex hull w') SUBSET
                 convex hull (w INTER w'))
     ==> simplicial_complex {convex hull w | w IN ww}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[simplicial_complex] THEN
  ASM_SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE] THEN REWRITE_TAC[IN_IMAGE] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `&(CARD(w:real^N->bool)) - &1:int` THEN
    MATCH_MP_TAC SIMPLEX_CONVEX_HULL THEN ASM_SIMP_TAC[] THEN INT_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`f:real^N->bool`; `s:real^N->bool`] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    MP_TAC(ISPECL [`w:real^N->bool`; `f:real^N->bool`]
      FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
    ASM_SIMP_TAC[] THEN UNDISCH_TAC `(f:real^N->bool) face_of s` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `w':real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `w':real^N->bool` THEN ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `s':real^N->bool`] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `w':real^N->bool` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(convex hull w) INTER (convex hull w') =
                  convex hull ((w:real^N->bool) INTER w')` SUBST1_TAC THENL
     [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[];
        REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THEN MATCH_MP_TAC HULL_MONO THEN
        SET_TAC[]];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`w:real^N->bool`; `convex hull (w INTER w'):real^N->bool`]
        FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT);
      MP_TAC(ISPECL [`w':real^N->bool`; `convex hull (w INTER w'):real^N->bool`]
        FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT)] THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
    EXISTS_TAC `(w:real^N->bool) INTER w'` THEN SET_TAC[]]);;

let MOI_LFI_HULL_INTER_INDEP = prove
 (`!(v:real^N->bool) u u'.
     ~affine_dependent v /\ u SUBSET v /\ u' SUBSET v
     ==> (convex hull u) INTER (convex hull u') = convex hull (u INTER u')`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THEN MATCH_MP_TAC HULL_MONO THEN
    SET_TAC[]] THEN
  SUBGOAL_THEN `(convex hull u) face_of (convex hull v) /\
                (convex hull u') face_of (convex hull (v:real^N->bool))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`v:real^N->bool`;
                 `(convex hull u) INTER (convex hull u'):real^N->bool`]
    FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
  ASM_SIMP_TAC[FACE_OF_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_MONO THEN
  REWRITE_TAC[SUBSET_INTER] THEN
  SUBGOAL_THEN `!w:real^N->bool. w SUBSET v /\ c SUBSET convex hull w
                                 ==> c SUBSET w`
  (fun th -> CONJ_TAC THEN MATCH_MP_TAC th THEN ASM_REWRITE_TAC[] THEN
             MATCH_MP_TAC SUBSET_TRANS THEN
             EXISTS_TAC `convex hull c:real^N->bool` THEN
             REWRITE_TAC[HULL_SUBSET] THEN ASM SET_TAC[]) THEN
  X_GEN_TAC `w:real^N->bool` THEN STRIP_TAC THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(x:real^N) IN w` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~affine_dependent (v:real^N->bool)` THEN
  REWRITE_TAC[affine_dependent] THEN EXISTS_TAC `x:real^N` THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE `!s t:real^N->bool. x IN s /\ s SUBSET t ==> x IN t`) THEN
  EXISTS_TAC `convex hull w:real^N->bool` THEN CONJ_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `convex hull (v DELETE (x:real^N))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[];
    REWRITE_TAC[CONVEX_HULL_SUBSET_AFFINE_HULL]]);;

let MOI_LFI_HULL_INTER_FACE = prove
 (`!(s:real^N->bool) f x.
     convex s /\ f face_of s /\ FINITE x /\ x SUBSET s
     ==> (convex hull x) INTER f = convex hull (x INTER f)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(f INTER convex hull x) face_of (convex hull (x:real^N->bool))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:real^N->bool`; `s:real^N->bool`;
                   `convex hull x:real^N->bool`] FACE_OF_SLICE) THEN
    ASM_REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
    SUBGOAL_THEN `s INTER convex hull x = convex hull (x:real^N->bool)`
      (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC(SET_RULE `(t:real^N->bool) SUBSET s ==> s INTER t = t`) THEN
    MATCH_MP_TAC HULL_MINIMAL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`x:real^N->bool`; `f INTER convex hull x:real^N->bool`]
    FACE_OF_CONVEX_HULL_SUBSET) THEN
  ASM_SIMP_TAC[FINITE_IMP_COMPACT] THEN
  DISCH_THEN(X_CHOOSE_THEN `x':real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `convex (f:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_OF_IMP_CONVEX]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HULL_MONO THEN REWRITE_TAC[SUBSET_INTER] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `convex hull x':real^N->bool` THEN
    REWRITE_TAC[HULL_SUBSET] THEN UNDISCH_TAC
     `f INTER convex hull x = convex hull (x':real^N->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN SET_TAC[];
    REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      MATCH_MP_TAC HULL_MINIMAL THEN ASM_REWRITE_TAC[] THEN SET_TAC[]]]);;

let MOI_LFI_MAXHULLS_COMPLEX = prove
 (`!mx:(real^N->bool)->bool.
     FINITE mx /\ (!x. x IN mx ==> FINITE x /\ ~affine_dependent x) /\
     (!x y. x IN mx /\ y IN mx
            ==> (convex hull x) INTER (convex hull y) SUBSET
                convex hull (x INTER y))
     ==> simplicial_complex
           {convex hull w | w IN {w | ?x. x IN mx /\ w SUBSET x}}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_LFI_HULLS_COMPLEX_GEN THEN
  REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `UNIONS (IMAGE (\x:real^N->bool. {w | w SUBSET x}) mx)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FINITE_UNIONS] THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
      REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[FINITE_POWERSET];
      REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE; IN_ELIM_THM] THEN
      MESON_TAC[]];
    ASM_MESON_TAC[AFFINE_INDEPENDENT_SUBSET];
    MESON_TAC[SUBSET_TRANS];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`w:real^N->bool`; `w':real^N->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `x:real^N->bool` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `y:real^N->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `~affine_dependent (x:real^N->bool) /\
                ~affine_dependent (y:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(convex hull w) INTER (convex hull w') SUBSET
                convex hull (x INTER (y:real^N->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `(convex hull x) INTER (convex hull (y:real^N->bool))` THEN
    ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC(SET_RULE
     `(a:real^N->bool) SUBSET c /\ b SUBSET d ==> a INTER b SUBSET c INTER d`) THEN
    CONJ_TAC THEN MATCH_MP_TAC HULL_MONO THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(convex hull w) INTER (convex hull (x INTER y)) =
    convex hull (w INTER (x INTER (y:real^N->bool))) /\
    (convex hull w') INTER (convex hull (x INTER y)) =
    convex hull (w' INTER (x INTER (y:real^N->bool)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_LFI_HULL_INTER_INDEP THENL
     [EXISTS_TAC `x:real^N->bool`; EXISTS_TAC `y:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(convex hull (w INTER (x INTER y))) INTER (convex hull (w' INTER (x INTER y))) =
    convex hull ((w INTER (x INTER y)) INTER (w' INTER (x INTER (y:real^N->bool))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LFI_HULL_INTER_INDEP THEN EXISTS_TAC `x:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `convex hull ((w INTER (x INTER y)) INTER
                           (w' INTER (x INTER (y:real^N->bool))))` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `(convex hull w) INTER (convex hull (x INTER y)) =
                 convex hull (w INTER (x INTER (y:real^N->bool)))` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `(convex hull w') INTER (convex hull (x INTER y)) =
                 convex hull (w' INTER (x INTER (y:real^N->bool)))` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM SET_TAC[];
    MATCH_MP_TAC HULL_MONO THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 6. The template triangulation of std_triangle used in every sector: the   *)
(* inner triangle {0, b1/2, b2/2} and the ring triangles {b1, b2, b2/2} and  *)
(* {b1, b1/2, b2/2}, described by linear inequalities.                       *)
(* ------------------------------------------------------------------------- *)

let MOI_LFI_HULL3_REGION = prove
 (`!(a:real^2) b c P.
     (!x. x IN convex hull {a,b,c} ==> P x) /\
     (!x. P x ==> ?u v w. &0 <= u /\ &0 <= v /\ &0 <= w /\ u + v + w = &1 /\
                          x = u % a + v % b + w % c)
     ==> convex hull {a,b,c} = {x | P x}`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_ELIM_THM] THEN EQ_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN
  ASM_MESON_TAC[]);;

let MOI_LFI_COMPONENTS_2 = prove
 (`!(x:real^2) y. x = y <=> x$1 = y$1 /\ x$2 = y$2`,
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2]);;

let MOI_LFI_TEMPLATE_A = prove
 (`convex hull {vec 0:real^2, inv(&2) % basis 1, inv(&2) % basis 2} =
   {x:real^2 | &0 <= x$1 /\ &0 <= x$2 /\ x$1 + x$2 <= inv(&2)}`,
  MATCH_MP_TAC MOI_LFI_HULL3_REGION THEN CONJ_TAC THENL
   [REWRITE_TAC[CONVEX_HULL_3; FORALL_IN_GSPEC] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT;
             BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC;
    X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`&1 - &2 * (x:real^2)$1 - &2 * x$2`; `&2 * (x:real^2)$1`; `&2 * (x:real^2)$2`] THEN
    REWRITE_TAC[MOI_LFI_COMPONENTS_2] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT;
             BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN ASM_REAL_ARITH_TAC]);;

let MOI_LFI_TEMPLATE_B = prove
 (`convex hull {basis 1:real^2, basis 2, inv(&2) % basis 2} =
   {x:real^2 | &0 <= x$1 /\ x$1 + x$2 <= &1 /\ &1 <= x$1 + &2 * x$2}`,
  MATCH_MP_TAC MOI_LFI_HULL3_REGION THEN CONJ_TAC THENL
   [REWRITE_TAC[CONVEX_HULL_3; FORALL_IN_GSPEC] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT;
             BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC;
    X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`(x:real^2)$1`; `(x:real^2)$1 + &2 * x$2 - &1`;
      `&2 - &2 * (x:real^2)$1 - &2 * x$2`] THEN
    REWRITE_TAC[MOI_LFI_COMPONENTS_2] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT;
             BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN ASM_REAL_ARITH_TAC]);;

let MOI_LFI_TEMPLATE_C = prove
 (`convex hull {basis 1:real^2, inv(&2) % basis 1, inv(&2) % basis 2} =
   {x:real^2 | &0 <= x$2 /\ inv(&2) <= x$1 + x$2 /\ x$1 + &2 * x$2 <= &1}`,
  MATCH_MP_TAC MOI_LFI_HULL3_REGION THEN CONJ_TAC THENL
   [REWRITE_TAC[CONVEX_HULL_3; FORALL_IN_GSPEC] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT;
             BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC;
    X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`&2 * (x:real^2)$1 + &2 * x$2 - &1`; `&2 - &2 * (x:real^2)$1 - &4 * x$2`;
      `&2 * (x:real^2)$2`] THEN
    REWRITE_TAC[MOI_LFI_COMPONENTS_2] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT;
             BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN ASM_REAL_ARITH_TAC]);;

let MOI_LFI_STD_REGION = prove
 (`std_triangle = {x:real^2 | &0 <= x$1 /\ &0 <= x$2 /\ x$1 + x$2 <= &1}`,
  REWRITE_TAC[std_triangle] THEN MATCH_MP_TAC MOI_LFI_HULL3_REGION THEN
  CONJ_TAC THENL
   [REWRITE_TAC[CONVEX_HULL_3; FORALL_IN_GSPEC] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT;
             BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC;
    X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`&1 - (x:real^2)$1 - x$2`; `(x:real^2)$1`; `(x:real^2)$2`] THEN
    REWRITE_TAC[MOI_LFI_COMPONENTS_2] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT;
             BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN ASM_REAL_ARITH_TAC]);;

let MOI_LFI_TEMPLATE_FACTS = prove
 (`let a1 = inv(&2) % basis 1:real^2 and a2 = inv(&2) % basis 2:real^2 in
   let ta = {vec 0,a1,a2} and tb = {basis 1,basis 2,a2}
   and tc = {basis 1,a1,a2} in
   (convex hull ta) INTER (convex hull tb) SUBSET convex hull (ta INTER tb) /\
   (convex hull ta) INTER (convex hull tc) SUBSET convex hull (ta INTER tc) /\
   (convex hull tb) INTER (convex hull tc) SUBSET convex hull (tb INTER tc) /\
   (convex hull ta) UNION (convex hull tb) UNION (convex hull tc) = std_triangle /\
   convex hull ta SUBSET std_triangle /\ convex hull tb SUBSET std_triangle /\
   convex hull tc SUBSET std_triangle /\
   ~(a1 IN segment[vec 0:real^2,basis 2]) /\
   ~(basis 1 IN segment[vec 0:real^2,basis 2]) /\
   ~(a2 IN segment[vec 0:real^2,basis 1]) /\
   ~(basis 2 IN segment[vec 0:real^2,basis 1]) /\
   a1 = midpoint(vec 0:real^2,basis 1) /\ a2 = midpoint(vec 0:real^2,basis 2)`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[MOI_LFI_TEMPLATE_A; MOI_LFI_TEMPLATE_B; MOI_LFI_TEMPLATE_C;
              MOI_LFI_STD_REGION] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `{inv(&2) % basis 2:real^2}` THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; IN_SING] THEN
      X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
      REWRITE_TAC[MOI_LFI_COMPONENTS_2] THEN
      SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SING_SUBSET] THEN MATCH_MP_TAC HULL_INC THEN
      REWRITE_TAC[IN_INTER; IN_INSERT]];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `convex hull {inv(&2) % basis 1:real^2,inv(&2) % basis 2}` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; SUBSET; IN_INTER; IN_ELIM_THM;
                  IN_SEGMENT] THEN
      X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
      EXISTS_TAC `&2 * (x:real^2)$2` THEN
      REWRITE_TAC[MOI_LFI_COMPONENTS_2] THEN
      SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT;
               DIMINDEX_2; ARITH] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[]];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `convex hull {basis 1:real^2,inv(&2) % basis 2}` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; SUBSET; IN_INTER; IN_ELIM_THM;
                  IN_SEGMENT] THEN
      X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
      EXISTS_TAC `&2 * (x:real^2)$2` THEN
      REWRITE_TAC[MOI_LFI_COMPONENTS_2] THEN
      SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT;
               DIMINDEX_2; ARITH] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[]];
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    REWRITE_TAC[MOI_LFI_SIDE3; ONCE_REWRITE_RULE[SEGMENT_SYM] MOI_LFI_SIDE3;
                IN_ELIM_THM] THEN
    SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[ONCE_REWRITE_RULE[SEGMENT_SYM] MOI_LFI_SIDE3; IN_ELIM_THM] THEN
    SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[MOI_LFI_SIDE1; IN_ELIM_THM] THEN
    SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[MOI_LFI_SIDE1; IN_ELIM_THM] THEN
    SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[midpoint] THEN VECTOR_ARITH_TAC;
    REWRITE_TAC[midpoint] THEN VECTOR_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 7. Sectors: the barycentre z, the sector maps phi_j from std_triangle onto *)
(* conv{z,x_j,x_j+1} (injective: the determinant of x_j - z, x_j+1 - z is    *)
(* nonzero because x_j, x_j+1 lie on one side and z does not), and the       *)
(* inner points y_j = midpoint(z,x_j).                                       *)
(* ------------------------------------------------------------------------- *)

let moi_lfi_z = new_definition
 `moi_lfi_z:real^2 = inv(&3) % (basis 1 + basis 2)`;;

let moi_lfi_y = new_definition
 `moi_lfi_y m j = midpoint(moi_lfi_z,moi_lfi_x m j)`;;

let moi_lfi_phi = new_definition
 `moi_lfi_phi m j (u:real^2) =
    moi_lfi_z + u$1 % (moi_lfi_x m j - moi_lfi_z) +
    u$2 % (moi_lfi_x m (j + 1) - moi_lfi_z)`;;

let MOI_LFI_Z_COMPONENTS = prove
 (`moi_lfi_z$1 = inv(&3) /\ moi_lfi_z$2 = inv(&3)`,
  SIMP_TAC[moi_lfi_z; VECTOR_MUL_COMPONENT; VECTOR_ADD_COMPONENT;
           BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC);;

let MOI_LFI_X_SIDES = prove
 (`!m j. 1 <= m /\ j < 4 * m
         ==> ((moi_lfi_x m j)$2 = &0 /\ (moi_lfi_x m (j + 1))$2 = &0) \/
             ((moi_lfi_x m j)$1 + (moi_lfi_x m j)$2 = &1 /\
              (moi_lfi_x m (j + 1))$1 + (moi_lfi_x m (j + 1))$2 = &1) \/
             ((moi_lfi_x m j)$1 = &0 /\ (moi_lfi_x m (j + 1))$1 = &0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &(4 * m)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_LFI_X_LOOP; LT_IMP_LE; ARITH_RULE `j < n ==> j + 1 <= n`] THEN
  SUBGOAL_THEN
   `(!a b. &a / &(4 * m) <= &b / &4 <=> &4 * &a <= &b * &(4 * m)) /\
    (!a b. &b / &4 <= &a / &(4 * m) <=> &b * &(4 * m) <= &4 * &a)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT GEN_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LDIV_EQ]; ASM_SIMP_TAC[REAL_LE_RDIV_EQ]] THEN
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &j / &(4 * m) /\ &(j + 1) / &(4 * m) <= &1`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LE_LDIV_EQ; REAL_MUL_LID;
                 REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `j + 1 <= 2 * m` THENL
   [DISJ1_TAC THEN
    SUBGOAL_THEN `&j / &(4 * m) <= &1 / &2 /\ &(j + 1) / &(4 * m) <= &1 / &2`
    STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_ARITH `&1 / &2 = &2 / &4`] THEN
      UNDISCH_TAC `j + 1 <= 2 * m` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_ADD;
                  GSYM REAL_OF_NUM_MUL] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[CONJUNCT1 MOI_LFI_LOOP_LIFT_PIECES; REAL_LE_DIV; REAL_POS] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT;
             BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `2 * m <= j` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 / &2 <= &j / &(4 * m)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_ARITH `&1 / &2 = &2 / &4`] THEN
    UNDISCH_TAC `2 * m <= j` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_MUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `j + 1 <= 3 * m` THENL
   [DISJ2_TAC THEN DISJ1_TAC THEN
    SUBGOAL_THEN `&(j + 1) / &(4 * m) <= &3 / &4` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `j + 1 <= 3 * m` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_ADD;
                  GSYM REAL_OF_NUM_MUL] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&j / &(4 * m) <= &3 / &4 /\ &1 / &2 <= &(j + 1) / &(4 * m)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
       [EXISTS_TAC `&(j + 1) / &(4 * m)`; EXISTS_TAC `&j / &(4 * m)`] THEN
      ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_OF_NUM_LE] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[CONJUNCT1(CONJUNCT2 MOI_LFI_LOOP_LIFT_PIECES)] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT;
             VEC_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT DISJ2_TAC THEN
  SUBGOAL_THEN `&3 / &4 <= &j / &(4 * m)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `3 * m <= j` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_MUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&j / &(4 * m) <= &1 /\ &3 / &4 <= &(j + 1) / &(4 * m)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `&(j + 1) / &(4 * m)`; EXISTS_TAC `&j / &(4 * m)`] THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_OF_NUM_LE] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[CONJUNCT2(CONJUNCT2 MOI_LFI_LOOP_LIFT_PIECES)] THEN
  SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_NEG_COMPONENT;
           VEC_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
  REAL_ARITH_TAC);;

let MOI_LFI_X_NEXT_NE = prove
 (`!m j. 1 <= m /\ j < 4 * m ==> ~(moi_lfi_x m j = moi_lfi_x m (j + 1))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `j + 1 = 4 * m` THENL
   [UNDISCH_TAC `moi_lfi_x m j = moi_lfi_x m (j + 1)` THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[MOI_LFI_X_ZERO] THEN
    ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
    SUBGOAL_THEN `vec 0 = moi_lfi_x m 0` SUBST1_TAC THENL
     [ASM_SIMP_TAC[MOI_LFI_X_ZERO]; ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(SPECL [`m:num`; `0`; `j:num`] MOI_LFI_X_INJ) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    MP_TAC(SPECL [`m:num`; `j:num`; `j + 1`] MOI_LFI_X_INJ) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 8. The sector determinant, injectivity of phi_j, affine independence of  *)
(* the sector vertices, spokes, and the transported template.                *)
(* ------------------------------------------------------------------------- *)

let MOI_LFI_DET_INJ = prove
 (`!p q:real^2.
     ~(p$1 * q$2 - p$2 * q$1 = &0)
     ==> !a b. a % p + b % q = vec 0 ==> a = &0 /\ b = &0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[MOI_LFI_COMPONENTS_2] THEN
  SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT;
           DIMINDEX_2; ARITH] THEN STRIP_TAC THEN
  SUBGOAL_THEN `a * (p$1 * q$2 - p$2 * (q:real^2)$1) = &0 /\
                b * (p$1 * q$2 - (p:real^2)$2 * q$1) = &0` MP_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN
       `a * ((p:real^2)$1 * (q:real^2)$2 - p$2 * q$1) =
        q$2 * (a * p$1 + b * q$1) - q$1 * (a * p$2 + b * q$2)`
      SUBST1_TAC THENL [CONV_TAC REAL_RING; ALL_TAC];
      SUBGOAL_THEN
       `b * ((p:real^2)$1 * (q:real^2)$2 - p$2 * q$1) =
        p$1 * (a * p$2 + b * q$2) - p$2 * (a * p$1 + b * q$1)`
      SUBST1_TAC THENL [CONV_TAC REAL_RING; ALL_TAC]] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[REAL_ENTIRE]]);;

let MOI_LFI_DET_SIDE = prove
 (`!a b:real^2.
     ((a$2 = &0 /\ b$2 = &0) \/ (a$1 + a$2 = &1 /\ b$1 + b$2 = &1) \/
      (a$1 = &0 /\ b$1 = &0)) /\ ~(a = b)
     ==> ~((a - moi_lfi_z)$1 * (b - moi_lfi_z)$2 -
           (a - moi_lfi_z)$2 * (b - moi_lfi_z)$1 = &0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOI_LFI_COMPONENTS_2] THEN
  SIMP_TAC[VECTOR_SUB_COMPONENT; DIMINDEX_2; ARITH; MOI_LFI_Z_COMPONENTS] THEN
  STRIP_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~((a:real^2)$1 = (b:real^2)$1 /\ a$2 = b$2)` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `(a:real^2)$1 = &1 - a$2 /\ (b:real^2)$1 = &1 - b$2`
    STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `~((a:real^2)$1 = (b:real^2)$1 /\ a$2 = b$2)` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~((a:real^2)$1 = (b:real^2)$1 /\ a$2 = b$2)` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let MOI_LFI_SECTOR_DET = prove
 (`!m j. 1 <= m /\ j < 4 * m
         ==> ~((moi_lfi_x m j - moi_lfi_z)$1 * (moi_lfi_x m (j + 1) - moi_lfi_z)$2 -
               (moi_lfi_x m j - moi_lfi_z)$2 * (moi_lfi_x m (j + 1) - moi_lfi_z)$1 =
               &0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC MOI_LFI_DET_SIDE THEN
  ASM_SIMP_TAC[MOI_LFI_X_SIDES; MOI_LFI_X_NEXT_NE]);;

let MOI_LFI_PHI_AFFINE = prove
 (`!m j. moi_lfi_phi m j =
         (\u. (\u:real^2. u$1 % (moi_lfi_x m j - moi_lfi_z) +
                          u$2 % (moi_lfi_x m (j + 1) - moi_lfi_z)) u + moi_lfi_z) /\
         linear (\u:real^2. u$1 % (moi_lfi_x m j - moi_lfi_z) +
                            u$2 % (moi_lfi_x m (j + 1) - moi_lfi_z))`,
  REPEAT GEN_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; moi_lfi_phi] THEN VECTOR_ARITH_TAC;
    REWRITE_TAC[linear; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    VECTOR_ARITH_TAC]);;

let MOI_LFI_PHI_INJ = prove
 (`!m j u v. 1 <= m /\ j < 4 * m /\ moi_lfi_phi m j u = moi_lfi_phi m j v
             ==> u = v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`m:num`; `j:num`] MOI_LFI_SECTOR_DET) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`(u:real^2)$1 - (v:real^2)$1`; `(u:real^2)$2 - (v:real^2)$2`] o
    MATCH_MP MOI_LFI_DET_INJ) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `moi_lfi_phi m j u = moi_lfi_phi m j v` THEN
    REWRITE_TAC[moi_lfi_phi] THEN VECTOR_ARITH_TAC;
    REWRITE_TAC[MOI_LFI_COMPONENTS_2] THEN REAL_ARITH_TAC]);;

let MOI_LFI_PHI_POINTS = prove
 (`!m j. moi_lfi_phi m j (vec 0) = moi_lfi_z /\
         moi_lfi_phi m j (basis 1) = moi_lfi_x m j /\
         moi_lfi_phi m j (basis 2) = moi_lfi_x m (j + 1) /\
         moi_lfi_phi m j (inv(&2) % basis 1) = moi_lfi_y m j /\
         moi_lfi_phi m j (inv(&2) % basis 2) = moi_lfi_y m (j + 1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lfi_phi; moi_lfi_y; midpoint] THEN
  SIMP_TAC[VEC_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2;
           ARITH] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REPEAT CONJ_TAC THEN VECTOR_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 9. The three triangles of each sector, as images of the template.         *)
(* ------------------------------------------------------------------------- *)

let moi_lfi_ta = new_definition
 `moi_lfi_ta = {vec 0:real^2, inv(&2) % basis 1, inv(&2) % basis 2}`;;

let moi_lfi_tb = new_definition
 `moi_lfi_tb = {basis 1:real^2, basis 2, inv(&2) % basis 2}`;;

let moi_lfi_tc = new_definition
 `moi_lfi_tc = {basis 1:real^2, inv(&2) % basis 1, inv(&2) % basis 2}`;;

let moi_lfi_sa = new_definition
 `moi_lfi_sa m j = {moi_lfi_z, moi_lfi_y m j, moi_lfi_y m (j + 1)}`;;

let moi_lfi_sb = new_definition
 `moi_lfi_sb m j = {moi_lfi_x m j, moi_lfi_x m (j + 1), moi_lfi_y m (j + 1)}`;;

let moi_lfi_sc = new_definition
 `moi_lfi_sc m j = {moi_lfi_x m j, moi_lfi_y m j, moi_lfi_y m (j + 1)}`;;

let MOI_LFI_SECTOR_SETS = prove
 (`!m j. IMAGE (moi_lfi_phi m j) moi_lfi_ta = moi_lfi_sa m j /\
         IMAGE (moi_lfi_phi m j) moi_lfi_tb = moi_lfi_sb m j /\
         IMAGE (moi_lfi_phi m j) moi_lfi_tc = moi_lfi_sc m j /\
         IMAGE (moi_lfi_phi m j) {vec 0,basis 1,basis 2} =
         {moi_lfi_z, moi_lfi_x m j, moi_lfi_x m (j + 1)}`,
  REWRITE_TAC[moi_lfi_ta; moi_lfi_tb; moi_lfi_tc; moi_lfi_sa; moi_lfi_sb;
              moi_lfi_sc; IMAGE_CLAUSES; MOI_LFI_PHI_POINTS]);;

let MOI_LFI_PHI_HULL = prove
 (`!m j s. IMAGE (moi_lfi_phi m j) (convex hull s) =
           convex hull (IMAGE (moi_lfi_phi m j) s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONJUNCT1(SPEC_ALL MOI_LFI_PHI_AFFINE)] THEN
  MATCH_MP_TAC MOI_FSAP_AFFINE_HULL_IMAGE THEN
  REWRITE_TAC[CONJUNCT2(SPEC_ALL MOI_LFI_PHI_AFFINE)]);;

let MOI_LFI_PHI_INTER = prove
 (`!m j s t. 1 <= m /\ j < 4 * m
             ==> IMAGE (moi_lfi_phi m j) (s INTER t) =
                 IMAGE (moi_lfi_phi m j) s INTER IMAGE (moi_lfi_phi m j) t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC IMAGE_INTER_INJ THEN
  ASM_MESON_TAC[MOI_LFI_PHI_INJ]);;

let MOI_LFI_SECTOR_PAIR = prove
 (`!m j x y. 1 <= m /\ j < 4 * m /\
             x IN {moi_lfi_sa m j, moi_lfi_sb m j, moi_lfi_sc m j} /\
             y IN {moi_lfi_sa m j, moi_lfi_sb m j, moi_lfi_sc m j}
             ==> (convex hull x) INTER (convex hull y) SUBSET
                 convex hull (x INTER y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!tx ty. (convex hull tx) INTER (convex hull ty) SUBSET convex hull (tx INTER ty)
            ==> (convex hull (IMAGE (moi_lfi_phi m j) tx)) INTER
                (convex hull (IMAGE (moi_lfi_phi m j) ty)) SUBSET
                convex hull (IMAGE (moi_lfi_phi m j) tx INTER
                             IMAGE (moi_lfi_phi m j) ty)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[GSYM MOI_LFI_PHI_HULL; GSYM MOI_LFI_PHI_INTER; IMAGE_SUBSET];
    ALL_TAC] THEN
  MP_TAC MOI_LFI_TEMPLATE_FACTS THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[GSYM moi_lfi_ta; GSYM moi_lfi_tb; GSYM moi_lfi_tc] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!tx:real^2->bool. (convex hull tx) INTER (convex hull tx) SUBSET
                                  convex hull (tx INTER tx)` ASSUME_TAC THENL
   [REWRITE_TAC[INTER_IDEMPOT; SUBSET_REFL]; ALL_TAC] THEN
  UNDISCH_TAC `(x:real^2->bool) IN {moi_lfi_sa m j, moi_lfi_sb m j, moi_lfi_sc m j}` THEN
  UNDISCH_TAC `(y:real^2->bool) IN {moi_lfi_sa m j, moi_lfi_sb m j, moi_lfi_sc m j}` THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; GSYM MOI_LFI_SECTOR_SETS] THEN
  REPEAT(DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC)) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_MESON_TAC[INTER_COMM]);;

let MOI_LFI_SECTOR_UNION = prove
 (`!m j. convex hull (moi_lfi_sa m j) UNION convex hull (moi_lfi_sb m j) UNION
         convex hull (moi_lfi_sc m j) =
         convex hull {moi_lfi_z, moi_lfi_x m j, moi_lfi_x m (j + 1)}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM MOI_LFI_SECTOR_SETS] THEN
  REWRITE_TAC[GSYM MOI_LFI_PHI_HULL; GSYM IMAGE_UNION] THEN
  AP_TERM_TAC THEN MP_TAC MOI_LFI_TEMPLATE_FACTS THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[GSYM moi_lfi_ta; GSYM moi_lfi_tb; GSYM moi_lfi_tc] THEN
  SIMP_TAC[std_triangle]);;

(* ------------------------------------------------------------------------- *)
(* 10. The cone complex over the polygon, sector intersections, and the     *)
(* complex k0 of all template triangles of all sectors.                      *)
(* ------------------------------------------------------------------------- *)

let MOI_LFI_Z_RELINT = prove
 (`moi_lfi_z IN relative_interior std_triangle`,
  MATCH_MP_TAC(REWRITE_RULE[SUBSET] INTERIOR_SUBSET_RELATIVE_INTERIOR) THEN
  REWRITE_TAC[IN_INTERIOR; MOI_LFI_STD_REGION] THEN
  EXISTS_TAC `&1 / &10` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_BALL; IN_ELIM_THM] THEN X_GEN_TAC `x:real^2` THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`moi_lfi_z - x:real^2`; `1`] COMPONENT_LE_NORM) THEN
  MP_TAC(ISPECL [`moi_lfi_z - x:real^2`; `2`] COMPONENT_LE_NORM) THEN
  SIMP_TAC[VECTOR_SUB_COMPONENT; DIMINDEX_2; ARITH; MOI_LFI_Z_COMPONENTS] THEN
  UNDISCH_TAC `dist(moi_lfi_z,x:real^2) < &1 / &10` THEN REWRITE_TAC[dist] THEN
  REAL_ARITH_TAC);;

let moi_lfi_cc = new_definition
 `moi_lfi_cc m = moi_lfi_pcx m UNION
                 {convex hull (moi_lfi_z INSERT s) | s IN moi_lfi_pcx m}`;;

let MOI_LFI_CC_COMPLEX = prove
 (`!m. 1 <= m
       ==> simplicial_complex (moi_lfi_cc m) /\ UNIONS (moi_lfi_cc m) = std_triangle`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[moi_lfi_cc] THEN
  MATCH_MP_TAC MOI_CON_CONE_OVER_RF THEN EXISTS_TAC `&2:int` THEN
  ASM_SIMP_TAC[MOI_LFI_PCX_COMPLEX; MOI_LTD_STD_TRIANGLE_SIMPLEX;
               MOI_LFI_Z_RELINT; MOI_LTD_FRONTIER_SUBSET_TRIANGLE]);;

let MOI_LFI_SECTOR_IN_CC = prove
 (`!m j. j < 4 * m
         ==> convex hull {moi_lfi_z, moi_lfi_x m j, moi_lfi_x m (j + 1)} IN
             moi_lfi_cc m`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_lfi_cc; IN_UNION] THEN DISJ2_TAC THEN
  REWRITE_TAC[IN_ELIM_THM; moi_lfi_pcx] THEN
  EXISTS_TAC `convex hull {moi_lfi_x m j, moi_lfi_x m (j + 1)}` THEN
  REWRITE_TAC[GSYM HULL_INSERT] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  EXISTS_TAC `{moi_lfi_x m j, moi_lfi_x m (j + 1)}` THEN
  REWRITE_TAC[MOI_LFI_IN_VS] THEN DISJ1_TAC THEN EXISTS_TAC `j:num` THEN
  ASM_REWRITE_TAC[]);;

let MOI_LFI_SECTOR_INDEP = prove
 (`!m j. 1 <= m /\ j < 4 * m
         ==> ~affine_dependent {moi_lfi_z, moi_lfi_x m j, moi_lfi_x m (j + 1)} /\
             ~(moi_lfi_z = moi_lfi_x m j) /\ ~(moi_lfi_z = moi_lfi_x m (j + 1)) /\
             ~(moi_lfi_x m j = moi_lfi_x m (j + 1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`m:num`; `j:num`] MOI_LFI_SECTOR_DET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o MATCH_MP MOI_LFI_DET_INJ) THEN
  ASM_SIMP_TAC[MOI_LFI_X_NEXT_NE] THEN
  SUBGOAL_THEN `~(moi_lfi_z = moi_lfi_x m j) /\ ~(moi_lfi_z = moi_lfi_x m (j + 1))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`&1`; `&0`]);
      FIRST_X_ASSUM(MP_TAC o SPECL [`&0`; `&1`])] THEN
    ASM_REWRITE_TAC[VECTOR_SUB_REFL] THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_RZERO; VECTOR_ADD_LID;
                VECTOR_ADD_RID] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[]] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) AFFINE_DEPENDENT_CHOOSE o rand o snd) THEN
  REWRITE_TAC[AFFINE_INDEPENDENT_2] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; AFFINE_HULL_2; IN_ELIM_THM] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:real`; `b:real`]) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `moi_lfi_z = a % moi_lfi_x m j + b % moi_lfi_x m (j + 1)` THEN
    UNDISCH_TAC `a + b = &1` THEN
    REWRITE_TAC[REAL_ARITH `a + b = &1 <=> b = &1 - a`] THEN
    DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let MOI_LFI_SUC_MOD = prove
 (`!n j. j < n ==> (j + 1) MOD n = if j + 1 = n then 0 else j + 1`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[MOD_REFL] THEN
  MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

let MOI_LFI_IDX_ARITH = prove
 (`!n j j'. 4 <= n /\ j < n /\ j' < n /\ ~(j = j')
            ==> ~(j = (if j' + 1 = n then 0 else j' + 1) /\
                  (if j + 1 = n then 0 else j + 1) = j') /\
                ~((if j + 1 = n then 0 else j + 1) =
                  (if j' + 1 = n then 0 else j' + 1))`,
  REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC);;

let MOI_LFI_X_COMMON1 = prove
 (`!m j j' p. 1 <= m /\ j < 4 * m /\ j' < 4 * m /\ ~(j = j') /\
              p IN {moi_lfi_x m j, moi_lfi_x m (j + 1)} /\
              p IN {moi_lfi_x m j', moi_lfi_x m (j' + 1)}
              ==> (p = moi_lfi_x m j /\
                   j = (if j' + 1 = 4 * m then 0 else j' + 1)) \/
                  (p = moi_lfi_x m (j + 1) /\
                   (if j + 1 = 4 * m then 0 else j + 1) = j')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `moi_lfi_x m (j + 1) = moi_lfi_x m (if j + 1 = 4 * m then 0 else j + 1) /\
    moi_lfi_x m (j' + 1) = moi_lfi_x m (if j' + 1 = 4 * m then 0 else j' + 1)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_LFI_X_MOD; MOI_LFI_SUC_MOD]; ALL_TAC] THEN
  SUBGOAL_THEN `(if j + 1 = 4 * m then 0 else j + 1) < 4 * m /\
                (if j' + 1 = 4 * m then 0 else j' + 1) < 4 * m`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN COND_CASES_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`4 * m`; `j:num`; `j':num`] MOI_LFI_IDX_ARITH) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  UNDISCH_TAC `(p:real^2) IN {moi_lfi_x m j, moi_lfi_x m (j + 1)}` THEN
  UNDISCH_TAC `(p:real^2) IN {moi_lfi_x m j', moi_lfi_x m (j' + 1)}` THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  ABBREV_TAC `jj = if j + 1 = 4 * m then 0 else j + 1` THEN
  ABBREV_TAC `jj' = if j' + 1 = 4 * m then 0 else j' + 1` THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `p:real^2`)) THEN
  ASM_MESON_TAC[MOI_LFI_X_INJ]);;

let MOI_LFI_X_COMMON = prove
 (`!m j j' p q. 1 <= m /\ j < 4 * m /\ j' < 4 * m /\ ~(j = j') /\
                p IN {moi_lfi_x m j, moi_lfi_x m (j + 1)} /\
                p IN {moi_lfi_x m j', moi_lfi_x m (j' + 1)} /\
                q IN {moi_lfi_x m j, moi_lfi_x m (j + 1)} /\
                q IN {moi_lfi_x m j', moi_lfi_x m (j' + 1)}
                ==> p = q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`m:num`; `j:num`; `j':num`; `p:real^2`] MOI_LFI_X_COMMON1) THEN
  MP_TAC(SPECL [`m:num`; `j:num`; `j':num`; `q:real^2`] MOI_LFI_X_COMMON1) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`4 * m`; `j:num`; `j':num`] MOI_LFI_IDX_ARITH) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `jj = if j + 1 = 4 * m then 0 else j + 1` THEN
  ABBREV_TAC `jj' = if j' + 1 = 4 * m then 0 else j' + 1` THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let MOI_LFI_OFF_SEG = prove
 (`!z p q:real^2 c.
     ~(p$1 * q$2 - p$2 * q$1 = &0) /\ ~(c = &0)
     ==> ~(z + c % q IN segment[z,z + p]) /\ ~(z + c % p IN segment[z,z + q])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_LFI_DET_INJ) THEN
  REWRITE_TAC[IN_SEGMENT] THEN CONJ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`--t:real`; `c:real`]);
    FIRST_X_ASSUM(MP_TAC o SPECL [`c:real`; `--t:real`])] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN VECTOR_ARITH_TAC);;

let MOI_LFI_MID_SEGS = prove
 (`!z c:real^N.
     ~(z = c)
     ==> segment[z,midpoint(z,c)] INTER segment[midpoint(z,c),c] =
         {midpoint(z,c)} /\
         ~(midpoint(z,c) = z) /\ ~(midpoint(z,c) = c)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[MIDPOINT_EQ_ENDPOINT] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[IN_INTER; IN_SING] THEN EQ_TAC THENL
   [ALL_TAC; DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ENDS_IN_SEGMENT]] THEN
  REWRITE_TAC[IN_SEGMENT; midpoint] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(s / &2 - (&1 / &2 + t / &2)) % (c - z:real^N) = vec 0`
  MP_TAC THENL
   [UNDISCH_TAC `x = (&1 - s) % z + s % inv(&2) % (z + c:real^N)` THEN
    UNDISCH_TAC `x = (&1 - t) % inv(&2) % (z + c) + t % (c:real^N)` THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN
  SUBGOAL_THEN `~(c:real^N = z)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN SUBGOAL_THEN `t = &0 /\ s = &1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `x = (&1 - s) % z + s % inv(&2) % (z + c:real^N)` THEN
  ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC);;

let MOI_LFI_SECTOR_MEET = prove
 (`!m j j'. 1 <= m /\ j < 4 * m /\ j' < 4 * m
            ==> (convex hull {moi_lfi_z, moi_lfi_x m j, moi_lfi_x m (j + 1)}) INTER
                (convex hull {moi_lfi_z, moi_lfi_x m j', moi_lfi_x m (j' + 1)})
                SUBSET
                convex hull ({moi_lfi_z, moi_lfi_x m j, moi_lfi_x m (j + 1)} INTER
                             {moi_lfi_z, moi_lfi_x m j', moi_lfi_x m (j' + 1)})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`m:num`; `j:num`] MOI_LFI_SECTOR_INDEP) THEN
  MP_TAC(SPECL [`m:num`; `j':num`] MOI_LFI_SECTOR_INDEP) THEN
  MP_TAC(SPECL [`m:num`; `j:num`] MOI_LFI_SECTOR_IN_CC) THEN
  MP_TAC(SPECL [`m:num`; `j':num`] MOI_LFI_SECTOR_IN_CC) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`{moi_lfi_z, moi_lfi_x m j', moi_lfi_x m (j' + 1)}`,`v':real^2->bool`) THEN
  SPEC_TAC(`{moi_lfi_z, moi_lfi_x m j, moi_lfi_x m (j + 1)}`,`v:real^2->bool`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `FINITE (v:real^2->bool) /\ FINITE (v':real^2->bool)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(convex hull v INTER convex hull v') face_of convex hull (v:real^2->bool) /\
    (convex hull v INTER convex hull v') face_of convex hull (v':real^2->bool)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `m:num` MOI_LFI_CC_COMPLEX) THEN
    ASM_REWRITE_TAC[simplicial_complex] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `convex hull v INTER convex hull v' =
    convex hull {x:real^2 | x extreme_point_of (convex hull v INTER convex hull v')}`
  SUBST1_TAC THENL
   [MATCH_MP_TAC KREIN_MILMAN_MINKOWSKI THEN
    ASM_SIMP_TAC[CONVEX_INTER; CONVEX_CONVEX_HULL; COMPACT_INTER;
                 COMPACT_CONVEX_HULL; FINITE_IMP_COMPACT];
    ALL_TAC] THEN
  MATCH_MP_TAC HULL_MONO THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTER] THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`convex hull v INTER convex hull v':real^2->bool`;
                   `convex hull v:real^2->bool`; `x:real^2`] EXTREME_POINT_OF_FACE);
    MP_TAC(ISPECL [`convex hull v INTER convex hull v':real^2->bool`;
                   `convex hull v':real^2->bool`; `x:real^2`] EXTREME_POINT_OF_FACE)] THEN
  ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT]);;

let MOI_LFI_SECTOR_VS = prove
 (`!m j j'. 1 <= m /\ j < 4 * m /\ j' < 4 * m /\ ~(j = j')
            ==> {moi_lfi_z, moi_lfi_x m j, moi_lfi_x m (j + 1)} INTER
                {moi_lfi_z, moi_lfi_x m j', moi_lfi_x m (j' + 1)} SUBSET {moi_lfi_z} \/
                ?c. c IN {moi_lfi_x m j, moi_lfi_x m (j + 1)} /\
                    c IN {moi_lfi_x m j', moi_lfi_x m (j' + 1)} /\
                    {moi_lfi_z, moi_lfi_x m j, moi_lfi_x m (j + 1)} INTER
                    {moi_lfi_z, moi_lfi_x m j', moi_lfi_x m (j' + 1)} SUBSET
                    {moi_lfi_z, c}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`m:num`; `j:num`] MOI_LFI_SECTOR_INDEP) THEN
  MP_TAC(SPECL [`m:num`; `j':num`] MOI_LFI_SECTOR_INDEP) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `?c:real^2. c IN {moi_lfi_x m j, moi_lfi_x m (j + 1)} /\
                           c IN {moi_lfi_x m j', moi_lfi_x m (j' + 1)}` THENL
   [DISJ2_TAC THEN FIRST_X_ASSUM(X_CHOOSE_THEN `c:real^2` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `c:real^2` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `p:real^2` THEN STRIP_TAC THEN
    ASM_CASES_TAC `p:real^2 = moi_lfi_z` THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    MATCH_MP_TAC MOI_LFI_X_COMMON THEN
    MAP_EVERY EXISTS_TAC [`m:num`; `j:num`; `j':num`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    DISJ1_TAC THEN ASM SET_TAC[]]);;

let MOI_LFI_SECTOR_POINTS = prove
 (`!m j. let p = moi_lfi_x m j - moi_lfi_z and q = moi_lfi_x m (j + 1) - moi_lfi_z in
         moi_lfi_x m j = moi_lfi_z + p /\ moi_lfi_x m (j + 1) = moi_lfi_z + q /\
         moi_lfi_y m j = moi_lfi_z + inv(&2) % p /\
         moi_lfi_y m (j + 1) = moi_lfi_z + inv(&2) % q`,
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[moi_lfi_y; midpoint] THEN REPEAT CONJ_TAC THEN VECTOR_ARITH_TAC);;

let MOI_LFI_TEMPLATE_IN_SECTOR = prove
 (`!m j. moi_lfi_sa m j SUBSET
         convex hull {moi_lfi_z, moi_lfi_x m j, moi_lfi_x m (j + 1)} /\
         moi_lfi_sb m j SUBSET
         convex hull {moi_lfi_z, moi_lfi_x m j, moi_lfi_x m (j + 1)} /\
         moi_lfi_sc m j SUBSET
         convex hull {moi_lfi_z, moi_lfi_x m j, moi_lfi_x m (j + 1)} /\
         FINITE (moi_lfi_sa m j) /\ FINITE (moi_lfi_sb m j) /\
         FINITE (moi_lfi_sc m j)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[moi_lfi_sa; moi_lfi_sb; moi_lfi_sc; FINITE_INSERT; FINITE_EMPTY] THEN
  REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; moi_lfi_y] THEN
  SUBGOAL_THEN
   `moi_lfi_z IN convex hull {moi_lfi_z, moi_lfi_x m j, moi_lfi_x m (j + 1)} /\
    moi_lfi_x m j IN convex hull {moi_lfi_z, moi_lfi_x m j, moi_lfi_x m (j + 1)} /\
    moi_lfi_x m (j + 1) IN
    convex hull {moi_lfi_z, moi_lfi_x m j, moi_lfi_x m (j + 1)}`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MIDPOINT_IN_CONVEX; CONVEX_CONVEX_HULL]);;

let MOI_LFI_SPOKE_SPLIT = prove
 (`!m j x c. 1 <= m /\ j < 4 * m /\
             x IN {moi_lfi_sa m j, moi_lfi_sb m j, moi_lfi_sc m j} /\
             (c = moi_lfi_x m j \/ c = moi_lfi_x m (j + 1))
             ==> x INTER segment[moi_lfi_z,c] SUBSET {moi_lfi_z, midpoint(moi_lfi_z,c)} \/
                 x INTER segment[moi_lfi_z,c] SUBSET {midpoint(moi_lfi_z,c), c}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`m:num`; `j:num`] MOI_LFI_SECTOR_DET) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`m:num`; `j:num`] MOI_LFI_SECTOR_POINTS) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[GSYM moi_lfi_y] THEN
  SPEC_TAC(`moi_lfi_x m (j + 1) - moi_lfi_z`,`q:real^2`) THEN
  SPEC_TAC(`moi_lfi_x m j - moi_lfi_z`,`p:real^2`) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`moi_lfi_z`; `p:real^2`; `q:real^2`; `&1`] MOI_LFI_OFF_SEG) THEN
  MP_TAC(SPECL [`moi_lfi_z`; `p:real^2`; `q:real^2`; `inv(&2)`] MOI_LFI_OFF_SEG) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LID] THEN
  REWRITE_TAC[REAL_INV_EQ_0; REAL_OF_NUM_EQ; ARITH] THEN
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `(x:real^2->bool) IN {moi_lfi_sa m j, moi_lfi_sb m j, moi_lfi_sc m j}` THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[moi_lfi_sa; moi_lfi_sb; moi_lfi_sc] THEN
  ASM_REWRITE_TAC[midpoint; VECTOR_ARITH
   `inv(&2) % (z + z + p:real^2) = z + inv(&2) % p`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_LFI_EXT_SUBSET = prove
 (`!(s:real^N->bool) t z.
     z extreme_point_of s /\ z IN t /\ t SUBSET s ==> z extreme_point_of t`,
  REWRITE_TAC[extreme_point_of] THEN SET_TAC[]);;

let MOI_LFI_PAIR_MID_IN = prove
 (`!z c:real^N w.
     ~(z = c) /\ (w SUBSET {z,midpoint(z,c)} \/ w SUBSET {midpoint(z,c),c}) /\
     midpoint(z,c) IN convex hull w
     ==> midpoint(z,c) IN w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`z:real^N`; `c:real^N`] MOI_LFI_MID_SEGS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `midpoint(z:real^N,c) IN w` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `convex hull w SUBSET {z:real^N}` MP_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `convex hull {z:real^N}` THEN
      CONJ_TAC THENL [MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[];
                      REWRITE_TAC[CONVEX_HULL_SING; SUBSET_REFL]];
      ASM SET_TAC[]];
    SUBGOAL_THEN `convex hull w SUBSET {c:real^N}` MP_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `convex hull {c:real^N}` THEN
      CONJ_TAC THENL [MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[];
                      REWRITE_TAC[CONVEX_HULL_SING; SUBSET_REFL]];
      ASM SET_TAC[]]]);;

let MOI_LFI_PAIR_CROSS = prove
 (`!z c:real^N w w'.
     ~(z = c) /\ w SUBSET {z,midpoint(z,c)} /\ w' SUBSET {midpoint(z,c),c}
     ==> (convex hull w) INTER (convex hull w') SUBSET convex hull (w INTER w')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`z:real^N`; `c:real^N`] MOI_LFI_MID_SEGS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `p:real^N` THEN STRIP_TAC THEN
  SUBGOAL_THEN `p = midpoint(z:real^N,c)` SUBST_ALL_TAC THENL
   [SUBGOAL_THEN `(p:real^N) IN segment[z,midpoint(z,c)] INTER segment[midpoint(z,c),c]`
    MP_TAC THENL
     [REWRITE_TAC[IN_INTER; SEGMENT_CONVEX_HULL] THEN
      ASM_MESON_TAC[HULL_MONO; SUBSET];
      ASM_REWRITE_TAC[IN_SING]];
    ALL_TAC] THEN
  MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INTER] THEN
  CONJ_TAC THEN MATCH_MP_TAC MOI_LFI_PAIR_MID_IN THEN ASM_MESON_TAC[]);;

let MOI_LFI_HULL_PAIR_MEET = prove
 (`!z c:real^N u u'.
     ~(z = c) /\
     (u SUBSET {z,midpoint(z,c)} \/ u SUBSET {midpoint(z,c),c}) /\
     (u' SUBSET {z,midpoint(z,c)} \/ u' SUBSET {midpoint(z,c),c})
     ==> (convex hull u) INTER (convex hull u') SUBSET convex hull (u INTER u')`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC MP_TAC)) THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
   [MATCH_MP_TAC(SET_RULE `s = t ==> (s:real^N->bool) SUBSET t`) THEN
    MATCH_MP_TAC MOI_LFI_HULL_INTER_INDEP THEN
    EXISTS_TAC `{z:real^N,midpoint(z,c)}` THEN
    ASM_REWRITE_TAC[AFFINE_INDEPENDENT_2];
    ONCE_REWRITE_TAC[INTER_COMM] THEN
    MATCH_MP_TAC MOI_LFI_PAIR_CROSS THEN
    MAP_EVERY EXISTS_TAC [`z:real^N`; `c:real^N`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_LFI_PAIR_CROSS THEN
    MAP_EVERY EXISTS_TAC [`z:real^N`; `c:real^N`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC(SET_RULE `s = t ==> (s:real^N->bool) SUBSET t`) THEN
    MATCH_MP_TAC MOI_LFI_HULL_INTER_INDEP THEN
    EXISTS_TAC `{midpoint(z:real^N,c),c}` THEN
    ASM_REWRITE_TAC[AFFINE_INDEPENDENT_2]]);;

let MOI_LFI_Z_IN_TEMPLATE = prove
 (`!m j x. 1 <= m /\ j < 4 * m /\
           x IN {moi_lfi_sa m j, moi_lfi_sb m j, moi_lfi_sc m j} /\
           moi_lfi_z IN convex hull x
           ==> moi_lfi_z IN x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC EXTREME_POINT_OF_CONVEX_HULL THEN
  MATCH_MP_TAC MOI_LFI_EXT_SUBSET THEN
  EXISTS_TAC `convex hull {moi_lfi_z, moi_lfi_x m j, moi_lfi_x m (j + 1)}` THEN
  ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT;
               MOI_LFI_SECTOR_INDEP] THEN
  REWRITE_TAC[IN_INSERT] THEN MATCH_MP_TAC HULL_MINIMAL THEN
  REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
  UNDISCH_TAC `(x:real^2->bool) IN {moi_lfi_sa m j, moi_lfi_sb m j, moi_lfi_sc m j}` THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  REPEAT(DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC)) THEN
  REWRITE_TAC[MOI_LFI_TEMPLATE_IN_SECTOR]);;

let MOI_LFI_CROSS_PAIR = prove
 (`!m j j' x y. 1 <= m /\ j < 4 * m /\ j' < 4 * m /\ ~(j = j') /\
                x IN {moi_lfi_sa m j, moi_lfi_sb m j, moi_lfi_sc m j} /\
                y IN {moi_lfi_sa m j', moi_lfi_sb m j', moi_lfi_sc m j'}
                ==> (convex hull x) INTER (convex hull y) SUBSET
                    convex hull (x INTER y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `v = {moi_lfi_z, moi_lfi_x m j, moi_lfi_x m (j + 1)}` THEN
  ABBREV_TAC `v' = {moi_lfi_z, moi_lfi_x m j', moi_lfi_x m (j' + 1)}` THEN
  SUBGOAL_THEN `(x:real^2->bool) SUBSET convex hull v /\ FINITE x /\
                (y:real^2->bool) SUBSET convex hull v' /\ FINITE y`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["v"; "v'"] THEN
    UNDISCH_TAC `(x:real^2->bool) IN {moi_lfi_sa m j, moi_lfi_sb m j, moi_lfi_sc m j}` THEN
    UNDISCH_TAC `(y:real^2->bool) IN {moi_lfi_sa m j', moi_lfi_sb m j', moi_lfi_sc m j'}` THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    REPEAT(DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC)) THEN
    REWRITE_TAC[MOI_LFI_TEMPLATE_IN_SECTOR];
    ALL_TAC] THEN
  SUBGOAL_THEN `(convex hull x) INTER (convex hull y) SUBSET
                convex hull ((v:real^2->bool) INTER v')` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `(convex hull v) INTER (convex hull (v':real^2->bool))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `(a:real^2->bool) SUBSET c /\ b SUBSET d ==> a INTER b SUBSET c INTER d`) THEN
      CONJ_TAC THEN MATCH_MP_TAC HULL_MINIMAL THEN
      ASM_REWRITE_TAC[CONVEX_CONVEX_HULL];
      MAP_EVERY EXPAND_TAC ["v"; "v'"] THEN MATCH_MP_TAC MOI_LFI_SECTOR_MEET THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`m:num`; `j:num`; `j':num`] MOI_LFI_SECTOR_VS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `p:real^2` THEN STRIP_TAC THEN
    SUBGOAL_THEN `p = moi_lfi_z` SUBST_ALL_TAC THENL
     [SUBGOAL_THEN `(p:real^2) IN convex hull {moi_lfi_z}` MP_TAC THENL
       [MATCH_MP_TAC(SET_RULE `!s t:real^2->bool. p IN s /\ s SUBSET t ==> p IN t`) THEN
        EXISTS_TAC `convex hull (v INTER v':real^2->bool)` THEN
        CONJ_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC HULL_MONO THEN ASM_REWRITE_TAC[]];
        REWRITE_TAC[CONVEX_HULL_SING; IN_SING]];
      ALL_TAC] THEN
    MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INTER] THEN
    CONJ_TAC THEN MATCH_MP_TAC MOI_LFI_Z_IN_TEMPLATE THENL
     [EXISTS_TAC `m:num` THEN EXISTS_TAC `j:num`;
      EXISTS_TAC `m:num` THEN EXISTS_TAC `j':num`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[moi_lfi_z,c] face_of convex hull (v:real^2->bool) /\
                segment[moi_lfi_z,c] face_of convex hull (v':real^2->bool)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MAP_EVERY EXPAND_TAC ["v"; "v'"] THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT; MOI_LFI_SECTOR_INDEP] THEN
    CONJ_TAC THEN EXISTS_TAC `{moi_lfi_z,c}` THEN REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(convex hull x) INTER segment[moi_lfi_z,c] =
                convex hull (x INTER segment[moi_lfi_z,c]) /\
                (convex hull y) INTER segment[moi_lfi_z,c] =
                convex hull (y INTER segment[moi_lfi_z,c])`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_LFI_HULL_INTER_FACE THENL
     [EXISTS_TAC `convex hull v:real^2->bool`;
      EXISTS_TAC `convex hull v':real^2->bool`] THEN
    ASM_REWRITE_TAC[CONVEX_CONVEX_HULL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(convex hull x) INTER (convex hull y) SUBSET segment[moi_lfi_z,c]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `convex hull ((v:real^2->bool) INTER v')` THEN
    ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `convex hull ((x INTER segment[moi_lfi_z,c]) INTER
                           (y INTER segment[moi_lfi_z,c]))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `(convex hull (x INTER segment[moi_lfi_z,c])) INTER
                (convex hull (y INTER segment[moi_lfi_z,c]))` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `(convex hull x) INTER segment[moi_lfi_z,c] =
                   convex hull (x INTER segment[moi_lfi_z,c])` THEN
      UNDISCH_TAC `(convex hull y) INTER segment[moi_lfi_z,c] =
                   convex hull (y INTER segment[moi_lfi_z,c])` THEN
      REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN ASM SET_TAC[];
      MATCH_MP_TAC MOI_LFI_HULL_PAIR_MEET THEN
      MAP_EVERY EXISTS_TAC [`moi_lfi_z`; `c:real^2`] THEN
      REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[MOI_LFI_SECTOR_INDEP; IN_INSERT; NOT_IN_EMPTY];
        MATCH_MP_TAC MOI_LFI_SPOKE_SPLIT THEN
        MAP_EVERY EXISTS_TAC [`m:num`; `j:num`] THEN ASM_REWRITE_TAC[] THEN
        ASM SET_TAC[];
        MATCH_MP_TAC MOI_LFI_SPOKE_SPLIT THEN
        MAP_EVERY EXISTS_TAC [`m:num`; `j':num`] THEN ASM_REWRITE_TAC[] THEN
        ASM SET_TAC[]]];
    MATCH_MP_TAC HULL_MONO THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 11. The domain complex k0: all faces of the template triangles of all     *)
(* sectors.  It is a simplicial complex triangulating std_triangle.          *)
(* ------------------------------------------------------------------------- *)

let MOI_LFI_TEMPLATE_INDEP = prove
 (`~affine_dependent moi_lfi_ta /\ ~affine_dependent moi_lfi_tb /\
   ~affine_dependent moi_lfi_tc`,
  REWRITE_TAC[moi_lfi_ta; moi_lfi_tb; moi_lfi_tc] THEN REPEAT CONJ_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) AFFINE_DEPENDENT_CHOOSE o rand o snd) THEN
  REWRITE_TAC[AFFINE_INDEPENDENT_2] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DE_MORGAN_THM; AFFINE_HULL_2; IN_INSERT; NOT_IN_EMPTY;
              IN_ELIM_THM; NOT_EXISTS_THM] THEN
  DISJ2_TAC THEN MAP_EVERY X_GEN_TAC [`u:real`; `v:real`] THEN
  REWRITE_TAC[MOI_LFI_COMPONENTS_2] THEN
  SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT;
           BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC);;

let MOI_LFI_SECTOR_SETS_INDEP = prove
 (`!m j. 1 <= m /\ j < 4 * m
         ==> ~affine_dependent (moi_lfi_sa m j) /\
             ~affine_dependent (moi_lfi_sb m j) /\
             ~affine_dependent (moi_lfi_sc m j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM MOI_LFI_SECTOR_SETS] THEN
  REWRITE_TAC[CONJUNCT1(SPEC_ALL MOI_LFI_PHI_AFFINE)] THEN
  REWRITE_TAC[MOI_FSAP_AFFINE_IMAGE_SPLIT; AFFINE_DEPENDENT_TRANSLATION_EQ] THEN
  SUBGOAL_THEN
   `!s. affine_dependent
          (IMAGE (\u:real^2. u$1 % (moi_lfi_x m j - moi_lfi_z) +
                             u$2 % (moi_lfi_x m (j + 1) - moi_lfi_z)) s) <=>
        affine_dependent s`
   (fun th -> REWRITE_TAC[th; MOI_LFI_TEMPLATE_INDEP]) THEN
  GEN_TAC THEN MATCH_MP_TAC AFFINE_DEPENDENT_LINEAR_IMAGE_EQ THEN
  REWRITE_TAC[CONJUNCT2(SPEC_ALL MOI_LFI_PHI_AFFINE)] THEN
  MAP_EVERY X_GEN_TAC [`u:real^2`; `v:real^2`] THEN DISCH_TAC THEN
  MATCH_MP_TAC MOI_LFI_PHI_INJ THEN
  MAP_EVERY EXISTS_TAC [`m:num`; `j:num`] THEN ASM_REWRITE_TAC[moi_lfi_phi] THEN
  POP_ASSUM MP_TAC THEN VECTOR_ARITH_TAC);;

let moi_lfi_mx = new_definition
 `moi_lfi_mx m =
    {moi_lfi_sa m j | j | j < 4 * m} UNION {moi_lfi_sb m j | j | j < 4 * m} UNION
    {moi_lfi_sc m j | j | j < 4 * m}`;;

let moi_lfi_k0 = new_definition
 `moi_lfi_k0 m =
    {convex hull w | w IN {w:real^2->bool | ?x. x IN moi_lfi_mx m /\ w SUBSET x}}`;;

let MOI_LFI_IN_MX = prove
 (`!m x. x IN moi_lfi_mx m <=>
         ?j. j < 4 * m /\ x IN {moi_lfi_sa m j, moi_lfi_sb m j, moi_lfi_sc m j}`,
  REWRITE_TAC[moi_lfi_mx; IN_UNION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
  MESON_TAC[]);;

let MOI_LFI_K0_COMPLEX = prove
 (`!m. 1 <= m ==> simplicial_complex (moi_lfi_k0 m)`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[moi_lfi_k0] THEN
  MATCH_MP_TAC MOI_LFI_MAXHULLS_COMPLEX THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[moi_lfi_mx; FINITE_UNION] THEN REPEAT CONJ_TAC THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
    REWRITE_TAC[FINITE_NUMSEG_LT];
    REWRITE_TAC[MOI_LFI_IN_MX; IN_INSERT; NOT_IN_EMPTY] THEN
    GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[MOI_LFI_SECTOR_SETS_INDEP; MOI_LFI_TEMPLATE_IN_SECTOR];
    REWRITE_TAC[MOI_LFI_IN_MX] THEN
    MAP_EVERY X_GEN_TAC [`x:real^2->bool`; `y:real^2->bool`] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `j':num` STRIP_ASSUME_TAC)) THEN
    ASM_CASES_TAC `j:num = j'` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC MOI_LFI_SECTOR_PAIR THEN
      EXISTS_TAC `m:num` THEN EXISTS_TAC `j':num` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_LFI_CROSS_PAIR THEN
      MAP_EVERY EXISTS_TAC [`m:num`; `j:num`; `j':num`] THEN
      ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* 12. Union of k0, the frontier as a subcomplex, interior points, and the   *)
(* ring R and inner region D' with R INTER D' inside the inner polygon Q.    *)
(* ------------------------------------------------------------------------- *)

let MOI_LFI_X_IN_STD = prove
 (`!m j. 1 <= m ==> moi_lfi_x m j IN std_triangle`,
  MESON_TAC[MOI_LFI_X_IN_FRONTIER; MOI_LTD_FRONTIER_SUBSET_TRIANGLE; SUBSET]);;

let MOI_LFI_Z_IN_STD = prove
 (`moi_lfi_z IN std_triangle`,
  MESON_TAC[MOI_LFI_Z_RELINT; RELATIVE_INTERIOR_SUBSET; SUBSET]);;

let MOI_LFI_SECTOR_SUBSET = prove
 (`!m j. 1 <= m
         ==> convex hull {moi_lfi_z, moi_lfi_x m j, moi_lfi_x m (j + 1)} SUBSET
             std_triangle`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HULL_MINIMAL THEN
  REWRITE_TAC[MOI_LTD_STD_TRIANGLE_BASIC; INSERT_SUBSET; EMPTY_SUBSET] THEN
  ASM_SIMP_TAC[MOI_LFI_X_IN_STD; MOI_LFI_Z_IN_STD]);;

let MOI_LFI_SECTORS_UNION = prove
 (`!m. 1 <= m
       ==> UNIONS {convex hull {moi_lfi_z, moi_lfi_x m j, moi_lfi_x m (j + 1)} |
                   j | j < 4 * m} = std_triangle`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
    ASM_MESON_TAC[MOI_LFI_SECTOR_SUBSET; SUBSET];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV
    [SYM(CONJUNCT2(MATCH_MP MOI_LFI_CC_COMPLEX th))]) THEN
  REWRITE_TAC[SUBSET; IN_UNIONS; moi_lfi_cc; IN_UNION; IN_ELIM_THM;
              moi_lfi_pcx] THEN
  X_GEN_TAC `p:real^2` THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^2->bool` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `!w. w IN moi_lfi_vs m ==> ?j. j < 4 * m /\
                                  w SUBSET {moi_lfi_x m j, moi_lfi_x m (j + 1)}`
  ASSUME_TAC THENL
   [REWRITE_TAC[MOI_LFI_IN_VS] THEN GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THENL
     [EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[SUBSET_REFL];
      EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      EXISTS_TAC `0` THEN REWRITE_TAC[EMPTY_SUBSET] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `w:real^2->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `convex hull {moi_lfi_z, moi_lfi_x m j, moi_lfi_x m (j + 1)}` THEN
    CONJ_TAC THENL [EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(p:real^2) IN t` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET t ==> (p:real^2) IN s ==> p IN t`) THEN
    MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^2->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `convex hull {moi_lfi_z, moi_lfi_x m j, moi_lfi_x m (j + 1)}` THEN
    CONJ_TAC THENL [EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(p:real^2) IN t` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET t ==> (p:real^2) IN s ==> p IN t`) THEN
    ONCE_REWRITE_TAC[GSYM HULL_INSERT] THEN MATCH_MP_TAC HULL_MONO THEN
    ASM SET_TAC[]]);;

let MOI_LFI_Y_RELINT = prove
 (`!m j. 1 <= m ==> moi_lfi_y m j IN relative_interior std_triangle`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_lfi_y] THEN
  SUBGOAL_THEN `~(moi_lfi_z = moi_lfi_x m j)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(SPECL [`m:num`; `j:num`] MOI_LFI_X_IN_FRONTIER) THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[relative_frontier; IN_DIFF; MOI_LFI_Z_RELINT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`std_triangle`; `moi_lfi_z`; `moi_lfi_x m j`]
    IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CLOSURE_CLOSED; MOI_LTD_STD_TRIANGLE_BASIC; MOI_LFI_X_IN_STD;
                 MOI_LFI_Z_RELINT];
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[MIDPOINT_IN_SEGMENT]]);;

let MOI_LFI_NOT_FRONTIER = prove
 (`!m j. 1 <= m
         ==> ~(moi_lfi_z IN relative_frontier std_triangle) /\
             ~(moi_lfi_y m j IN relative_frontier std_triangle)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[relative_frontier; IN_DIFF] THEN
  ASM_SIMP_TAC[MOI_LFI_Z_RELINT; MOI_LFI_Y_RELINT]);;

let MOI_LFI_K0_UNION = prove
 (`!m. 1 <= m ==> UNIONS (moi_lfi_k0 m) = std_triangle`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV
    [SYM(MATCH_MP MOI_LFI_SECTORS_UNION th)]) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET; moi_lfi_k0; IN_ELIM_THM] THEN
    X_GEN_TAC `s:real^2->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^2->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `x:real^2->bool` STRIP_ASSUME_TAC) SUBST1_TAC)) THEN
    UNDISCH_TAC `(x:real^2->bool) IN moi_lfi_mx m` THEN
    REWRITE_TAC[MOI_LFI_IN_MX] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `convex hull {moi_lfi_z, moi_lfi_x m j, moi_lfi_x m (j + 1)}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `x:real^2->bool` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(x:real^2->bool) IN {moi_lfi_sa m j, moi_lfi_sb m j, moi_lfi_sc m j}` THEN
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
      REPEAT(DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC)) THEN
      REWRITE_TAC[MOI_LFI_TEMPLATE_IN_SECTOR];
      MATCH_MP_TAC(SET_RULE `(s:real^2->bool) IN f ==> s SUBSET UNIONS f`) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM MOI_LFI_SECTOR_UNION; UNION_SUBSET] THEN
    REPEAT CONJ_TAC THEN
    MATCH_MP_TAC(SET_RULE `(s:real^2->bool) IN f ==> s SUBSET UNIONS f`) THEN
    REWRITE_TAC[moi_lfi_k0; IN_ELIM_THM] THENL
     [EXISTS_TAC `moi_lfi_sa m j`; EXISTS_TAC `moi_lfi_sb m j`;
      EXISTS_TAC `moi_lfi_sc m j`] THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC(MESON[SUBSET_REFL] `(P:(real^2->bool)->bool) s ==> ?x. P x /\ s SUBSET x`) THEN
    REWRITE_TAC[MOI_LFI_IN_MX] THEN EXISTS_TAC `j:num` THEN
    ASM_REWRITE_TAC[IN_INSERT]]);;

(* ------------------------------------------------------------------------- *)
(* 13. The ring complex rc (faces of the ring triangles), the ring R, the   *)
(* inner region D', the inner polygon Q, and their mutual position.          *)
(* ------------------------------------------------------------------------- *)

let MOI_LFI_SUBCOMPLEX = prove
 (`!(k:(real^N->bool)->bool) k'.
     simplicial_complex k /\ k' SUBSET k /\
     (!s t. s IN k' /\ t face_of s ==> t IN k')
     ==> simplicial_complex k'`,
  REWRITE_TAC[simplicial_complex; SUBSET] THEN MESON_TAC[FINITE_SUBSET; SUBSET]);;

let moi_lfi_rc = new_definition
 `moi_lfi_rc m =
    {convex hull w | w IN {w:real^2->bool | ?j. j < 4 * m /\
                          (w SUBSET moi_lfi_sb m j \/ w SUBSET moi_lfi_sc m j)}}`;;

let moi_lfi_ring = new_definition
 `moi_lfi_ring m = UNIONS (moi_lfi_rc m)`;;

let moi_lfi_inner = new_definition
 `moi_lfi_inner m = UNIONS {convex hull (moi_lfi_sa m j) | j | j < 4 * m}`;;

let moi_lfi_q = new_definition
 `moi_lfi_q = IMAGE (\x. midpoint(moi_lfi_z,x)) (relative_frontier std_triangle)`;;

let MOI_LFI_RC_COMPLEX = prove
 (`!m. 1 <= m ==> moi_lfi_rc m SUBSET moi_lfi_k0 m /\
                  simplicial_complex (moi_lfi_rc m)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `moi_lfi_rc m SUBSET moi_lfi_k0 m` ASSUME_TAC THENL
   [REWRITE_TAC[moi_lfi_rc; moi_lfi_k0; SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `s:real^2->bool` THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `w:real^2->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [EXISTS_TAC `moi_lfi_sb m j`; EXISTS_TAC `moi_lfi_sc m j`] THEN
    ASM_REWRITE_TAC[MOI_LFI_IN_MX] THEN EXISTS_TAC `j:num` THEN
    ASM_REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_LFI_SUBCOMPLEX THEN
  EXISTS_TAC `moi_lfi_k0 m` THEN ASM_SIMP_TAC[MOI_LFI_K0_COMPLEX] THEN
  REWRITE_TAC[moi_lfi_rc; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`s:real^2->bool`; `t:real^2->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^2->bool`
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) SUBST_ALL_TAC)) THEN
  (SUBGOAL_THEN `~affine_dependent (w:real^2->bool)` ASSUME_TAC THENL
    [ASM_MESON_TAC[AFFINE_INDEPENDENT_SUBSET; MOI_LFI_SECTOR_SETS_INDEP];
     ALL_TAC]) THEN
  UNDISCH_TAC `t face_of convex hull (w:real^2->bool)` THEN
  ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `w':real^2->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `w':real^2->bool` THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_LFI_MID_IMAGE_SEGMENT = prove
 (`!a b z:real^N. IMAGE (\x. midpoint(z,x)) (segment[a,b]) =
                  segment[midpoint(z,a),midpoint(z,b)]`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `(\x:real^N. midpoint(z,x)) = (\x. (\x. inv(&2) % x) x + inv(&2) % z)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; midpoint] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
  MP_TAC(BETA_RULE(ISPECL [`\x:real^N. inv(&2) % x`; `inv(&2) % z:real^N`;
                           `{a:real^N,b}`] MOI_FSAP_AFFINE_HULL_IMAGE)) THEN
  ANTS_TAC THENL [REWRITE_TAC[linear] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[IMAGE_CLAUSES; midpoint] THEN
  REWRITE_TAC[VECTOR_ARITH `inv(&2) % a + inv(&2) % z:real^N = inv(&2) % (z + a)`]);;

let MOI_LFI_FRONTIER_SEGS = prove
 (`!m. 1 <= m
       ==> relative_frontier std_triangle =
           UNIONS {segment[moi_lfi_x m j,moi_lfi_x m (j + 1)] | j | j < 4 * m}`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[MOI_LFI_FRONTIER_IMAGE; SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1;
                DROP_VEC; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `t:real^1` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`m:num`; `t:real^1`] MOI_LFI_PARAM_COVER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `segment[moi_lfi_x m j,moi_lfi_x m (j + 1)]` THEN CONJ_TAC THENL
     [EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[MOI_LFI_X_SEGMENT] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP];
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[MOI_LFI_X_SEGMENT] THEN
    REWRITE_TAC[MOI_LFI_FRONTIER_IMAGE] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
    SUBGOAL_THEN `&0 < &(4 * m)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISJ2_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS];
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_OF_NUM_LE] THEN ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LID; REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC]]);;

let MOI_LFI_Q_SEGS = prove
 (`!m. 1 <= m
       ==> moi_lfi_q =
           UNIONS {segment[moi_lfi_y m j,moi_lfi_y m (j + 1)] | j | j < 4 * m}`,
  GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[moi_lfi_q; MOI_LFI_FRONTIER_SEGS] THEN
  REWRITE_TAC[moi_lfi_y; GSYM MOI_LFI_MID_IMAGE_SEGMENT] THEN
  REWRITE_TAC[IMAGE_UNIONS] THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF]);;

let MOI_LFI_RING_HULLS = prove
 (`!m j. j < 4 * m
         ==> convex hull (moi_lfi_sb m j) SUBSET moi_lfi_ring m /\
             convex hull (moi_lfi_sc m j) SUBSET moi_lfi_ring m`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[moi_lfi_ring] THEN
  MATCH_MP_TAC(SET_RULE `(s:real^2->bool) IN f /\ t IN f
                         ==> s SUBSET UNIONS f /\ t SUBSET UNIONS f`) THEN
  REWRITE_TAC[moi_lfi_rc; IN_ELIM_THM] THEN CONJ_TAC THENL
   [EXISTS_TAC `moi_lfi_sb m j`; EXISTS_TAC `moi_lfi_sc m j`] THEN
  REWRITE_TAC[] THEN EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[SUBSET_REFL]);;

let MOI_LFI_RING_INNER_Q = prove
 (`!m. 1 <= m ==> moi_lfi_ring m INTER moi_lfi_inner m SUBSET moi_lfi_q`,
  GEN_TAC THEN DISCH_TAC THEN GEN_REWRITE_TAC I [SUBSET] THEN
  X_GEN_TAC `p:real^2` THEN
  REWRITE_TAC[IN_INTER; moi_lfi_ring; moi_lfi_inner; IN_UNIONS;
              moi_lfi_rc; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `t:real^2->bool` (CONJUNCTS_THEN2
     (X_CHOOSE_THEN `w:real^2->bool` (CONJUNCTS_THEN2
       (X_CHOOSE_THEN `j:num` (CONJUNCTS_THEN ASSUME_TAC)) ASSUME_TAC))
     ASSUME_TAC))
   (X_CHOOSE_THEN `t':real^2->bool` (CONJUNCTS_THEN2
     (X_CHOOSE_THEN `j':num` STRIP_ASSUME_TAC) ASSUME_TAC))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `t':real^2->bool`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `t:real^2->bool`)) THEN
  ASM_SIMP_TAC[MOI_LFI_Q_SEGS; IN_UNIONS; IN_ELIM_THM] THEN
  EXISTS_TAC `segment[moi_lfi_y m j,moi_lfi_y m (j + 1)]` THEN
  CONJ_TAC THENL [EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
  SUBGOAL_THEN `?x. x IN {moi_lfi_sb m j, moi_lfi_sc m j} /\ (w:real^2->bool) SUBSET x`
   STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th))) THENL
     [EXISTS_TAC `moi_lfi_sb m j`; EXISTS_TAC `moi_lfi_sc m j`] THEN
    ASM_REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^2) IN convex hull x` ASSUME_TAC THENL
   [SUBGOAL_THEN `convex hull (w:real^2->bool) SUBSET convex hull x` MP_TAC THENL
     [MATCH_MP_TAC HULL_MONO THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^2) IN convex hull (x INTER moi_lfi_sa m j')` MP_TAC THENL
   [SUBGOAL_THEN `convex hull x INTER convex hull (moi_lfi_sa m j') SUBSET
                  convex hull (x INTER moi_lfi_sa m j')` MP_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[SUBSET; IN_INTER] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]] THEN
    ASM_CASES_TAC `j:num = j'` THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `j:num = j'`)) THEN
      MATCH_MP_TAC MOI_LFI_SECTOR_PAIR THEN
      MAP_EVERY EXISTS_TAC [`m:num`; `j':num`] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(x:real^2->bool) IN {moi_lfi_sb m j', moi_lfi_sc m j'}` THEN
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[];
      MATCH_MP_TAC MOI_LFI_CROSS_PAIR THEN
      MAP_EVERY EXISTS_TAC [`m:num`; `j:num`; `j':num`] THEN
      ASM_REWRITE_TAC[IN_INSERT] THEN
      UNDISCH_TAC `(x:real^2->bool) IN {moi_lfi_sb m j, moi_lfi_sc m j}` THEN
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE `s SUBSET t ==> (p:real^2) IN s ==> p IN t`) THEN
  MATCH_MP_TAC HULL_MONO THEN
  SUBGOAL_THEN `!k. ~(moi_lfi_x m k IN moi_lfi_sa m j')` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[moi_lfi_sa; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
    MP_TAC(SPECL [`m:num`; `k:num`] MOI_LFI_X_IN_FRONTIER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REPEAT CONJ_TAC THEN DISCH_THEN(SUBST_ALL_TAC) THEN
    ASM_MESON_TAC[MOI_LFI_NOT_FRONTIER];
    ALL_TAC] THEN
  UNDISCH_TAC `(x:real^2->bool) IN {moi_lfi_sb m j, moi_lfi_sc m j}` THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
  MP_TAC(SPEC `j:num` (ASSUME `!k. ~(moi_lfi_x m k IN moi_lfi_sa m j')`)) THEN
  MP_TAC(SPEC `j + 1` (ASSUME `!k. ~(moi_lfi_x m k IN moi_lfi_sa m j')`)) THEN
  REWRITE_TAC[moi_lfi_sb; moi_lfi_sc] THEN SET_TAC[]);;

let MOI_LFI_RING_INNER = prove
 (`!m. 1 <= m
       ==> moi_lfi_ring m UNION moi_lfi_inner m = std_triangle /\
           moi_lfi_ring m INTER moi_lfi_inner m SUBSET moi_lfi_q /\
           moi_lfi_q SUBSET moi_lfi_ring m /\
           relative_frontier std_triangle SUBSET moi_lfi_ring m /\
           moi_lfi_inner m SUBSET relative_interior std_triangle`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
       [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV
          [SYM(MATCH_MP MOI_LFI_K0_UNION th)]) THEN
        REWRITE_TAC[moi_lfi_ring] THEN MATCH_MP_TAC SUBSET_UNIONS THEN
        ASM_SIMP_TAC[MOI_LFI_RC_COMPLEX];
        REWRITE_TAC[moi_lfi_inner; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `convex hull {moi_lfi_z, moi_lfi_x m j, moi_lfi_x m (j + 1)}` THEN
        ASM_SIMP_TAC[MOI_LFI_SECTOR_SUBSET] THEN MATCH_MP_TAC HULL_MINIMAL THEN
        REWRITE_TAC[CONVEX_CONVEX_HULL; MOI_LFI_TEMPLATE_IN_SECTOR]];
      FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV
        [SYM(MATCH_MP MOI_LFI_SECTORS_UNION th)]) THEN
      REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      REWRITE_TAC[GSYM MOI_LFI_SECTOR_UNION; UNION_SUBSET] THEN
      ASM_SIMP_TAC[MOI_LFI_RING_HULLS; SUBSET_UNION; SET_RULE
       `(s:real^2->bool) SUBSET a ==> s SUBSET a UNION b`] THEN
      MATCH_MP_TAC(SET_RULE `(s:real^2->bool) SUBSET b ==> s SUBSET a UNION b`) THEN
      REWRITE_TAC[moi_lfi_inner] THEN
      MATCH_MP_TAC(SET_RULE `(s:real^2->bool) IN f ==> s SUBSET UNIONS f`) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[]];
    ASM_SIMP_TAC[MOI_LFI_RING_INNER_Q];
    ASM_SIMP_TAC[MOI_LFI_Q_SEGS; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `convex hull (moi_lfi_sc m j)` THEN
    ASM_SIMP_TAC[MOI_LFI_RING_HULLS] THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL; moi_lfi_sc] THEN
    MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    ASM_SIMP_TAC[MOI_LFI_FRONTIER_SEGS; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `convex hull (moi_lfi_sb m j)` THEN
    ASM_SIMP_TAC[MOI_LFI_RING_HULLS] THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL; moi_lfi_sb] THEN
    MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    REWRITE_TAC[moi_lfi_inner; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC HULL_MINIMAL THEN
    SIMP_TAC[CONVEX_RELATIVE_INTERIOR; MOI_LTD_STD_TRIANGLE_BASIC] THEN
    REWRITE_TAC[moi_lfi_sa; INSERT_SUBSET; EMPTY_SUBSET] THEN
    ASM_SIMP_TAC[MOI_LFI_Z_RELINT; MOI_LFI_Y_RELINT]]);;

(* ------------------------------------------------------------------------- *)
(* 14. Iterated subdivisions refine k0; sectors meet the frontier in their   *)
(* outer edge; fullness of the frontier in every ITER n sd k0; k0 simplices *)
(* off the inner region are ring simplices; radial segments in the ring.     *)
(* ------------------------------------------------------------------------- *)

let MOI_LFI_ITER_REFINES = prove
 (`!k:(real^N->bool)->bool.
     simplicial_complex k
     ==> !n s. s IN ITER n barycentric_subdivision k /\ ~(s = {})
               ==> ?t. t IN k /\ s SUBSET t`,
  GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN REWRITE_TAC[ITER] THENL
   [MESON_TAC[SUBSET_REFL]; ALL_TAC] THEN
  X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPEC `ITER n barycentric_subdivision (k:(real^N->bool)->bool)`
    BARYCENTRIC_SUBDIVISION_REFINES) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`k:(real^N->bool)->bool`; `n:num`] MOI_FSAP_ITER) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[MOI_SIMPLICIAL_COMPLEX_LF];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t':real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t':real^N->bool`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[SUBSET_TRANS]);;

let MOI_LFI_SEG_FRONTIER = prove
 (`!m j. 1 <= m /\ j < 4 * m
         ==> segment[moi_lfi_x m j,moi_lfi_x m (j + 1)] SUBSET
             relative_frontier std_triangle`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MOI_LFI_FRONTIER_SEGS] THEN
  MATCH_MP_TAC(SET_RULE `(t:real^2->bool) IN u ==> t SUBSET UNIONS u`) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[]);;

let MOI_LFI_SECTOR_FRONTIER = prove
 (`!m j. 1 <= m /\ j < 4 * m
         ==> convex hull {moi_lfi_z, moi_lfi_x m j, moi_lfi_x m (j + 1)} INTER
             relative_frontier std_triangle SUBSET
             segment[moi_lfi_x m j,moi_lfi_x m (j + 1)]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; IN_INTER] THEN
  X_GEN_TAC `p:real^2` THEN
  MP_TAC(ISPECL [`{moi_lfi_x m j,moi_lfi_x m (j + 1)}`; `moi_lfi_z`]
    CONVEX_HULL_INSERT) THEN
  REWRITE_TAC[NOT_INSERT_EMPTY] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[IN_ELIM_THM; GSYM SEGMENT_CONVEX_HULL] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `u:real` (X_CHOOSE_THEN `v:real`
      (X_CHOOSE_THEN `q:real^2` STRIP_ASSUME_TAC)))
    ASSUME_TAC) THEN
  ASM_CASES_TAC `u = &0` THENL
   [SUBGOAL_THEN `v = &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `p:real^2 = u % moi_lfi_z + v % q` THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_LID; VECTOR_ADD_LID] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^2) IN relative_interior std_triangle` MP_TAC THENL
   [ALL_TAC;
    UNDISCH_TAC `(p:real^2) IN relative_frontier std_triangle` THEN
    REWRITE_TAC[relative_frontier; IN_DIFF] THEN MESON_TAC[]] THEN
  SUBGOAL_THEN `(q:real^2) IN relative_frontier std_triangle` ASSUME_TAC THENL
   [MP_TAC(SPECL [`m:num`; `j:num`] MOI_LFI_SEG_FRONTIER) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `u = &1 - v` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `v = &0` THENL
   [ASM_REWRITE_TAC[REAL_SUB_RZERO; VECTOR_MUL_LZERO; VECTOR_MUL_LID;
                    VECTOR_ADD_RID; MOI_LFI_Z_RELINT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`std_triangle`; `moi_lfi_z`; `q:real^2`]
    IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[MOI_LFI_Z_RELINT] THEN CONJ_TAC THENL
     [REWRITE_TAC[std_triangle; CONVEX_CONVEX_HULL];
      UNDISCH_TAC `(q:real^2) IN relative_frontier std_triangle` THEN
      REWRITE_TAC[relative_frontier; IN_DIFF] THEN MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[IN_SEGMENT] THEN CONJ_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `(q:real^2) IN relative_frontier std_triangle` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MP_TAC(SPECL [`m:num`; `j:num`] MOI_LFI_NOT_FRONTIER) THEN ASM_SIMP_TAC[];
    EXISTS_TAC `v:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let MOI_LFI_K0_SECTOR = prove
 (`!m s. 1 <= m /\ s IN moi_lfi_k0 m
         ==> ?j. j < 4 * m /\
                 s SUBSET convex hull {moi_lfi_z, moi_lfi_x m j, moi_lfi_x m (j + 1)}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lfi_k0; IN_ELIM_THM; MOI_LFI_IN_MX] THEN
  STRIP_TAC THEN EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `x:real^2->bool` THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(x:real^2->bool) IN {moi_lfi_sa m j, moi_lfi_sb m j, moi_lfi_sc m j}` THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[MOI_LFI_TEMPLATE_IN_SECTOR]);;

let MOI_LFI_FRONTIER_FULL = prove
 (`!m n s. 1 <= m /\ s IN ITER n barycentric_subdivision (moi_lfi_k0 m) /\
           (!v. v extreme_point_of s ==> v IN relative_frontier std_triangle)
           ==> s SUBSET relative_frontier std_triangle`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `s:real^2->bool = {}` THENL
   [ASM_REWRITE_TAC[EMPTY_SUBSET]; ALL_TAC] THEN
  MP_TAC(SPEC `m:num` MOI_LFI_K0_COMPLEX) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `moi_lfi_k0 m` MOI_LFI_ITER_REFINES) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`n:num`; `s:real^2->bool`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^2->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`m:num`; `t:real^2->bool`] MOI_LFI_K0_SECTOR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`ITER n barycentric_subdivision (moi_lfi_k0 m)`; `s:real^2->bool`]
    MOI_FSAP_SIMPLEX_VERTICES) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MOI_FSAP_ITER]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^2->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(V:real^2->bool) SUBSET segment[moi_lfi_x m j,moi_lfi_x m (j + 1)]`
    ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `v:real^2` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`m:num`; `j:num`] MOI_LFI_SECTOR_FRONTIER) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_INTER] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(v:real^2) IN s` MP_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[];
        ASM SET_TAC[]];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `segment[moi_lfi_x m j,moi_lfi_x m (j + 1)]` THEN
  ASM_SIMP_TAC[MOI_LFI_SEG_FRONTIER] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
  MATCH_MP_TAC HULL_MINIMAL THEN
  REWRITE_TAC[CONVEX_CONVEX_HULL; GSYM SEGMENT_CONVEX_HULL] THEN
  ASM_REWRITE_TAC[]);;

let MOI_LFI_K0_RC = prove
 (`!m s. 1 <= m /\ s IN moi_lfi_k0 m /\ ~(s SUBSET moi_lfi_inner m)
         ==> s IN moi_lfi_rc m`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[moi_lfi_k0; moi_lfi_rc; IN_ELIM_THM; MOI_LFI_IN_MX] THEN
  STRIP_TAC THEN EXISTS_TAC `w:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(x:real^2->bool) IN {moi_lfi_sa m j, moi_lfi_sb m j, moi_lfi_sc m j}` THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THENL
   [UNDISCH_TAC `~(s SUBSET moi_lfi_inner m)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `convex hull (moi_lfi_sa m j)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HULL_MONO THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[moi_lfi_inner] THEN
    MATCH_MP_TAC(SET_RULE `(t:real^2->bool) IN u ==> t SUBSET UNIONS u`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

let MOI_LFI_TEMPLATE_RAY = prove
 (`!u0 v:real^2. u0 IN segment[basis 1,basis 2] /\ v IN segment[u0,inv(&2) % u0]
                 ==> v IN convex hull moi_lfi_tb UNION convex hull moi_lfi_tc`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `l:real` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(v:real^2)$1 = (&1 - s / &2) * (&1 - l) /\
                (v:real^2)$2 = (&1 - s / &2) * l`
    STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT;
                 DIMINDEX_2; ARITH] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (v:real^2)$1 /\ &0 <= (v:real^2)$2 /\
                (v:real^2)$1 + (v:real^2)$2 = &1 - s / &2`
    STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      CONV_TAC REAL_RING];
    ALL_TAC] THEN
  REWRITE_TAC[moi_lfi_tb; moi_lfi_tc; MOI_LFI_TEMPLATE_B; MOI_LFI_TEMPLATE_C;
              IN_UNION; IN_ELIM_THM] THEN
  ASM_REAL_ARITH_TAC);;

let MOI_LFI_PHI_HALF = prove
 (`!m j u. moi_lfi_phi m j (inv(&2) % u) = midpoint(moi_lfi_z,moi_lfi_phi m j u)`,
  REWRITE_TAC[moi_lfi_phi; midpoint; VECTOR_MUL_COMPONENT] THEN VECTOR_ARITH_TAC);;

let MOI_LFI_RING_SEGMENT = prove
 (`!m x. 1 <= m /\ x IN relative_frontier std_triangle
         ==> segment[x,midpoint(moi_lfi_z,x)] SUBSET moi_lfi_ring m`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `(x:real^2) IN relative_frontier std_triangle` THEN
  ASM_SIMP_TAC[MOI_LFI_FRONTIER_SEGS; IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^2->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `t:real^2->bool`)) THEN
  SUBGOAL_THEN `segment[moi_lfi_x m j,moi_lfi_x m (j + 1)] =
                IMAGE (moi_lfi_phi m j) (segment[basis 1,basis 2])`
    MP_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL; MOI_LFI_PHI_HULL; IMAGE_CLAUSES;
                MOI_LFI_PHI_POINTS];
    ALL_TAC] THEN
  DISCH_THEN(fun th ->
    UNDISCH_TAC `(x:real^2) IN segment[moi_lfi_x m j,moi_lfi_x m (j + 1)]` THEN
    REWRITE_TAC[th; IN_IMAGE]) THEN
  DISCH_THEN(X_CHOOSE_THEN `u0:real^2` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  REWRITE_TAC[GSYM MOI_LFI_PHI_HALF] THEN
  SUBGOAL_THEN `segment[moi_lfi_phi m j u0,moi_lfi_phi m j (inv(&2) % u0)] =
                IMAGE (moi_lfi_phi m j) (segment[u0,inv(&2) % u0])`
    SUBST1_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL; MOI_LFI_PHI_HULL; IMAGE_CLAUSES];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `IMAGE (moi_lfi_phi m j)
               (convex hull moi_lfi_tb UNION convex hull moi_lfi_tc)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET] THEN
    X_GEN_TAC `v:real^2` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_LFI_TEMPLATE_RAY THEN
    EXISTS_TAC `u0:real^2` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IMAGE_UNION; MOI_LFI_PHI_HULL; MOI_LFI_SECTOR_SETS; UNION_SUBSET] THEN
    ASM_SIMP_TAC[MOI_LFI_RING_HULLS]]);;

(* ------------------------------------------------------------------------- *)
(* 15. Uniform piecewise linear loops through a sequence of points (hat      *)
(* function sums), and the inner region as the half-size copy of the        *)
(* triangle about z.                                                         *)
(* ------------------------------------------------------------------------- *)

let moi_lfi_pl = new_definition
 `moi_lfi_pl (n:num) (w:num->real^N) (t:real^1) =
    vsum (0..n) (\j. max (&0) (&1 - abs(&n * drop t - &j)) % w j)`;;

let MOI_LFI_PL_CONTINUOUS = prove
 (`!n (w:num->real^N) s. moi_lfi_pl n w continuous_on s`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `moi_lfi_pl n (w:num->real^N) =
    (\t. vsum (0..n) (\j. max (&0) (&1 - abs(&n * drop t - &j)) % w j))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; moi_lfi_pl]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[CONTINUOUS_ON_CONST; o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MAX_1 THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
  REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
  REWRITE_TAC[CONTINUOUS_ON_CONST] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_ABS THEN
  REWRITE_TAC[LIFT_SUB; LIFT_CMUL; LIFT_DROP] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
  MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN REWRITE_TAC[CONTINUOUS_ON_ID]);;

let MOI_LFI_PL_COVER = prove
 (`!n t. 1 <= n /\ &0 <= drop t /\ drop t <= &1
         ==> ?i. i < n /\ &i / &n <= drop t /\ drop t <= &(i + 1) / &n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `&n * drop t`] MOI_LFI_NUM_COVER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; GSYM REAL_OF_NUM_ADD] THEN
  ASM_REAL_ARITH_TAC);;

let MOI_LFI_PL_SEG = prove
 (`!n (w:num->real^N) i t.
     i < n /\ &i / &n <= drop t /\ drop t <= &(i + 1) / &n
     ==> moi_lfi_pl n w t =
         (&1 - (&n * drop t - &i)) % w i + (&n * drop t - &i) % w (i + 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&i <= &n * drop t /\ &n * drop t <= &i + &1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `&i / &n <= drop t` THEN UNDISCH_TAC `drop t <= &(i + 1) / &n` THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; GSYM REAL_OF_NUM_ADD] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[moi_lfi_pl] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `vsum {i, i + 1}
    (\j. max (&0) (&1 - abs(&n * drop t - &j)) % (w:num->real^N) j)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_SUPERSET THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY; IN_NUMSEG] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `j:num` THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; IN_NUMSEG] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `&j + &1 <= &i \/ &i + &2 <= &j` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `max (&0) (&1 - abs(&n * drop t - &j)) = &0` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; REWRITE_TAC[VECTOR_MUL_LZERO]];
    ALL_TAC] THEN
  SIMP_TAC[VSUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY;
           ARITH_RULE `~(i = i + 1)`; VECTOR_ADD_RID] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  BINOP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_REAL_ARITH_TAC);;

let MOI_LFI_PL_VERTEX = prove
 (`!n (w:num->real^N) i. 1 <= n /\ i <= n ==> moi_lfi_pl n w (lift(&i / &n)) = w i`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `i:num = n` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(SPECL [`n:num`; `w:num->real^N`; `n - 1`; `lift(&n / &n)`]
      MOI_LFI_PL_SEG) THEN
    SUBGOAL_THEN `n - 1 + 1 = n` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&(n - 1) = &n - &1` SUBST1_TAC THENL
     [ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB]; ALL_TAC] THEN
    ASM_SIMP_TAC[LIFT_DROP; REAL_DIV_REFL; REAL_LT_IMP_NZ; REAL_LE_REFL] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_MUL_RID; REAL_ARITH `&n - (&n - &1) = &1`; REAL_SUB_REFL;
                VECTOR_MUL_LZERO; VECTOR_MUL_LID; VECTOR_ADD_LID];
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `w:num->real^N`; `i:num`; `lift(&i / &n)`]
    MOI_LFI_PL_SEG) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LIFT_DROP; REAL_LE_REFL] THEN CONJ_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_OF_NUM_LE] THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[LIFT_DROP; REAL_DIV_LMUL; REAL_LT_IMP_NZ; REAL_SUB_REFL;
               REAL_SUB_RZERO; VECTOR_MUL_LID; VECTOR_MUL_LZERO; VECTOR_ADD_RID]);;

let MOI_LFI_PL_PATH = prove
 (`!n (w:num->real^N).
     1 <= n
     ==> path (moi_lfi_pl n w) /\ pathstart (moi_lfi_pl n w) = w 0 /\
         pathfinish (moi_lfi_pl n w) = w n`,
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[path; MOI_LFI_PL_CONTINUOUS];
    REWRITE_TAC[pathstart] THEN
    MP_TAC(SPECL [`n:num`; `w:num->real^N`; `0`] MOI_LFI_PL_VERTEX) THEN
    ASM_REWRITE_TAC[LE_0; real_div; REAL_MUL_LZERO; LIFT_NUM];
    REWRITE_TAC[pathfinish] THEN
    MP_TAC(SPECL [`n:num`; `w:num->real^N`; `n:num`] MOI_LFI_PL_VERTEX) THEN
    SUBGOAL_THEN `&n / &n = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_DIV_REFL THEN REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC[LE_REFL; LIFT_NUM]]]);;

let MOI_LFI_PL_IN_SEG = prove
 (`!n (w:num->real^N) t.
     1 <= n /\ t IN interval[vec 0,vec 1]
     ==> ?i. i < n /\ &i / &n <= drop t /\ drop t <= &(i + 1) / &n /\
             moi_lfi_pl n w t IN segment[w i,w (i + 1)]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `t:real^1`] MOI_LFI_PL_COVER) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MOI_LFI_PL_SEG] THEN REWRITE_TAC[IN_SEGMENT] THEN
  EXISTS_TAC `&n * drop t - &i` THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `&i / &n <= drop t` THEN UNDISCH_TAC `drop t <= &(i + 1) / &n` THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; GSYM REAL_OF_NUM_ADD] THEN
  REAL_ARITH_TAC);;

let MOI_LFI_PL_IMAGE = prove
 (`!n (w:num->real^N) s.
     1 <= n /\ (!i. i < n ==> segment[w i,w (i + 1)] SUBSET s)
     ==> path_image (moi_lfi_pl n w) SUBSET s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[path_image; SUBSET; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`n:num`; `w:num->real^N`; `t:real^1`] MOI_LFI_PL_IN_SEG) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_LFI_MID_IMAGE_HULL = prove
 (`!z s:real^N->bool. IMAGE (\x. midpoint(z,x)) (convex hull s) =
                      convex hull (IMAGE (\x. midpoint(z,x)) s)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `(\x:real^N. midpoint(z,x)) = (\x. (\x. inv(&2) % x) x + inv(&2) % z)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; midpoint] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MOI_FSAP_AFFINE_HULL_IMAGE THEN
  REWRITE_TAC[linear] THEN VECTOR_ARITH_TAC);;

let MOI_LFI_MID_SECTOR = prove
 (`!m j. IMAGE (\x. midpoint(moi_lfi_z,x))
           (convex hull {moi_lfi_z, moi_lfi_x m j, moi_lfi_x m (j + 1)}) =
         convex hull (moi_lfi_sa m j)`,
  REWRITE_TAC[MOI_LFI_MID_IMAGE_HULL; IMAGE_CLAUSES; MIDPOINT_REFL;
              moi_lfi_sa; moi_lfi_y]);;

let MOI_LFI_INNER_IMAGE = prove
 (`!m. 1 <= m
       ==> moi_lfi_inner m = IMAGE (\x. midpoint(moi_lfi_z,x)) std_triangle`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
    [GSYM(MATCH_MP MOI_LFI_SECTORS_UNION th)]) THEN
  REWRITE_TAC[moi_lfi_inner; IMAGE_UNIONS] THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN
  X_GEN_TAC `t:real^2->bool` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `convex hull {moi_lfi_z, moi_lfi_x m j, moi_lfi_x m (j + 1)}` THEN
    ASM_REWRITE_TAC[MOI_LFI_MID_SECTOR] THEN EXISTS_TAC `j:num` THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `s:real^2->bool` (CONJUNCTS_THEN2 SUBST1_TAC
      (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC))) THEN
    EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[MOI_LFI_MID_SECTOR]]);;

let MOI_LFI_INNER_COMPACT = prove
 (`!m. 1 <= m ==> compact (moi_lfi_inner m) /\ moi_lfi_inner m SUBSET std_triangle`,
  GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[MOI_LFI_INNER_IMAGE] THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    REWRITE_TAC[std_triangle] THEN
    SIMP_TAC[COMPACT_CONVEX_HULL; FINITE_IMP_COMPACT; FINITE_INSERT; FINITE_EMPTY] THEN
    REWRITE_TAC[midpoint] THEN MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
    MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
    MP_TAC(SPEC `m:num` MOI_LFI_RING_INNER) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `std_triangle` RELATIVE_INTERIOR_SUBSET) THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 16. The mixed simplicial approximation on ITER n sd k0.  Vertices off    *)
(* the inner region take psi of a vertex of their k0-carrier (preferring    *)
(* non-frontier vertices), where G is simplicial on the ring complex rc;    *)
(* vertices in the inner region come from MOI_FSAP_VERTEX_CHOICE with      *)
(* avoidance of L.  Properness: the preimage of |L| is the frontier.         *)
(* ------------------------------------------------------------------------- *)

let MOI_LFI_VERTEX_IN_SUB = prove
 (`!(K:(real^N->bool)->bool) L v.
     simplicial_complex K /\ simplicial_subcomplex L K /\ {v} IN K /\ v IN UNIONS L
     ==> {v} IN L`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplicial_subcomplex; IN_UNIONS] THEN
  STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `t:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `{v:real^N} = {v} INTER t` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `simplicial_complex (K:(real^N->bool)->bool)` THEN
  REWRITE_TAC[simplicial_complex] THEN ASM_MESON_TAC[SUBSET]);;

let MOI_LFI_RING_STAR = prove
 (`!m n (K:(real^N->bool)->bool) (G:real^2->real^N) psi v r a.
     1 <= m /\ simplicial_complex K /\
     (!v. {v} IN moi_lfi_rc m ==> {psi v} IN K) /\
     (!s. s IN moi_lfi_rc m
          ==> ?t. t IN K /\ !v. v extreme_point_of s ==> psi v IN t) /\
     (!s x. s IN moi_lfi_rc m /\ x IN relative_interior s
            ==> G x IN relative_interior
                        (convex hull (IMAGE psi {v | v extreme_point_of s}))) /\
     ~(v IN moi_lfi_inner m) /\
     r IN moi_lfi_k0 m /\ v IN relative_interior r /\ a extreme_point_of r
     ==> !x. x IN UNIONS (ITER n barycentric_subdivision (moi_lfi_k0 m)) /\
             (!t. t IN ITER n barycentric_subdivision (moi_lfi_k0 m) /\ x IN t
                  ==> v IN t)
             ==> !s. s IN K /\ G x IN s ==> psi a IN s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
  X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
  MP_TAC(SPEC `m:num` MOI_LFI_K0_COMPLEX) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`moi_lfi_k0 m`; `n:num`] MOI_FSAP_ITER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ITER n barycentric_subdivision (moi_lfi_k0 m)`; `x:real^2`]
    MOI_FSAP_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `sg:real^2->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:real^2) IN sg` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^2) IN sg` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `moi_lfi_k0 m` MOI_LFI_ITER_REFINES) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`n:num`; `sg:real^2->bool`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tau:real^2->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`moi_lfi_k0 m`; `x:real^2`] MOI_FSAP_CARRIER) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:real^2->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(rho:real^2->bool) SUBSET tau` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FSAP_RELINT_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`moi_lfi_k0 m`; `x:real^2`] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(rho:real^2->bool) face_of tau` ASSUME_TAC THENL
   [SUBGOAL_THEN `rho = (rho:real^2->bool) INTER tau` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `simplicial_complex (moi_lfi_k0 m)` THEN
    REWRITE_TAC[simplicial_complex] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(sg:real^2->bool) SUBSET rho` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_OF_FACE_OF THEN EXISTS_TAC `tau:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `(r:real^2->bool) SUBSET rho` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FSAP_RELINT_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`moi_lfi_k0 m`; `v:real^2`] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^2) extreme_point_of rho` ASSUME_TAC THENL
   [SUBGOAL_THEN `(r:real^2->bool) face_of rho` ASSUME_TAC THENL
     [SUBGOAL_THEN `r = (r:real^2->bool) INTER rho` SUBST1_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `simplicial_complex (moi_lfi_k0 m)` THEN
      REWRITE_TAC[simplicial_complex] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_MESON_TAC[EXTREME_POINT_OF_FACE];
    ALL_TAC] THEN
  SUBGOAL_THEN `rho IN moi_lfi_rc m` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LFI_K0_RC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(MP (SPEC `rho:real^2->bool` (ASSUME
   `!s. s IN moi_lfi_rc m
        ==> ?t. t IN K /\ !v. v extreme_point_of s ==> (psi:real^2->real^N) v IN t`))
   (ASSUME `rho IN moi_lfi_rc m`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!v:real^2. v extreme_point_of rho ==> {v} IN moi_lfi_rc m`
    ASSUME_TAC THENL
   [MP_TAC(ISPECL [`moi_lfi_rc m`; `rho:real^2->bool`] MOI_FSAP_SIMPLEX_VERTICES) THEN
    ASM_SIMP_TAC[MOI_LFI_RC_COMPLEX] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `convex hull (IMAGE (psi:real^2->real^N) {v | v extreme_point_of rho}) IN K`
    ASSUME_TAC THENL
   [MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `t0:real^N->bool`;
                   `IMAGE (psi:real^2->real^N) {v | v extreme_point_of rho}`]
      MOI_FSAP_HULL_IN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `convex hull (IMAGE (psi:real^2->real^N) {v | v extreme_point_of rho}) SUBSET s`
    ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FSAP_RELINT_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`K:(real^N->bool)->bool`; `(G:real^2->real^N) x`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(ASSUME
     `!s x. s IN moi_lfi_rc m /\ x IN relative_interior s
            ==> (G:real^2->real^N) x IN relative_interior
                  (convex hull (IMAGE (psi:real^2->real^N) {v | v extreme_point_of s}))`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(psi:real^2->real^N) a IN
    convex hull (IMAGE (psi:real^2->real^N) {v | v extreme_point_of rho})`
    MP_TAC THENL
   [MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    EXISTS_TAC `a:real^2` THEN ASM_REWRITE_TAC[];
    ASM SET_TAC[]]);;

let MOI_LFI_CHI = prove
 (`!m n (K:(real^N->bool)->bool) (G:real^2->real^N) psi v.
     1 <= m /\ simplicial_complex K /\
     (!v. {v} IN moi_lfi_rc m ==> {psi v} IN K) /\
     (!s. s IN moi_lfi_rc m
          ==> ?t. t IN K /\ !v. v extreme_point_of s ==> psi v IN t) /\
     (!s x. s IN moi_lfi_rc m /\ x IN relative_interior s
            ==> G x IN relative_interior
                        (convex hull (IMAGE psi {v | v extreme_point_of s}))) /\
     {v} IN ITER n barycentric_subdivision (moi_lfi_k0 m) /\ ~(v IN moi_lfi_inner m)
     ==> ?a. {a} IN moi_lfi_rc m /\
             (a IN relative_frontier std_triangle
              ==> v IN relative_frontier std_triangle) /\
             !x. x IN UNIONS (ITER n barycentric_subdivision (moi_lfi_k0 m)) /\
                 (!t. t IN ITER n barycentric_subdivision (moi_lfi_k0 m) /\ x IN t
                      ==> v IN t)
                 ==> !s. s IN K /\ G x IN s ==> psi a IN s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `m:num` MOI_LFI_K0_COMPLEX) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`moi_lfi_k0 m`; `n:num`] MOI_FSAP_ITER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(v:real^2) IN UNIONS (moi_lfi_k0 m)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(v:real^2) IN UNIONS (ITER n barycentric_subdivision (moi_lfi_k0 m))`
      MP_TAC THENL
     [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{v:real^2}` THEN ASM_REWRITE_TAC[IN_SING];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_lfi_k0 m`; `v:real^2`] MOI_FSAP_CARRIER) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^2->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(v:real^2) IN r` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `r IN moi_lfi_rc m` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LFI_K0_RC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(v:real^2) IN r` THEN UNDISCH_TAC `~((v:real^2) IN moi_lfi_inner m)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a:real^2. a extreme_point_of r ==> {a} IN moi_lfi_rc m` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`moi_lfi_rc m`; `r:real^2->bool`] MOI_FSAP_SIMPLEX_VERTICES) THEN
    ASM_SIMP_TAC[MOI_LFI_RC_COMPLEX] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?a:real^2. a extreme_point_of r /\
               (a IN relative_frontier std_triangle
                ==> v IN relative_frontier std_triangle)`
    STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `(v:real^2) IN relative_frontier std_triangle` THEN
    ASM_REWRITE_TAC[] THENL
     [MP_TAC(ISPECL [`moi_lfi_k0 m`; `r:real^2->bool`] MOI_FSAP_SIMPLEX_VERTICES) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `V:real^2->bool` STRIP_ASSUME_TAC) THEN
      ASM_CASES_TAC `V:real^2->bool = {}` THENL
       [UNDISCH_TAC `(v:real^2) IN r` THEN
        ASM_REWRITE_TAC[CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
        ASM_MESON_TAC[MEMBER_NOT_EMPTY]];
      MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
      DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
      UNDISCH_TAC `~((v:real^2) IN relative_frontier std_triangle)` THEN
      REWRITE_TAC[] THEN
      MP_TAC(SPECL [`m:num`; `0`; `r:real^2->bool`] MOI_LFI_FRONTIER_FULL) THEN
      ASM_REWRITE_TAC[ITER] THEN ANTS_TAC THENL
       [ASM_MESON_TAC[];
        UNDISCH_TAC `(v:real^2) IN r` THEN SET_TAC[]]];
    ALL_TAC] THEN
  EXISTS_TAC `a:real^2` THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`m:num`; `n:num`; `K:(real^N->bool)->bool`; `G:real^2->real^N`;
                   `psi:real^2->real^N`; `v:real^2`; `r:real^2->bool`; `a:real^2`]
      MOI_LFI_RING_STAR) THEN
    ASM_REWRITE_TAC[]]);;

let MOI_LFI_FRONTIER_G = prove
 (`!m (K:(real^N->bool)->bool) L (G:real^2->real^N) psi x.
     1 <= m /\ simplicial_complex K /\ simplicial_subcomplex L K /\
     (!s. s IN K /\ ~(s = {}) /\ (!v. {v} IN K /\ v IN s ==> {v} IN L)
          ==> s IN L) /\
     (!v. {v} IN moi_lfi_rc m
          ==> {psi v} IN K /\
              (psi v IN UNIONS L <=> v IN relative_frontier std_triangle)) /\
     (!s. s IN moi_lfi_rc m
          ==> ?t. t IN K /\ !v. v extreme_point_of s ==> psi v IN t) /\
     (!s x. s IN moi_lfi_rc m /\ x IN relative_interior s
            ==> G x IN relative_interior
                        (convex hull (IMAGE psi {v | v extreme_point_of s}))) /\
     x IN relative_frontier std_triangle
     ==> ?h. h IN L /\ G x IN h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `m:num` MOI_LFI_RC_COMPLEX) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `m:num` MOI_LFI_RING_INNER) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`moi_lfi_rc m`; `x:real^2`] MOI_FSAP_CARRIER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM moi_lfi_ring] THEN
    UNDISCH_TAC `(x:real^2) IN relative_frontier std_triangle` THEN
    UNDISCH_TAC `relative_frontier std_triangle SUBSET moi_lfi_ring m` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^2->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(s:real^2->bool) SUBSET relative_frontier std_triangle` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^2) IN relative_frontier std_triangle` THEN
    ASM_SIMP_TAC[MOI_LFI_FRONTIER_SEGS; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^2->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `t:real^2->bool`)) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `segment[moi_lfi_x m j,moi_lfi_x m (j + 1)]` THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FSAP_RELINT_SUBSET THEN
      MAP_EVERY EXISTS_TAC [`moi_lfi_rc m`; `x:real^2`] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[moi_lfi_rc; IN_ELIM_THM; SEGMENT_CONVEX_HULL] THEN
      EXISTS_TAC `{moi_lfi_x m j, moi_lfi_x m (j + 1)}` THEN REWRITE_TAC[] THEN
      EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[moi_lfi_sb] THEN SET_TAC[];
      MATCH_MP_TAC(SET_RULE `(t:real^2->bool) IN u ==> t SUBSET UNIONS u`) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(MP (SPEC `s:real^2->bool` (ASSUME
   `!s. s IN moi_lfi_rc m
        ==> ?t. t IN K /\ !v. v extreme_point_of s ==> (psi:real^2->real^N) v IN t`))
   (ASSUME `s IN moi_lfi_rc m`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!a:real^2. a extreme_point_of s ==> {a} IN moi_lfi_rc m` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`moi_lfi_rc m`; `s:real^2->bool`] MOI_FSAP_SIMPLEX_VERTICES) THEN
    ASM_SIMP_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `H = convex hull (IMAGE (psi:real^2->real^N) {v | v extreme_point_of s})` THEN
  SUBGOAL_THEN `(H:real^N->bool) IN K` ASSUME_TAC THENL
   [EXPAND_TAC "H" THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `t0:real^N->bool`;
                   `IMAGE (psi:real^2->real^N) {v | v extreme_point_of s}`]
      MOI_FSAP_HULL_IN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(G:real^2->real^N) x IN H` ASSUME_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[SUBSET] RELATIVE_INTERIOR_SUBSET) THEN
    EXPAND_TAC "H" THEN
    MATCH_MP_TAC(ASSUME
     `!s x. s IN moi_lfi_rc m /\ x IN relative_interior s
            ==> (G:real^2->real^N) x IN relative_interior
                  (convex hull (IMAGE (psi:real^2->real^N) {v | v extreme_point_of s}))`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `H:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(ASSUME
   `!s. s IN K /\ ~(s = {}) /\ (!v. {v} IN K /\ v IN s ==> {v} IN L)
        ==> (s:real^N->bool) IN L`) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `(G:real^2->real^N) x IN H` THEN SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `p:real^N` THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_LFI_VERTEX_IN_SUB THEN EXISTS_TAC `K:(real^N->bool)->bool` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(p:real^N) extreme_point_of H` MP_TAC THENL
   [MATCH_MP_TAC MOI_FSAP_VERTEX_EXTREME THEN EXISTS_TAC `K:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXPAND_TAC "H" THEN
  DISCH_THEN(MP_TAC o MATCH_MP EXTREME_POINT_OF_CONVEX_HULL) THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^2` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `(a:real^2) IN relative_frontier std_triangle` ASSUME_TAC THENL
   [ASM_MESON_TAC[extreme_point_of; SUBSET]; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

let MOI_LFI_PROPER_CORE = prove
 (`!(k:(real^M->bool)->bool) (K:(real^N->bool)->bool) L (G:real^M->real^N)
    (f:real^M->real^N) phi P x.
     simplicial_complex k /\ simplicial_complex K /\ simplicial_subcomplex L K /\
     IMAGE G (UNIONS k) SUBSET UNIONS K /\
     (!v. {v} IN k
          ==> {phi v} IN K /\
              !x. x IN UNIONS k /\ (!t. t IN k /\ x IN t ==> v IN t)
                  ==> !s. s IN K /\ G x IN s ==> phi v IN s) /\
     (!x. x IN UNIONS k
          ==> ?r. r IN k /\ x IN relative_interior r /\
                  f x IN relative_interior
                          (convex hull (IMAGE phi {v | v extreme_point_of r}))) /\
     (!v. {v} IN k /\ phi v IN UNIONS L ==> v IN P) /\
     (!r. r IN k /\ (!v. v extreme_point_of r ==> v IN P) ==> r SUBSET P) /\
     x IN UNIONS k /\ f x IN UNIONS L
     ==> x IN P`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MP (SPEC `x:real^M` (ASSUME
   `!x. x IN UNIONS k
        ==> ?r. r IN k /\ x IN relative_interior r /\
                (f:real^M->real^N) x IN relative_interior
                  (convex hull (IMAGE (phi:real^M->real^N)
                                 {v | v extreme_point_of r}))`))
   (ASSUME `(x:real^M) IN UNIONS k`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^M->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!v:real^M. v extreme_point_of r ==> {v} IN k` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `r:real^M->bool`]
      MOI_FSAP_SIMPLEX_VERTICES) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v:real^M s. v extreme_point_of r /\ s IN K /\ (G:real^M->real^N) x IN s
                 ==> (phi:real^M->real^N) v IN s`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `{v:real^M} IN k` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `r:real^M->bool`; `x:real^M`; `v:real^M`]
      MOI_FSAP_RELINT_STAR) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(CONJUNCT2(MP (SPEC `v:real^M` (ASSUME
     `!v. {v} IN k
          ==> {(phi:real^M->real^N) v} IN K /\
              !x. x IN UNIONS k /\ (!t. t IN k /\ x IN t ==> v IN t)
                  ==> !s. s IN K /\ (G:real^M->real^N) x IN s ==> phi v IN s`))
     (ASSUME `{v:real^M} IN k`))) THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(G:real^M->real^N) x IN UNIONS K` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (G:real^M->real^N) (UNIONS k) SUBSET UNIONS K` THEN
    UNDISCH_TAC `(x:real^M) IN UNIONS k` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `(G:real^M->real^N) x`] MOI_FSAP_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(G:real^M->real^N) x IN C` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `convex hull (IMAGE (phi:real^M->real^N) {v | v extreme_point_of r}) IN K`
    ASSUME_TAC THENL
   [MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `C:real^N->bool`;
                   `IMAGE (phi:real^M->real^N) {v | v extreme_point_of r}`]
      MOI_FSAP_HULL_IN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `(f:real^M->real^N) x IN UNIONS L` THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(t:real^N->bool) IN K` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `convex hull (IMAGE (phi:real^M->real^N) {v | v extreme_point_of r}) SUBSET t`
    ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FSAP_RELINT_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`K:(real^N->bool)->bool`; `(f:real^M->real^N) x`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(r:real^M->bool) SUBSET P` MP_TAC THENL
   [MATCH_MP_TAC(ASSUME
     `!r. r IN k /\ (!v. v extreme_point_of r ==> v IN P) ==> (r:real^M->bool) SUBSET P`) THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real^M` THEN DISCH_TAC THEN
    MATCH_MP_TAC(ASSUME
     `!v. {v} IN k /\ (phi:real^M->real^N) v IN UNIONS L ==> (v:real^M) IN P`) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(phi:real^M->real^N) v IN convex hull (IMAGE phi {v | v extreme_point_of r})`
      MP_TAC THENL
     [MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
      EXISTS_TAC `v:real^M` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC
       `convex hull (IMAGE (phi:real^M->real^N) {v | v extreme_point_of r}) SUBSET t` THEN
      UNDISCH_TAC `(t:real^N->bool) IN L` THEN SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE `(x:real^M) IN s ==> s SUBSET p ==> x IN p`) THEN
  ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]);;

let MOI_LFI_MIXED = prove
 (`!m (K:(real^N->bool)->bool) L (G:real^2->real^N) psi.
     1 <= m /\ simplicial_complex K /\ ~(K = {}) /\ simplicial_subcomplex L K /\
     (!s. s IN K /\ ~(s = {}) /\ (!v. {v} IN K /\ v IN s ==> {v} IN L)
          ==> s IN L) /\
     G continuous_on std_triangle /\ IMAGE G std_triangle SUBSET UNIONS K /\
     DISJOINT (IMAGE G (moi_lfi_inner m)) (UNIONS L) /\
     (!v. {v} IN moi_lfi_rc m
          ==> {psi v} IN K /\
              (psi v IN UNIONS L <=> v IN relative_frontier std_triangle)) /\
     (!s. s IN moi_lfi_rc m
          ==> ?t. t IN K /\ !v. v extreme_point_of s ==> psi v IN t) /\
     (!s x. s IN moi_lfi_rc m /\ x IN relative_interior s
            ==> G x IN relative_interior
                        (convex hull (IMAGE psi {v | v extreme_point_of s})))
     ==> ?n f. simplicial_map_on (ITER n barycentric_subdivision (moi_lfi_k0 m)) K f /\
               f continuous_on std_triangle /\
               (!x. x IN std_triangle
                    ==> (f x IN UNIONS L <=> x IN relative_frontier std_triangle)) /\
               (!x s. x IN std_triangle /\ s IN K /\ G x IN s ==> f x IN s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `m:num` MOI_LFI_K0_COMPLEX) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC `m:num` MOI_LFI_K0_UNION) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC `m:num` MOI_LFI_INNER_COMPACT) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`moi_lfi_k0 m`; `K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `G:real^2->real^N`; `moi_lfi_inner m`] MOI_FSAP_VERTEX_CHOICE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "vc"))) THEN
  MP_TAC(ISPECL [`moi_lfi_k0 m`; `e:real`] ITERATED_BARYCENTRIC_SUBDIVISION_FINE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  EXISTS_TAC `n:num` THEN
  MP_TAC(ISPECL [`moi_lfi_k0 m`; `n:num`] MOI_FSAP_ITER) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  REMOVE_THEN "vc" (MP_TAC o SPEC `ITER n barycentric_subdivision (moi_lfi_k0 m)`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `phi1:real^2->real^N` (LABEL_TAC "phi1")) THEN
  SUBGOAL_THEN
   `?chi:real^2->real^2.
      !v. {v} IN ITER n barycentric_subdivision (moi_lfi_k0 m) /\
          ~(v IN moi_lfi_inner m)
          ==> {chi v} IN moi_lfi_rc m /\
              (chi v IN relative_frontier std_triangle
               ==> v IN relative_frontier std_triangle) /\
              !x. x IN std_triangle /\
                  (!t. t IN ITER n barycentric_subdivision (moi_lfi_k0 m) /\ x IN t
                       ==> v IN t)
                  ==> !s. s IN K /\ G x IN s ==> (psi:real^2->real^N) (chi v) IN s`
    (X_CHOOSE_THEN `chi:real^2->real^2` (LABEL_TAC "chi")) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN X_GEN_TAC `v:real^2` THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`m:num`; `n:num`; `K:(real^N->bool)->bool`; `G:real^2->real^N`;
                   `psi:real^2->real^N`; `v:real^2`] MOI_LFI_CHI) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `phi = \v:real^2. if v IN moi_lfi_inner m then (phi1:real^2->real^N) v
                               else (psi:real^2->real^N) (chi v)` THEN
  SUBGOAL_THEN
   `!v. {v} IN ITER n barycentric_subdivision (moi_lfi_k0 m)
        ==> {(phi:real^2->real^N) v} IN K /\
            !x. x IN std_triangle /\
                (!t. t IN ITER n barycentric_subdivision (moi_lfi_k0 m) /\ x IN t
                     ==> v IN t)
                ==> !s. s IN K /\ G x IN s ==> phi v IN s`
    ASSUME_TAC THENL
   [X_GEN_TAC `v:real^2` THEN DISCH_TAC THEN EXPAND_TAC "phi" THEN
    ASM_CASES_TAC `(v:real^2) IN moi_lfi_inner m` THEN ASM_REWRITE_TAC[] THENL
     [USE_THEN "phi1" (fun th -> MP_TAC(MP (SPEC `v:real^2` th)
        (ASSUME `{v:real^2} IN ITER n barycentric_subdivision (moi_lfi_k0 m)`))) THEN
      MESON_TAC[];
      USE_THEN "chi" (fun th -> MP_TAC(MP (SPEC `v:real^2` th)
        (CONJ (ASSUME `{v:real^2} IN ITER n barycentric_subdivision (moi_lfi_k0 m)`)
              (ASSUME `~((v:real^2) IN moi_lfi_inner m)`)))) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(CONJUNCT1(MP (SPEC `(chi:real^2->real^2) v` (ASSUME
       `!v. {v} IN moi_lfi_rc m
            ==> {(psi:real^2->real^N) v} IN K /\
                (psi v IN UNIONS L <=> v IN relative_frontier std_triangle)`))
       (ASSUME `{(chi:real^2->real^2) v} IN moi_lfi_rc m`))) THEN
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v. {v} IN ITER n barycentric_subdivision (moi_lfi_k0 m) /\
        (phi:real^2->real^N) v IN UNIONS L
        ==> v IN relative_frontier std_triangle`
    ASSUME_TAC THENL
   [X_GEN_TAC `v:real^2` THEN EXPAND_TAC "phi" THEN STRIP_TAC THEN
    ASM_CASES_TAC `(v:real^2) IN moi_lfi_inner m` THENL
     [UNDISCH_TAC
       `(if (v:real^2) IN moi_lfi_inner m then (phi1:real^2->real^N) v
         else (psi:real^2->real^N) (chi v)) IN UNIONS L` THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      USE_THEN "phi1" (fun th -> MP_TAC(MP (SPEC `v:real^2` th)
        (ASSUME `{v:real^2} IN ITER n barycentric_subdivision (moi_lfi_k0 m)`))) THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `{(phi1:real^2->real^N) v} IN L` MP_TAC THENL
       [MATCH_MP_TAC MOI_LFI_VERTEX_IN_SUB THEN EXISTS_TAC `K:(real^N->bool)->bool` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `~({(phi1:real^2->real^N) v} IN L)` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `v:real^2` THEN
        ASM_REWRITE_TAC[] THEN MESON_TAC[];
        CONV_TAC TAUT];
      UNDISCH_TAC
       `(if (v:real^2) IN moi_lfi_inner m then (phi1:real^2->real^N) v
         else (psi:real^2->real^N) (chi v)) IN UNIONS L` THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      USE_THEN "chi" (fun th -> MP_TAC(MP (SPEC `v:real^2` th)
        (CONJ (ASSUME `{v:real^2} IN ITER n barycentric_subdivision (moi_lfi_k0 m)`)
              (ASSUME `~((v:real^2) IN moi_lfi_inner m)`)))) THEN
      STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      MP_TAC(CONJUNCT2(MP (SPEC `(chi:real^2->real^2) v` (ASSUME
       `!v. {v} IN moi_lfi_rc m
            ==> {(psi:real^2->real^N) v} IN K /\
                (psi v IN UNIONS L <=> v IN relative_frontier std_triangle)`))
       (ASSUME `{(chi:real^2->real^2) v} IN moi_lfi_rc m`))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ITER n barycentric_subdivision (moi_lfi_k0 m)`; `K:(real^N->bool)->bool`;
                 `G:real^2->real^N`; `phi:real^2->real^N`] MOI_FSAP_STAR_MAP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^N` STRIP_ASSUME_TAC o
    REWRITE_RULE[ASSUME
     `UNIONS (ITER n barycentric_subdivision (moi_lfi_k0 m)) = std_triangle`]) THEN
  EXISTS_TAC `f:real^2->real^N` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`ITER n barycentric_subdivision (moi_lfi_k0 m)`;
                   `K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                   `G:real^2->real^N`; `f:real^2->real^N`; `phi:real^2->real^N`;
                   `relative_frontier std_triangle`; `x:real^2`] MOI_LFI_PROPER_CORE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_LFI_FRONTIER_FULL THEN
    MAP_EVERY EXISTS_TAC [`m:num`; `n:num`] THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`m:num`; `K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                   `G:real^2->real^N`; `psi:real^2->real^N`; `x:real^2`]
      MOI_LFI_FRONTIER_G) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `h:real^N->bool` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `h:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[simplicial_subcomplex; SUBSET]]);;

(* ------------------------------------------------------------------------- *)
(* 17. The ring map.  The vertex map psi sends x_j to w j and y_j to u j;   *)
(* MOI_FSAP_EXTEND on the ring complex rc gives the simplicial ring map g,  *)
(* whose restrictions to the frontier and to q are the PL loops of w and u. *)
(* ------------------------------------------------------------------------- *)

let moi_lfi_psi = new_definition
 `moi_lfi_psi m (w:num->real^N) (u:num->real^N) (v:real^2) =
    if v IN relative_frontier std_triangle
    then w (@j. j < 4 * m /\ v = moi_lfi_x m j)
    else u (@j. j < 4 * m /\ v = moi_lfi_y m j)`;;

let MOI_LFI_Y_INJ = prove
 (`!m i j. 1 <= m /\ i < 4 * m /\ j < 4 * m /\ moi_lfi_y m i = moi_lfi_y m j
           ==> i = j`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_LFI_X_INJ THEN EXISTS_TAC `m:num` THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `moi_lfi_y m i = moi_lfi_y m j` THEN
  REWRITE_TAC[moi_lfi_y; midpoint] THEN VECTOR_ARITH_TAC);;

let MOI_LFI_PSI_VALUES = prove
 (`!m (w:num->real^N) u j.
     1 <= m /\ j <= 4 * m /\ w (4 * m) = w 0 /\ u (4 * m) = u 0
     ==> moi_lfi_psi m w u (moi_lfi_x m j) = w j /\
         moi_lfi_psi m w u (moi_lfi_y m j) = u j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `j0 = if j = 4 * m then 0 else j` THEN
  SUBGOAL_THEN `j0 < 4 * m /\ moi_lfi_x m j = moi_lfi_x m j0 /\
                (w:num->real^N) j = w j0 /\ (u:num->real^N) j = u j0`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "j0" THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [ASM_SIMP_TAC[MOI_LFI_X_ZERO] THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_lfi_y m j = moi_lfi_y m j0` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[moi_lfi_y]; ALL_TAC] THEN
  REWRITE_TAC[moi_lfi_psi] THEN
  SIMP_TAC[ASSUME `1 <= m`; MOI_LFI_X_IN_FRONTIER; MOI_LFI_NOT_FRONTIER] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `(@i. i < 4 * m /\ moi_lfi_x m j = moi_lfi_x m i) = j0`
      SUBST1_TAC THENL
     [MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `i:num` THEN
      ASM_REWRITE_TAC[] THEN EQ_TAC THENL
       [STRIP_TAC THEN MATCH_MP_TAC MOI_LFI_X_INJ THEN EXISTS_TAC `m:num` THEN
        ASM_MESON_TAC[];
        DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
      ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `(@i. i < 4 * m /\ moi_lfi_y m j = moi_lfi_y m i) = j0`
      SUBST1_TAC THENL
     [MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `i:num` THEN
      ASM_REWRITE_TAC[] THEN EQ_TAC THENL
       [STRIP_TAC THEN MATCH_MP_TAC MOI_LFI_Y_INJ THEN EXISTS_TAC `m:num` THEN
        ASM_MESON_TAC[];
        DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
      ASM_REWRITE_TAC[]]]);;

let MOI_LFI_RC_VERTEX = prove
 (`!m v. {v} IN moi_lfi_rc m
         ==> ?j. j < 4 * m /\
                 (v = moi_lfi_x m j \/ v = moi_lfi_x m (j + 1) \/
                  v = moi_lfi_y m j \/ v = moi_lfi_y m (j + 1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lfi_rc; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^2->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `j:num` (CONJUNCTS_THEN ASSUME_TAC)) ASSUME_TAC)) THEN
  EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(v:real^2) IN w` MP_TAC THENL
   [ASM_CASES_TAC `w:real^2->bool = {}` THENL
     [UNDISCH_TAC `{v:real^2} = convex hull w` THEN
      ASM_REWRITE_TAC[CONVEX_HULL_EMPTY] THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(w:real^2->bool) SUBSET {v}` MP_TAC THENL
     [ASM_REWRITE_TAC[HULL_SUBSET]; ALL_TAC] THEN
    UNDISCH_TAC `~(w:real^2->bool = {})` THEN SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `w SUBSET moi_lfi_sb m j \/ w SUBSET moi_lfi_sc m j` THEN
  REWRITE_TAC[moi_lfi_sb; moi_lfi_sc] THEN SET_TAC[]);;

let MOI_LFI_RC_HULL = prove
 (`!m j w. j < 4 * m /\ (w SUBSET moi_lfi_sb m j \/ w SUBSET moi_lfi_sc m j)
           ==> convex hull w IN moi_lfi_rc m`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_lfi_rc; IN_ELIM_THM] THEN
  EXISTS_TAC `w:real^2->bool` THEN REWRITE_TAC[] THEN EXISTS_TAC `j:num` THEN
  ASM_REWRITE_TAC[]);;

let MOI_LFI_AFFINE_COMB = prove
 (`!(g:real^M->real^N) L y s a b l.
     linear L /\ (!x. x IN s ==> g x = L x + y) /\ a IN s /\ b IN s /\
     (&1 - l) % a + l % b IN s
     ==> g((&1 - l) % a + l % b) = (&1 - l) % g a + l % g b`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th; MATCH_MP LINEAR_CMUL th]) THEN
  VECTOR_ARITH_TAC);;

let MOI_LFI_RING_MAP = prove
 (`!m (K:(real^N->bool)->bool) w u.
     1 <= m /\ simplicial_complex K /\ w (4 * m) = w 0 /\ u (4 * m) = u 0 /\
     (!j. j <= 4 * m ==> {w j} IN K /\ {u j} IN K) /\
     (!j. j < 4 * m
          ==> (?t. t IN K /\ w j IN t /\ w (j + 1) IN t /\ u (j + 1) IN t) /\
              (?t. t IN K /\ w j IN t /\ u j IN t /\ u (j + 1) IN t))
     ==> (!v. {v} IN moi_lfi_rc m ==> {moi_lfi_psi m w u v} IN K) /\
         (!s. s IN moi_lfi_rc m
              ==> ?t. t IN K /\
                      !v. v extreme_point_of s ==> moi_lfi_psi m w u v IN t) /\
         ?g. g continuous_on moi_lfi_ring m /\
             simplicial_map_on (moi_lfi_rc m) K g /\
             IMAGE g (moi_lfi_ring m) SUBSET UNIONS K /\
             (!s x. s IN moi_lfi_rc m /\ x IN relative_interior s
                    ==> g x IN relative_interior
                          (convex hull (IMAGE (moi_lfi_psi m w u)
                                          {v | v extreme_point_of s}))) /\
             (!t. t IN interval[vec 0,vec 1]
                  ==> g (std_triangle_loop t) = moi_lfi_pl (4 * m) w t /\
                      g (midpoint(moi_lfi_z,std_triangle_loop t)) =
                      moi_lfi_pl (4 * m) u t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `m:num` MOI_LFI_RC_COMPLEX) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!v. {v} IN moi_lfi_rc m ==> {moi_lfi_psi m w u v} IN (K:(real^N->bool)->bool)`
    ASSUME_TAC THENL
   [X_GEN_TAC `v:real^2` THEN DISCH_THEN(MP_TAC o MATCH_MP MOI_LFI_RC_VERTEX) THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    SUBGOAL_THEN `j <= 4 * m /\ j + 1 <= 4 * m` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[MOI_LFI_PSI_VALUES];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s IN moi_lfi_rc m
        ==> ?t. t IN K /\
                !v. v extreme_point_of s ==> moi_lfi_psi m w u v IN (t:real^N->bool)`
    ASSUME_TAC THENL
   [X_GEN_TAC `s:real^2->bool` THEN REWRITE_TAC[moi_lfi_rc; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `W:real^2->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) SUBST1_TAC)) THEN
    (SUBGOAL_THEN `j <= 4 * m /\ j + 1 <= 4 * m` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC]) THEN
    MP_TAC(MP (SPEC `j:num` (ASSUME
     `!j. j < 4 * m
          ==> (?t. t IN K /\ (w:num->real^N) j IN t /\ w (j + 1) IN t /\
                   (u:num->real^N) (j + 1) IN t) /\
              (?t. t IN K /\ w j IN t /\ u j IN t /\ u (j + 1) IN t)`))
     (ASSUME `j < 4 * m`)) THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `tb:real^N->bool` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `tc:real^N->bool` STRIP_ASSUME_TAC)) THENL
     [EXISTS_TAC `tb:real^N->bool`; EXISTS_TAC `tc:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real^2` THEN
    DISCH_THEN(MP_TAC o MATCH_MP EXTREME_POINT_OF_CONVEX_HULL) THEN DISCH_TAC THENL
     [SUBGOAL_THEN `(v:real^2) IN moi_lfi_sb m j` MP_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[moi_lfi_sb; IN_INSERT; NOT_IN_EMPTY] THEN
      STRIP_TAC THEN ASM_SIMP_TAC[MOI_LFI_PSI_VALUES];
      SUBGOAL_THEN `(v:real^2) IN moi_lfi_sc m j` MP_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[moi_lfi_sc; IN_INSERT; NOT_IN_EMPTY] THEN
      STRIP_TAC THEN ASM_SIMP_TAC[MOI_LFI_PSI_VALUES]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`moi_lfi_rc m`; `K:(real^N->bool)->bool`;
                 `moi_lfi_psi m (w:num->real^N) u`] MOI_FSAP_EXTEND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^2->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `g:real^2->real^N` THEN ASM_REWRITE_TAC[moi_lfi_ring] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_UNIONS] THEN
    MAP_EVERY X_GEN_TAC [`s:real^2->bool`; `x:real^2`] THEN STRIP_TAC THEN
    REWRITE_TAC[IN_UNIONS] THEN
    EXISTS_TAC `IMAGE (g:real^2->real^N) s` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[simplicial_map_on];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `IMAGE (g:real^2->real^N) (relative_interior s) =
      relative_interior (convex hull (IMAGE (moi_lfi_psi m w u)
                                       {v | v extreme_point_of s}))`
      (SUBST1_TAC o SYM) THENL
     [ASM_MESON_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`m:num`; `t:real^1`] MOI_LFI_PARAM_COVER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `t IN interval[vec 0:real^1,vec 1]` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `j <= 4 * m /\ j + 1 <= 4 * m` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`m:num`; `j:num`; `t:real^1`] MOI_LFI_LOOP_AFFINE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`4 * m`; `w:num->real^N`; `j:num`; `t:real^1`] MOI_LFI_PL_SEG) THEN
  MP_TAC(SPECL [`4 * m`; `u:num->real^N`; `j:num`; `t:real^1`] MOI_LFI_PL_SEG) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`m:num`; `j:num`; `t:real^1`] MOI_LFI_PARAM_RANGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `l = &(4 * m) * drop t - &j` THEN
  SUBGOAL_THEN `&0 <= l /\ l <= &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!S a b. convex hull S IN moi_lfi_rc m /\ a IN S /\ b IN S /\
            {a} IN moi_lfi_rc m /\ {b} IN moi_lfi_rc m
            ==> (g:real^2->real^N) ((&1 - l) % a + l % b) =
                (&1 - l) % moi_lfi_psi m w u a + l % moi_lfi_psi m w u b`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `simplicial_map_on (moi_lfi_rc m) K (g:real^2->real^N)` THEN
    REWRITE_TAC[simplicial_map_on] THEN
    DISCH_THEN(MP_TAC o SPEC `convex hull S:real^2->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `L:real^2->real^N` (X_CHOOSE_THEN `y:real^N`
      STRIP_ASSUME_TAC) o CONJUNCT2) THEN
    MP_TAC(ISPECL [`g:real^2->real^N`; `L:real^2->real^N`; `y:real^N`;
                   `convex hull S:real^2->bool`; `a:real^2`; `b:real^2`; `l:real`]
      MOI_LFI_AFFINE_COMB) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[HULL_INC] THEN
      MATCH_MP_TAC(REWRITE_RULE[convex] CONVEX_CONVEX_HULL) THEN
      ASM_SIMP_TAC[HULL_INC] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `midpoint(moi_lfi_z,(&1 - l) % moi_lfi_x m j + l % moi_lfi_x m (j + 1)) =
    (&1 - l) % moi_lfi_y m j + l % moi_lfi_y m (j + 1)`
    SUBST1_TAC THENL
   [REWRITE_TAC[moi_lfi_y; midpoint] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`moi_lfi_sb m j`; `moi_lfi_x m j`; `moi_lfi_x m (j + 1)`]
      (ASSUME
       `!S a b. convex hull S IN moi_lfi_rc m /\ a IN S /\ b IN S /\
                {a} IN moi_lfi_rc m /\ {b} IN moi_lfi_rc m
                ==> (g:real^2->real^N) ((&1 - l) % a + l % b) =
                    (&1 - l) % moi_lfi_psi m w u a + l % moi_lfi_psi m w u b`));
    MP_TAC(SPECL [`moi_lfi_sc m j`; `moi_lfi_y m j`; `moi_lfi_y m (j + 1)`]
      (ASSUME
       `!S a b. convex hull S IN moi_lfi_rc m /\ a IN S /\ b IN S /\
                {a} IN moi_lfi_rc m /\ {b} IN moi_lfi_rc m
                ==> (g:real^2->real^N) ((&1 - l) % a + l % b) =
                    (&1 - l) % moi_lfi_psi m w u a + l % moi_lfi_psi m w u b`))] THEN
  ANTS_TAC THEN
  TRY(DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[MOI_LFI_PSI_VALUES] THEN NO_TAC) THEN
  REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[moi_lfi_sb; moi_lfi_sc; IN_INSERT] THEN NO_TAC) THEN
  TRY(ONCE_REWRITE_TAC[GSYM CONVEX_HULL_SING]) THEN
  MATCH_MP_TAC MOI_LFI_RC_HULL THEN EXISTS_TAC `j:num` THEN
  ASM_REWRITE_TAC[moi_lfi_sb; moi_lfi_sc] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 18. Rays from z through the frontier; a loop that is null-homotopic in   *)
(* a set s extends over std_triangle into s (quotient map from the square,   *)
(* QUOTIENT_MAP_LIFT_EXISTS).                                                *)
(* ------------------------------------------------------------------------- *)

let MOI_LFI_RAY_INSIDE = prove
 (`!x l. x IN relative_frontier std_triangle /\ &0 < l /\ l < &1
         ==> moi_lfi_z + l % (x - moi_lfi_z) IN relative_interior std_triangle`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`std_triangle`; `moi_lfi_z`; `x:real^2`]
    IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[MOI_LTD_STD_TRIANGLE_BASIC; MOI_LFI_Z_RELINT] THEN
    UNDISCH_TAC `(x:real^2) IN relative_frontier std_triangle` THEN
    REWRITE_TAC[relative_frontier; IN_DIFF] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[IN_SEGMENT] THEN CONJ_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `(x:real^2) IN relative_frontier std_triangle` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MP_TAC(SPECL [`1`; `0`] MOI_LFI_NOT_FRONTIER) THEN REWRITE_TAC[ARITH] THEN
    MESON_TAC[];
    EXISTS_TAC `l:real` THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC]);;

let MOI_LFI_RAY_UNIQUE = prove
 (`!x x' r r'. x IN relative_frontier std_triangle /\
               x' IN relative_frontier std_triangle /\ &0 < r /\ &0 < r' /\
               moi_lfi_z + r % (x - moi_lfi_z) = moi_lfi_z + r' % (x' - moi_lfi_z)
               ==> r = r' /\ x = x'`,
  SUBGOAL_THEN
   `!x x' r r'. x IN relative_frontier std_triangle /\
                x' IN relative_frontier std_triangle /\ &0 < r /\ &0 < r' /\
                moi_lfi_z + r % (x - moi_lfi_z) = moi_lfi_z + r' % (x' - moi_lfi_z)
                ==> ~(r < r')`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`x:real^2`; `r / r'`] MOI_LFI_RAY_INSIDE) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_LDIV_EQ; REAL_MUL_LID] THEN
    SUBGOAL_THEN `moi_lfi_z + r / r' % (x - moi_lfi_z) = x'` SUBST1_TAC THENL
     [SUBGOAL_THEN `x' - moi_lfi_z = inv r' % (r % (x - moi_lfi_z))` MP_TAC THENL
       [UNDISCH_TAC
         `moi_lfi_z + r % (x - moi_lfi_z) = moi_lfi_z + r' % (x' - moi_lfi_z)` THEN
        REWRITE_TAC[VECTOR_ARITH `z + a:real^2 = z + b <=> a = b`] THEN
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
        ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
        REWRITE_TAC[VECTOR_MUL_ASSOC; real_div] THEN
        REWRITE_TAC[REAL_MUL_SYM] THEN VECTOR_ARITH_TAC];
      UNDISCH_TAC `(x':real^2) IN relative_frontier std_triangle` THEN
      REWRITE_TAC[relative_frontier; IN_DIFF] THEN MESON_TAC[]];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `r:real = r'` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `~(r < r') /\ ~(r' < r) ==> r:real = r'`) THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`x:real^2`; `x':real^2`];
      MAP_EVERY EXISTS_TAC [`x':real^2`; `x:real^2`]] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  UNDISCH_TAC
   `moi_lfi_z + r' % (x - moi_lfi_z) = moi_lfi_z + r' % (x' - moi_lfi_z)` THEN
  REWRITE_TAC[VECTOR_ARITH `z + a:real^2 = z + b <=> a = b`] THEN
  ASM_SIMP_TAC[VECTOR_MUL_LCANCEL; REAL_LT_IMP_NZ] THEN VECTOR_ARITH_TAC);;

let MOI_LFI_RAY_ONTO = prove
 (`!y. y IN std_triangle
       ==> ?r t. &0 <= r /\ r <= &1 /\ t IN interval[vec 0,vec 1] /\
                 y = moi_lfi_z + r % (std_triangle_loop t - moi_lfi_z)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `y:real^2 = moi_lfi_z` THENL
   [MAP_EVERY EXISTS_TAC [`&0`; `vec 0:real^1`] THEN
    ASM_REWRITE_TAC[REAL_POS; REAL_LE_01; ENDS_IN_UNIT_INTERVAL; VECTOR_MUL_LZERO;
                    VECTOR_ADD_RID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`std_triangle`; `moi_lfi_z`; `y - moi_lfi_z:real^2`]
    RAY_TO_RELATIVE_FRONTIER) THEN
  ANTS_TAC THENL
   [SIMP_TAC[MOI_LTD_STD_TRIANGLE_BASIC; COMPACT_IMP_BOUNDED; MOI_LFI_Z_RELINT] THEN
    REWRITE_TAC[VECTOR_ARITH `z + (y - z):real^2 = y`] THEN
    ASM_SIMP_TAC[HULL_INC; VECTOR_SUB_EQ];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&1 <= d` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`std_triangle`; `moi_lfi_z`; `y:real^2`]
      IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[MOI_LTD_STD_TRIANGLE_BASIC; MOI_LFI_Z_RELINT; CLOSURE_CLOSED];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN
    DISCH_THEN(MP_TAC o SPEC `moi_lfi_z + d % (y - moi_lfi_z)`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_SEGMENT] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[]; EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
        VECTOR_ARITH_TAC];
      UNDISCH_TAC `moi_lfi_z + d % (y - moi_lfi_z) IN relative_frontier std_triangle` THEN
      REWRITE_TAC[relative_frontier; IN_DIFF] THEN MESON_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_lfi_z + d % (y - moi_lfi_z) IN relative_frontier std_triangle` THEN
  REWRITE_TAC[MOI_LFI_FRONTIER_IMAGE; IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^1` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`inv d:real`; `t:real^1`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    can (find_term ((=) `std_triangle_loop`)) (concl th))) THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE; REAL_INV_LE_1] THEN
  REWRITE_TAC[VECTOR_ARITH `(z + d % (y - z)) - z:real^2 = d % (y - z)`] THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN
  VECTOR_ARITH_TAC);;

let MOI_LFI_LOOP_IN_STD = prove
 (`!t. t IN interval[vec 0,vec 1] ==> std_triangle_loop t IN std_triangle /\
                                      std_triangle_loop t IN relative_frontier std_triangle`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `std_triangle_loop t IN relative_frontier std_triangle` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_LFI_FRONTIER_IMAGE] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[MOI_LTD_FRONTIER_SUBSET_TRIANGLE; SUBSET]]);;

let MOI_LFI_DISK_FILL = prove
 (`!(g:real^1->real^N) s a.
     homotopic_loops s g (linepath(a,a))
     ==> ?f. f continuous_on std_triangle /\ IMAGE f std_triangle SUBSET s /\
             !t. t IN interval[vec 0,vec 1] ==> f(std_triangle_loop t) = g t`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[homotopic_loops; HOMOTOPIC_WITH_EUCLIDEAN; LINEPATH_REFL;
              pathstart; pathfinish] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^(1,1)finite_sum->real^N` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC
   `Phi = \z:real^(1,1)finite_sum.
            moi_lfi_z + drop(fstcart z) % (std_triangle_loop(sndcart z) - moi_lfi_z)` THEN
  ABBREV_TAC
   `K = \z:real^(1,1)finite_sum.
          (h:real^(1,1)finite_sum->real^N) (pastecart (vec 1 - fstcart z) (sndcart z))` THEN
  SUBGOAL_THEN
   `(Phi:real^(1,1)finite_sum->real^2) continuous_on
    (interval[vec 0,vec 1] PCROSS interval[vec 0,vec 1])`
    ASSUME_TAC THENL
   [EXPAND_TAC "Phi" THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    CONJ_TAC THENL
     [REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX] THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    SUBGOAL_THEN `(\z:real^(1,1)finite_sum. std_triangle_loop(sndcart z)) =
                  std_triangle_loop o sndcart` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
    REWRITE_TAC[GSYM path; MOI_LTD_STD_TRIANGLE_LOOP] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS;
                SNDCART_PASTECART] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (Phi:real^(1,1)finite_sum->real^2)
      (interval[vec 0,vec 1] PCROSS interval[vec 0,vec 1]) = std_triangle`
    ASSUME_TAC THENL
   [EXPAND_TAC "Phi" THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS;
                FSTCART_PASTECART; SNDCART_PASTECART] THEN
    X_GEN_TAC `y:real^2` THEN EQ_TAC THENL
     [REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`r:real^1`; `t:real^1`] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[VECTOR_ARITH `z + r % (x - z):real^2 = (&1 - r) % z + r % x`] THEN
      MATCH_MP_TAC(REWRITE_RULE[convex] (CONJUNCT1(CONJUNCT2 MOI_LTD_STD_TRIANGLE_BASIC))) THEN
      ASM_SIMP_TAC[MOI_LFI_Z_IN_STD; MOI_LFI_LOOP_IN_STD] THEN
      UNDISCH_TAC `(r:real^1) IN interval[vec 0,vec 1]` THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN REAL_ARITH_TAC;
      DISCH_THEN(MP_TAC o MATCH_MP MOI_LFI_RAY_ONTO) THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`lift r`; `t:real^1`] THEN
      ASM_REWRITE_TAC[LIFT_DROP; IN_INTERVAL_1; DROP_VEC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z z'. z IN interval[vec 0,vec 1] PCROSS interval[vec 0,vec 1] /\
           z' IN interval[vec 0,vec 1] PCROSS interval[vec 0,vec 1] /\
           (Phi:real^(1,1)finite_sum->real^2) z = Phi z'
           ==> (K:real^(1,1)finite_sum->real^N) z = K z'`
    ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
    MAP_EVERY X_GEN_TAC [`r:real^1`; `t:real^1`; `r':real^1`; `t':real^1`] THEN
    EXPAND_TAC "Phi" THEN EXPAND_TAC "K" THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN STRIP_TAC THEN
    MP_TAC(SPEC `t:real^1` MOI_LFI_LOOP_IN_STD) THEN
    MP_TAC(SPEC `t':real^1` MOI_LFI_LOOP_IN_STD) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `!x. x IN relative_frontier std_triangle ==> ~(x - moi_lfi_z = vec 0)`
      ASSUME_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[VECTOR_SUB_EQ] THEN
      MP_TAC(SPECL [`1`; `0`] MOI_LFI_NOT_FRONTIER) THEN REWRITE_TAC[ARITH] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `drop r = &0` THENL
     [SUBGOAL_THEN `drop r' = &0` ASSUME_TAC THENL
       [UNDISCH_TAC
         `moi_lfi_z + drop r % (std_triangle_loop t - moi_lfi_z) =
          moi_lfi_z + drop r' % (std_triangle_loop t' - moi_lfi_z)` THEN
        ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
        REWRITE_TAC[VECTOR_ARITH `z:real^2 = z + a <=> a = vec 0`; VECTOR_MUL_EQ_0] THEN
        ASM_MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `r:real^1 = vec 0 /\ r':real^1 = vec 0` (CONJUNCTS_THEN SUBST1_TAC) THENL
       [ASM_REWRITE_TAC[GSYM DROP_EQ; DROP_VEC]; ALL_TAC] THEN
      ASM_REWRITE_TAC[VECTOR_SUB_RZERO];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(drop r' = &0)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC
       `moi_lfi_z + drop r % (std_triangle_loop t - moi_lfi_z) =
        moi_lfi_z + drop r' % (std_triangle_loop t' - moi_lfi_z)` THEN
      ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
      REWRITE_TAC[VECTOR_ARITH `z + a:real^2 = z <=> a = vec 0`; VECTOR_MUL_EQ_0] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPECL [`std_triangle_loop t`; `std_triangle_loop t'`; `drop r`; `drop r'`]
      MOI_LFI_RAY_UNIQUE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(r:real^1) IN interval[vec 0,vec 1]` THEN
      UNDISCH_TAC `(r':real^1) IN interval[vec 0,vec 1]` THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[DROP_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
    MP_TAC MOI_LFI_LOOP_SIMPLE THEN REWRITE_TAC[simple_path] THEN
    DISCH_THEN(MP_TAC o SPECL [`t:real^1`; `t':real^1`] o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `vec 1 - r':real^1 IN interval[vec 0,vec 1]` ASSUME_TAC THENL
     [UNDISCH_TAC `(r':real^1) IN interval[vec 0,vec 1]` THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; DROP_SUB] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(K:real^(1,1)finite_sum->real^N) continuous_on
      (interval[vec 0,vec 1] PCROSS interval[vec 0,vec 1]) /\
    IMAGE K (interval[vec 0,vec 1] PCROSS interval[vec 0,vec 1]) SUBSET s`
    STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `IMAGE (\z:real^(1,1)finite_sum. pastecart (vec 1 - fstcart z) (sndcart z))
        (interval[vec 0,vec 1] PCROSS interval[vec 0,vec 1]) SUBSET
      interval[vec 0,vec 1] PCROSS interval[vec 0,vec 1]`
      ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS;
                  FSTCART_PASTECART; SNDCART_PASTECART] THEN
      SIMP_TAC[IN_INTERVAL_1; DROP_VEC; DROP_SUB] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(K:real^(1,1)finite_sum->real^N) =
      h o (\z. pastecart (vec 1 - fstcart z) (sndcart z))`
      SUBST1_TAC THENL
     [EXPAND_TAC "K" THEN REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
          SIMP_TAC[CONTINUOUS_ON_CONST; LINEAR_CONTINUOUS_ON; LINEAR_FSTCART];
          SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART]];
        ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]];
      REWRITE_TAC[IMAGE_o] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`subtopology euclidean
      (interval[vec 0:real^1,vec 1] PCROSS interval[vec 0:real^1,vec 1])`;
    `subtopology euclidean std_triangle`;
    `subtopology euclidean (s:real^N->bool)`;
    `Phi:real^(1,1)finite_sum->real^2`; `K:real^(1,1)finite_sum->real^N`]
    QUOTIENT_MAP_LIFT_EXISTS) THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; CONTINUOUS_MAP_EUCLIDEAN2] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_IMP_QUOTIENT_MAP THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; CONTINUOUS_MAP_EUCLIDEAN2;
                COMPACT_SPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    ASM_SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY; HAUSDORFF_SPACE_EUCLIDEAN;
                 COMPACT_PCROSS; COMPACT_INTERVAL; SUBSET_REFL];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `fl:real^2->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `fl:real^2->real^N` THEN ASM_REWRITE_TAC[] THEN
  TRY(CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
  X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (vec 1:real^1) (t:real^1)`) THEN
  ASM_REWRITE_TAC[PASTECART_IN_PCROSS; ENDS_IN_UNIT_INTERVAL] THEN
  EXPAND_TAC "Phi" THEN EXPAND_TAC "K" THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; DROP_VEC; VECTOR_SUB_REFL;
              VECTOR_MUL_LID; VECTOR_ARITH `z + (x - z):real^2 = x`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 19. (C) a loop in |c| minus the boundary that is null-homotopic in |c|   *)
(* is null-homotopic off the boundary: push along the collar of the         *)
(* boundary (BOUNDARY_COLLAR), faded out by an Urysohn function supported   *)
(* in the collar.                                                            *)
(* ------------------------------------------------------------------------- *)

let MOI_LFI_PUSH_LOOPS = prove
 (`!(H:real^(1,N)finite_sum->real^N) X U (g:real^1->real^N) a.
     H continuous_on (interval[vec 0,vec 1] PCROSS X) /\
     IMAGE H (interval[vec 0,vec 1] PCROSS X) SUBSET X /\
     (!y. y IN X ==> H(pastecart (vec 0) y) = y) /\
     (!t y. t IN interval[vec 0,vec 1] /\ y IN U ==> H(pastecart t y) IN U) /\
     (!y. y IN X ==> H(pastecart (vec 1) y) IN U) /\
     U SUBSET X /\
     path g /\ pathfinish g = pathstart g /\ path_image g SUBSET U /\
     homotopic_loops X g (linepath(a,a))
     ==> ?b. homotopic_loops U g (linepath(b,b))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `h1 = \y:real^N. (H:real^(1,N)finite_sum->real^N) (pastecart (vec 1) y)` THEN
  SUBGOAL_THEN `(h1:real^N->real^N) continuous_on X /\ IMAGE h1 X SUBSET U`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "h1" THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(\y:real^N. (H:real^(1,N)finite_sum->real^N) (pastecart (vec 1) y)) =
                    H o (\y. pastecart (vec 1) y)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
        REWRITE_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `interval[vec 0:real^1,vec 1] PCROSS (X:real^N->bool)` THEN
        ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS;
                        ENDS_IN_UNIT_INTERVAL]];
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s IN interval[vec 0:real^1,vec 1] ==> (g:real^1->real^N) s IN U`
    ASSUME_TAC THENL
   [UNDISCH_TAC `path_image (g:real^1->real^N) SUBSET U` THEN
    REWRITE_TAC[path_image] THEN SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `(h1:real^N->real^N) a` THEN
  MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN EXISTS_TAC `(h1:real^N->real^N) o (g:real^1->real^N)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    SUBGOAL_THEN `linepath((h1:real^N->real^N) a,h1 a) = h1 o linepath(a:real^N,a)`
      SUBST1_TAC THENL
     [REWRITE_TAC[LINEPATH_REFL; FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE THEN EXISTS_TAC `X:real^N->bool` THEN
    ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[homotopic_loops; HOMOTOPIC_WITH_EUCLIDEAN] THEN
  EXISTS_TAC `\z:real^(1,1)finite_sum.
                if fstcart z = vec 0 then (g:real^1->real^N) (sndcart z)
                else (H:real^(1,N)finite_sum->real^N)
                       (pastecart (fstcart z) (g (sndcart z)))` THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; pathstart; pathfinish] THEN
  REWRITE_TAC[VEC_EQ; ARITH_EQ] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
    EXISTS_TAC `\z:real^(1,1)finite_sum. (H:real^(1,N)finite_sum->real^N)
                       (pastecart (fstcart z) ((g:real^1->real^N) (sndcart z)))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; FSTCART_PASTECART;
                  SNDCART_PASTECART] THEN
      MAP_EVERY X_GEN_TAC [`t:real^1`; `s:real^1`] THEN STRIP_TAC THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[SUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\z:real^(1,1)finite_sum. (H:real^(1,N)finite_sum->real^N)
         (pastecart (fstcart z) ((g:real^1->real^N) (sndcart z)))) =
      H o (\z. pastecart (fstcart z) (g (sndcart z)))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
      SUBGOAL_THEN `(\z:real^(1,1)finite_sum. (g:real^1->real^N) (sndcart z)) =
                    g o sndcart` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[path]; ALL_TAC] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS;
                  SNDCART_PASTECART] THEN
      SIMP_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `interval[vec 0:real^1,vec 1] PCROSS (X:real^N->bool)` THEN
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS;
                      FSTCART_PASTECART; SNDCART_PASTECART] THEN
      ASM_MESON_TAC[SUBSET]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS;
                FSTCART_PASTECART; SNDCART_PASTECART] THEN
    MAP_EVERY X_GEN_TAC [`t:real^1`; `s:real^1`] THEN STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[];
    EXPAND_TAC "h1" THEN REWRITE_TAC[o_THM];
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `pathfinish (g:real^1->real^N) = pathstart g` THEN
    REWRITE_TAC[pathstart; pathfinish] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[]]);;

let MOI_LFI_PUSH_ARITH = prove
 (`!s c. &0 <= s /\ s <= &1 /\ &0 <= c /\ c <= &1
         ==> &0 <= s + c / &2 * (&1 - s) /\ s + c / &2 * (&1 - s) <= &1 /\
             (&0 < s ==> &0 < s + c / &2 * (&1 - s)) /\
             (s = &0 /\ &0 < c ==> &0 < s + c / &2 * (&1 - s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `&1 - s`] REAL_LE_MUL) THEN
  MP_TAC(SPECL [`&1 - c`; `&1 - s`] REAL_LE_MUL) THEN
  ASM_REWRITE_TAC[REAL_SUB_LE] THEN REPEAT STRIP_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC]);;

let MOI_LFI_COLLAR_PUSH = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c
     ==> ?H:real^(1,N)finite_sum->real^N.
           H continuous_on (interval[vec 0,vec 1] PCROSS UNIONS c) /\
           IMAGE H (interval[vec 0,vec 1] PCROSS UNIONS c) SUBSET UNIONS c /\
           (!y. y IN UNIONS c ==> H(pastecart (vec 0) y) = y) /\
           (!t y. t IN interval[vec 0,vec 1] /\
                  y IN UNIONS c DIFF complex_boundary c
                  ==> H(pastecart t y) IN UNIONS c DIFF complex_boundary c) /\
           (!y. y IN UNIONS c
                ==> H(pastecart (vec 1) y) IN UNIONS c DIFF complex_boundary c)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_LTD_FINITE_COMPLEX_CLOSED) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; STRIP_TAC] THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_LTD_COMPLEX_BOUNDARY_SUBSET) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `UNIONS c:real^N->bool`] BOUNDARY_COLLAR) THEN
  ASM_REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN; SUBSET_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool`
   (X_CHOOSE_THEN `p:real^(N,1)finite_sum->real^N`
     (X_CHOOSE_THEN `q:real^N->real^(N,1)finite_sum` STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `X = UNIONS (c:(real^N->bool)->bool)` THEN
  ABBREV_TAC `B = complex_boundary (c:(real^N->bool)->bool)` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun u -> is_const u &&
    fst(dest_const u) = "pl_homeomorphism")) (concl th))) THEN
  REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
  ABBREV_TAC `oo = (subtopology euclidean X) interior_of (w:real^N->bool)` THEN
  SUBGOAL_THEN `open_in (subtopology euclidean X) (oo:real^N->bool) /\ oo SUBSET w`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "oo" THEN REWRITE_TAC[OPEN_IN_INTERIOR_OF; INTERIOR_OF_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`B:real^N->bool`; `X DIFF oo:real^N->bool`; `X:real^N->bool`;
                 `vec 1:real^1`; `vec 0:real^1`] URYSOHN_LOCAL) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_SUBSET THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CLOSED_IN_DIFF THEN
      ASM_REWRITE_TAC[CLOSED_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN; SUBSET_UNIV];
      UNDISCH_TAC `B SUBSET (oo:real^N->bool)` THEN SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^N->real^1` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!y. y IN X ==> &0 <= drop((f:real^N->real^1) y) /\ drop(f y) <= &1`
    ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o check (fun th ->
      can (find_term (fun u -> u = `segment[vec 1:real^1,vec 0]`)) (concl th))) THEN
    ASM_REWRITE_TAC[SEGMENT_1; DROP_VEC; REAL_ARITH `~(&1 <= &0)`; IN_INTERVAL_1];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN w
        ==> fstcart((q:real^N->real^(N,1)finite_sum) y) IN B /\
            &0 <= drop(sndcart(q y)) /\ drop(sndcart(q y)) <= &1 /\
            (p:real^(N,1)finite_sum->real^N)
              (pastecart (fstcart(q y)) (sndcart(q y))) = y`
    ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(q:real^N->real^(N,1)finite_sum) y IN
                  B PCROSS interval[vec 0,vec 1]` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o ONCE_REWRITE_RULE[GSYM PASTECART_FST_SND]) THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; DROP_VEC] THEN
    REWRITE_TAC[PASTECART_FST_SND] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x s. x IN B /\ s IN interval[vec 0,vec 1] /\
          (p:real^(N,1)finite_sum->real^N) (pastecart x s) IN B
          ==> s = vec 0`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `pastecart x s =
      pastecart ((p:real^(N,1)finite_sum->real^N) (pastecart x s)) (vec 0:real^1)`
      MP_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `(q:real^N->real^(N,1)finite_sum)
                    ((p:real^(N,1)finite_sum->real^N) (pastecart x s))` THEN
      CONJ_TAC THENL
       [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term ((=) `q:real^N->real^(N,1)finite_sum`)) (concl th) &&
          is_forall(concl th) &&
          can (find_term ((=) `p:real^(N,1)finite_sum->real^N`)) (concl th))) THEN
        ASM_REWRITE_TAC[PASTECART_IN_PCROSS];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `(p:real^(N,1)finite_sum->real^N) (pastecart (p (pastecart x s)) (vec 0)) =
        p (pastecart x s)`
        (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM th]) THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term ((=) `vec 0:real^1`)) (concl th) &&
          is_forall(concl th) && not(can (find_term ((=) `q:real^N->real^(N,1)finite_sum`)) (concl th)) &&
          can (find_term ((=) `p:real^(N,1)finite_sum->real^N`)) (concl th))) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `q:real^N->real^(N,1)finite_sum`)) (concl th) &&
        is_forall(concl th) &&
        can (find_term ((=) `p:real^(N,1)finite_sum->real^N`)) (concl th))) THEN
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS; ENDS_IN_UNIT_INTERVAL];
      REWRITE_TAC[PASTECART_INJ] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC
   `sg = \z:real^(1,N)finite_sum.
           sndcart((q:real^N->real^(N,1)finite_sum) (sndcart z)) +
           ((drop(fstcart z) * drop((f:real^N->real^1) (sndcart z))) / &2) %
           (vec 1 - sndcart(q (sndcart z)))` THEN
  SUBGOAL_THEN
   `!t y. t IN interval[vec 0,vec 1] /\ y IN w
          ==> pastecart (fstcart((q:real^N->real^(N,1)finite_sum) y))
                        ((sg:real^(1,N)finite_sum->real^1) (pastecart t y))
                IN B PCROSS interval[vec 0,vec 1] /\
              (&0 < drop(sndcart(q y)) ==> &0 < drop(sg(pastecart t y))) /\
              (drop(sndcart(q y)) = &0 /\ &0 < drop t * drop((f:real^N->real^1) y)
               ==> &0 < drop(sg(pastecart t y)))`
    ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN EXPAND_TAC "sg" THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; PASTECART_IN_PCROSS;
                IN_INTERVAL_1; DROP_VEC; DROP_ADD; DROP_CMUL; DROP_SUB] THEN
    SUBGOAL_THEN `(y:real^N) IN X` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^N) IN w` THEN UNDISCH_TAC `(w:real^N->bool) SUBSET X` THEN
      SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(MP (SPEC `y:real^N` (ASSUME
     `!y. y IN w
          ==> fstcart((q:real^N->real^(N,1)finite_sum) y) IN B /\
              &0 <= drop(sndcart(q y)) /\ drop(sndcart(q y)) <= &1 /\
              (p:real^(N,1)finite_sum->real^N)
                (pastecart (fstcart(q y)) (sndcart(q y))) = y`))
     (ASSUME `(y:real^N) IN w`)) THEN
    STRIP_TAC THEN
    MP_TAC(MP (SPEC `y:real^N` (ASSUME
     `!y. y IN X ==> &0 <= drop((f:real^N->real^1) y) /\ drop(f y) <= &1`))
     (ASSUME `(y:real^N) IN X`)) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= drop(t:real^1) /\ drop t <= &1` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(t:real^1) IN interval[vec 0,vec 1]` THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC];
      ALL_TAC] THEN
    MP_TAC(SPECL [`drop(sndcart((q:real^N->real^(N,1)finite_sum) y))`;
                  `drop(t:real^1) * drop((f:real^N->real^1) y)`] MOI_LFI_PUSH_ARITH) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC(REAL_ARITH `x <= &1 * &1 ==> x <= &1`) THEN
        MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC
   `\z:real^(1,N)finite_sum.
      if sndcart z IN w
      then (p:real^(N,1)finite_sum->real^N)
             (pastecart (fstcart((q:real^N->real^(N,1)finite_sum) (sndcart z)))
                        ((sg:real^(1,N)finite_sum->real^1) z))
      else sndcart z` THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  SUBGOAL_THEN `(w:real^N->bool) SUBSET X` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t y. t IN interval[vec 0,vec 1] /\ y IN w
          ==> (p:real^(N,1)finite_sum->real^N)
                (pastecart (fstcart((q:real^N->real^(N,1)finite_sum) y))
                           ((sg:real^(1,N)finite_sum->real^1) (pastecart t y))) IN w`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC
     `IMAGE (p:real^(N,1)finite_sum->real^N) (B PCROSS interval[vec 0,vec 1]) = w` THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t y. t IN interval[vec 0,vec 1] /\ y IN w /\
          drop((f:real^N->real^1) y) = &0
          ==> (sg:real^(1,N)finite_sum->real^1) (pastecart t y) =
              sndcart((q:real^N->real^(N,1)finite_sum) y)`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "sg" THEN
    ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; REAL_MUL_RZERO; real_div;
                    REAL_MUL_LZERO; VECTOR_MUL_LZERO; VECTOR_ADD_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN w ==> (sg:real^(1,N)finite_sum->real^1) (pastecart (vec 0) y) =
                   sndcart((q:real^N->real^(N,1)finite_sum) y)`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "sg" THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; DROP_VEC; REAL_MUL_LZERO;
                real_div; VECTOR_MUL_LZERO; VECTOR_ADD_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t y. t IN interval[vec 0,vec 1] /\ y IN w /\ ~(y IN B)
          ==> ~((p:real^(N,1)finite_sum->real^N)
                 (pastecart (fstcart((q:real^N->real^(N,1)finite_sum) y))
                            ((sg:real^(1,N)finite_sum->real^1) (pastecart t y))) IN B)`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(MP (SPEC `y:real^N` (ASSUME
     `!y. y IN w
          ==> fstcart((q:real^N->real^(N,1)finite_sum) y) IN B /\
              &0 <= drop(sndcart(q y)) /\ drop(sndcart(q y)) <= &1 /\
              (p:real^(N,1)finite_sum->real^N)
                (pastecart (fstcart(q y)) (sndcart(q y))) = y`))
     (ASSUME `(y:real^N) IN w`)) THEN
    STRIP_TAC THEN
    MP_TAC(MP (SPECL [`t:real^1`; `y:real^N`] (ASSUME
     `!t y. t IN interval[vec 0,vec 1] /\ y IN w
            ==> pastecart (fstcart((q:real^N->real^(N,1)finite_sum) y))
                          ((sg:real^(1,N)finite_sum->real^1) (pastecart t y))
                  IN B PCROSS interval[vec 0,vec 1] /\
                (&0 < drop(sndcart(q y)) ==> &0 < drop(sg(pastecart t y))) /\
                (drop(sndcart(q y)) = &0 /\ &0 < drop t * drop((f:real^N->real^1) y)
                 ==> &0 < drop(sg(pastecart t y)))`))
     (CONJ (ASSUME `(t:real^1) IN interval[vec 0,vec 1]`) (ASSUME `(y:real^N) IN w`))) THEN
    REWRITE_TAC[PASTECART_IN_PCROSS] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(sg:real^(1,N)finite_sum->real^1) (pastecart t y) = vec 0` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `vec 0:real^1`)) (concl th) &&
        can (find_term ((=) `p:real^(N,1)finite_sum->real^N`)) (concl th) &&
        not(can (find_term ((=) `q:real^N->real^(N,1)finite_sum`)) (concl th)) &&
        can (find_term (fun u -> u = `s:real^1`)) (concl th))) THEN
      EXISTS_TAC `fstcart((q:real^N->real^(N,1)finite_sum) y)` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `drop(sndcart((q:real^N->real^(N,1)finite_sum) y)) = &0` ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(&0 < x) ==> x = &0`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      UNDISCH_TAC `&0 < drop(sndcart((q:real^N->real^(N,1)finite_sum) y))
                   ==> &0 < drop((sg:real^(1,N)finite_sum->real^1) (pastecart t y))` THEN
      ASM_REWRITE_TAC[DROP_VEC; REAL_LT_REFL];
      ALL_TAC] THEN
    UNDISCH_TAC `~((y:real^N) IN B)` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `sndcart((q:real^N->real^(N,1)finite_sum) y) = vec 0` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[GSYM DROP_EQ; DROP_VEC]; ALL_TAC] THEN
    UNDISCH_TAC `(p:real^(N,1)finite_sum->real^N)
                   (pastecart (fstcart((q:real^N->real^(N,1)finite_sum) y))
                              (sndcart(q y))) = y` THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `fstcart((q:real^N->real^(N,1)finite_sum) y)` o check
      (fun th -> is_forall(concl th) &&
        can (find_term ((=) `vec 0:real^1`)) (concl th) &&
        can (find_term ((=) `p:real^(N,1)finite_sum->real^N`)) (concl th) &&
        not(can (find_term ((=) `q:real^N->real^(N,1)finite_sum`)) (concl th)) &&
        not(can (find_term (fun u -> u = `s:real^1`)) (concl th)))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z:real^(1,N)finite_sum. (q:real^N->real^(N,1)finite_sum) (sndcart z))
    continuous_on (interval[vec 0,vec 1] PCROSS w) /\
    (\z:real^(1,N)finite_sum. (f:real^N->real^1) (sndcart z))
    continuous_on (interval[vec 0,vec 1] PCROSS w)`
    STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `IMAGE (sndcart:real^(1,N)finite_sum->real^N)
        (interval[vec 0,vec 1] PCROSS w) SUBSET w`
      ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS;
                  SNDCART_PASTECART] THEN SIMP_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THENL
     [EXISTS_TAC `w:real^N->bool`; EXISTS_TAC `X:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(sg:real^(1,N)finite_sum->real^1) continuous_on (interval[vec 0,vec 1] PCROSS w)`
    ASSUME_TAC THENL
   [EXPAND_TAC "sg" THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `lift o (\z:real^(1,N)finite_sum.
                  (drop(fstcart z) * drop((f:real^N->real^1) (sndcart z))) / &2) =
        (\z. inv(&2) % (drop(fstcart z) % f(sndcart z)))`
        SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM; GSYM DROP_EQ; LIFT_DROP; DROP_CMUL] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
      ASM_REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX] THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART];
      MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `interval[vec 0:real^1,vec 1] PCROSS (X:real^N->bool) =
    (interval[vec 0,vec 1] PCROSS w) UNION (interval[vec 0,vec 1] PCROSS (X DIFF oo))`
    ASSUME_TAC THENL
   [REWRITE_TAC[GSYM PCROSS_UNION] THEN AP_TERM_TAC THEN
    UNDISCH_TAC `(w:real^N->bool) SUBSET X` THEN
    UNDISCH_TAC `(oo:real^N->bool) SUBSET w` THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THEN
    MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM th]) THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_SUBSET THEN CONJ_TAC THENL
       [MATCH_MP_TAC PCROSS_MONO THEN ASM_REWRITE_TAC[SUBSET_REFL]; ALL_TAC] THEN
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_PCROSS THEN
      REWRITE_TAC[COMPACT_INTERVAL] THEN
      UNDISCH_TAC
       `IMAGE (p:real^(N,1)finite_sum->real^N) (B PCROSS interval[vec 0,vec 1]) = w` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_SIMP_TAC[COMPACT_PCROSS; COMPACT_INTERVAL];
      MATCH_MP_TAC CLOSED_IN_PCROSS THEN
      REWRITE_TAC[CLOSED_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN; SUBSET_UNIV] THEN
      MATCH_MP_TAC CLOSED_IN_DIFF THEN
      ASM_REWRITE_TAC[CLOSED_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN; SUBSET_UNIV];
      SUBGOAL_THEN
       `(\z:real^(1,N)finite_sum. (p:real^(N,1)finite_sum->real^N)
           (pastecart (fstcart((q:real^N->real^(N,1)finite_sum) (sndcart z)))
                      ((sg:real^(1,N)finite_sum->real^1) z))) =
        p o (\z. pastecart (fstcart(q (sndcart z))) (sg z))`
        SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN ASM_REWRITE_TAC[] THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `(B:real^N->bool) PCROSS interval[vec 0:real^1,vec 1]` THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS;
                    FSTCART_PASTECART; SNDCART_PASTECART] THEN
        MAP_EVERY X_GEN_TAC [`t:real^1`; `y:real^N`] THEN STRIP_TAC THEN
        MP_TAC(MP (SPECL [`t:real^1`; `y:real^N`] (ASSUME
         `!t y. t IN interval[vec 0,vec 1] /\ y IN w
                ==> pastecart (fstcart((q:real^N->real^(N,1)finite_sum) y))
                              ((sg:real^(1,N)finite_sum->real^1) (pastecart t y))
                      IN B PCROSS interval[vec 0,vec 1] /\
                    (&0 < drop(sndcart(q y)) ==> &0 < drop(sg(pastecart t y))) /\
                    (drop(sndcart(q y)) = &0 /\ &0 < drop t * drop((f:real^N->real^1) y)
                     ==> &0 < drop(sg(pastecart t y)))`))
         (CONJ (ASSUME `(t:real^1) IN interval[vec 0,vec 1]`)
               (ASSUME `(y:real^N) IN w`))) THEN
        SIMP_TAC[PASTECART_IN_PCROSS]];
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART];
      REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; FSTCART_PASTECART;
                  SNDCART_PASTECART] THEN
      MAP_EVERY X_GEN_TAC [`t:real^1`; `y:real^N`] THEN
      DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
       [UNDISCH_TAC `~((y:real^N) IN w)` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `drop((f:real^N->real^1) y) = &0` ASSUME_TAC THENL
       [SUBGOAL_THEN `(f:real^N->real^1) y = vec 0` (fun th -> REWRITE_TAC[th; DROP_VEC]) THEN
        MATCH_MP_TAC(ASSUME `!x. x IN X DIFF oo ==> (f:real^N->real^1) x = vec 0`) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN
      UNDISCH_TAC `(y:real^N) IN X DIFF oo` THEN UNDISCH_TAC `(oo:real^N->bool) SUBSET w` THEN
      SET_TAC[]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS;
                FSTCART_PASTECART; SNDCART_PASTECART] THEN
    MAP_EVERY X_GEN_TAC [`t:real^1`; `y:real^N`] THEN STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(w:real^N->bool) SUBSET X` THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`t:real^1`; `y:real^N`] THEN
    REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `(w:real^N->bool) SUBSET X` THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(y:real^N) IN B` THENL
     [ALL_TAC;
      COND_CASES_TAC THEN ASM_SIMP_TAC[IN_DIFF; ENDS_IN_UNIT_INTERVAL] THEN
      UNDISCH_TAC `(w:real^N->bool) SUBSET X` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[ENDS_IN_UNIT_INTERVAL]] THEN
    SUBGOAL_THEN `(y:real^N) IN w` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^N) IN B` THEN UNDISCH_TAC `B SUBSET (oo:real^N->bool)` THEN
      UNDISCH_TAC `(oo:real^N->bool) SUBSET w` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(w:real^N->bool) SUBSET X` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[ENDS_IN_UNIT_INTERVAL];
      ALL_TAC] THEN
    SUBGOAL_THEN `(q:real^N->real^(N,1)finite_sum) y = pastecart y (vec 0)` ASSUME_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `(q:real^N->real^(N,1)finite_sum)
                    ((p:real^(N,1)finite_sum->real^N) (pastecart y (vec 0)))` THEN
      CONJ_TAC THENL
       [AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check
         (fun th -> is_forall(concl th) &&
           can (find_term ((=) `vec 0:real^1`)) (concl th) &&
           can (find_term ((=) `p:real^(N,1)finite_sum->real^N`)) (concl th) &&
           not(can (find_term ((=) `q:real^N->real^(N,1)finite_sum`)) (concl th)) &&
           not(can (find_term (fun u -> u = `s:real^1`)) (concl th)))) THEN
        ASM_REWRITE_TAC[];
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term ((=) `q:real^N->real^(N,1)finite_sum`)) (concl th) &&
          is_forall(concl th) &&
          can (find_term ((=) `p:real^(N,1)finite_sum->real^N`)) (concl th) &&
          can (find_term (fun u -> u = `(B:real^N->bool) PCROSS interval[vec 0:real^1,vec 1]`)) (concl th))) THEN
        ASM_REWRITE_TAC[PASTECART_IN_PCROSS; ENDS_IN_UNIT_INTERVAL]];
      ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(MP (SPECL [`vec 1:real^1`; `y:real^N`] (ASSUME
     `!t y. t IN interval[vec 0,vec 1] /\ y IN w
            ==> pastecart (fstcart((q:real^N->real^(N,1)finite_sum) y))
                          ((sg:real^(1,N)finite_sum->real^1) (pastecart t y))
                  IN B PCROSS interval[vec 0,vec 1] /\
                (&0 < drop(sndcart(q y)) ==> &0 < drop(sg(pastecart t y))) /\
                (drop(sndcart(q y)) = &0 /\ &0 < drop t * drop((f:real^N->real^1) y)
                 ==> &0 < drop(sg(pastecart t y)))`))
     (CONJ (prove(`vec 1 IN interval[vec 0:real^1,vec 1]`,
                  REWRITE_TAC[ENDS_IN_UNIT_INTERVAL]))
           (ASSUME `(y:real^N) IN w`))) THEN
    REWRITE_TAC[PASTECART_IN_PCROSS] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(sg:real^(1,N)finite_sum->real^1) (pastecart (vec 1) y) = vec 0`
      MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `vec 0:real^1`)) (concl th) &&
        can (find_term ((=) `p:real^(N,1)finite_sum->real^N`)) (concl th) &&
        not(can (find_term ((=) `q:real^N->real^(N,1)finite_sum`)) (concl th)) &&
        can (find_term (fun u -> u = `s:real^1`)) (concl th))) THEN
      EXISTS_TAC `fstcart((q:real^N->real^(N,1)finite_sum) y)` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN
    UNDISCH_TAC
     `drop(sndcart((q:real^N->real^(N,1)finite_sum) y)) = &0 /\
      &0 < drop(vec 1:real^1) * drop((f:real^N->real^1) y)
      ==> &0 < drop((sg:real^(1,N)finite_sum->real^1) (pastecart (vec 1) y))` THEN
    ASM_SIMP_TAC[SNDCART_PASTECART; DROP_VEC; REAL_MUL_LID; REAL_LT_01; REAL_LT_REFL]]);;

let MOI_LFI_INTERIOR_NULL = prove
 (`!(c:(real^N->bool)->bool) (g:real^1->real^N) a.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     path g /\ pathfinish g = pathstart g /\
     path_image g SUBSET UNIONS c DIFF complex_boundary c /\
     homotopic_loops (UNIONS c) g (linepath(a,a))
     ==> ?b. homotopic_loops (UNIONS c DIFF complex_boundary c) g (linepath(b,b))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_LFI_COLLAR_PUSH) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `H:real^(1,N)finite_sum->real^N` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC MOI_LFI_PUSH_LOOPS THEN
  MAP_EVERY EXISTS_TAC [`H:real^(1,N)finite_sum->real^N`; `UNIONS c:real^N->bool`;
                        `a:real^N`] THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 20. Facts on K = sd c and its boundary subcomplex L, simplices spanned    *)
(* by non-L vertices miss |L|, the ring is closed, and the assembly of      *)
(* LT_FILL from collar data (w,u).                                           *)
(* ------------------------------------------------------------------------- *)

let MOI_LFI_HULL_OFF_SUB = prove
 (`!(K:(real^N->bool)->bool) L t W.
     simplicial_complex K /\ simplicial_subcomplex L K /\ t IN K /\ W SUBSET t /\
     (!v. v IN W ==> {v} IN K /\ ~(v IN UNIONS L))
     ==> DISJOINT (convex hull W) (UNIONS L)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `t:real^N->bool`; `W:real^N->bool`]
    MOI_FSAP_HULL_IN) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
  UNDISCH_TAC `(y:real^N) IN UNIONS L` THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `t':real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(t':real^N->bool) IN K` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `y:real^N`] MOI_FSAP_CARRIER) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[IN_UNIONS]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(C:real^N->bool) SUBSET t' /\ C SUBSET convex hull W`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_FSAP_RELINT_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`K:(real^N->bool)->bool`; `y:real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `C:real^N->bool`] MOI_FSAP_SIMPLEX_VERTICES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?a:real^N. a IN V` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN DISCH_TAC THEN
    UNDISCH_TAC `(y:real^N) IN relative_interior C` THEN
    ASM_REWRITE_TAC[CONVEX_HULL_EMPTY; RELATIVE_INTERIOR_EMPTY; NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `(C:real^N->bool) face_of convex hull W` ASSUME_TAC THENL
   [SUBGOAL_THEN `C = (C:real^N->bool) INTER convex hull W` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `simplicial_complex (K:(real^N->bool)->bool)` THEN
    REWRITE_TAC[simplicial_complex] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^N) IN W` ASSUME_TAC THENL
   [MATCH_MP_TAC EXTREME_POINT_OF_CONVEX_HULL THEN
    MP_TAC(ISPECL [`C:real^N->bool`; `convex hull W:real^N->bool`; `a:real^N`]
      EXTREME_POINT_OF_FACE) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^N) IN C` ASSUME_TAC THENL
   [ASM_MESON_TAC[extreme_point_of]; ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^N) IN UNIONS L` MP_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `t':real^N->bool` THEN ASM SET_TAC[];
    ASM_SIMP_TAC[]]);;

let MOI_LFI_SD_FACTS = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c
     ==> simplicial_complex (barycentric_subdivision c) /\
         ~(barycentric_subdivision c = {}) /\
         UNIONS (barycentric_subdivision c) = UNIONS c /\
         simplicial_subcomplex (boundary_complex (barycentric_subdivision c))
                               (barycentric_subdivision c) /\
         UNIONS (boundary_complex (barycentric_subdivision c)) = complex_boundary c /\
         (!s. s IN barycentric_subdivision c /\ ~(s = {}) /\
              (!v. {v} IN barycentric_subdivision c /\ v IN s
                   ==> {v} IN boundary_complex (barycentric_subdivision c))
              ==> s IN boundary_complex (barycentric_subdivision c))`,
  GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCL_CMWB_SETUP) THEN
  MP_TAC(ISPEC `barycentric_subdivision c:(real^N->bool)->bool` MOI_FCL_CMWB_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (barycentric_subdivision c:(real^N->bool)->bool)`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_SIMPLICIAL_COMPLEX_LF; MOI_BAR_SUBDIVISION_FINITE]; ALL_TAC] THEN
  ASM_SIMP_TAC[UNIONS_BARYCENTRIC_SUBDIVISION] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `{}:real^N->bool` THEN
    REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN EXISTS_TAC `{}:(real^N->bool)->bool` THEN
    REWRITE_TAC[moi_bar_chain; EMPTY_SUBSET; FINITE_EMPTY; NOT_IN_EMPTY;
                IMAGE_CLAUSES; CONVEX_HULL_EMPTY];
    ALL_TAC] THEN
  X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_FTA_BS_FULL THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `{a:real^N} IN barycentric_subdivision c /\ (a:real^N) IN s`
    STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`barycentric_subdivision c:(real^N->bool)->bool`; `s:real^N->bool`]
      MOI_FSAP_SIMPLEX_VERTICES) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[extreme_point_of];
    ALL_TAC] THEN
  SUBGOAL_THEN `{a:real^N} IN barycentric_subdivision (boundary_complex c)` MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `a:real^N` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun u -> is_const u && fst(dest_const u) = "boundary_complex"))
        (concl th) && can (find_term (fun u -> u = `{v:real^N}`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(a:real^N) IN UNIONS (barycentric_subdivision (boundary_complex c))`
    MP_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{a:real^N}` THEN ASM_REWRITE_TAC[IN_SING];
    ASM_SIMP_TAC[UNIONS_BARYCENTRIC_SUBDIVISION]]);;

let MOI_LFI_RING_CLOSED = prove
 (`!m. 1 <= m ==> closed (moi_lfi_ring m)`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[moi_lfi_ring] THEN
  MATCH_MP_TAC CLOSED_UNIONS THEN
  MP_TAC(SPEC `m:num` MOI_LFI_RC_COMPLEX) THEN ASM_REWRITE_TAC[simplicial_complex] THEN
  MESON_TAC[SIMPLEX_IMP_CLOSED]);;

let MOI_LFI_MIDLOOP = prove
 (`path (\t. midpoint(moi_lfi_z,std_triangle_loop t)) /\
   pathfinish (\t. midpoint(moi_lfi_z,std_triangle_loop t)) =
   pathstart (\t. midpoint(moi_lfi_z,std_triangle_loop t))`,
  REWRITE_TAC[pathstart; pathfinish] THEN CONJ_TAC THENL
   [REWRITE_TAC[path; midpoint] THEN MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
    MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    REWRITE_TAC[ETA_AX; GSYM path; MOI_LTD_STD_TRIANGLE_LOOP];
    MP_TAC MOI_LTD_STD_TRIANGLE_LOOP THEN
    REWRITE_TAC[pathstart; pathfinish] THEN SIMP_TAC[]]);;

let MOI_LFI_RING_HOMOTOPY = prove
 (`!m. 1 <= m
       ==> homotopic_loops (moi_lfi_ring m) std_triangle_loop
             (\t. midpoint(moi_lfi_z,std_triangle_loop t))`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC HOMOTOPIC_LOOPS_LINEAR THEN
  REWRITE_TAC[MOI_LFI_MIDLOOP] THEN
  MP_TAC MOI_LTD_STD_TRIANGLE_LOOP THEN SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_LFI_RING_SEGMENT THEN
  ASM_SIMP_TAC[MOI_LFI_LOOP_IN_STD]);;

let MOI_LFI_Q_PARAM = prove
 (`!x. x IN moi_lfi_q
       ==> ?t. t IN interval[vec 0,vec 1] /\
               x = midpoint(moi_lfi_z,std_triangle_loop t)`,
  GEN_TAC THEN REWRITE_TAC[moi_lfi_q; MOI_LFI_FRONTIER_IMAGE; IN_IMAGE] THEN
  MESON_TAC[]);;

let MOI_LFI_GLUE_G = prove
 (`!m (g:real^2->real^N) f0 u U.
     1 <= m /\ g continuous_on moi_lfi_ring m /\
     (!t. t IN interval[vec 0,vec 1]
          ==> g (midpoint(moi_lfi_z,std_triangle_loop t)) = moi_lfi_pl (4 * m) u t) /\
     f0 continuous_on std_triangle /\ IMAGE f0 std_triangle SUBSET U /\
     (!t. t IN interval[vec 0,vec 1]
          ==> f0 (std_triangle_loop t) = moi_lfi_pl (4 * m) u t)
     ==> (\x. if x IN moi_lfi_ring m then g x else f0(&2 % x - moi_lfi_z))
           continuous_on std_triangle /\
         (!x. x IN moi_lfi_inner m /\ ~(x IN moi_lfi_ring m)
              ==> f0(&2 % x - moi_lfi_z) IN U) /\
         (!x. x IN moi_lfi_inner m /\ x IN moi_lfi_ring m
              ==> ?t. t IN interval[vec 0,vec 1] /\ g x = moi_lfi_pl (4 * m) u t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `m:num` MOI_LFI_RING_INNER) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. x IN moi_lfi_inner m ==> &2 % x - moi_lfi_z IN std_triangle`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_LFI_INNER_IMAGE; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[midpoint; VECTOR_ARITH `&2 % inv(&2) % (z + x) - z:real^2 = x`];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    MATCH_MP_TAC CONTINUOUS_ON_CASES THEN
    ASM_SIMP_TAC[MOI_LFI_RING_CLOSED; MOI_LFI_INNER_COMPACT; COMPACT_IMP_CLOSED] THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
        MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN REWRITE_TAC[CONTINUOUS_ON_ID];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
        ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]];
      X_GEN_TAC `x:real^2` THEN
      DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
       [UNDISCH_TAC `~((x:real^2) IN moi_lfi_ring m)` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(x:real^2) IN moi_lfi_q` MP_TAC THENL
       [UNDISCH_TAC `moi_lfi_ring m INTER moi_lfi_inner m SUBSET moi_lfi_q` THEN
        UNDISCH_TAC `(x:real^2) IN moi_lfi_ring m` THEN
        UNDISCH_TAC `(x:real^2) IN moi_lfi_inner m` THEN SET_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o MATCH_MP MOI_LFI_Q_PARAM) THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC) THEN
      ASM_SIMP_TAC[] THEN
      REWRITE_TAC[midpoint; VECTOR_ARITH `&2 % inv(&2) % (z + x) - z:real^2 = x`] THEN
      ASM_SIMP_TAC[]];
    REPEAT STRIP_TAC THEN
    UNDISCH_TAC `IMAGE (f0:real^2->real^N) std_triangle SUBSET U` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^2) IN moi_lfi_q` MP_TAC THENL
     [UNDISCH_TAC `moi_lfi_ring m INTER moi_lfi_inner m SUBSET moi_lfi_q` THEN
      UNDISCH_TAC `(x:real^2) IN moi_lfi_ring m` THEN
      UNDISCH_TAC `(x:real^2) IN moi_lfi_inner m` THEN SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP MOI_LFI_Q_PARAM) THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t:real^1` THEN ASM_SIMP_TAC[]]);;

let MOI_LFI_FROM_DATA = prove
 (`!(c:(real^N->bool)->bool) b (p:real^1->real^N) m w u.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     b IN components (complex_boundary c) /\
     homotopic_loops (UNIONS c) p (linepath(pathstart p,pathstart p)) /\
     1 <= m /\ w (4 * m) = w 0 /\ u (4 * m) = u 0 /\
     (!j. j <= 4 * m
          ==> {w j} IN barycentric_subdivision c /\ w j IN b /\
              {u j} IN barycentric_subdivision c /\ ~(u j IN complex_boundary c)) /\
     (!j. j < 4 * m
          ==> (?t. t IN barycentric_subdivision c /\
                   w j IN t /\ w (j + 1) IN t /\ u (j + 1) IN t) /\
              (?t. t IN barycentric_subdivision c /\
                   w j IN t /\ u j IN t /\ u (j + 1) IN t)) /\
     homotopic_loops b (moi_lfi_pl (4 * m) w) p
     ==> ?n (k:(real^2->bool)->bool) (f:real^2->real^N).
           simplicial_complex k /\ UNIONS k = std_triangle /\
           simplicial_map_on k (ITER n barycentric_subdivision c) f /\
           {x | x IN std_triangle /\ f x IN complex_boundary c} =
           relative_frontier std_triangle /\
           homotopic_loops b (f o std_triangle_loop) p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_LFI_SD_FACTS) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `K = barycentric_subdivision (c:(real^N->bool)->bool)` THEN
  ABBREV_TAC `L = boundary_complex (K:(real^N->bool)->bool)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `b SUBSET complex_boundary (c:(real^N->bool)->bool) /\
                complex_boundary c SUBSET UNIONS c`
    STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[IN_COMPONENTS_SUBSET; MOI_LTD_COMPLEX_BOUNDARY_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`m:num`; `K:(real^N->bool)->bool`; `w:num->real^N`; `u:num->real^N`]
    MOI_LFI_RING_MAP) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `g:real^2->real^N` STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `U = UNIONS c DIFF complex_boundary (c:(real^N->bool)->bool)` THEN
  SUBGOAL_THEN
   `!j. j < 4 * m ==> segment[(u:num->real^N) j,u (j + 1)] SUBSET U`
    ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MP_TAC(MP (SPEC `j:num` (ASSUME
     `!j. j < 4 * m
          ==> (?t. t IN K /\ (w:num->real^N) j IN t /\ w (j + 1) IN t /\
                   (u:num->real^N) (j + 1) IN t) /\
              (?t. t IN K /\ w j IN t /\ u j IN t /\ u (j + 1) IN t)`))
     (ASSUME `j < 4 * m`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC o CONJUNCT2) THEN
    SUBGOAL_THEN `j <= 4 * m /\ j + 1 <= 4 * m` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`; `t:real^N->bool`;
                   `{(u:num->real^N) j, u (j + 1)}`] MOI_LFI_HULL_OFF_SUB) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN
    SUBGOAL_THEN `segment[(u:num->real^N) j,u (j + 1)] SUBSET t` MP_TAC THENL
     [SUBGOAL_THEN `convex (t:real^N->bool)` MP_TAC THENL
       [UNDISCH_TAC `simplicial_complex (K:(real^N->bool)->bool)` THEN
        REWRITE_TAC[simplicial_complex] THEN ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
        ASM_SIMP_TAC[CONVEX_CONTAINS_SEGMENT_IMP]];
      ALL_TAC] THEN
    EXPAND_TAC "U" THEN
    UNDISCH_TAC `UNIONS (K:(real^N->bool)->bool) = UNIONS c` THEN
    UNDISCH_TAC `UNIONS (L:(real^N->bool)->bool) = complex_boundary c` THEN
    UNDISCH_TAC `(t:real^N->bool) IN K` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`4 * m`; `u:num->real^N`] MOI_LFI_PL_PATH) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `path_image (moi_lfi_pl (4 * m) (u:num->real^N)) SUBSET U`
    ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LFI_PL_IMAGE THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_LOOP o check
    (fun th -> can (find_term ((=) `w:num->real^N`)) (concl th) &&
               can (find_term ((=) `b:real^N->bool`)) (concl th) &&
               is_comb(concl th) &&
               fst(dest_const(fst(strip_comb(concl th)))) = "homotopic_loops")) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_PATH o check
    (fun th -> can (find_term ((=) `w:num->real^N`)) (concl th) &&
               can (find_term ((=) `b:real^N->bool`)) (concl th) &&
               is_comb(concl th) &&
               fst(dest_const(fst(strip_comb(concl th)))) = "homotopic_loops")) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_SUBSET o check
    (fun th -> can (find_term ((=) `w:num->real^N`)) (concl th) &&
               can (find_term ((=) `b:real^N->bool`)) (concl th) &&
               is_comb(concl th) &&
               fst(dest_const(fst(strip_comb(concl th)))) = "homotopic_loops")) THEN
  SUBGOAL_THEN
   `homotopic_loops (UNIONS c) (moi_lfi_pl (4 * m) (u:num->real^N))
                    (linepath(pathstart p,pathstart (p:real^1->real^N)))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN EXISTS_TAC `p:real^1->real^N` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
    EXISTS_TAC `(g:real^2->real^N) o (\t. midpoint(moi_lfi_z,std_triangle_loop t))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_LOOPS_EQ THEN ASM_REWRITE_TAC[o_THM] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
    EXISTS_TAC `(g:real^2->real^N) o std_triangle_loop` THEN CONJ_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE THEN
      EXISTS_TAC `moi_lfi_ring m` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [ONCE_REWRITE_TAC[HOMOTOPIC_LOOPS_SYM] THEN ASM_SIMP_TAC[MOI_LFI_RING_HOMOTOPY];
        ASM_MESON_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
    EXISTS_TAC `moi_lfi_pl (4 * m) (w:num->real^N)` THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[HOMOTOPIC_LOOPS_SYM] THEN MATCH_MP_TAC HOMOTOPIC_LOOPS_EQ THEN
      ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL [ASM SET_TAC[]; ASM_SIMP_TAC[]];
      MATCH_MP_TAC HOMOTOPIC_LOOPS_SUBSET THEN EXISTS_TAC `b:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `moi_lfi_pl (4 * m) (u:num->real^N)`;
                 `pathstart(p:real^1->real^N)`] MOI_LFI_INTERIOR_NULL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (MP_TAC o MATCH_MP MOI_LFI_DISK_FILL)) THEN
  DISCH_THEN(X_CHOOSE_THEN `f0:real^2->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`m:num`; `g:real^2->real^N`; `f0:real^2->real^N`; `u:num->real^N`;
                 `U:real^N->bool`] MOI_LFI_GLUE_G) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `G = \x. if x IN moi_lfi_ring m then (g:real^2->real^N) x
                      else (f0:real^2->real^N) (&2 % x - moi_lfi_z)` THEN
  MP_TAC(SPEC `m:num` MOI_LFI_RING_INNER) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x. x IN moi_lfi_ring m ==> (G:real^2->real^N) x = g x`
    ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN moi_lfi_inner m ==> (G:real^2->real^N) x IN U`
    ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(x:real^2) IN moi_lfi_ring m` THENL
     [ASM_SIMP_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `g:real^2->real^N`)) (concl th) &&
        can (find_term (fun u -> u = `moi_lfi_inner m`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `path_image (moi_lfi_pl (4 * m) (u:num->real^N)) SUBSET U` THEN
      REWRITE_TAC[path_image; SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
      EXPAND_TAC "G" THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:num`; `K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `G:real^2->real^N`; `moi_lfi_psi m (w:num->real^N) u`] MOI_LFI_MIXED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      ASM_CASES_TAC `(x:real^2) IN moi_lfi_ring m` THENL
       [ASM_SIMP_TAC[] THEN
        UNDISCH_TAC `IMAGE (g:real^2->real^N) (moi_lfi_ring m) SUBSET UNIONS K` THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
        SUBGOAL_THEN `(x:real^2) IN moi_lfi_inner m` ASSUME_TAC THENL
         [UNDISCH_TAC `moi_lfi_ring m UNION moi_lfi_inner m = std_triangle` THEN
          UNDISCH_TAC `(x:real^2) IN std_triangle` THEN
          UNDISCH_TAC `~((x:real^2) IN moi_lfi_ring m)` THEN SET_TAC[];
          ALL_TAC] THEN
        SUBGOAL_THEN `(G:real^2->real^N) x IN U` MP_TAC THENL
         [ASM_SIMP_TAC[]; ALL_TAC] THEN
        EXPAND_TAC "U" THEN REWRITE_TAC[IN_DIFF] THEN ASM_REWRITE_TAC[] THEN
        SIMP_TAC[]];
      ASM_REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
      X_GEN_TAC `y:real^N` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC)
        ASSUME_TAC) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `y:real^N`)) THEN
      SUBGOAL_THEN `(G:real^2->real^N) x IN U` MP_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "U" THEN REWRITE_TAC[IN_DIFF] THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `v:real^2` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP MOI_LFI_RC_VERTEX) THEN
      DISCH_THEN(X_CHOOSE_THEN `j:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      SUBGOAL_THEN `j <= 4 * m /\ j + 1 <= 4 * m` STRIP_ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN
       `!i. i <= 4 * m ==> (w:num->real^N) i IN complex_boundary c /\
                           ~((u:num->real^N) i IN complex_boundary c)`
        ASSUME_TAC THENL
       [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
        MP_TAC(MP (SPEC `i:num` (ASSUME
         `!j. j <= 4 * m
              ==> {(w:num->real^N) j} IN K /\ w j IN b /\
                  {(u:num->real^N) j} IN K /\ ~(u j IN complex_boundary c)`))
         (ASSUME `i <= 4 * m`)) THEN
        UNDISCH_TAC `b SUBSET complex_boundary (c:(real^N->bool)->bool)` THEN
        SET_TAC[];
        ALL_TAC] THEN
      STRIP_TAC THEN ASM_SIMP_TAC[MOI_LFI_PSI_VALUES; MOI_LFI_X_IN_FRONTIER;
                                  MOI_LFI_NOT_FRONTIER];
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `(x:real^2) IN moi_lfi_ring m` ASSUME_TAC THENL
       [REWRITE_TAC[moi_lfi_ring; IN_UNIONS] THEN EXISTS_TAC `s:real^2->bool` THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(REWRITE_RULE[SUBSET] RELATIVE_INTERIOR_SUBSET) THEN
        ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n0:num` (X_CHOOSE_THEN `f:real^2->real^N`
    STRIP_ASSUME_TAC o REWRITE_RULE[ASSUME
      `UNIONS (L:(real^N->bool)->bool) = complex_boundary c`])) THEN
  MAP_EVERY EXISTS_TAC [`1`; `ITER n0 barycentric_subdivision (moi_lfi_k0 m)`;
                        `f:real^2->real^N`] THEN
  MP_TAC(SPEC `m:num` MOI_LFI_K0_COMPLEX) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC `m:num` MOI_LFI_K0_UNION) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`moi_lfi_k0 m`; `n0:num`] MOI_FSAP_ITER) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `ITER 1 barycentric_subdivision c = (K:(real^N->bool)->bool)`
    SUBST1_TAC THENL
   [EXPAND_TAC "K" THEN REWRITE_TAC[num_CONV `1`; ITER]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:real^2` THEN
    ASM_CASES_TAC `(x:real^2) IN std_triangle` THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[MOI_LTD_FRONTIER_SUBSET_TRIANGLE; SUBSET];
    ALL_TAC] THEN
  MP_TAC MOI_LTD_STD_TRIANGLE_LOOP THEN STRIP_TAC THEN
  SUBGOAL_THEN `path ((f:real^2->real^N) o std_triangle_loop) /\
                path ((G:real^2->real^N) o std_triangle_loop)`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
    ASM_REWRITE_TAC[MOI_LTD_FRONTIER_SUBSET_TRIANGLE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t IN interval[vec 0,vec 1]
        ==> (G:real^2->real^N) (std_triangle_loop t) = moi_lfi_pl (4 * m) w t`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `std_triangle_loop t IN moi_lfi_ring m` ASSUME_TAC THENL
     [UNDISCH_TAC `relative_frontier std_triangle SUBSET moi_lfi_ring m` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[MOI_LFI_LOOP_IN_STD];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
  EXISTS_TAC `moi_lfi_pl (4 * m) (w:num->real^N)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
  EXISTS_TAC `(G:real^2->real^N) o std_triangle_loop` THEN CONJ_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_LOOPS_LINEAR THEN
    ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; o_THM] THEN
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    MP_TAC(SPEC `t:real^1` MOI_LFI_LOOP_IN_STD) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(G:real^2->real^N) (std_triangle_loop t) IN b` ASSUME_TAC THENL
     [ASM_SIMP_TAC[] THEN
      UNDISCH_TAC `path_image (moi_lfi_pl (4 * m) (w:num->real^N)) SUBSET b` THEN
      REWRITE_TAC[path_image; SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(G:real^2->real^N) (std_triangle_loop t) IN UNIONS L` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `t':real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `(G:real^2->real^N) (std_triangle_loop t)`]
      MOI_FSAP_CARRIER_MIN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `t':real^N->bool` THEN
      ASM_MESON_TAC[simplicial_subcomplex; SUBSET];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `C:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(t':real^N->bool) IN K` ASSUME_TAC THENL
     [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `(f:real^2->real^N) (std_triangle_loop t) IN C` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `f:real^2->real^N`)) (concl th) &&
        can (find_term ((=) `G:real^2->real^N`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `convex (C:real^N->bool)` ASSUME_TAC THENL
     [UNDISCH_TAC `simplicial_complex (K:(real^N->bool)->bool)` THEN
      REWRITE_TAC[simplicial_complex] THEN ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
      ALL_TAC] THEN
    SUBGOAL_THEN `(C:real^N->bool) SUBSET b` ASSUME_TAC THENL
     [MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
      EXISTS_TAC `complex_boundary (c:(real^N->bool)->bool)` THEN
      ASM_SIMP_TAC[CONVEX_CONNECTED] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `t':real^N->bool` THEN
        CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        UNDISCH_TAC `UNIONS (L:(real^N->bool)->bool) = complex_boundary c` THEN
        UNDISCH_TAC `(t':real^N->bool) IN L` THEN SET_TAC[];
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
        EXISTS_TAC `(G:real^2->real^N) (std_triangle_loop t)` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `C:real^N->bool` THEN
    ASM_SIMP_TAC[CONVEX_CONTAINS_SEGMENT_IMP];
    MATCH_MP_TAC HOMOTOPIC_LOOPS_EQ THEN
    ASM_SIMP_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; o_THM] THEN
    REWRITE_TAC[path_image; SUBSET; FORALL_IN_IMAGE; o_THM] THEN
    ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `path_image (moi_lfi_pl (4 * m) (w:num->real^N)) SUBSET b` THEN
    REWRITE_TAC[path_image; SUBSET; FORALL_IN_IMAGE] THEN SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 21. Walks.  moi_lfi_conn R x y: x and y are joined by a finite R-walk.    *)
(* Reflexivity, steps, transitivity, symmetry, transfer along a map, and    *)
(* walks of any prescribed length beyond a bound (padding by a loop at y).  *)
(* ------------------------------------------------------------------------- *)

let moi_lfi_conn = new_definition
 `moi_lfi_conn (R:A->A->bool) x y <=>
    ?n f. f 0 = x /\ f n = y /\ !i. i < n ==> R (f i) (f (i + 1))`;;

let MOI_LFI_CONN_REFL = prove
 (`!R x:A. moi_lfi_conn R x x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lfi_conn] THEN
  MAP_EVERY EXISTS_TAC [`0`; `\i:num. (x:A)`] THEN REWRITE_TAC[LT]);;

let MOI_LFI_CONN_STEP = prove
 (`!R x y:A. R x y ==> moi_lfi_conn R x y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_lfi_conn] THEN
  MAP_EVERY EXISTS_TAC [`1`; `\i:num. if i = 0 then (x:A) else y`] THEN
  REWRITE_TAC[ARITH_RULE `i < 1 <=> i = 0`; ARITH] THEN
  GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[ARITH]);;

let MOI_LFI_CONN_SNOC = prove
 (`!R x y z:A. moi_lfi_conn R x y /\ R y z ==> moi_lfi_conn R x z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lfi_conn] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `f:num->A` STRIP_ASSUME_TAC))
    ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`n + 1`; `\i:num. if i <= n then (f:num->A) i else z`] THEN
  ASM_REWRITE_TAC[LE_0; ARITH_RULE `~(n + 1 <= n)`] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `i + 1 <= (n:num)` THENL
   [SUBGOAL_THEN `i <= (n:num) /\ i < (n:num)` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ASM_SIMP_TAC[]];
    SUBGOAL_THEN `i:num = n` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[LE_REFL; ARITH_RULE `~(n + 1 <= n)`]]);;

let MOI_LFI_CONN_TRANS = prove
 (`!R x y z:A. moi_lfi_conn R x y /\ moi_lfi_conn R y z ==> moi_lfi_conn R x z`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[moi_lfi_conn] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `g:num->A` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!k. k <= (n:num) ==> moi_lfi_conn R (x:A) ((g:num->A) k)` MP_TAC THENL
   [INDUCT_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_LFI_CONN_SNOC THEN EXISTS_TAC `(g:num->A) k` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC[ADD1] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
    DISCH_THEN(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[LE_REFL; moi_lfi_conn]]);;

let MOI_LFI_CONN_MAP = prove
 (`!(R:A->A->bool) (R':B->B->bool) h.
     (!x y. R x y ==> moi_lfi_conn R' (h x) (h y))
     ==> !x y. moi_lfi_conn R x y ==> moi_lfi_conn R' (h x) (h y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [moi_lfi_conn] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `f:num->A` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!k. k <= (n:num) ==> moi_lfi_conn R' ((h:A->B) x) (h ((f:num->A) k))` MP_TAC THENL
   [INDUCT_TAC THENL [ASM_REWRITE_TAC[MOI_LFI_CONN_REFL]; ALL_TAC] THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_LFI_CONN_TRANS THEN EXISTS_TAC `(h:A->B) ((f:num->A) k)` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[ADD1] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
    DISCH_THEN(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[LE_REFL]]);;

let MOI_LFI_CONN_SYM = prove
 (`!R:A->A->bool.
     (!x y. R x y ==> R y x) ==> !x y. moi_lfi_conn R x y ==> moi_lfi_conn R y x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[moi_lfi_conn] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `f:num->A` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `\i:num. (f:num->A) (n - i)`] THEN
  ASM_REWRITE_TAC[SUB_0; SUB_REFL] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  SUBGOAL_THEN `(n:num) - i = (n - (i + 1)) + 1` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let MOI_LFI_CONN_EXACT = prove
 (`!R x y:A.
     moi_lfi_conn R x y /\ R y y
     ==> ?n0. !n. n0 <= n
                  ==> ?f. f 0 = x /\ f n = y /\ !i. i < n ==> R (f i) (f (i + 1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lfi_conn] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `n0:num` (X_CHOOSE_THEN `f:num->A` STRIP_ASSUME_TAC))
    ASSUME_TAC) THEN
  EXISTS_TAC `n0:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  EXISTS_TAC `\i:num. (f:num->A) (MIN i n0)` THEN
  ASM_REWRITE_TAC[ARITH_RULE `MIN 0 n0 = 0`] THEN
  ASM_SIMP_TAC[ARITH_RULE `n0 <= n ==> MIN n n0 = n0`] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `i < (n0:num)` THENL
   [ASM_SIMP_TAC[ARITH_RULE `i < n0 ==> MIN i n0 = i /\ MIN (i + 1) n0 = i + 1`];
    ASM_SIMP_TAC[ARITH_RULE `~(i < n0) ==> MIN i n0 = n0 /\ MIN (i + 1) n0 = n0`]]);;

(* ------------------------------------------------------------------------- *)
(* 22. In a simplicial complex with connected union, any two vertices are   *)
(* joined by an injective walk along simplices (general, real^N).           *)
(* ------------------------------------------------------------------------- *)

let MOI_LFI_VERTEX_CLOSED = prove
 (`!(k:(real^N->bool)->bool) s t.
     simplicial_complex k /\ s IN k /\ t IN k /\ ~(s INTER t = {})
     ==> ?z. {z} IN k /\ z IN s /\ z IN t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(s INTER t) face_of (s:real^N->bool) /\ (s INTER t) face_of t`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_complex (k:(real^N->bool)->bool)` THEN
    REWRITE_TAC[simplicial_complex] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `s INTER t:real^N->bool` EXTREME_POINT_EXISTS_CONVEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `compact (s:real^N->bool) /\ compact (t:real^N->bool) /\
                  convex s /\ convex t` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `simplicial_complex (k:(real^N->bool)->bool)` THEN
      REWRITE_TAC[simplicial_complex] THEN
      ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; SIMPLEX_IMP_CONVEX];
      ASM_SIMP_TAC[COMPACT_INTER; CONVEX_INTER]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `z:real^N`) THEN EXISTS_TAC `z:real^N` THEN
  SUBGOAL_THEN `(z:real^N) extreme_point_of s` ASSUME_TAC THENL
   [ASM_MESON_TAC[EXTREME_POINT_OF_FACE]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`k:(real^N->bool)->bool`; `s:real^N->bool`]
      MOI_FSAP_SIMPLEX_VERTICES) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[extreme_point_of; IN_INTER]]);;

let MOI_LFI_GRAPH_REACH = prove
 (`!(k:(real^N->bool)->bool) a y.
     simplicial_complex k /\ connected (UNIONS k) /\ {a} IN k /\ {y} IN k
     ==> moi_lfi_conn (\x y. {x} IN k /\ {y} IN k /\
                             ?s. s IN k /\ x IN s /\ y IN s) a y`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `E = \x y:real^N. {x} IN k /\ {y} IN k /\
                               ?s. s IN k /\ x IN s /\ y IN s` THEN
  ABBREV_TAC `A = {y:real^N | {y} IN k /\ moi_lfi_conn E a y}` THEN
  SUBGOAL_THEN
   `!s y1 y2. s IN k /\ y1 IN s /\ y2 IN s /\ {y1} IN k /\ {y2} IN k /\
              (y1:real^N) IN A ==> y2 IN A`
    ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "A" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_LFI_CONN_SNOC THEN EXISTS_TAC `y1:real^N` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "E" THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN k /\ ~(s = {}) ==> ?z. {z} IN k /\ z IN s`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`k:(real^N->bool)->bool`; `s:real^N->bool`; `s:real^N->bool`]
      MOI_LFI_VERTEX_CLOSED) THEN
    ASM_REWRITE_TAC[INTER_IDEMPOT] THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `X1 = UNIONS {s:real^N->bool | s IN k /\ ?z. {z} IN k /\ z IN s /\ z IN A}` THEN
  ABBREV_TAC `X2 = UNIONS {s:real^N->bool | s IN k /\ ~(s = {}) /\
                                            !z. {z} IN k /\ z IN s ==> ~(z IN A)}` THEN
  SUBGOAL_THEN `closed (X1:real^N->bool) /\ closed (X2:real^N->bool)`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "X1" THEN EXPAND_TAC "X2" THEN CONJ_TAC THEN
    MATCH_MP_TAC CLOSED_UNIONS THEN
    UNDISCH_TAC `simplicial_complex (k:(real^N->bool)->bool)` THEN
    REWRITE_TAC[simplicial_complex; IN_ELIM_THM] THEN STRIP_TAC THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `k:(real^N->bool)->bool` THEN
       ASM_REWRITE_TAC[] THEN SET_TAC[];
       ASM_MESON_TAC[SIMPLEX_IMP_CLOSED]]);
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS k SUBSET (X1:real^N->bool) UNION X2` ASSUME_TAC THENL
   [EXPAND_TAC "X1" THEN EXPAND_TAC "X2" THEN
    REWRITE_TAC[SUBSET; FORALL_IN_UNIONS; IN_UNION; IN_UNIONS; IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `x:real^N`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `?z:real^N. {z} IN k /\ z IN s /\ z IN A` THENL
     [DISJ1_TAC THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(X1:real^N->bool) INTER X2 = {}` ASSUME_TAC THENL
   [EXPAND_TAC "X1" THEN EXPAND_TAC "X2" THEN
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `s1:real^N->bool` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `s2:real^N->bool` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`k:(real^N->bool)->bool`; `s1:real^N->bool`; `s2:real^N->bool`]
      MOI_LFI_VERTEX_CLOSED) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `z0:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(z0:real^N) IN A` (fun th -> ASM_MESON_TAC[th]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun u -> u = `A:real^N->bool`)) (concl th) &&
      can (find_term (fun u -> u = `y1:real^N`)) (concl th))) THEN
    MAP_EVERY EXISTS_TAC [`s1:real^N->bool`; `z:real^N`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^N) IN A` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[MOI_LFI_CONN_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN A` MP_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    UNDISCH_TAC `connected (UNIONS (k:(real^N->bool)->bool))` THEN
    REWRITE_TAC[CONNECTED_CLOSED] THEN
    MAP_EVERY EXISTS_TAC [`X1:real^N->bool`; `X2:real^N->bool`] THEN
    ASM_REWRITE_TAC[GSYM INTER_ASSOC; INTER_EMPTY] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `a:real^N` THEN
      CONJ_TAC THENL
       [EXPAND_TAC "X1" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
        EXISTS_TAC `{a:real^N}` THEN ASM_REWRITE_TAC[IN_SING] THEN
        TRY(EXISTS_TAC `a:real^N`) THEN ASM_REWRITE_TAC[IN_SING];
        REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{a:real^N}` THEN
        ASM_REWRITE_TAC[IN_SING]];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `y:real^N` THEN
      CONJ_TAC THENL
       [EXPAND_TAC "X2" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
        EXISTS_TAC `{y:real^N}` THEN ASM_REWRITE_TAC[IN_SING; NOT_INSERT_EMPTY] THEN
        GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{y:real^N}` THEN
        ASM_REWRITE_TAC[IN_SING]]];
    EXPAND_TAC "A" THEN REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[]]);;

let MOI_LFI_MIN_WALK = prove
 (`!(R:A->A->bool) x y.
     moi_lfi_conn R x y
     ==> ?n f. f 0 = x /\ f n = y /\ (!i. i < n ==> R (f i) (f (i + 1))) /\
               (!i j. i <= n /\ j <= n /\ f i = f j ==> i = j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lfi_conn] THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `f:num->A` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `f:num->A`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!i j. i < j /\ j <= n /\ (f:num->A) i = f j ==> F` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n - (j - i):num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN
    EXISTS_TAC `\l:num. if l <= i then (f:num->A) l else f (l + (j - i))` THEN
    REWRITE_TAC[LE_0] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_CASES_TAC `n - (j - i) <= (i:num)` THEN ASM_REWRITE_TAC[] THENL
       [SUBGOAL_THEN `j:num = n /\ n - (j - i) = i` STRIP_ASSUME_TAC THENL
         [ASM_ARITH_TAC; ASM_MESON_TAC[]];
        SUBGOAL_THEN `n - (j - i) + (j - i):num = n` SUBST1_TAC THENL
         [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]];
      ALL_TAC] THEN
    X_GEN_TAC `l:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `l + 1 <= (i:num)` THENL
     [SUBGOAL_THEN `l <= (i:num) /\ l < (n:num)` STRIP_ASSUME_TAC THENL
       [ASM_ARITH_TAC; ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    ASM_CASES_TAC `l:num = i` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      REWRITE_TAC[LE_REFL; ARITH_RULE `~(i + 1 <= i)`] THEN
      SUBGOAL_THEN `(i + 1) + (j - i) = j + 1 /\ j < (n:num)` STRIP_ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(l <= (i:num)) /\ ~(l + 1 <= i) /\ l + (j - i) < (n:num) /\
                  (l + 1) + (j - i) = (l + (j - i)) + 1`
      STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `i:num = j` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `i < (j:num) \/ j < i` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_MESON_TAC[]; ASM_MESON_TAC[]]);;

let MOI_LFI_GRAPH_WALK = prove
 (`!(k:(real^N->bool)->bool) a a'.
     simplicial_complex k /\ connected (UNIONS k) /\ {a} IN k /\ {a'} IN k
     ==> ?n f. f 0 = a /\ f n = a' /\ (!i. i <= n ==> {f i} IN k) /\
               (!i. i < n ==> ?s. s IN k /\ f i IN s /\ f (i + 1) IN s) /\
               (!i j. i <= n /\ j <= n /\ f i = f j ==> i = j)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:(real^N->bool)->bool`; `a:real^N`; `a':real^N`]
    MOI_LFI_GRAPH_REACH) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_LFI_MIN_WALK) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:num->real^N` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `i:num = n` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun u -> u = `{x:real^N}`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun u -> u = `{x:real^N}`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 23. Dual complexes.  moi_lfi_dcx c s: the derived simplices spanned by   *)
(* chains of simplices properly containing s; a simplicial complex whose    *)
(* union is moi_fcl_ldual c s, with vertices the barycentres of the         *)
(* simplices properly containing s, and comparable simplices for vertices   *)
(* sharing a simplex.                                                        *)
(* ------------------------------------------------------------------------- *)

let MOI_LFI_BARY_RELINT = prove
 (`!(c:(real^N->bool)->bool) y.
     simplicial_complex c /\ y IN c /\ ~(y = {})
     ==> simplex_barycentre y IN relative_interior y /\ simplex_barycentre y IN y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplicial_complex] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?n. n simplex (y:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[SIMPLEX_BARYCENTRE_IN_RELATIVE_INTERIOR; RELATIVE_INTERIOR_SUBSET;
                SUBSET]);;

let MOI_LFI_BARY_INJ = prove
 (`!(c:(real^N->bool)->bool) y z.
     simplicial_complex c /\ y IN c /\ z IN c /\ ~(y = {}) /\ ~(z = {}) /\
     simplex_barycentre y = simplex_barycentre z
     ==> y = z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `y:real^N->bool`] MOI_LFI_BARY_RELINT) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:real^N->bool`] MOI_LFI_BARY_RELINT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN CONJ_TAC THEN
  MATCH_MP_TAC MOI_FSAP_RELINT_SUBSET THEN
  MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `simplex_barycentre (z:real^N->bool)`] THEN
  ASM_MESON_TAC[]);;

let moi_lfi_dcx = new_definition
 `moi_lfi_dcx (c:(real^N->bool)->bool) (s:real^N->bool) =
    {convex hull (IMAGE simplex_barycentre f) | f |
       moi_bar_chain c f /\ !t. t IN f ==> s SUBSET t /\ ~(t = s)}`;;

let MOI_LFI_DCX_COMPLEX = prove
 (`!(c:(real^N->bool)->bool) s.
     simplicial_complex c
     ==> simplicial_complex (moi_lfi_dcx c s) /\
         moi_lfi_dcx c s SUBSET barycentric_subdivision c /\
         UNIONS (moi_lfi_dcx c s) = moi_fcl_ldual c s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_SIMPLICIAL_COMPLEX]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_lfi_dcx c (s:real^N->bool) SUBSET barycentric_subdivision c`
    ASSUME_TAC THENL
   [REWRITE_TAC[moi_lfi_dcx; SUBSET; FORALL_IN_GSPEC; MOI_BAR_IN_SUBDIVISION] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_LFI_SUBCOMPLEX THEN
    EXISTS_TAC `barycentric_subdivision c:(real^N->bool)->bool` THEN
    ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_SIMPLICIAL_COMPLEX] THEN
    REWRITE_TAC[moi_lfi_dcx; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `f:(real^N->bool)->bool` THEN DISCH_TAC THEN DISCH_TAC THEN
    X_GEN_TAC `t:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~affine_dependent (IMAGE simplex_barycentre (f:(real^N->bool)->bool))`
      ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_BAR_CHAIN_AFFINE_INDEPENDENT THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`IMAGE simplex_barycentre (f:(real^N->bool)->bool)`; `t:real^N->bool`]
      FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `W:real^N->bool` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    EXISTS_TAC `{y:real^N->bool | y IN f /\ simplex_barycentre y IN W}` THEN
    CONJ_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THEN
        EXISTS_TAC `f:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
        REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]];
      ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
      UNDISCH_TAC `W SUBSET IMAGE simplex_barycentre (f:(real^N->bool)->bool)` THEN
      SET_TAC[]];
    REWRITE_TAC[moi_fcl_ldual; moi_lfi_dcx] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
      EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `f:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `(x:real^N) IN t` THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
      MESON_TAC[]]]);;

let MOI_LFI_SING_CHAIN = prove
 (`!(c:(real^N->bool)->bool) y. y IN c /\ ~(y = {}) ==> moi_bar_chain c {y}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[moi_bar_chain; FINITE_SING; SING_SUBSET; IN_SING] THEN
  ASM_MESON_TAC[SUBSET_REFL]);;

let MOI_LFI_DCX_VERTEX = prove
 (`!(c:(real^N->bool)->bool) s d.
     simplicial_complex c
     ==> ({d} IN moi_lfi_dcx c s <=>
          ?y. y IN c /\ ~(y = {}) /\ s SUBSET y /\ ~(y = s) /\
              d = simplex_barycentre y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_lfi_dcx; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?y:real^N->bool. y IN f` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN DISCH_TAC THEN
      UNDISCH_TAC `{d:real^N} = convex hull IMAGE simplex_barycentre f` THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_INSERT_EMPTY];
      ALL_TAC] THEN
    EXISTS_TAC `y:real^N->bool` THEN
    UNDISCH_TAC `moi_bar_chain c (f:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_bar_chain] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [ASM SET_TAC[]; ASM_MESON_TAC[]; ASM_MESON_TAC[]; ASM_MESON_TAC[];
      SUBGOAL_THEN `simplex_barycentre (y:real^N->bool) IN {d}` MP_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
        SIMP_TAC[IN_SING]]];
    DISCH_THEN(X_CHOOSE_THEN `y:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `{y:real^N->bool}` THEN
    ASM_SIMP_TAC[MOI_LFI_SING_CHAIN; IN_SING; IMAGE_CLAUSES; CONVEX_HULL_SING] THEN
    ASM_MESON_TAC[]]);;

let MOI_LFI_DCX_ADJ = prove
 (`!(c:(real^N->bool)->bool) s y y' t.
     simplicial_complex c /\ y IN c /\ y' IN c /\ ~(y = {}) /\ ~(y' = {}) /\
     t IN moi_lfi_dcx c s /\ simplex_barycentre y IN t /\
     simplex_barycentre y' IN t
     ==> y SUBSET y' \/ y' SUBSET y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(t:real^N->bool) IN moi_lfi_dcx c s` THEN
  REWRITE_TAC[moi_lfi_dcx; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `simplicial_complex (barycentric_subdivision c:(real^N->bool)->bool) /\
                (t:real^N->bool) IN barycentric_subdivision c`
    STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_SIMPLICIAL_COMPLEX] THEN
    REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^N->bool. z IN c /\ ~(z = {}) /\ simplex_barycentre z IN t ==> z IN f`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `simplex_barycentre (z:real^N->bool) extreme_point_of t` MP_TAC THENL
     [MATCH_MP_TAC MOI_FSAP_VERTEX_EXTREME THEN
      EXISTS_TAC `barycentric_subdivision c:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
      EXISTS_TAC `{z:real^N->bool}` THEN
      ASM_SIMP_TAC[MOI_LFI_SING_CHAIN; IMAGE_CLAUSES; CONVEX_HULL_SING];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP EXTREME_POINT_OF_CONVEX_HULL) THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `z':real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `z:real^N->bool = z'` (fun th -> ASM_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC MOI_LFI_BARY_INJ THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_bar_chain c (f:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_bar_chain] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_bar_chain c (f:(real^N->bool)->bool)` THEN
  REWRITE_TAC[moi_bar_chain] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 24. Flags at a boundary vertex v: pairs (x,r) with x a boundary simplex   *)
(* containing v properly and r a non-boundary simplex containing x; moves   *)
(* change one coordinate to a comparable one.  Books: around a boundary     *)
(* edge e, any two non-boundary simplices containing e are joined by inner  *)
(* moves (MOI_FCL_EDGE_LDUAL_ARC, GRAPH_WALK).                               *)
(* ------------------------------------------------------------------------- *)

let moi_lfi_flag = new_definition
 `moi_lfi_flag (c:(real^N->bool)->bool) (v:real^N)
               (p:(real^N->bool)#(real^N->bool)) <=>
    FST p IN boundary_complex c /\ v IN FST p /\ ~(FST p = {v}) /\
    SND p IN c /\ ~(SND p IN boundary_complex c) /\ FST p SUBSET SND p`;;

let moi_lfi_move = new_definition
 `moi_lfi_move (c:(real^N->bool)->bool) (v:real^N)
               (p:(real^N->bool)#(real^N->bool)) q <=>
    moi_lfi_flag c v p /\ moi_lfi_flag c v q /\
    ((FST p = FST q /\ (SND p SUBSET SND q \/ SND q SUBSET SND p)) \/
     (SND p = SND q /\ (FST p SUBSET FST q \/ FST q SUBSET FST p)))`;;

let MOI_LFI_CELL_CONNECTED = prove
 (`!n (s:real^N->bool) b. pl_cell_with_boundary n s b ==> connected s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism;
                                  homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rand(concl th) = `s:real^N->bool`)) THEN
  MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[CONVEX_CONNECTED; SIMPLEX_IMP_CONVEX]);;

let MOI_LFI_C_COMPLEX = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c
     ==> simplicial_complex c /\ lf_simplicial_complex c /\
         simplicial_complex (boundary_complex c) /\
         boundary_complex c SUBSET c`,
  GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCL_CMWB_SETUP) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `boundary_complex c SUBSET (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[boundary_complex] THEN SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF] THEN
  ASM_MESON_TAC[FINITE_SUBSET]);;

let MOI_LFI_BOOK = prove
 (`!(c:(real^N->bool)->bool) v e r r'.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     e IN boundary_complex c /\ aff_dim e = &1 /\ v IN e /\
     r IN c /\ ~(r IN boundary_complex c) /\ e SUBSET r /\
     r' IN c /\ ~(r' IN boundary_complex c) /\ e SUBSET r'
     ==> moi_lfi_conn (moi_lfi_move c v) (e,r) (e,r')`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_LFI_C_COMPLEX) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(e:real^N->bool) IN c /\ ~(e = {}) /\ ~(e = {v})` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      DISCH_TAC THEN UNDISCH_TAC `aff_dim(e:real^N->bool) = &1` THEN
      ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
      DISCH_TAC THEN UNDISCH_TAC `aff_dim(e:real^N->bool) = &1` THEN
      ASM_REWRITE_TAC[AFF_DIM_SING] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FCL_EDGE_LDUAL_ARC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:real^N->bool` (X_CHOOSE_THEN `s2:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FCL_EDGE_COFACES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real^N->bool` (X_CHOOSE_THEN `t2:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `connected (UNIONS (moi_lfi_dcx c (e:real^N->bool)))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_LFI_DCX_COMPLEX] THEN MATCH_MP_TAC MOI_LFI_CELL_CONNECTED THEN
    MAP_EVERY EXISTS_TAC
     [`1`; `{simplex_barycentre s1, simplex_barycentre (s2:real^N->bool)}`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(r:real^N->bool = {}) /\ ~(r = e) /\ ~(r':real^N->bool = {}) /\
                ~(r' = e)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THENL
     [UNDISCH_TAC `(e:real^N->bool) SUBSET {}` THEN ASM_REWRITE_TAC[SUBSET_EMPTY];
      UNDISCH_TAC `~((e:real^N->bool) IN boundary_complex c)` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `(e:real^N->bool) SUBSET {}` THEN ASM_REWRITE_TAC[SUBSET_EMPTY];
      UNDISCH_TAC `~((e:real^N->bool) IN boundary_complex c)` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_lfi_dcx c (e:real^N->bool)`; `simplex_barycentre (r:real^N->bool)`;
                 `simplex_barycentre (r':real^N->bool)`] MOI_LFI_GRAPH_WALK) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MOI_LFI_DCX_COMPLEX; MOI_LFI_DCX_VERTEX] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `d:num->real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `?y:num->(real^N->bool).
      !i. i <= n ==> y i IN c /\ ~(y i = {}) /\ e SUBSET y i /\ ~(y i = e) /\
                     d i = simplex_barycentre (y i)`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `i:num` THEN
    REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `(d:num->real^N) i`]
      MOI_LFI_DCX_VERTEX) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:num->real^N->bool) 0 = r /\ y n = r'` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_LFI_BARY_INJ THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_SIMP_TAC[LE_0; LE_REFL] THEN
    ASM_MESON_TAC[LE_0; LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. i <= n /\ j <= n /\ (y:num->real^N->bool) i = y j ==> i = j`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `d:num->real^N`)) (concl th) &&
      not(can (find_term (fun u -> is_const u && fst(dest_const u) = "moi_lfi_dcx")) (concl th)) &&
      can (find_term (fun u -> u = `j:num`)) (concl th))) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i < n ==> (y:num->real^N->bool) i SUBSET y (i + 1) \/ y (i + 1) SUBSET y i`
    ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun u -> is_const u && fst(dest_const u) = "moi_lfi_dcx")) (concl th) &&
      can (find_term (fun u -> u = `i + 1`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `sg:real^N->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC MOI_LFI_DCX_ADJ THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `e:real^N->bool`;
                          `sg:real^N->bool`] THEN
    SUBGOAL_THEN `i <= n /\ i + 1 <= n` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i <= n ==> ~((y:num->real^N->bool) i IN boundary_complex c)`
    ASSUME_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[moi_lfi_conn] THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `\i. (e:real^N->bool),(y:num->real^N->bool) i`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `i <= n /\ i + 1 <= n` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[moi_lfi_move; moi_lfi_flag]] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:num->real^N->bool) i IN {t1,t2}` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `{t1:real^N->bool,t2}`)) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(i = 0) /\ ~(i:num = n)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim((y:num->real^N->bool) i) = &2` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:num->real^N->bool) i IN {t1,t2}` THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `(y:num->real^N->bool) i`]
    MOI_FCL_TRIANGLE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `T0:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!j. j <= n /\ ~((y:num->real^N->bool) j = y i) /\
        (y j SUBSET y i \/ y i SUBSET y j)
        ==> y j = T0`
    ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN STRIP_TAC THENL
     [FIRST_ASSUM(fun th -> if is_forall(concl th) &&
         can (find_term (fun u -> u = `simplex_barycentre ((y:num->real^N->bool) i)`))
           (concl th)
       then MP_TAC(CONJ (MP (SPEC `j:num` th) (ASSUME `j <= (n:num)`))
                        (MP (SPEC `i:num` th) (ASSUME `i <= (n:num)`)))
       else NO_TAC) THEN
      STRIP_TAC THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`;
                     `(y:num->real^N->bool) j`] MOI_FCL_PROPER_DIM_LT) THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `(y:num->real^N->bool) j`;
                     `(y:num->real^N->bool) i`] MOI_FCL_PROPER_DIM_LT) THEN
      ASM_REWRITE_TAC[] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM(ASSUME `aff_dim((y:num->real^N->bool) i) = &2`)]) THEN
      ASM_MESON_TAC[INT_ARITH `!a b c:int. a = &1 /\ c = &2 ==> ~(a < b /\ b < c)`];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun u -> u = `T0:real^N->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(fun th -> if is_forall(concl th) &&
         can (find_term (fun u -> u = `simplex_barycentre ((y:num->real^N->bool) i)`))
           (concl th)
       then MP_TAC(MP (SPEC `j:num` th) (ASSUME `j <= (n:num)`)) else NO_TAC) THEN
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:num->real^N->bool) (i - 1) = T0 /\ y (i + 1) = T0`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THENL
     [SUBGOAL_THEN `i - 1 <= n /\ i - 1 < n /\ (i - 1) + 1 = i` STRIP_ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [DISCH_TAC THEN
        SUBGOAL_THEN `i - 1 = i` MP_TAC THENL [ASM_MESON_TAC[]; ASM_ARITH_TAC];
        ASM_MESON_TAC[]];
      SUBGOAL_THEN `i + 1 <= n /\ i < n` STRIP_ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [DISCH_TAC THEN
        SUBGOAL_THEN `i + 1 = i` MP_TAC THENL [ASM_MESON_TAC[]; ARITH_TAC];
        ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `i - 1 = i + 1` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `y:num->real^N->bool`)) (concl th) &&
      can (find_term (fun u -> u = `i:num = j`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 25. Any two flags at a boundary vertex v are joined by moves: books at   *)
(* edges, unique cofaces at triangles, and the dual circle of v             *)
(* (MOI_FCL_VERTEX_LDUAL, a PL 1-sphere, hence connected; GRAPH_REACH).      *)
(* ------------------------------------------------------------------------- *)

let MOI_LFI_BC_PURE = prove
 (`!(c:(real^N->bool)->bool) x.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     x IN boundary_complex c /\ ~(x = {})
     ==> ?t. t IN boundary_complex c /\ aff_dim t = &2 /\ x SUBSET t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_LFI_C_COMPLEX) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^N->bool) IN c /\ x SUBSET complex_boundary c` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N->bool) IN boundary_complex c` THEN
    REWRITE_TAC[boundary_complex; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `x:real^N->bool`] MOI_LFI_BARY_RELINT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplex_barycentre (x:real^N->bool) IN complex_boundary c` MP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [MOI_FCL_CB_TRIANGLES] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[boundary_complex; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MOI_FCL_CB_TRIANGLES] THEN
    MATCH_MP_TAC(SET_RULE `(t:real^N->bool) IN u ==> t SUBSET UNIONS u`) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    MATCH_MP_TAC MOI_FSAP_RELINT_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`;
                          `simplex_barycentre (x:real^N->bool)`] THEN
    ASM_REWRITE_TAC[]]);;

let MOI_LFI_TRI_COFACE = prove
 (`!(c:(real^N->bool)->bool) t.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     t IN boundary_complex c /\ aff_dim t = &2
     ==> ?T. T IN c /\ ~(T IN boundary_complex c) /\ t SUBSET T /\
             !r. r IN c /\ t SUBSET r /\ ~(r = t) ==> r = T`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`] MOI_FCL_TRIANGLE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `T0:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `T0:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `T0:real^N->bool`] MOI_FCL_BD_AFF_DIM) THEN
  ASM_REWRITE_TAC[] THEN INT_ARITH_TAC);;

let MOI_LFI_FLAG_EXISTS = prove
 (`!(c:(real^N->bool)->bool) x.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     x IN boundary_complex c /\ ~(x = {})
     ==> ?r. r IN c /\ ~(r IN boundary_complex c) /\ x SUBSET r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `x:real^N->bool`] MOI_LFI_BC_PURE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`] MOI_LFI_TRI_COFACE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `T0:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `T0:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_LFI_FLAG_DIM = prove
 (`!(c:(real^N->bool)->bool) v x.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\ {v} IN c /\
     x IN boundary_complex c /\ v IN x /\ ~(x = {v})
     ==> aff_dim x = &1 \/ aff_dim x = &2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_LFI_C_COMPLEX) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^N->bool) IN c` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `{v:real^N} SUBSET x` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `{v:real^N}`; `x:real^N->bool`]
    MOI_FCL_PROPER_DIM_LT) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `x:real^N->bool`] MOI_FCL_BD_AFF_DIM) THEN
  ASM_REWRITE_TAC[AFF_DIM_SING] THEN INT_ARITH_TAC);;

let MOI_LFI_SAME_X = prove
 (`!(c:(real^N->bool)->bool) v x r r'.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\ {v} IN c /\
     moi_lfi_flag c v (x,r) /\ moi_lfi_flag c v (x,r')
     ==> moi_lfi_conn (moi_lfi_move c v) (x,r) (x,r')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lfi_flag] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `x:real^N->bool`]
    MOI_LFI_FLAG_DIM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [MATCH_MP_TAC MOI_LFI_BOOK THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `x:real^N->bool`] MOI_LFI_TRI_COFACE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `T0:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `r:real^N->bool = T0 /\ r' = T0` (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[];
      REWRITE_TAC[MOI_LFI_CONN_REFL]]]);;

let MOI_LFI_FLAG_CONN = prove
 (`!(c:(real^N->bool)->bool) v p q.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     {v} IN boundary_complex c /\ moi_lfi_flag c v p /\ moi_lfi_flag c v q
     ==> moi_lfi_conn (moi_lfi_move c v) p q`,
  REPEAT GEN_TAC THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`q:(real^N->bool)#(real^N->bool)`;
                                     `p:(real^N->bool)#(real^N->bool)`] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N->bool`; `r:real^N->bool`;
                       `x':real^N->bool`; `r':real^N->bool`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_LFI_C_COMPLEX) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `{v:real^N} IN c /\ v IN complex_boundary c` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FCL_BD_VERTEX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FCL_VERTEX_LDUAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`boundary_complex c:(real^N->bool)->bool`; `{v:real^N}`]
    MOI_LFI_DCX_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `kv = moi_lfi_dcx (boundary_complex c) {v:real^N}` THEN
  SUBGOAL_THEN `connected (UNIONS (kv:(real^N->bool)->bool))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S4O_SPHERE1_CONNECTED THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `X = \d:real^N. @x. x IN boundary_complex c /\ ~(x = {}) /\ {v} SUBSET x /\
                       ~(x = {v}) /\ d = simplex_barycentre x` THEN
  ABBREV_TAC
   `rho = \x:real^N->bool. @r. r IN c /\ ~(r IN boundary_complex c) /\ x SUBSET r` THEN
  SUBGOAL_THEN
   `!y:real^N->bool. y IN boundary_complex c /\ v IN y /\ ~(y = {v})
                     ==> (X:real^N->real^N->bool) (simplex_barycentre y) = y`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "X" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `z:real^N->bool` THEN EQ_TAC THENL
     [STRIP_TAC THEN MATCH_MP_TAC MOI_LFI_BARY_INJ THEN
      EXISTS_TAC `boundary_complex c:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^N->bool. y IN boundary_complex c /\ ~(y = {})
                     ==> (rho:(real^N->bool)->real^N->bool) y IN c /\
                         ~(rho y IN boundary_complex c) /\ y SUBSET rho y`
    ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN EXPAND_TAC "rho" THEN REWRITE_TAC[] THEN
    CONV_TAC SELECT_CONV THEN MATCH_MP_TAC MOI_LFI_FLAG_EXISTS THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `h = \d:real^N. ((X:real^N->real^N->bool) d,
                    (rho:(real^N->bool)->real^N->bool) (X d))` THEN
  SUBGOAL_THEN
   `!y:real^N->bool. y IN boundary_complex c /\ v IN y /\ ~(y = {v})
                     ==> (h:real^N->(real^N->bool)#(real^N->bool))
                           (simplex_barycentre y) = (y,rho y) /\
                         moi_lfi_flag c v (y,(rho:(real^N->bool)->real^N->bool) y)`
    ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN EXPAND_TAC "h" THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `~(y:real^N->bool = {})` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[moi_lfi_flag];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!d. {d} IN kv
        ==> ?y:real^N->bool. y IN boundary_complex c /\ v IN y /\ ~(y = {v}) /\
                             d = simplex_barycentre y`
    ASSUME_TAC THENL
   [X_GEN_TAC `d:real^N` THEN EXPAND_TAC "kv" THEN
    ASM_SIMP_TAC[MOI_LFI_DCX_VERTEX] THEN MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^N->bool. y IN boundary_complex c /\ v IN y /\ ~(y = {v})
                     ==> {simplex_barycentre y} IN kv`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "kv" THEN ASM_SIMP_TAC[MOI_LFI_DCX_VERTEX] THEN
    EXISTS_TAC `y:real^N->bool` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\x y:real^N. {x} IN kv /\ {y} IN kv /\ ?s. s IN kv /\ x IN s /\ y IN s`;
    `moi_lfi_move c (v:real^N)`; `h:real^N->(real^N->bool)#(real^N->bool)`]
    MOI_LFI_CONN_MAP) THEN
  ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`d:real^N`; `d':real^N`] THEN BETA_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `sg:real^N->bool` STRIP_ASSUME_TAC))) THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) &&
      can (find_term (fun u -> u = `kv:(real^N->bool)->bool`)) (concl th) &&
      is_exists(snd(dest_imp(snd(dest_forall(concl th)))))
      then MP_TAC(MP (SPEC `d:real^N` th) (ASSUME `{d:real^N} IN kv`)) else NO_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N->bool` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) &&
      can (find_term (fun u -> u = `kv:(real^N->bool)->bool`)) (concl th) &&
      is_exists(snd(dest_imp(snd(dest_forall(concl th)))))
      then MP_TAC(MP (SPEC `d':real^N` th) (ASSUME `{d':real^N} IN kv`)) else NO_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `y':real^N->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `~(y:real^N->bool = {}) /\ ~(y':real^N->bool = {})`
      STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^N->bool) SUBSET y' \/ y' SUBSET y` MP_TAC THENL
     [MATCH_MP_TAC MOI_LFI_DCX_ADJ THEN
      MAP_EVERY EXISTS_TAC [`boundary_complex c:(real^N->bool)->bool`; `{v:real^N}`;
                            `sg:real^N->bool`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(MP (SPEC `y:real^N->bool` (ASSUME
     `!y:real^N->bool. y IN boundary_complex c /\ v IN y /\ ~(y = {v})
                       ==> (h:real^N->(real^N->bool)#(real^N->bool))
                             (simplex_barycentre y) = (y,rho y) /\
                           moi_lfi_flag c v (y,(rho:(real^N->bool)->real^N->bool) y)`))
     (CONJ (ASSUME `(y:real^N->bool) IN boundary_complex c`)
           (CONJ (ASSUME `(v:real^N) IN y`) (ASSUME `~(y:real^N->bool = {v})`)))) THEN
    MP_TAC(MP (SPEC `y':real^N->bool` (ASSUME
     `!y:real^N->bool. y IN boundary_complex c /\ v IN y /\ ~(y = {v})
                       ==> (h:real^N->(real^N->bool)#(real^N->bool))
                             (simplex_barycentre y) = (y,rho y) /\
                           moi_lfi_flag c v (y,(rho:(real^N->bool)->real^N->bool) y)`))
     (CONJ (ASSUME `(y':real^N->bool) IN boundary_complex c`)
           (CONJ (ASSUME `(v:real^N) IN y'`) (ASSUME `~(y':real^N->bool = {v})`)))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `!a b:real^N->bool.
        moi_lfi_flag c v (a,rho a) /\ moi_lfi_flag c v (b,rho b) /\ a SUBSET b
        ==> moi_lfi_conn (moi_lfi_move c v) (a,rho a) (b,rho b) /\
            moi_lfi_conn (moi_lfi_move c v) (b,rho b) (a,rho a)`
      MP_TAC THENL
     [REPEAT GEN_TAC THEN STRIP_TAC THEN
      SUBGOAL_THEN `moi_lfi_flag c v (a,(rho:(real^N->bool)->real^N->bool) b)`
        ASSUME_TAC THENL
       [UNDISCH_TAC `moi_lfi_flag c v (a,(rho:(real^N->bool)->real^N->bool) a)` THEN
        UNDISCH_TAC `moi_lfi_flag c v (b,(rho:(real^N->bool)->real^N->bool) b)` THEN
        REWRITE_TAC[moi_lfi_flag] THEN ASM SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `moi_lfi_move c v (a,(rho:(real^N->bool)->real^N->bool) b) (b,rho b) /\
        moi_lfi_move c v (b,rho b) (a,rho b)`
        STRIP_ASSUME_TAC THENL
       [ASM_REWRITE_TAC[moi_lfi_move] THEN ASM SET_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MOI_LFI_CONN_TRANS THEN
        EXISTS_TAC `(a:real^N->bool),(rho:(real^N->bool)->real^N->bool) b` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC MOI_LFI_SAME_X THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC MOI_LFI_CONN_STEP THEN ASM_REWRITE_TAC[]];
        MATCH_MP_TAC MOI_LFI_CONN_TRANS THEN
        EXISTS_TAC `(a:real^N->bool),(rho:(real^N->bool)->real^N->bool) b` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC MOI_LFI_CONN_STEP THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC MOI_LFI_SAME_X THEN ASM_REWRITE_TAC[]]];
      ALL_TAC] THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th))) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`simplex_barycentre (x:real^N->bool)`;
                             `simplex_barycentre (x':real^N->bool)`]) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC MOI_LFI_GRAPH_REACH THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_lfi_flag c v (x:real^N->bool,r)` THEN
    UNDISCH_TAC `moi_lfi_flag c v (x':real^N->bool,r')` THEN
    REWRITE_TAC[moi_lfi_flag] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_lfi_flag c v (x:real^N->bool,(rho:(real^N->bool)->real^N->bool) x) /\
    moi_lfi_flag c v (x':real^N->bool,rho x') /\
    (h:real^N->(real^N->bool)#(real^N->bool)) (simplex_barycentre x) = (x,rho x) /\
    h (simplex_barycentre x') = (x',rho x')`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_lfi_flag c v (x:real^N->bool,r)` THEN
    UNDISCH_TAC `moi_lfi_flag c v (x':real^N->bool,r')` THEN
    REWRITE_TAC[moi_lfi_flag] THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[moi_lfi_flag];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC MOI_LFI_CONN_TRANS THEN
  EXISTS_TAC `(x:real^N->bool),(rho:(real^N->bool)->real^N->bool) x` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_LFI_SAME_X THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_LFI_CONN_TRANS THEN
  EXISTS_TAC `(x':real^N->bool),(rho:(real^N->bool)->real^N->bool) x'` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_LFI_SAME_X THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 26. (B1) a cyclic vertex sequence for the loop p: each piece of p over   *)
(* [k/N,(k+1)/N] lies in the open star of v k in the boundary complex, and *)
(* p((k+1)/N) also in the open star of v (k+1) (Lebesgue number and        *)
(* uniform continuity).                                                      *)
(* ------------------------------------------------------------------------- *)

let MOI_LFI_BC_IN_COMPONENT = prove
 (`!(c:(real^N->bool)->bool) b t.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     b IN components (complex_boundary c) /\
     t IN boundary_complex c /\ ~(t INTER b = {})
     ==> t SUBSET b`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_LFI_C_COMPLEX) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
  EXISTS_TAC `complex_boundary (c:(real^N->bool)->bool)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONVEX_CONNECTED THEN
    UNDISCH_TAC `simplicial_complex (boundary_complex c:(real^N->bool)->bool)` THEN
    REWRITE_TAC[simplicial_complex] THEN ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
    UNDISCH_TAC `(t:real^N->bool) IN boundary_complex c` THEN
    REWRITE_TAC[boundary_complex; IN_ELIM_THM] THEN SIMP_TAC[];
    ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[]]);;

let MOI_LFI_PARAM_DIST = prove
 (`!N k s. 1 <= N /\ k < N /\ &k / &N <= drop s /\ drop s <= &(k + 1) / &N
           ==> s IN interval[vec 0,vec 1] /\ lift(&k / &N) IN interval[vec 0,vec 1] /\
               dist(s,lift(&k / &N)) <= inv(&N)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &N` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&(k + 1) / &N = &k / &N + inv(&N)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_ADD; real_div; REAL_ADD_RDISTRIB; REAL_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &k / &N /\ &(k + 1) / &N <= &1` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LE_LDIV_EQ; REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP; DIST_1] THEN
  SUBGOAL_THEN `&0 <= inv(&N)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV THEN REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `&(k + 1) / &N = &k / &N + inv(&N)` THEN
  UNDISCH_TAC `&(k + 1) / &N <= &1` THEN UNDISCH_TAC `&0 <= &k / &N` THEN
  UNDISCH_TAC `&k / &N <= drop s` THEN UNDISCH_TAC `drop s <= &(k + 1) / &N` THEN
  REAL_ARITH_TAC);;

let MOI_LFI_VERTEX_SEQ = prove
 (`!(c:(real^N->bool)->bool) b (p:real^1->real^N).
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     b IN components (complex_boundary c) /\
     path p /\ path_image p SUBSET b /\ pathfinish p = pathstart p
     ==> ?N v. 1 <= N /\ v N = v 0 /\
               (!k. {v k} IN boundary_complex c /\ v k IN b) /\
               (!k s t. k < N /\ &k / &N <= drop s /\ drop s <= &(k + 1) / &N /\
                        t IN boundary_complex c /\ p s IN t
                        ==> v k IN t) /\
               (!k t. k < N /\ t IN boundary_complex c /\
                      p (lift(&(k + 1) / &N)) IN t
                      ==> v (k + 1) IN t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_LFI_C_COMPLEX) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_FCL_CMWB_SETUP) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(b:real^N->bool) SUBSET complex_boundary c` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`boundary_complex c:(real^N->bool)->bool`;
                 `{w:real^N | {w} IN boundary_complex c /\ w IN b}`;
                 `path_image (p:real^1->real^N)`] MOI_FSAP_LEBESGUE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_PATH_IMAGE] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`boundary_complex c:(real^N->bool)->bool`; `y:real^N`]
      MOI_FSAP_STAR_COVER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    SUBGOAL_THEN `?t0:real^N->bool. t0 IN boundary_complex c /\ y IN t0`
      STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM IN_UNIONS] THEN ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(t0:real^N->bool) SUBSET b` MP_TAC THENL
     [MATCH_MP_TAC MOI_LFI_BC_IN_COMPONENT THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`p:real^1->real^N`; `interval[vec 0:real^1,vec 1]`]
    COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[path; COMPACT_INTERVAL]; ALL_TAC] THEN
  REWRITE_TAC[uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `d:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `del:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `del:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < &N` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. lift(&(k MOD N) / &N) IN interval[vec 0,vec 1]`
    ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LE_LDIV_EQ; REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN
    MP_TAC(SPECL [`k:num`; `N:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?vv:num->real^N.
      !k. ({vv k} IN boundary_complex c /\ vv k IN b) /\
          !z t. dist(p(lift(&(k MOD N) / &N)),z) < d /\ t IN boundary_complex c /\
                z IN t ==> vv k IN t`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `k:num` THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun u -> u = `d:real`)) (concl th) &&
      can (find_term (fun u -> u = `path_image (p:real^1->real^N)`)) (concl th))) THEN
    REWRITE_TAC[path_image] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`N:num`; `\k. (vv:num->real^N) (k MOD N)`] THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `N MOD N = 0 /\ 0 MOD N = 0` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_SIMP_TAC[MOD_REFL; MOD_0]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`k:num`; `s:real^1`; `t:real^N->bool`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `k MOD N = k` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun u -> u = `vv:num->real^N`)) (concl th))) THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    EXISTS_TAC `(p:real^1->real^N) s` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_SIMP_TAC[MOD_LT] THEN
    MP_TAC(SPECL [`N:num`; `k:num`; `s:real^1`] MOI_LFI_PARAM_DIST) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `inv(&N) < del` THEN
    UNDISCH_TAC `dist(s:real^1,lift(&k / &N)) <= inv(&N)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `t:real^N->bool`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(k + 1) MOD N` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun u -> u = `vv:num->real^N`)) (concl th))) THEN
  REWRITE_TAC[MOD_MOD_REFL] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
  EXISTS_TAC `(p:real^1->real^N) (lift(&(k + 1) / &N))` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `k + 1 < N` THENL
   [ASM_SIMP_TAC[MOD_LT; DIST_REFL];
    SUBGOAL_THEN `k + 1 = N` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[MOD_REFL; REAL_DIV_REFL; REAL_LT_IMP_NZ] THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; LIFT_NUM] THEN
    UNDISCH_TAC `pathfinish (p:real^1->real^N) = pathstart p` THEN
    REWRITE_TAC[pathstart; pathfinish] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[DIST_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* 27. Consequences of moves for the barycentres: chains, a common simplex  *)
(* of sd c, a boundary triangle through v, and the vertex conditions.       *)
(* ------------------------------------------------------------------------- *)

let MOI_LFI_MOVE_CHAIN = prove
 (`!(c:(real^N->bool)->bool) v p q.
     moi_lfi_move c v p q
     ==> moi_bar_chain c {FST p, FST q, SND p, SND q}`,
  REPEAT GEN_TAC THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`q:(real^N->bool)#(real^N->bool)`;
                                     `p:(real^N->bool)#(real^N->bool)`] THEN
  REWRITE_TAC[FORALL_PAIR_THM; moi_lfi_move; moi_lfi_flag] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N->bool`; `r:real^N->bool`;
                       `a':real^N->bool`; `r':real^N->bool`] THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[moi_bar_chain; FINITE_INSERT; FINITE_EMPTY; INSERT_SUBSET; EMPTY_SUBSET;
              IN_INSERT; NOT_IN_EMPTY] THEN
  (SUBGOAL_THEN `(a:real^N->bool) IN c /\ a' IN c` STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `(a:real^N->bool) IN boundary_complex c` THEN
     UNDISCH_TAC `(a':real^N->bool) IN boundary_complex c` THEN
     REWRITE_TAC[boundary_complex; IN_ELIM_THM] THEN SIMP_TAC[];
     ALL_TAC]) THEN
  ASM_REWRITE_TAC[] THEN
  (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC)) THEN
  ASM_MESON_TAC[SUBSET_REFL; SUBSET_TRANS]);;

let MOI_LFI_MOVE_SD = prove
 (`!(c:(real^N->bool)->bool) v p q.
     moi_lfi_move c v p q
     ==> ?t. t IN barycentric_subdivision c /\
             simplex_barycentre (FST p) IN t /\ simplex_barycentre (FST q) IN t /\
             simplex_barycentre (SND p) IN t /\ simplex_barycentre (SND q) IN t`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_LFI_MOVE_CHAIN) THEN
  EXISTS_TAC `convex hull (IMAGE simplex_barycentre
               {FST (p:(real^N->bool)#(real^N->bool)), FST q, SND p, SND q})` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC HULL_INC THEN
  REWRITE_TAC[IMAGE_CLAUSES; IN_INSERT]);;

let MOI_LFI_MOVE_TRI = prove
 (`!(c:(real^N->bool)->bool) v p q.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\ moi_lfi_move c v p q
     ==> ?t. t IN boundary_complex c /\ aff_dim t = &2 /\ v IN t /\
             simplex_barycentre (FST p) IN t /\ simplex_barycentre (FST q) IN t`,
  REPEAT GEN_TAC THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`q:(real^N->bool)#(real^N->bool)`;
                                     `p:(real^N->bool)#(real^N->bool)`] THEN
  REWRITE_TAC[FORALL_PAIR_THM; moi_lfi_move] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N->bool`; `r:real^N->bool`;
                       `a':real^N->bool`; `r':real^N->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  REWRITE_TAC[moi_lfi_flag; FST; SND] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_LFI_C_COMPLEX) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `?x:real^N->bool. x IN boundary_complex c /\ ~(x = {}) /\ a SUBSET x /\ a' SUBSET x`
    STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET_REFL; MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `x:real^N->bool`] MOI_LFI_BC_PURE) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(a:real^N->bool) IN c /\ a' IN c` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `a:real^N->bool`] MOI_LFI_BARY_RELINT) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `a':real^N->bool`] MOI_LFI_BARY_RELINT) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(a:real^N->bool = {}) /\ ~(a':real^N->bool = {})` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_LFI_FLAG_POINTS = prove
 (`!(c:(real^N->bool)->bool) b v p.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     b IN components (complex_boundary c) /\ v IN b /\ moi_lfi_flag c v p
     ==> {simplex_barycentre (FST p)} IN barycentric_subdivision c /\
         simplex_barycentre (FST p) IN b /\
         {simplex_barycentre (SND p)} IN barycentric_subdivision c /\
         ~(simplex_barycentre (SND p) IN complex_boundary c)`,
  REPEAT GEN_TAC THEN
  SPEC_TAC(`p:(real^N->bool)#(real^N->bool)`,`p:(real^N->bool)#(real^N->bool)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; moi_lfi_flag] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N->bool`; `r:real^N->bool`] THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_LFI_C_COMPLEX) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(a:real^N->bool) IN c /\ ~(a = {}) /\ ~(r:real^N->bool = {})`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `a:real^N->bool`] MOI_LFI_BARY_RELINT) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `r:real^N->bool`] MOI_LFI_BARY_RELINT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN EXISTS_TAC `{a:real^N->bool}` THEN
    ASM_SIMP_TAC[MOI_LFI_SING_CHAIN; IMAGE_CLAUSES; CONVEX_HULL_SING];
    SUBGOAL_THEN `(a:real^N->bool) SUBSET b` MP_TAC THENL
     [MATCH_MP_TAC MOI_LFI_BC_IN_COMPONENT THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ASM SET_TAC[]];
    REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN EXISTS_TAC `{r:real^N->bool}` THEN
    ASM_SIMP_TAC[MOI_LFI_SING_CHAIN; IMAGE_CLAUSES; CONVEX_HULL_SING];
    UNDISCH_TAC `~((r:real^N->bool) IN boundary_complex c)` THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `simplex_barycentre (r:real^N->bool) IN complex_boundary c` THEN
    MP_TAC(MP (ISPEC `c:(real^N->bool)->bool` MOI_FCL_CMWB_SETUP)
      (ASSUME `combinatorial_manifold_with_boundary 3 (c:(real^N->bool)->bool)`)) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM(el 3 (CONJUNCTS th))]) THEN
    REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[boundary_complex; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `t:real^N->bool` THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FSAP_RELINT_SUBSET THEN
      MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`;
                            `simplex_barycentre (r:real^N->bool)`] THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      UNDISCH_TAC `(t:real^N->bool) IN boundary_complex c` THEN
      REWRITE_TAC[boundary_complex; IN_ELIM_THM] THEN SIMP_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* 28. Homotopies of PL loops: straight lines between two PL loops (or a    *)
(* loop and a PL loop) whose pieces share convex sets, and reparametrizing  *)
(* a loop by a monotone-free PL map of [0,1] fixing the ends.               *)
(* ------------------------------------------------------------------------- *)

let MOI_LFI_PL_LAMBDA = prove
 (`!n i t. 1 <= n /\ &i / &n <= drop t /\ drop t <= &(i + 1) / &n
           ==> &0 <= &n * drop t - &i /\ &n * drop t - &i <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `&i / &n <= drop t` THEN UNDISCH_TAC `drop t <= &(i + 1) / &n` THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; GSYM REAL_OF_NUM_ADD] THEN
  REAL_ARITH_TAC);;

let MOI_LFI_PL_IN_CONVEX = prove
 (`!n (P:num->real^N) i t C.
     i < n /\ &i / &n <= drop t /\ drop t <= &(i + 1) / &n /\
     convex C /\ P i IN C /\ P (i + 1) IN C
     ==> moi_lfi_pl n P t IN C`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MOI_LFI_PL_SEG] THEN
  MP_TAC(SPECL [`n:num`; `i:num`; `t:real^1`] MOI_LFI_PL_LAMBDA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[convex] o check (fun th ->
    is_comb(concl th) && fst(dest_const(fst(strip_comb(concl th)))) = "convex")) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let MOI_LFI_PATH_PL_COMPARE = prove
 (`!n (g:real^1->real^N) Q X.
     1 <= n /\ path g /\ pathfinish g = pathstart g /\ Q n = Q 0 /\
     (!i t. i < n /\ &i / &n <= drop t /\ drop t <= &(i + 1) / &n
            ==> ?C. convex C /\ C SUBSET X /\ g t IN C /\ Q i IN C /\ Q (i + 1) IN C)
     ==> homotopic_loops X g (moi_lfi_pl n Q)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMOTOPIC_LOOPS_LINEAR THEN
  MP_TAC(SPECL [`n:num`; `Q:num->real^N`] MOI_LFI_PL_PATH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`n:num`; `t:real^1`] MOI_LFI_PL_COVER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `t IN interval[vec 0:real^1,vec 1]` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `t:real^1`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real^N->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `C:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `moi_lfi_pl n (Q:num->real^N) t IN C` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LFI_PL_IN_CONVEX THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[CONVEX_CONTAINS_SEGMENT_IMP]]);;

let MOI_LFI_PL_COMPARE = prove
 (`!n (P:num->real^N) Q X.
     1 <= n /\ P n = P 0 /\ Q n = Q 0 /\
     (!i. i < n ==> ?C. convex C /\ C SUBSET X /\ P i IN C /\ P (i + 1) IN C /\
                        Q i IN C /\ Q (i + 1) IN C)
     ==> homotopic_loops X (moi_lfi_pl n P) (moi_lfi_pl n Q)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_LFI_PATH_PL_COMPARE THEN
  MP_TAC(SPECL [`n:num`; `P:num->real^N`] MOI_LFI_PL_PATH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `C:real^N->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_LFI_PL_IN_CONVEX THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]);;

let MOI_LFI_REPARAM = prove
 (`!(p:real^1->real^N) X n Th.
     path p /\ path_image p SUBSET X /\ pathfinish p = pathstart p /\ 1 <= n /\
     Th 0 = vec 0 /\ Th n = vec 1 /\ (!i. i <= n ==> Th i IN interval[vec 0,vec 1])
     ==> homotopic_loops X p (p o moi_lfi_pl n Th)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `Th:num->real^1`] MOI_LFI_PL_PATH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_IMP_HOMOTOPIC_LOOPS THEN
  ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE] THEN CONJ_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_PATHS_REPARAMETRIZE THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `moi_lfi_pl n (Th:num->real^1)` THEN
    REWRITE_TAC[MOI_LFI_PL_CONTINUOUS; o_THM] THEN
    UNDISCH_TAC `pathstart (moi_lfi_pl n (Th:num->real^1)) = vec 0` THEN
    UNDISCH_TAC `pathfinish (moi_lfi_pl n (Th:num->real^1)) = vec 1` THEN
    REWRITE_TAC[pathstart; pathfinish] THEN REPEAT DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`n:num`; `t:real^1`] MOI_LFI_PL_COVER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `t IN interval[vec 0:real^1,vec 1]` THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC MOI_LFI_PL_IN_CONVEX THEN EXISTS_TAC `i:num` THEN
    ASM_REWRITE_TAC[CONVEX_INTERVAL] THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    REWRITE_TAC[pathstart; pathfinish] THEN
    UNDISCH_TAC `pathstart (moi_lfi_pl n (Th:num->real^1)) = vec 0` THEN
    UNDISCH_TAC `pathfinish (moi_lfi_pl n (Th:num->real^1)) = vec 1` THEN
    REWRITE_TAC[pathstart; pathfinish] THEN REPEAT DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `pathfinish (p:real^1->real^N) = pathstart p` THEN
    REWRITE_TAC[pathstart; pathfinish]]);;

(* ------------------------------------------------------------------------- *)
(* 29. (B) the collar data.  Index arithmetic for blocks of length R, then  *)
(* MOI_LFI_COLLAR_DATA: cyclic vertex sequence, ports (boundary triangles   *)
(* through consecutive vertices), blocks of flag moves of a uniform length, *)
(* the state sequence, and the homotopy p ~ PL loop of w in b.             *)
(* ------------------------------------------------------------------------- *)

let MOI_LFI_IDX_STEP = prove
 (`!R i. 2 <= R
         ==> (i MOD R + 1 < R ==> (i + 1) DIV R = i DIV R /\
                                  (i + 1) MOD R = i MOD R + 1) /\
             (i MOD R + 1 = R ==> (i + 1) DIV R = i DIV R + 1 /\ (i + 1) MOD R = 0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`i:num`; `R:num`] DIVISION) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN CONJ_TAC THEN DISCH_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `i MOD R + 1`;
      MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `i DIV R`] THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    CONJ_TAC THENL
     [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0`;
      MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `i DIV R + 1`] THEN
    ASM_ARITH_TAC]);;

let MOI_LFI_IDX_RANGE = prove
 (`!R N i. 2 <= R /\ 1 <= N /\ i < R * N
           ==> i DIV R < N /\ (i DIV R) MOD N = i DIV R /\ i MOD R < R`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`i:num`; `R:num`] DIVISION) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `i DIV R < N` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_RULE `2 <= R ==> ~(R = 0)`] THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[MOD_LT]]);;

let MOI_LFI_IDX_END = prove
 (`!R N. 2 <= R /\ 1 <= N
         ==> (R * N) DIV R = N /\ (R * N) MOD R = 0 /\ N MOD N = 0 /\
             0 DIV R = 0 /\ 0 MOD R = 0 /\ 0 MOD N = 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[MOD_REFL; MOD_0; DIV_0] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN ASM_ARITH_TAC;
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `N:num` THEN ASM_ARITH_TAC]);;

let MOI_LFI_IDX_PREV = prove
 (`!N k. 1 <= N /\ k < N
         ==> (k + N - 1) MOD N < N /\ ((k + N - 1) MOD N + 1) MOD N = k /\
             (((k + 1) MOD N) + N - 1) MOD N = k`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(SPECL [`k + N - 1`; `N:num`] DIVISION) THEN ASM_ARITH_TAC;
    ASM_CASES_TAC `k = 0` THENL
     [ASM_REWRITE_TAC[ADD_CLAUSES] THEN
      SUBGOAL_THEN `(N - 1) MOD N = N - 1` SUBST1_TAC THENL
       [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `N - 1 + 1 = N` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[MOD_REFL];
      SUBGOAL_THEN `(k + N - 1) MOD N = k - 1` SUBST1_TAC THENL
       [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `k - 1 + 1 = k` SUBST1_TAC THENL
       [ASM_ARITH_TAC; MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC]];
    ASM_CASES_TAC `k + 1 = N` THENL
     [SUBGOAL_THEN `(k + 1) MOD N = 0` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[MOD_REFL]; ALL_TAC] THEN
      REWRITE_TAC[ADD_CLAUSES] THEN
      SUBGOAL_THEN `N - 1 = k` SUBST1_TAC THENL
       [ASM_ARITH_TAC; MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC];
      SUBGOAL_THEN `(k + 1) MOD N = k + 1` SUBST1_TAC THENL
       [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1` THEN ASM_ARITH_TAC]]);;

let MOI_LFI_COLLAR_DATA = prove
 (`!(c:(real^N->bool)->bool) b (p:real^1->real^N).
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     b IN components (complex_boundary c) /\
     path p /\ path_image p SUBSET b /\ pathfinish p = pathstart p
     ==> ?m w u. 1 <= m /\ w (4 * m) = w 0 /\ u (4 * m) = u 0 /\
                 (!j. j <= 4 * m
                      ==> {w j} IN barycentric_subdivision c /\ w j IN b /\
                          {u j} IN barycentric_subdivision c /\
                          ~(u j IN complex_boundary c)) /\
                 (!j. j < 4 * m
                      ==> (?t. t IN barycentric_subdivision c /\
                               w j IN t /\ w (j + 1) IN t /\ u (j + 1) IN t) /\
                          (?t. t IN barycentric_subdivision c /\
                               w j IN t /\ u j IN t /\ u (j + 1) IN t)) /\
                 homotopic_loops b (moi_lfi_pl (4 * m) w) p`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_LFI_C_COMPLEX) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(MP (ISPEC `c:(real^N->bool)->bool` MOI_FCL_CMWB_SETUP)
    (ASSUME `combinatorial_manifold_with_boundary 3 (c:(real^N->bool)->bool)`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(b:real^N->bool) SUBSET complex_boundary c` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `b:real^N->bool`; `p:real^1->real^N`]
    MOI_LFI_VERTEX_SEQ) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (X_CHOOSE_THEN `v:num->real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `!s. s IN interval[vec 0,vec 1]
        ==> ?C. C IN boundary_complex c /\ (p:real^1->real^N) s IN C /\ C SUBSET b /\
                convex C`
    ASSUME_TAC THENL
   [X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(p:real^1->real^N) s IN UNIONS (boundary_complex c)` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `path_image (p:real^1->real^N) SUBSET b` THEN
      UNDISCH_TAC `(b:real^N->bool) SUBSET complex_boundary c` THEN
      UNDISCH_TAC `(s:real^1) IN interval[vec 0,vec 1]` THEN
      REWRITE_TAC[path_image] THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `C:real^N->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_LFI_BC_IN_COMPONENT THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `(p:real^1->real^N) s` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `path_image (p:real^1->real^N) SUBSET b` THEN
      UNDISCH_TAC `(s:real^1) IN interval[vec 0,vec 1]` THEN
      REWRITE_TAC[path_image] THEN SET_TAC[];
      UNDISCH_TAC `simplicial_complex (boundary_complex c:(real^N->bool)->bool)` THEN
      REWRITE_TAC[simplicial_complex] THEN ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?tau:num->real^N->bool.
      !k. k < N ==> tau k IN boundary_complex c /\ aff_dim (tau k) = &2 /\
                    v k IN tau k /\ v (k + 1) IN tau k /\ tau k SUBSET b`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `k:num` THEN
    REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `lift(&(k + 1) / &N)` o check (fun th ->
      is_forall(concl th) && can (find_term (fun u -> u = `C:real^N->bool`)) (concl th))) THEN
    ANTS_TAC THENL
     [MP_TAC(SPECL [`N:num`; `k:num`; `lift(&(k + 1) / &N)`] MOI_LFI_PARAM_DIST) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      ASM_REWRITE_TAC[LIFT_DROP; REAL_LE_REFL] THEN
      SUBGOAL_THEN `&0 < &N` ASSUME_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_OF_NUM_LE] THEN ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `C:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(v:num->real^N) k IN C /\ v (k + 1) IN C` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term (fun u -> u = `s:real^1`)) (concl th))) THEN
        EXISTS_TAC `lift(&(k + 1) / &N)` THEN ASM_REWRITE_TAC[LIFT_DROP; REAL_LE_REFL] THEN
        SUBGOAL_THEN `&0 < &N` ASSUME_TAC THENL
         [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_OF_NUM_LE] THEN ARITH_TAC;
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term (fun u -> u = `v (k + 1):real^N`)) (concl th))) THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `C:real^N->bool`] MOI_LFI_BC_PURE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ASM SET_TAC[]; ASM SET_TAC[];
      MATCH_MP_TAC MOI_LFI_BC_IN_COMPONENT THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `(v:num->real^N) k` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?Tc:num->real^N->bool.
      !k. k < N ==> Tc k IN c /\ ~(Tc k IN boundary_complex c) /\ tau k SUBSET Tc k`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `k:num` THEN
    REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `(tau:num->real^N->bool) k`]
      MOI_LFI_TRI_COFACE) THEN
    ASM_SIMP_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!j. j < N ==> (v:num->real^N) (j + 1) = v ((j + 1) MOD N)`
    ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN ASM_CASES_TAC `j + 1 < N` THENL
     [ASM_SIMP_TAC[MOD_LT];
      SUBGOAL_THEN `j + 1 = N` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[MOD_REFL]];
    ALL_TAC] THEN
  ABBREV_TAC
   `port = \k. (tau:num->real^N->bool) (k MOD N), (Tc:num->real^N->bool) (k MOD N)` THEN
  SUBGOAL_THEN
   `!j. j < N ==> port j = ((tau:num->real^N->bool) j,(Tc:num->real^N->bool) j)`
    ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN EXPAND_TAC "port" THEN
    ASM_SIMP_TAC[MOD_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. k < N
        ==> moi_lfi_flag c ((v:num->real^N) k)
              ((port:num->(real^N->bool)#(real^N->bool)) ((k + N - 1) MOD N)) /\
            moi_lfi_flag c (v k) (port k) /\
            moi_lfi_move c (v k) (port k) (port k)`
    ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`N:num`; `k:num`] MOI_LFI_IDX_PREV) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    ABBREV_TAC `j = (k + N - 1) MOD N` THEN
    SUBGOAL_THEN `(v:num->real^N) k = v (j + 1)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[moi_lfi_move; moi_lfi_flag; FST; SND; SUBSET_REFL] THEN
    SUBGOAL_THEN `!i x. i < N /\ x IN (tau:num->real^N->bool) i
                        ==> ~(tau i = {x:real^N})`
      ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun u -> u = `aff_dim((tau:num->real^N->bool) k)`)) (concl th))) THEN
      ASM_REWRITE_TAC[AFF_DIM_SING] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
        FIRST_ASSUM(fun th -> if is_forall(concl th) &&
        can (find_term (fun u -> u = `aff_dim((tau:num->real^N->bool) k)`)) (concl th)
      then MP_TAC(CONJ (MP (SPEC `j:num` th) (ASSUME `j < (N:num)`))
                       (MP (SPEC `k:num` th) (ASSUME `k < (N:num)`)))
      else NO_TAC) THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) &&
        can (find_term (fun u -> u = `(Tc:num->real^N->bool) k IN c`)) (concl th)
      then MP_TAC(CONJ (MP (SPEC `j:num` th) (ASSUME `j < (N:num)`))
                       (MP (SPEC `k:num` th) (ASSUME `k < (N:num)`)))
      else NO_TAC) THEN
    REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `~((tau:num->real^N->bool) j = {v (k:num)}) /\ ~(tau k = {v k})`
      STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. k < N
        ==> ?n0. !n. n0 <= n
                     ==> ?f. f 0 = (port:num->(real^N->bool)#(real^N->bool))
                                     ((k + N - 1) MOD N) /\
                             f n = port k /\
                             !i. i < n ==> moi_lfi_move c ((v:num->real^N) k)
                                                         (f i) (f (i + 1))`
    MP_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC(ISPECL
     [`moi_lfi_move c ((v:num->real^N) k)`;
      `(port:num->(real^N->bool)#(real^N->bool)) ((k + N - 1) MOD N)`;
      `(port:num->(real^N->bool)#(real^N->bool)) k`] MOI_LFI_CONN_EXACT) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun u -> is_const u && fst(dest_const u) = "moi_lfi_move"))
        (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_LFI_FLAG_CONN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n0:num->num`
    (X_CHOOSE_TAC `ff:num->num->num->(real^N->bool)#(real^N->bool)`) o
    REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  SUBGOAL_THEN `?R0. !k. k < N ==> (n0:num->num) k <= R0` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `IMAGE (n0:num->num) {k | k < N}` num_FINITE) THEN
    SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT; FORALL_IN_IMAGE; IN_ELIM_THM];
    ALL_TAC] THEN
  ABBREV_TAC `R = 4 * (R0 + 2)` THEN
  SUBGOAL_THEN `2 <= R /\ R0 + 1 <= R - 1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `?G:num->num->(real^N->bool)#(real^N->bool).
      !k. k < N
          ==> G k 0 = port ((k + N - 1) MOD N) /\ G k (R - 1) = port k /\
              !i. i < R - 1 ==> moi_lfi_move c ((v:num->real^N) k) (G k i) (G k (i + 1))`
    STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `\k:num. (ff:num->num->num->(real^N->bool)#(real^N->bool)) k (R - 1)` THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun u -> u = `n0:num->num`)) (concl th) &&
      can (find_term (fun u -> is_const u && fst(dest_const u) = "moi_lfi_move"))
        (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `R - 1`) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `R0:num` THEN ASM_SIMP_TAC[] THEN
      ASM_ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC
   `S = \i. (G:num->num->(real^N->bool)#(real^N->bool))
              ((i DIV R) MOD N) (MIN (i MOD R) (R - 1))` THEN
  SUBGOAL_THEN
   `!i. i < R * N
        ==> moi_lfi_move c ((v:num->real^N) (i DIV R))
              ((S:num->(real^N->bool)#(real^N->bool)) i) (S (i + 1)) /\
            (i MOD R + 1 = R ==> S i = port (i DIV R) /\ S (i + 1) = port (i DIV R))`
    ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`R:num`; `N:num`; `i:num`] MOI_LFI_IDX_RANGE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`R:num`; `i:num`] MOI_LFI_IDX_STEP) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) &&
        can (find_term (fun u -> u = `G:num->num->(real^N->bool)#(real^N->bool)`))
          (concl th) &&
        can (find_term (fun u -> u = `R - 1`)) (concl th)
      then ASSUME_TAC(MP (SPEC `i DIV R` th) (ASSUME `i DIV R < N`)) else NO_TAC) THEN
    ASM_CASES_TAC `i MOD R + 1 < R` THENL
     [SUBGOAL_THEN `~(i MOD R + 1 = R)` (fun th -> REWRITE_TAC[th]) THENL
       [UNDISCH_TAC `i MOD R + 1 < R` THEN ARITH_TAC; ALL_TAC] THEN
      EXPAND_TAC "S" THEN REWRITE_TAC[] THEN ASM_SIMP_TAC[] THEN
      SUBGOAL_THEN `MIN (i MOD R) (R - 1) = i MOD R /\
                    MIN (i MOD R + 1) (R - 1) = i MOD R + 1 /\ i MOD R < R - 1`
        STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `i MOD R + 1 < R` THEN ARITH_TAC; ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `i MOD R + 1 = R` (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `~(i MOD R + 1 < R)` THEN UNDISCH_TAC `i MOD R < R` THEN ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`N:num`; `i DIV R`] MOI_LFI_IDX_PREV) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(i DIV R + 1) MOD N < N` ASSUME_TAC THENL
     [REWRITE_TAC[MOD_LT_EQ] THEN UNDISCH_TAC `1 <= N` THEN ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) &&
        can (find_term (fun u -> u = `G:num->num->(real^N->bool)#(real^N->bool)`))
          (concl th) &&
        can (find_term (fun u -> u = `R - 1`)) (concl th)
      then ASSUME_TAC(MP (SPEC `(i DIV R + 1) MOD N` th)
                         (ASSUME `(i DIV R + 1) MOD N < N`)) else NO_TAC) THEN
    SUBGOAL_THEN
     `(S:num->(real^N->bool)#(real^N->bool)) i = port (i DIV R) /\
      S (i + 1) = port (i DIV R)`
      STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "S" THEN REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[ARITH_RULE `MIN (R - 1) (R - 1) = R - 1`;
                   ARITH_RULE `MIN 0 (R - 1) = 0`] THEN
      SUBGOAL_THEN `i MOD R = R - 1` SUBST1_TAC THENL
       [UNDISCH_TAC `i MOD R + 1 = R` THEN ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[ARITH_RULE `MIN (R - 1) (R - 1) = R - 1`];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i DIV R` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun u -> is_const u && fst(dest_const u) = "moi_lfi_flag"))
        (concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(S:num->(real^N->bool)#(real^N->bool)) (R * N) = S 0` ASSUME_TAC THENL
   [MP_TAC(SPECL [`R:num`; `N:num`] MOI_LFI_IDX_END) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN EXPAND_TAC "S" THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. j <= R * N
        ==> ?k. moi_lfi_flag c ((v:num->real^N) k)
                  ((S:num->(real^N->bool)#(real^N->bool)) j)`
    ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?j'. j' < R * N /\ (S:num->(real^N->bool)#(real^N->bool)) j = S j'`
      STRIP_ASSUME_TAC THENL
     [ASM_CASES_TAC `j < R * (N:num)` THENL
       [EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[];
        EXISTS_TAC `0` THEN
        SUBGOAL_THEN `j = R * (N:num)` SUBST1_TAC THENL
         [UNDISCH_TAC `~(j < R * (N:num))` THEN UNDISCH_TAC `j <= R * (N:num)` THEN ARITH_TAC;
          ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `2 <= R` THEN UNDISCH_TAC `1 <= N` THEN
          REWRITE_TAC[LT_MULT] THEN ARITH_TAC]];
      ALL_TAC] THEN
    EXISTS_TAC `j' DIV R` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j':num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun u -> u = `S:num->(real^N->bool)#(real^N->bool)`)) (concl th) &&
      can (find_term (fun u -> is_const u && fst(dest_const u) = "moi_lfi_move"))
        (concl th))) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[moi_lfi_move];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`(R0 + 2) * N`;
    `\i. simplex_barycentre (FST ((S:num->(real^N->bool)#(real^N->bool)) i))`;
    `\i. simplex_barycentre (SND ((S:num->(real^N->bool)#(real^N->bool)) i))`] THEN
  SUBGOAL_THEN `4 * (R0 + 2) * N = R * N` (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "R" THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [UNDISCH_TAC `1 <= N` THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun u -> is_const u && fst(dest_const u) = "moi_lfi_flag"))
        (concl th) &&
      can (find_term (fun u -> u = `S:num->(real^N->bool)#(real^N->bool)`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
    MATCH_MP_TAC MOI_LFI_FLAG_POINTS THEN EXISTS_TAC `(v:num->real^N) k` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun u -> u = `S:num->(real^N->bool)#(real^N->bool)`)) (concl th) &&
      can (find_term (fun u -> is_const u && fst(dest_const u) = "moi_lfi_move"))
        (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP MOI_LFI_MOVE_SD o CONJUNCT1) THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    CONJ_TAC THEN EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `w = \i. simplex_barycentre (FST ((S:num->(real^N->bool)#(real^N->bool)) i))` THEN
  ABBREV_TAC `Q = \i. (v:num->real^N) (i DIV R)` THEN
  ABBREV_TAC
   `Th = \i. lift((&(i DIV R) + (if i MOD R = 0 then &0 else &1)) / &N)` THEN
  MP_TAC(SPECL [`R:num`; `N:num`] MOI_LFI_IDX_END) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `1 <= R * N /\ &0 < &N` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN
    UNDISCH_TAC `2 <= R` THEN UNDISCH_TAC `1 <= N` THEN
    REWRITE_TAC[ARITH_RULE `1 <= R * N <=> 0 < R * N`; LT_MULT] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i < R * N
        ==> (Th:num->real^1) (i + 1) = lift(&(i DIV R + 1) / &N) /\
            &(i DIV R) / &N <= drop(Th i) /\ drop(Th i) <= &(i DIV R + 1) / &N /\
            (i MOD R + 1 = R ==> Th i = lift(&(i DIV R + 1) / &N)) /\
            (Q:num->real^N) i = v (i DIV R) /\
            (i MOD R + 1 < R ==> Q (i + 1) = v (i DIV R)) /\
            (i MOD R + 1 = R ==> Q (i + 1) = v (i DIV R + 1))`
    ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`R:num`; `i:num`] MOI_LFI_IDX_STEP) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN EXPAND_TAC "Th" THEN EXPAND_TAC "Q" THEN REWRITE_TAC[LIFT_DROP] THEN
    ASM_CASES_TAC `i MOD R + 1 < R` THENL
     [SUBGOAL_THEN `~(i MOD R + 1 = R) /\ ~(i MOD R + 1 = 0)` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `i MOD R + 1 < R` THEN ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[GSYM REAL_OF_NUM_ADD] THEN
      COND_CASES_TAC THEN
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_ADD_RID; REAL_LE_REFL] THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `i MOD R + 1 = R /\ ~(i MOD R = 0)` STRIP_ASSUME_TAC THENL
       [MP_TAC(SPECL [`i:num`; `R:num`] DIVISION) THEN
        ANTS_TAC THENL [UNDISCH_TAC `2 <= R` THEN ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `~(i MOD R + 1 < R)` THEN UNDISCH_TAC `2 <= R` THEN
        ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[GSYM REAL_OF_NUM_ADD; REAL_ADD_RID; REAL_LE_REFL] THEN
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(Th:num->real^1) 0 = vec 0 /\ Th (R * N) = vec 1 /\
    (!i. i <= R * N ==> Th i IN interval[vec 0,vec 1])`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Th" THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_ADD_RID; real_div; REAL_MUL_LZERO; LIFT_NUM;
                 REAL_MUL_RINV; REAL_LT_IMP_NZ] THEN
    REWRITE_TAC[GSYM real_div] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_LDIV_EQ; REAL_MUL_LID; REAL_LT_IMP_LE] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_POS] THEN
      COND_CASES_TAC THEN REWRITE_TAC[REAL_POS];
      ALL_TAC] THEN
    ASM_CASES_TAC `i < R * (N:num)` THENL
     [MP_TAC(SPECL [`R:num`; `N:num`; `i:num`] MOI_LFI_IDX_RANGE) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&(i DIV R) + &1` THEN CONJ_TAC THENL
       [COND_CASES_TAC THEN REAL_ARITH_TAC;
        REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
        UNDISCH_TAC `i DIV R < N` THEN ARITH_TAC];
      SUBGOAL_THEN `i = R * (N:num)` SUBST1_TAC THENL
       [UNDISCH_TAC `~(i < R * (N:num))` THEN UNDISCH_TAC `i <= R * (N:num)` THEN
        ARITH_TAC;
        ASM_REWRITE_TAC[REAL_ADD_RID; REAL_LE_REFL]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `path (moi_lfi_pl (R * N) (Th:num->real^1)) /\
    path_image (moi_lfi_pl (R * N) Th) SUBSET interval[vec 0,vec 1] /\
    pathstart (moi_lfi_pl (R * N) Th) = vec 0 /\
    pathfinish (moi_lfi_pl (R * N) Th) = vec 1`
    STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`R * (N:num)`; `Th:num->real^1`] MOI_LFI_PL_PATH) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_LFI_PL_IMAGE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MINIMAL THEN
    REWRITE_TAC[CONVEX_INTERVAL; INSERT_SUBSET; EMPTY_SUBSET] THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `i < R * (N:num)` THEN ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[HOMOTOPIC_LOOPS_SYM] THEN
  MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
  EXISTS_TAC `(p:real^1->real^N) o moi_lfi_pl (R * N) Th` THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_LFI_REPARAM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
  EXISTS_TAC `moi_lfi_pl (R * N) (Q:num->real^N)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_LFI_PATH_PL_COMPARE THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN ASM_MESON_TAC[path];
      REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `pathfinish (p:real^1->real^N) = pathstart p` THEN
      REWRITE_TAC[pathstart; pathfinish];
      EXPAND_TAC "Q" THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `t:real^1`] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`R:num`; `N:num`; `i:num`] MOI_LFI_IDX_RANGE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(MP (SPEC `i:num` (ASSUME
     `!i. i < R * N
          ==> (Th:num->real^1) (i + 1) = lift(&(i DIV R + 1) / &N) /\
              &(i DIV R) / &N <= drop(Th i) /\ drop(Th i) <= &(i DIV R + 1) / &N /\
              (i MOD R + 1 = R ==> Th i = lift(&(i DIV R + 1) / &N)) /\
              (Q:num->real^N) i = v (i DIV R) /\
              (i MOD R + 1 < R ==> Q (i + 1) = v (i DIV R)) /\
              (i MOD R + 1 = R ==> Q (i + 1) = v (i DIV R + 1))`))
     (ASSUME `i < R * (N:num)`)) THEN
    STRIP_TAC THEN
    MP_TAC(SPECL [`R * (N:num)`; `i:num`; `t:real^1`] MOI_LFI_PARAM_DIST) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `moi_lfi_pl (R * N) (Th:num->real^1) t IN
      interval[lift(&(i DIV R) / &N),lift(&(i DIV R + 1) / &N)]`
      ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_LFI_PL_IN_CONVEX THEN EXISTS_TAC `i:num` THEN
      ASM_REWRITE_TAC[CONVEX_INTERVAL; IN_INTERVAL_1; LIFT_DROP; REAL_LE_REFL] THEN
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_OF_NUM_LE] THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `moi_lfi_pl (R * N) (Th:num->real^1) t IN interval[vec 0,vec 1]`
      ASSUME_TAC THENL
     [UNDISCH_TAC `path_image (moi_lfi_pl (R * N) (Th:num->real^1)) SUBSET
                   interval[vec 0,vec 1]` THEN
      REWRITE_TAC[path_image; SUBSET; FORALL_IN_IMAGE] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) &&
        can (find_term (fun u -> u = `C:real^N->bool`)) (concl th)
      then MP_TAC(MP (SPEC `moi_lfi_pl (R * N) (Th:num->real^1) t` th)
                     (ASSUME `moi_lfi_pl (R * N) (Th:num->real^1) t IN
                              interval[vec 0,vec 1]`))
      else NO_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `C:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `C:real^N->bool` THEN ASM_REWRITE_TAC[o_THM] THEN
    UNDISCH_TAC `moi_lfi_pl (R * N) (Th:num->real^1) t IN
                 interval[lift(&(i DIV R) / &N),lift(&(i DIV R + 1) / &N)]` THEN
    REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(v:num->real^N) (i DIV R) IN C` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun u -> u = `s:real^1`)) (concl th) &&
        can (find_term (fun u -> u = `v (k:num):real^N`)) (concl th))) THEN
      EXISTS_TAC `moi_lfi_pl (R * N) (Th:num->real^1) t` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `i MOD R + 1 < R` THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `i MOD R + 1 = R` ASSUME_TAC THENL
     [UNDISCH_TAC `~(i MOD R + 1 < R)` THEN UNDISCH_TAC `i MOD R < R` THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(Q:num->real^N) (i + 1) = v (i DIV R + 1)` SUBST1_TAC THENL
     [MATCH_MP_TAC(ASSUME
       `i MOD R + 1 = R ==> (Q:num->real^N) (i + 1) = v (i DIV R + 1)`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun u -> u = `v (k + 1):real^N`)) (concl th) &&
      not(can (find_term (fun u -> u = `s:real^1`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `moi_lfi_pl (R * N) (Th:num->real^1) t = lift(&(i DIV R + 1) / &N)`
      (fun th -> ASM_MESON_TAC[th]) THEN
    MATCH_MP_TAC(SET_RULE `!x a:real^1. x IN {a} ==> x = a`) THEN
    MATCH_MP_TAC MOI_LFI_PL_IN_CONVEX THEN EXISTS_TAC `i:num` THEN
    ASM_SIMP_TAC[CONVEX_SING; IN_SING];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_LFI_PL_COMPARE THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [EXPAND_TAC "Q" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [EXPAND_TAC "w" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`R:num`; `N:num`; `i:num`] MOI_LFI_IDX_RANGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(MP (SPEC `i:num` (ASSUME
   `!i. i < R * N
        ==> (Th:num->real^1) (i + 1) = lift(&(i DIV R + 1) / &N) /\
            &(i DIV R) / &N <= drop(Th i) /\ drop(Th i) <= &(i DIV R + 1) / &N /\
            (i MOD R + 1 = R ==> Th i = lift(&(i DIV R + 1) / &N)) /\
            (Q:num->real^N) i = v (i DIV R) /\
            (i MOD R + 1 < R ==> Q (i + 1) = v (i DIV R)) /\
            (i MOD R + 1 = R ==> Q (i + 1) = v (i DIV R + 1))`))
   (ASSUME `i < R * (N:num)`)) THEN
  STRIP_TAC THEN
  FIRST_ASSUM(fun th -> if is_forall(concl th) &&
      can (find_term (fun u -> u = `S:num->(real^N->bool)#(real^N->bool)`)) (concl th) &&
      can (find_term (fun u -> is_const u && fst(dest_const u) = "moi_lfi_move"))
        (concl th)
    then MP_TAC(MP (SPEC `i:num` th) (ASSUME `i < R * (N:num)`)) else NO_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  EXPAND_TAC "w" THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `i MOD R + 1 < R` THENL
   [SUBGOAL_THEN `(Q:num->real^N) (i + 1) = v (i DIV R)` SUBST1_TAC THENL
     [MATCH_MP_TAC(ASSUME
       `i MOD R + 1 < R ==> (Q:num->real^N) (i + 1) = v (i DIV R)`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `(v:num->real^N) (i DIV R)`;
                   `(S:num->(real^N->bool)#(real^N->bool)) i`;
                   `(S:num->(real^N->bool)#(real^N->bool)) (i + 1)`] MOI_LFI_MOVE_TRI) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t':real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t':real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `simplicial_complex (boundary_complex c:(real^N->bool)->bool)` THEN
      REWRITE_TAC[simplicial_complex] THEN ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
      MATCH_MP_TAC MOI_LFI_BC_IN_COMPONENT THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `(v:num->real^N) (i DIV R)` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `i MOD R + 1 = R` ASSUME_TAC THENL
   [UNDISCH_TAC `~(i MOD R + 1 < R)` THEN UNDISCH_TAC `i MOD R < R` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(Q:num->real^N) (i + 1) = v (i DIV R + 1)` SUBST1_TAC THENL
   [MATCH_MP_TAC(ASSUME
     `i MOD R + 1 = R ==> (Q:num->real^N) (i + 1) = v (i DIV R + 1)`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(S:num->(real^N->bool)#(real^N->bool)) i = port (i DIV R) /\
    S (i + 1) = port (i DIV R)`
    STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(port:num->(real^N->bool)#(real^N->bool)) (i DIV R) =
    ((tau:num->real^N->bool) (i DIV R),(Tc:num->real^N->bool) (i DIV R))`
    SUBST1_TAC THENL
   [FIRST_ASSUM(fun th -> if is_forall(concl th) &&
        can (find_term (fun u -> u = `port:num->(real^N->bool)#(real^N->bool)`))
          (concl th) &&
        not(can (find_term (fun u -> is_const u &&
          fst(dest_const u) = "moi_lfi_flag")) (concl th))
      then MATCH_MP_TAC th else NO_TAC) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if is_forall(concl th) &&
      can (find_term (fun u -> u = `aff_dim((tau:num->real^N->bool) k)`)) (concl th)
    then MP_TAC(MP (SPEC `i DIV R` th) (ASSUME `i DIV R < N`)) else NO_TAC) THEN
  STRIP_TAC THEN
  EXISTS_TAC `(tau:num->real^N->bool) (i DIV R)` THEN ASM_REWRITE_TAC[FST] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `simplicial_complex (boundary_complex c:(real^N->bool)->bool)` THEN
    REWRITE_TAC[simplicial_complex] THEN ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `(tau:num->real^N->bool) (i DIV R)`]
    MOI_LFI_BARY_RELINT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `(v:num->real^N) (i DIV R)` THEN ASM_REWRITE_TAC[];
    SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 30. The main theorem LT_FILL : |- MOI_LT_FILL (collar data + assembly).   *)
(* ------------------------------------------------------------------------- *)

let LT_FILL = prove
 (MOI_LT_FILL,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `b:real^N->bool`; `p:real^1->real^N`]
    MOI_LFI_COLLAR_DATA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` (X_CHOOSE_THEN `w:num->real^N`
    (X_CHOOSE_THEN `u:num->real^N` STRIP_ASSUME_TAC))) THEN
  MATCH_MP_TAC MOI_LFI_FROM_DATA THEN
  MAP_EVERY EXISTS_TAC [`m:num`; `w:num->real^N`; `u:num->real^N`] THEN
  ASM_REWRITE_TAC[]);;


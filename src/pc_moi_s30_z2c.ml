(* ========================================================================= *)
(* pc_moi_s30_z2c: Z/2 counts for surfaces, replacing the classification of *)
(* surfaces on Moise pp.216-217.  Main theorems (statements of              *)
(* pc_moi_s3032_stmt.ml, with the character counts MOI_S33_CHAR_COUNT(_BD)  *)
(* of pc_moi_s33_stmt.ml as antecedents):                                   *)
(*   Z2_SC_CLOSED   = MOI_S30_Z2_SC_CLOSED   (simply connected: chi 2)      *)
(*   Z2_SC_BOUNDARY = MOI_S30_Z2_SC_BOUNDARY (simply connected: chi 1)      *)
(*   Z2_TORUS_BOUND = MOI_S30_Z2_TORUS_BOUND (pi_1-injective into the torus: *)
(*                    chi >= 0)                                              *)
(* Characters vanish on null-homotopic loops, which gives the simply        *)
(* connected cases; for Z2_TORUS_BOUND the characters are determined by the *)
(* winding pairs of loops in the torus S^1 x S^1, two loops determine every *)
(* character, so there are at most four.                                    *)
(* ========================================================================= *)

needs "src/pc_moi_s3032_stmt.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Part 1: characters vanish on null-homotopic loops; the simply connected  *)
(* cases Z2_SC_CLOSED and Z2_SC_BOUNDARY.                                   *)
(* ========================================================================= *)

let MOI_S3Z2_CHAR_CONST = prove
 (`!(s:real^N->bool) phi a.
     moi_s33_char s phi /\ a IN s ==> ~phi(linepath(a,a))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s33_char] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`linepath(a:real^N,a)`; `linepath(a:real^N,a)`]) THEN
  REWRITE_TAC[PATH_LINEPATH; PATH_IMAGE_LINEPATH; PATHSTART_LINEPATH;
              PATHFINISH_LINEPATH; SEGMENT_REFL; SING_SUBSET] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `linepath(a:real^N,a) ++ linepath(a,a) = linepath(a,a)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; joinpaths; LINEPATH_REFL; COND_ID]; ALL_TAC] THEN
  CONV_TAC TAUT);;

let MOI_S3Z2_CHAR_NULL = prove
 (`!(s:real^N->bool) phi p.
     moi_s33_char s phi /\
     path p /\ path_image p SUBSET s /\ pathfinish p = pathstart p /\
     homotopic_loops s p (linepath(pathstart p,pathstart p))
     ==> ~phi p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(phi:(real^1->real^N)->bool) p <=> phi(linepath(pathstart p,pathstart p))`
  SUBST1_TAC THENL
   [UNDISCH_TAC `moi_s33_char s (phi:(real^1->real^N)->bool)` THEN
    REWRITE_TAC[moi_s33_char] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S3Z2_CHAR_CONST THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `path_image (p:real^1->real^N) SUBSET s` THEN
    MP_TAC(ISPEC `p:real^1->real^N` PATHSTART_IN_PATH_IMAGE) THEN SET_TAC[]]);;

let MOI_S3Z2_CHAR_FALSE = prove
 (`!s:real^N->bool. moi_s33_char s (\p. F)`,
  REWRITE_TAC[moi_s33_char]);;

(* In a simply connected set the only character is the trivial one. *)

let MOI_S3Z2_CHARS_TRIVIAL = prove
 (`!s:real^N->bool.
     (!p. path p /\ pathfinish p = pathstart p /\ path_image p SUBSET s
          ==> homotopic_loops s p (linepath(pathstart p,pathstart p)))
     ==> {phi | moi_s33_char s phi} = {\p:real^1->real^N. F}`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  X_GEN_TAC `phi:(real^1->real^N)->bool` THEN REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `p:real^1->real^N` THEN
    REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `path (p:real^1->real^N) /\ path_image p SUBSET s /\
                  pathfinish p = pathstart p` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[moi_s33_char]; ALL_TAC] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `phi:(real^1->real^N)->bool`; `p:real^1->real^N`]
      MOI_S3Z2_CHAR_NULL) THEN
    ASM_SIMP_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MOI_S3Z2_CHAR_FALSE]]);;

let MOI_S3Z2_EXP_EQ_1 = prove
 (`!n. 2 EXP n = 1 <=> n = 0`,
  REWRITE_TAC[EXP_EQ_1; ARITH_EQ]);;

let Z2_SC_CLOSED = prove
 (MOI_S30_Z2_SC_CLOSED,
  DISCH_TAC THEN X_GEN_TAC `m:(real^N->bool)->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:(real^N->bool)->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `UNIONS m:real^N->bool` MOI_S3Z2_CHARS_TRIVIAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  UNDISCH_TAC `{\p:real^1->real^N. F} HAS_SIZE 2 EXP n` THEN
  REWRITE_TAC[HAS_SIZE; FINITE_SING; CARD_SING] THEN
  ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN REWRITE_TAC[MOI_S3Z2_EXP_EQ_1] THEN
  DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC);;

let Z2_SC_BOUNDARY = prove
 (MOI_S30_Z2_SC_BOUNDARY,
  DISCH_TAC THEN X_GEN_TAC `c:(real^N->bool)->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:(real^N->bool)->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `UNIONS c:real^N->bool` MOI_S3Z2_CHARS_TRIVIAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  UNDISCH_TAC `{\p:real^1->real^N. F} HAS_SIZE 2 EXP n` THEN
  REWRITE_TAC[HAS_SIZE; FINITE_SING; CARD_SING] THEN
  ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN REWRITE_TAC[MOI_S3Z2_EXP_EQ_1] THEN
  DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Part 2: winding pairs of loops in the torus moi_s30_tt = S^1 x S^1      *)
(* (complex = real^2): integer valued, additive, negated by reversal, and a *)
(* loop with winding pair (0,0) is null-homotopic in the torus.            *)
(* ========================================================================= *)

let moi_s3z2_w1 = new_definition
 `moi_s3z2_w1 (g:real^1->real^(2,2)finite_sum) =
    Re(winding_number(fstcart o g,Cx(&0)))`;;

let moi_s3z2_w2 = new_definition
 `moi_s3z2_w2 (g:real^1->real^(2,2)finite_sum) =
    Re(winding_number(sndcart o g,Cx(&0)))`;;

let MOI_S3Z2_TT_IN = prove
 (`!z:real^(2,2)finite_sum.
     z IN moi_s30_tt <=>
     fstcart z IN sphere(vec 0,&1) /\ sndcart z IN sphere(vec 0,&1)`,
  GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM PASTECART_FST_SND] THEN
  REWRITE_TAC[moi_s30_tt; PASTECART_IN_PCROSS]);;

(* The two components of a loop in the torus. *)

let MOI_S3Z2_COMPONENTS = prove
 (`!g:real^1->real^(2,2)finite_sum.
     path g /\ path_image g SUBSET moi_s30_tt
     ==> path (fstcart o g) /\ path_image (fstcart o g) SUBSET sphere(vec 0,&1) /\
         ~(Cx(&0) IN path_image (fstcart o g)) /\
         path (sndcart o g) /\ path_image (sndcart o g) SUBSET sphere(vec 0,&1) /\
         ~(Cx(&0) IN path_image (sndcart o g))`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `path_image (fstcart o (g:real^1->real^(2,2)finite_sum)) SUBSET sphere(vec 0,&1) /\
    path_image (sndcart o (g:real^1->real^(2,2)finite_sum)) SUBSET sphere(vec 0,&1)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[PATH_IMAGE_COMPOSE; SUBSET; FORALL_IN_IMAGE] THEN
    UNDISCH_TAC `path_image (g:real^1->real^(2,2)finite_sum) SUBSET moi_s30_tt` THEN
    REWRITE_TAC[SUBSET; MOI_S3Z2_TT_IN] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART];
    UNDISCH_TAC `path_image (fstcart o (g:real^1->real^(2,2)finite_sum)) SUBSET sphere(vec 0,&1)` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `Cx(&0)`) THEN
    REWRITE_TAC[IN_SPHERE_0; COMPLEX_NORM_CX; REAL_ABS_NUM; REAL_OF_NUM_EQ; ARITH_EQ];
    MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART];
    UNDISCH_TAC `path_image (sndcart o (g:real^1->real^(2,2)finite_sum)) SUBSET sphere(vec 0,&1)` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `Cx(&0)`) THEN
    REWRITE_TAC[IN_SPHERE_0; COMPLEX_NORM_CX; REAL_ABS_NUM; REAL_OF_NUM_EQ; ARITH_EQ]]);;

let MOI_S3Z2_W_INTEGER = prove
 (`!g:real^1->real^(2,2)finite_sum.
     path g /\ path_image g SUBSET moi_s30_tt /\ pathfinish g = pathstart g
     ==> integer (moi_s3z2_w1 g) /\ integer (moi_s3z2_w2 g) /\
         winding_number(fstcart o g,Cx(&0)) = Cx(moi_s3z2_w1 g) /\
         winding_number(sndcart o g,Cx(&0)) = Cx(moi_s3z2_w2 g)`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `g:real^1->real^(2,2)finite_sum` MOI_S3Z2_COMPONENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`fstcart o (g:real^1->real^(2,2)finite_sum)`; `Cx(&0)`]
    INTEGER_WINDING_NUMBER) THEN
  MP_TAC(ISPECL [`sndcart o (g:real^1->real^(2,2)finite_sum)`; `Cx(&0)`]
    INTEGER_WINDING_NUMBER) THEN
  ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; complex_integer] THEN
  REWRITE_TAC[moi_s3z2_w1; moi_s3z2_w2] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[COMPLEX_EQ; RE_CX; IM_CX] THEN ASM_REWRITE_TAC[]);;

let MOI_S3Z2_W_JOIN = prove
 (`!g h:real^1->real^(2,2)finite_sum.
     path g /\ path_image g SUBSET moi_s30_tt /\
     path h /\ path_image h SUBSET moi_s30_tt /\ pathfinish g = pathstart h
     ==> moi_s3z2_w1 (g ++ h) = moi_s3z2_w1 g + moi_s3z2_w1 h /\
         moi_s3z2_w2 (g ++ h) = moi_s3z2_w2 g + moi_s3z2_w2 h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `g:real^1->real^(2,2)finite_sum` MOI_S3Z2_COMPONENTS) THEN
  MP_TAC(ISPEC `h:real^1->real^(2,2)finite_sum` MOI_S3Z2_COMPONENTS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[moi_s3z2_w1; moi_s3z2_w2; PATH_COMPOSE_JOIN] THEN
  ASM_SIMP_TAC[WINDING_NUMBER_JOIN; PATHSTART_COMPOSE; PATHFINISH_COMPOSE; RE_ADD]);;

let MOI_S3Z2_W_REVERSE = prove
 (`!g:real^1->real^(2,2)finite_sum.
     path g /\ path_image g SUBSET moi_s30_tt
     ==> moi_s3z2_w1 (reversepath g) = --(moi_s3z2_w1 g) /\
         moi_s3z2_w2 (reversepath g) = --(moi_s3z2_w2 g)`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `g:real^1->real^(2,2)finite_sum` MOI_S3Z2_COMPONENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[moi_s3z2_w1; moi_s3z2_w2; PATH_COMPOSE_REVERSEPATH] THEN
  ASM_SIMP_TAC[WINDING_NUMBER_REVERSEPATH; RE_NEG]);;

(* A loop in the circle with winding number 0 is null-homotopic in it. *)

let MOI_S3Z2_CIRCLE_NULL = prove
 (`!p:real^1->complex.
     path p /\ path_image p SUBSET sphere(vec 0,&1) /\ pathfinish p = pathstart p /\
     winding_number(p,Cx(&0)) = Cx(&0)
     ==> ?b. homotopic_loops (sphere(vec 0,&1)) p (\t. b)`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(Cx(&0) IN path_image (p:real^1->complex))` ASSUME_TAC THENL
   [UNDISCH_TAC `path_image (p:real^1->complex) SUBSET sphere(vec 0,&1)` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `Cx(&0)`) THEN
    REWRITE_TAC[IN_SPHERE_0; COMPLEX_NORM_CX; REAL_ABS_NUM; REAL_OF_NUM_EQ; ARITH_EQ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:real^1->complex`; `Cx(&0)`] WINDING_NUMBER_HOMOTOPIC_LOOPS_NULL_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `a:complex`) THEN
  ABBREV_TAC `r = \w:complex. inv(norm w) % w` THEN
  SUBGOAL_THEN `(r:complex->complex) continuous_on ((:complex) DELETE Cx(&0)) /\
                IMAGE r ((:complex) DELETE Cx(&0)) SUBSET sphere(vec 0,&1)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
      REWRITE_TAC[o_DEF] THEN
      MP_TAC(ISPECL [`norm:complex->real`; `(:complex) DELETE Cx(&0)`]
        CONTINUOUS_ON_INV) THEN
      REWRITE_TAC[o_DEF; IN_DELETE; IN_UNIV; NORM_EQ_0; GSYM COMPLEX_VEC_0] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[REWRITE_RULE[o_DEF] CONTINUOUS_ON_LIFT_NORM];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DELETE; IN_UNIV; IN_SPHERE_0] THEN
      X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
      REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
      MATCH_MP_TAC REAL_MUL_LINV THEN
      ASM_REWRITE_TAC[NORM_EQ_0; COMPLEX_VEC_0]];
    ALL_TAC] THEN
  EXISTS_TAC `(r:complex->complex) a` THEN
  MP_TAC(ISPECL [`p:real^1->complex`; `(\t. a):real^1->complex`; `r:complex->complex`;
                 `(:complex) DELETE Cx(&0)`; `sphere(vec 0:complex,&1)`]
    HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
  EXISTS_TAC `(r:complex->complex) o (p:real^1->complex)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_LOOPS_EQ THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(p:real^1->complex) t IN sphere(vec 0,&1)` MP_TAC THENL
     [UNDISCH_TAC `path_image (p:real^1->complex) SUBSET sphere(vec 0,&1)` THEN
      REWRITE_TAC[path_image; SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "r" THEN REWRITE_TAC[IN_SPHERE_0; o_THM] THEN
    SIMP_TAC[REAL_INV_1; VECTOR_MUL_LID];
    UNDISCH_TAC `homotopic_loops (sphere(vec 0,&1)) ((r:complex->complex) o
                   (p:real^1->complex)) (r o (\t:real^1. a))` THEN
    REWRITE_TAC[o_DEF]]);;

(* Diagonal products of homotopies of loops. *)

let MOI_S3Z2_LOOPS_PASTECART = prove
 (`!(s:real^M->bool) (t:real^N->bool) p1 q1 p2 q2.
     homotopic_loops s p1 q1 /\ homotopic_loops t p2 q2
     ==> homotopic_loops (s PCROSS t) (\x. pastecart (p1 x) (p2 x))
                         (\x. pastecart (q1 x) (q2 x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HOMOTOPIC_LOOPS] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `h1:real^(1,1)finite_sum->real^M` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `h2:real^(1,1)finite_sum->real^N` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `\z:real^(1,1)finite_sum. pastecart ((h1:real^(1,1)finite_sum->real^M) z)
                                                ((h2:real^(1,1)finite_sum->real^N) z)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `IMAGE (h1:real^(1,1)finite_sum->real^M)
                   (interval[vec 0,vec 1] PCROSS interval[vec 0,vec 1]) SUBSET s` THEN
    UNDISCH_TAC `IMAGE (h2:real^(1,1)finite_sum->real^N)
                   (interval[vec 0,vec 1] PCROSS interval[vec 0,vec 1]) SUBSET t` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS] THEN MESON_TAC[];
    X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN ASM_SIMP_TAC[];
    X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN ASM_SIMP_TAC[];
    X_GEN_TAC `u:real^1` THEN DISCH_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `u:real^1` o check (fun th ->
      is_forall (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "pathfinish")) (concl th)))) THEN
    ASM_REWRITE_TAC[pathstart; pathfinish; o_THM; PASTECART_INJ] THEN
    MESON_TAC[]]);;

(* Winding pair (0,0): null-homotopic in the torus (linepath form). *)

let MOI_S3Z2_W_NULL = prove
 (`!g:real^1->real^(2,2)finite_sum.
     path g /\ path_image g SUBSET moi_s30_tt /\ pathfinish g = pathstart g /\
     moi_s3z2_w1 g = &0 /\ moi_s3z2_w2 g = &0
     ==> homotopic_loops moi_s30_tt g (linepath(pathstart g,pathstart g))`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `g:real^1->real^(2,2)finite_sum` MOI_S3Z2_COMPONENTS) THEN
  MP_TAC(ISPEC `g:real^1->real^(2,2)finite_sum` MOI_S3Z2_W_INTEGER) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `fstcart o (g:real^1->real^(2,2)finite_sum)` MOI_S3Z2_CIRCLE_NULL) THEN
  MP_TAC(ISPEC `sndcart o (g:real^1->real^(2,2)finite_sum)` MOI_S3Z2_CIRCLE_NULL) THEN
  ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE] THEN
  DISCH_THEN(X_CHOOSE_TAC `b2:complex`) THEN DISCH_THEN(X_CHOOSE_TAC `b1:complex`) THEN
  MP_TAC(ISPECL [`sphere(vec 0:real^2,&1)`; `sphere(vec 0:real^2,&1)`;
                 `fstcart o (g:real^1->real^(2,2)finite_sum)`; `(\t. b1):real^1->real^2`;
                 `sndcart o (g:real^1->real^(2,2)finite_sum)`; `(\t. b2):real^1->real^2`]
    MOI_S3Z2_LOOPS_PASTECART) THEN
  ASM_REWRITE_TAC[o_THM; PASTECART_FST_SND; ETA_AX; GSYM moi_s30_tt] THEN
  REWRITE_TAC[GSYM LINEPATH_REFL] THEN DISCH_TAC THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_IMP_HOMOTOPIC_LOOPS THEN ASM_REWRITE_TAC[PATHFINISH_LINEPATH] THEN
  MATCH_MP_TAC HOMOTOPIC_LOOPS_IMP_HOMOTOPIC_PATHS_NULL THEN
  EXISTS_TAC `pastecart (b1:real^2) (b2:real^2)` THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Part 3: subgroups of the integers are cyclic; a subgroup of Z^2 (as      *)
(* pairs of integer reals) is generated by an element (a1,b1) and an       *)
(* element (0,b2).                                                          *)
(* ========================================================================= *)

let MOI_S3Z2_INT_MULTIPLES = prove
 (`!S x. &0 IN S /\ (!x y. x IN S /\ y IN S ==> x - y IN S) /\ x IN S
         ==> !k. integer k ==> k * x IN S`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n. &n * x IN S` ASSUME_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC[REAL_MUL_LZERO] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_ADD_RDISTRIB; REAL_MUL_LID] THEN
    SUBGOAL_THEN `&n * x + x = &n * x - (&0 - x)` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  GEN_TAC THEN REWRITE_TAC[INTEGER_CASES] THEN
  DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `n:num` SUBST1_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_MUL_LNEG; REAL_ARITH `--y = &0 - y`] THEN ASM_MESON_TAC[]);;

let MOI_S3Z2_INT_SUBGROUP = prove
 (`!S. &0 IN S /\ (!x y. x IN S /\ y IN S ==> x - y IN S) /\
       (!x. x IN S ==> integer x)
       ==> ?d. d IN S /\ !x. x IN S ==> ?k. integer k /\ x = k * d`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `!x. x IN S ==> x = &0` THENL
   [EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `&0` THEN REWRITE_TAC[INTEGER_CLOSED; REAL_MUL_LZERO] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?n. 0 < n /\ &n IN S` MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
    REWRITE_TAC[NOT_IMP] THEN DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `integer (x:real)` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[INTEGER_CASES] THEN
    DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `n:num` SUBST_ALL_TAC)) THEN
    EXISTS_TAC `n:num` THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(&n = &0)` THEN REWRITE_TAC[REAL_OF_NUM_EQ] THEN ARITH_TAC;
      CONJ_TAC THENL
       [UNDISCH_TAC `~(-- &n = &0)` THEN REWRITE_TAC[REAL_NEG_EQ_0; REAL_OF_NUM_EQ] THEN
        ARITH_TAC;
        SUBGOAL_THEN `&n = &0 - -- &n` SUBST1_TAC THENL
         [REAL_ARITH_TAC; ASM_MESON_TAC[]]]];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` (CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC)) THEN
  EXISTS_TAC `&d` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &d` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LT]; ALL_TAC] THEN
  EXISTS_TAC `floor (x / &d)` THEN REWRITE_TAC[FLOOR] THEN
  ABBREV_TAC `k = floor (x / &d)` THEN
  SUBGOAL_THEN `integer k /\ k * &d <= x /\ x < (k + &1) * &d` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN REWRITE_TAC[FLOOR] THEN
    ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; GSYM REAL_LT_LDIV_EQ; FLOOR];
    ALL_TAC] THEN
  SUBGOAL_THEN `x - k * &d IN S` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) && length (fst (strip_forall (concl th))) = 2)) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`S:real->bool`; `&d`] MOI_S3Z2_INT_MULTIPLES) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `integer (x - k * &d)` MP_TAC THENL
   [MATCH_MP_TAC(ASSUME `!x:real. x IN S ==> integer x`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[INTEGER_CASES] THEN
  DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_TAC `m:num`)) THENL
   [ASM_CASES_TAC `m = 0` THENL
     [UNDISCH_TAC `x - k * &d = &m` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
      SUBGOAL_THEN `m < (d:num)` (fun th -> REWRITE_TAC[th]) THENL
       [REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN
        UNDISCH_TAC `x - k * &d = &m` THEN UNDISCH_TAC `x < (k + &1) * &d` THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `0 < (m:num)` (fun th -> REWRITE_TAC[th]) THENL
       [UNDISCH_TAC `~(m = 0)` THEN ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `x - k * &d IN S` THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]];
    UNDISCH_TAC `x - k * &d = -- &m` THEN UNDISCH_TAC `k * &d <= x` THEN
    REWRITE_TAC[REAL_ARITH `x - kd = --m <=> kd = x + m`] THEN
    MP_TAC(SPEC `m:num` REAL_POS) THEN REAL_ARITH_TAC]);;

let MOI_S3Z2_PAIR_MULTIPLES = prove
 (`!(H:(real#real)->bool) x y.
     (&0,&0) IN H /\ (!x y u v. (x,y) IN H /\ (u,v) IN H ==> (x - u,y - v) IN H) /\
     (x,y) IN H
     ==> !k. integer k ==> (k * x,k * y) IN H`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n. (&n * x,&n * y) IN H` ASSUME_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC[REAL_MUL_LZERO] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_ADD_RDISTRIB; REAL_MUL_LID] THEN
    SUBGOAL_THEN `&n * x + x = &n * x - (&0 - x) /\ &n * y + y = &n * y - (&0 - y)`
    (fun th -> REWRITE_TAC[th]) THENL [REAL_ARITH_TAC; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  GEN_TAC THEN REWRITE_TAC[INTEGER_CASES] THEN
  DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `n:num` SUBST1_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_MUL_LNEG; REAL_ARITH `--y = &0 - y`] THEN ASM_MESON_TAC[]);;

let MOI_S3Z2_Z2_SUBGROUP = prove
 (`!H:(real#real)->bool.
     (&0,&0) IN H /\
     (!x y u v. (x,y) IN H /\ (u,v) IN H ==> (x - u,y - v) IN H) /\
     (!x y. (x,y) IN H ==> integer x /\ integer y)
     ==> ?a1 b1 b2. (a1,b1) IN H /\ (&0,b2) IN H /\
                    !x y. (x,y) IN H
                          ==> ?k j. integer k /\ integer j /\
                                    x = k * a1 /\ y = k * b1 + j * b2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `{x:real | ?y. (x,y) IN (H:(real#real)->bool)}` MOI_S3Z2_INT_SUBGROUP) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
     [EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:real` (CONJUNCTS_THEN2
    (X_CHOOSE_TAC `b1:real`) (LABEL_TAC "A"))) THEN
  MP_TAC(ISPEC `{y:real | (&0,y) IN (H:(real#real)->bool)}` MOI_S3Z2_INT_SUBGROUP) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `&0 = &0 - &0` SUBST1_TAC THENL [REAL_ARITH_TAC; ASM_MESON_TAC[]];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `b2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "B"))) THEN
  MAP_EVERY EXISTS_TAC [`a1:real`; `b1:real`; `b2:real`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN DISCH_TAC THEN
  USE_THEN "A" (MP_TAC o SPEC `x:real`) THEN
  ANTS_TAC THENL [EXISTS_TAC `y:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(k * a1,k * b1) IN (H:(real#real)->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`H:(real#real)->bool`; `a1:real`; `b1:real`] MOI_S3Z2_PAIR_MULTIPLES) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  USE_THEN "B" (MP_TAC o SPEC `y - k * b1`) THEN ANTS_TAC THENL
   [SUBGOAL_THEN `&0 = x - k * a1` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`k:real`; `j:real`] THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Part 4: characters versus winding pairs (loops at one base point with     *)
(* equal winding pairs have equal characters); iterated loops.               *)
(* ========================================================================= *)

let MOI_S3Z2_CHAR_REV = prove
 (`!(s:real^N->bool) phi p.
     moi_s33_char s phi /\
     path p /\ path_image p SUBSET s /\ pathfinish p = pathstart p
     ==> (phi (reversepath p) <=> phi p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `phi:(real^1->real^N)->bool`;
                 `p ++ reversepath (p:real^1->real^N)`] MOI_S3Z2_CHAR_NULL) THEN
  ASM_SIMP_TAC[PATH_JOIN; PATH_REVERSEPATH; PATH_IMAGE_JOIN; PATH_IMAGE_REVERSEPATH;
               PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH; PATHSTART_JOIN;
               PATHFINISH_JOIN; UNION_SUBSET] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_PATHS_IMP_HOMOTOPIC_LOOPS THEN
    ASM_SIMP_TAC[HOMOTOPIC_PATHS_RINV; PATHFINISH_JOIN; PATHSTART_JOIN;
                 PATHFINISH_REVERSEPATH; PATHFINISH_LINEPATH];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_s33_char s (phi:(real^1->real^N)->bool)` THEN
  REWRITE_TAC[moi_s33_char] THEN
  DISCH_THEN(MP_TAC o SPECL [`p:real^1->real^N`; `reversepath p:real^1->real^N`] o
    CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[PATH_REVERSEPATH; PATH_IMAGE_REVERSEPATH; PATHSTART_REVERSEPATH;
                  PATHFINISH_REVERSEPATH] THEN
  CONV_TAC TAUT);;

(* The hypothesis of TORUS_BOUND, as a predicate. *)

let moi_s3z2_inj = new_definition
 `moi_s3z2_inj (s:real^N->bool) (g:real^N->real^(2,2)finite_sum) <=>
    g continuous_on s /\ IMAGE g s SUBSET moi_s30_tt /\
    (!p. path p /\ pathfinish p = pathstart p /\ path_image p SUBSET s /\
         homotopic_loops moi_s30_tt (g o p) (linepath(g(pathstart p),g(pathstart p)))
         ==> homotopic_loops s p (linepath(pathstart p,pathstart p)))`;;

let MOI_S3Z2_COMP_LOOP = prove
 (`!(s:real^N->bool) g p.
     moi_s3z2_inj s g /\
     path p /\ path_image p SUBSET s /\ pathfinish p = pathstart p
     ==> path (g o p) /\ path_image (g o p) SUBSET moi_s30_tt /\
         pathfinish (g o p) = pathstart (g o p)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s3z2_inj] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATH_IMAGE_COMPOSE] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    UNDISCH_TAC `IMAGE (g:real^N->real^(2,2)finite_sum) s SUBSET moi_s30_tt` THEN
    UNDISCH_TAC `path_image (p:real^1->real^N) SUBSET s` THEN SET_TAC[]]);;

(* Loops at one base point with the same winding pair have the same value *)
(* under every character.                                                   *)

let MOI_S3Z2_CHAR_W_EQ = prove
 (`!(s:real^N->bool) g phi p q.
     moi_s3z2_inj s g /\ moi_s33_char s phi /\
     path p /\ path_image p SUBSET s /\ pathfinish p = pathstart p /\
     path q /\ path_image q SUBSET s /\ pathfinish q = pathstart q /\
     pathstart q = pathstart p /\
     moi_s3z2_w1 (g o p) = moi_s3z2_w1 (g o q) /\
     moi_s3z2_w2 (g o p) = moi_s3z2_w2 (g o q)
     ==> (phi p <=> phi q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `r = p ++ reversepath (q:real^1->real^N)` THEN
  SUBGOAL_THEN `path (r:real^1->real^N) /\ path_image r SUBSET s /\
                pathstart r = pathstart p /\ pathfinish r = pathstart r`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN
    ASM_SIMP_TAC[PATH_JOIN; PATH_REVERSEPATH; PATH_IMAGE_JOIN; PATH_IMAGE_REVERSEPATH;
                 PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH; PATHSTART_JOIN;
                 PATHFINISH_JOIN; UNION_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `g:real^N->real^(2,2)finite_sum`; `p:real^1->real^N`]
    MOI_S3Z2_COMP_LOOP) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `g:real^N->real^(2,2)finite_sum`; `q:real^1->real^N`]
    MOI_S3Z2_COMP_LOOP) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_s3z2_w1 ((g:real^N->real^(2,2)finite_sum) o (r:real^1->real^N)) = &0 /\
                moi_s3z2_w2 (g o r) = &0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN REWRITE_TAC[PATH_COMPOSE_JOIN; PATH_COMPOSE_REVERSEPATH] THEN
    MP_TAC(ISPECL [`(g:real^N->real^(2,2)finite_sum) o (p:real^1->real^N)`;
                   `reversepath ((g:real^N->real^(2,2)finite_sum) o (q:real^1->real^N))`] MOI_S3Z2_W_JOIN) THEN
    MP_TAC(ISPEC `(g:real^N->real^(2,2)finite_sum) o (q:real^1->real^N)` MOI_S3Z2_W_REVERSE) THEN
    ASM_REWRITE_TAC[PATH_REVERSEPATH; PATH_IMAGE_REVERSEPATH; PATHSTART_REVERSEPATH] THEN
    STRIP_TAC THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `g:real^N->real^(2,2)finite_sum`; `r:real^1->real^N`]
    MOI_S3Z2_COMP_LOOP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `(g:real^N->real^(2,2)finite_sum) o (r:real^1->real^N)` MOI_S3Z2_W_NULL) THEN
  ASM_REWRITE_TAC[PATHSTART_COMPOSE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `homotopic_loops s r (linepath(pathstart r,pathstart (r:real^1->real^N)))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s3z2_inj s (g:real^N->real^(2,2)finite_sum)` THEN
    REWRITE_TAC[moi_s3z2_inj] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `phi:(real^1->real^N)->bool`; `r:real^1->real^N`]
    MOI_S3Z2_CHAR_NULL) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `phi:(real^1->real^N)->bool`; `q:real^1->real^N`]
    MOI_S3Z2_CHAR_REV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN EXPAND_TAC "r" THEN
  UNDISCH_TAC `moi_s33_char s (phi:(real^1->real^N)->bool)` THEN
  REWRITE_TAC[moi_s33_char] THEN
  DISCH_THEN(MP_TAC o SPECL [`p:real^1->real^N`; `reversepath q:real^1->real^N`] o
    CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[PATH_REVERSEPATH; PATH_IMAGE_REVERSEPATH; PATHSTART_REVERSEPATH;
                  PATHFINISH_REVERSEPATH] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC TAUT);;

(* Iterated loops. *)

let moi_s3z2_pow = define
 `moi_s3z2_pow (p:real^1->real^N) 0 = linepath(pathstart p,pathstart p) /\
  moi_s3z2_pow p (SUC n) = p ++ moi_s3z2_pow p n`;;

let MOI_S3Z2_POW_LOOP = prove
 (`!(s:real^N->bool) p n.
     path p /\ path_image p SUBSET s /\ pathfinish p = pathstart p
     ==> path (moi_s3z2_pow p n) /\ path_image (moi_s3z2_pow p n) SUBSET s /\
         pathstart (moi_s3z2_pow p n) = pathstart p /\
         pathfinish (moi_s3z2_pow p n) = pathstart p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN SPEC_TAC(`n:num`,`n:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[moi_s3z2_pow] THENL
   [REWRITE_TAC[PATH_LINEPATH; PATH_IMAGE_LINEPATH; PATHSTART_LINEPATH;
                PATHFINISH_LINEPATH; SEGMENT_REFL; SING_SUBSET] THEN
    UNDISCH_TAC `path_image (p:real^1->real^N) SUBSET s` THEN
    MP_TAC(ISPEC `p:real^1->real^N` PATHSTART_IN_PATH_IMAGE) THEN SET_TAC[];
    ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN;
                 UNION_SUBSET]]);;

let MOI_S3Z2_POW_CHAR = prove
 (`!(s:real^N->bool) phi p n.
     moi_s33_char s phi /\
     path p /\ path_image p SUBSET s /\ pathfinish p = pathstart p
     ==> (phi (moi_s3z2_pow p n) <=> ODD n /\ phi p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN SPEC_TAC(`n:num`,`n:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[moi_s3z2_pow; ODD] THENL
   [MATCH_MP_TAC MOI_S3Z2_CHAR_CONST THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `path_image (p:real^1->real^N) SUBSET s` THEN
    MP_TAC(ISPEC `p:real^1->real^N` PATHSTART_IN_PATH_IMAGE) THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `p:real^1->real^N`; `n:num`] MOI_S3Z2_POW_LOOP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_s33_char s (phi:(real^1->real^N)->bool)` THEN
  REWRITE_TAC[moi_s33_char] THEN
  DISCH_THEN(MP_TAC o SPECL [`p:real^1->real^N`; `moi_s3z2_pow (p:real^1->real^N) n`] o
    CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CONV_TAC TAUT);;

let MOI_S3Z2_POW_W = prove
 (`!(s:real^N->bool) g p n.
     moi_s3z2_inj s g /\
     path p /\ path_image p SUBSET s /\ pathfinish p = pathstart p
     ==> moi_s3z2_w1 (g o moi_s3z2_pow p n) = &n * moi_s3z2_w1 (g o p) /\
         moi_s3z2_w2 (g o moi_s3z2_pow p n) = &n * moi_s3z2_w2 (g o p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `g:real^N->real^(2,2)finite_sum`; `p:real^1->real^N`]
    MOI_S3Z2_COMP_LOOP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pathstart (p:real^1->real^N) IN s` ASSUME_TAC THENL
   [UNDISCH_TAC `path_image (p:real^1->real^N) SUBSET s` THEN
    MP_TAC(ISPEC `p:real^1->real^N` PATHSTART_IN_PATH_IMAGE) THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `c = linepath((g:real^N->real^(2,2)finite_sum)(pathstart p),g(pathstart p))` THEN
  SUBGOAL_THEN `moi_s3z2_w1 c = &0 /\ moi_s3z2_w2 c = &0` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `path c /\ path_image c SUBSET moi_s30_tt /\
                  pathstart c = (g:real^N->real^(2,2)finite_sum)(pathstart p) /\
                  pathfinish c = g(pathstart p)`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "c" THEN
      REWRITE_TAC[PATH_LINEPATH; PATH_IMAGE_LINEPATH; PATHSTART_LINEPATH;
                  PATHFINISH_LINEPATH; SEGMENT_REFL; SING_SUBSET] THEN
      UNDISCH_TAC `moi_s3z2_inj s (g:real^N->real^(2,2)finite_sum)` THEN
      REWRITE_TAC[moi_s3z2_inj] THEN STRIP_TAC THEN
      UNDISCH_TAC `IMAGE (g:real^N->real^(2,2)finite_sum) s SUBSET moi_s30_tt` THEN
      UNDISCH_TAC `pathstart (p:real^1->real^N) IN s` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `c ++ c = (c:real^1->real^(2,2)finite_sum)` ASSUME_TAC THENL
     [EXPAND_TAC "c" THEN REWRITE_TAC[FUN_EQ_THM; joinpaths; LINEPATH_REFL; COND_ID];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:real^1->real^(2,2)finite_sum`; `c:real^1->real^(2,2)finite_sum`]
      MOI_S3Z2_W_JOIN) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^N->real^(2,2)finite_sum) o
                linepath(pathstart (p:real^1->real^N),pathstart p) = c`
  ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[LINEPATH_REFL; o_DEF]; ALL_TAC] THEN
  SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[moi_s3z2_pow; REAL_MUL_LZERO] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `p:real^1->real^N`; `n:num`] MOI_S3Z2_POW_LOOP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `g:real^N->real^(2,2)finite_sum`;
                 `moi_s3z2_pow (p:real^1->real^N) n`] MOI_S3Z2_COMP_LOOP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[PATH_COMPOSE_JOIN] THEN
  MP_TAC(ISPECL [`(g:real^N->real^(2,2)finite_sum) o (p:real^1->real^N)`;
                 `(g:real^N->real^(2,2)finite_sum) o moi_s3z2_pow (p:real^1->real^N) n`] MOI_S3Z2_W_JOIN) THEN
  ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Part 5: integer powers of loops; two loops (whose winding pairs           *)
(* generate the image subgroup of Z^2) determine a character.                *)
(* ========================================================================= *)

let MOI_S3Z2_POW_INT = prove
 (`!(s:real^N->bool) g p k.
     moi_s3z2_inj s g /\
     path p /\ path_image p SUBSET s /\ pathfinish p = pathstart p /\ integer k
     ==> ?q b. path q /\ path_image q SUBSET s /\
               pathstart q = pathstart p /\ pathfinish q = pathstart p /\
               moi_s3z2_w1 (g o q) = k * moi_s3z2_w1 (g o p) /\
               moi_s3z2_w2 (g o q) = k * moi_s3z2_w2 (g o p) /\
               !phi. moi_s33_char s phi ==> (phi q <=> b /\ phi p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `integer k` THEN REWRITE_TAC[INTEGER_CASES] THEN
  DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `n:num` SUBST1_TAC)) THENL
   [MAP_EVERY EXISTS_TAC [`moi_s3z2_pow (p:real^1->real^N) n`; `ODD n`] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `p:real^1->real^N`; `n:num`] MOI_S3Z2_POW_LOOP) THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `g:real^N->real^(2,2)finite_sum`; `p:real^1->real^N`;
                   `n:num`] MOI_S3Z2_POW_W) THEN
    ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `phi:(real^1->real^N)->bool`; `p:real^1->real^N`;
                   `n:num`] MOI_S3Z2_POW_CHAR) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `p' = reversepath (p:real^1->real^N)` THEN
  SUBGOAL_THEN `path (p':real^1->real^N) /\ path_image p' SUBSET s /\
                pathstart p' = pathstart p /\ pathfinish p' = pathstart p'`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "p'" THEN
    ASM_REWRITE_TAC[PATH_REVERSEPATH; PATH_IMAGE_REVERSEPATH; PATHSTART_REVERSEPATH;
                    PATHFINISH_REVERSEPATH];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`moi_s3z2_pow (p':real^1->real^N) n`; `ODD n`] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `p':real^1->real^N`; `n:num`] MOI_S3Z2_POW_LOOP) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `g:real^N->real^(2,2)finite_sum`; `p':real^1->real^N`;
                 `n:num`] MOI_S3Z2_POW_W) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `g:real^N->real^(2,2)finite_sum`; `p:real^1->real^N`]
    MOI_S3Z2_COMP_LOOP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `(g:real^N->real^(2,2)finite_sum) o (p:real^1->real^N)` MOI_S3Z2_W_REVERSE) THEN
  ASM_REWRITE_TAC[GSYM PATH_COMPOSE_REVERSEPATH] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `phi:(real^1->real^N)->bool` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `phi:(real^1->real^N)->bool`; `p':real^1->real^N`;
                 `n:num`] MOI_S3Z2_POW_CHAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  EXPAND_TAC "p'" THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `phi:(real^1->real^N)->bool`; `p:real^1->real^N`]
    MOI_S3Z2_CHAR_REV) THEN
  ASM_SIMP_TAC[]);;

(* Two loops at a base point determine every character. *)

let MOI_S3Z2_TWO_LOOPS = prove
 (`!(s:real^N->bool) g a.
     moi_s3z2_inj s g /\ path_connected s /\ a IN s
     ==> ?p1 p2.
           !phi phi'. moi_s33_char s phi /\ moi_s33_char s phi' /\
                      (phi p1 <=> phi' p1) /\ (phi p2 <=> phi' p2)
                      ==> phi = phi'`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `H = {(moi_s3z2_w1 ((g:real^N->real^(2,2)finite_sum) o p),
                    moi_s3z2_w2 (g o p)) | p |
                   path p /\ path_image p SUBSET s /\
                   pathstart p = a /\ pathfinish (p:real^1->real^N) = a}` THEN
  SUBGOAL_THEN
   `!x y. (x,y) IN H <=>
          ?p:real^1->real^N. (path p /\ path_image p SUBSET s /\
                              pathstart p = a /\ pathfinish p = a) /\
             moi_s3z2_w1 ((g:real^N->real^(2,2)finite_sum) o p) = x /\
             moi_s3z2_w2 (g o p) = y`
  ASSUME_TAC THENL
   [EXPAND_TAC "H" THEN REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `H:(real#real)->bool` MOI_S3Z2_Z2_SUBGROUP) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXISTS_TAC `linepath(a:real^N,a)` THEN
      ASM_REWRITE_TAC[PATH_LINEPATH; PATH_IMAGE_LINEPATH; PATHSTART_LINEPATH;
                      PATHFINISH_LINEPATH; SEGMENT_REFL; SING_SUBSET] THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `g:real^N->real^(2,2)finite_sum`;
                     `linepath(a:real^N,a)`; `0`] MOI_S3Z2_POW_W) THEN
      ASM_REWRITE_TAC[moi_s3z2_pow; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                      PATH_LINEPATH; PATH_IMAGE_LINEPATH; SEGMENT_REFL; SING_SUBSET;
                      REAL_MUL_LZERO];
      MAP_EVERY X_GEN_TAC [`x:real`; `y:real`; `u:real`; `v:real`] THEN
      DISCH_THEN(CONJUNCTS_THEN2
        (X_CHOOSE_THEN `p:real^1->real^N` STRIP_ASSUME_TAC)
        (X_CHOOSE_THEN `q:real^1->real^N` STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `(p:real^1->real^N) ++ reversepath q` THEN
      ASM_SIMP_TAC[PATH_JOIN; PATH_REVERSEPATH; PATH_IMAGE_JOIN; PATH_IMAGE_REVERSEPATH;
                   PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH; PATHSTART_JOIN;
                   PATHFINISH_JOIN; UNION_SUBSET] THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `g:real^N->real^(2,2)finite_sum`; `p:real^1->real^N`]
        MOI_S3Z2_COMP_LOOP) THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `g:real^N->real^(2,2)finite_sum`; `q:real^1->real^N`]
        MOI_S3Z2_COMP_LOOP) THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[PATH_COMPOSE_JOIN; PATH_COMPOSE_REVERSEPATH] THEN
      MP_TAC(ISPECL [`(g:real^N->real^(2,2)finite_sum) o (p:real^1->real^N)`;
                     `reversepath ((g:real^N->real^(2,2)finite_sum) o (q:real^1->real^N))`]
        MOI_S3Z2_W_JOIN) THEN
      MP_TAC(ISPEC `(g:real^N->real^(2,2)finite_sum) o (q:real^1->real^N)`
        MOI_S3Z2_W_REVERSE) THEN
      ASM_REWRITE_TAC[PATH_REVERSEPATH; PATH_IMAGE_REVERSEPATH; PATHSTART_REVERSEPATH;
                      PATHSTART_COMPOSE; PATHFINISH_COMPOSE] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN
      DISCH_THEN(X_CHOOSE_THEN `p:real^1->real^N` (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
        (CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (SUBST1_TAC o SYM)))) THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `g:real^N->real^(2,2)finite_sum`; `p:real^1->real^N`]
        MOI_S3Z2_COMP_LOOP) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(ISPEC `(g:real^N->real^(2,2)finite_sum) o (p:real^1->real^N)`
        MOI_S3Z2_W_INTEGER) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:real` (X_CHOOSE_THEN `b1:real` (X_CHOOSE_THEN `b2:real`
    (CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "gen")))))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p2:real^1->real^N` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `p1:real^1->real^N` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`p1:real^1->real^N`; `p2:real^1->real^N`] THEN
  MAP_EVERY X_GEN_TAC [`phi:(real^1->real^N)->bool`; `phi':(real^1->real^N)->bool`] THEN
  STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `p:real^1->real^N` THEN
  ASM_CASES_TAC `path (p:real^1->real^N) /\ path_image p SUBSET s /\
                 pathfinish p = pathstart p` THENL
   [ALL_TAC; ASM_MESON_TAC[moi_s33_char]] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  SUBGOAL_THEN `pathstart (p:real^1->real^N) IN s` ASSUME_TAC THENL
   [UNDISCH_TAC `path_image (p:real^1->real^N) SUBSET s` THEN
    MP_TAC(ISPEC `p:real^1->real^N` PATHSTART_IN_PATH_IMAGE) THEN SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `path_connected (s:real^N->bool)` THEN REWRITE_TAC[path_connected] THEN
  DISCH_THEN(MP_TAC o SPECL [`a:real^N`; `pathstart (p:real^1->real^N)`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^1->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `path ((d:real^1->real^N) ++ p ++ reversepath d) /\
                path_image (d ++ p ++ reversepath d) SUBSET s /\
                pathstart (d ++ p ++ reversepath d) = a /\
                pathfinish (d ++ p ++ reversepath d) = a /\
                homotopic_loops s (d ++ p ++ reversepath d) p`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[PATH_JOIN; PATH_REVERSEPATH; PATH_IMAGE_JOIN; PATH_IMAGE_REVERSEPATH;
                 PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH; PATHSTART_JOIN;
                 PATHFINISH_JOIN; UNION_SUBSET] THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_CONJUGATE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `p0 = (d:real^1->real^N) ++ p ++ reversepath d` THEN
  SUBGOAL_THEN `!psi:(real^1->real^N)->bool. moi_s33_char s psi ==> (psi p <=> psi p0)`
  (LABEL_TAC "conj") THENL
   [X_GEN_TAC `psi:(real^1->real^N)->bool` THEN DISCH_TAC THEN
    UNDISCH_TAC `moi_s33_char s (psi:(real^1->real^N)->bool)` THEN
    REWRITE_TAC[moi_s33_char] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
    ONCE_REWRITE_TAC[HOMOTOPIC_LOOPS_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "conj" (fun th ->
    MP_TAC(MATCH_MP th (ASSUME `moi_s33_char s (phi:(real^1->real^N)->bool)`)) THEN
    MP_TAC(MATCH_MP th (ASSUME `moi_s33_char s (phi':(real^1->real^N)->bool)`))) THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  USE_THEN "gen" (MP_TAC o SPECL
    [`moi_s3z2_w1 ((g:real^N->real^(2,2)finite_sum) o (p0:real^1->real^N))`;
     `moi_s3z2_w2 ((g:real^N->real^(2,2)finite_sum) o (p0:real^1->real^N))`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `p0:real^1->real^N` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` (X_CHOOSE_THEN `j:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `g:real^N->real^(2,2)finite_sum`; `p1:real^1->real^N`;
                 `k:real`] MOI_S3Z2_POW_INT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q1:real^1->real^N` (X_CHOOSE_THEN `c1:bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `g:real^N->real^(2,2)finite_sum`; `p2:real^1->real^N`;
                 `j:real`] MOI_S3Z2_POW_INT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q2:real^1->real^N` (X_CHOOSE_THEN `c2:bool`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `q = (q1:real^1->real^N) ++ q2` THEN
  SUBGOAL_THEN `path (q:real^1->real^N) /\ path_image q SUBSET s /\
                pathstart q = a /\ pathfinish q = a`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN
    ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN;
                 UNION_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_s3z2_w1 ((g:real^N->real^(2,2)finite_sum) o (q:real^1->real^N)) =
    moi_s3z2_w1 (g o p0) /\
    moi_s3z2_w2 (g o q) = moi_s3z2_w2 (g o (p0:real^1->real^N))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN REWRITE_TAC[PATH_COMPOSE_JOIN] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `g:real^N->real^(2,2)finite_sum`; `q1:real^1->real^N`]
      MOI_S3Z2_COMP_LOOP) THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `g:real^N->real^(2,2)finite_sum`; `q2:real^1->real^N`]
      MOI_S3Z2_COMP_LOOP) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`(g:real^N->real^(2,2)finite_sum) o (q1:real^1->real^N)`;
                   `(g:real^N->real^(2,2)finite_sum) o (q2:real^1->real^N)`]
      MOI_S3Z2_W_JOIN) THEN
    ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!psi:(real^1->real^N)->bool.
                  moi_s33_char s psi ==> (psi p0 <=> ~((c1 /\ psi p1) <=> (c2 /\ psi p2)))`
  (fun th -> MP_TAC(SPEC `phi:(real^1->real^N)->bool` th) THEN
             MP_TAC(SPEC `phi':(real^1->real^N)->bool` th)) THENL
   [X_GEN_TAC `psi:(real^1->real^N)->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `g:real^N->real^(2,2)finite_sum`;
                   `psi:(real^1->real^N)->bool`; `p0:real^1->real^N`; `q:real^1->real^N`]
      MOI_S3Z2_CHAR_W_EQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "q" THEN
    SUBGOAL_THEN `(psi:(real^1->real^N)->bool) (q1 ++ q2) <=> ~(psi q1 <=> psi q2)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `moi_s33_char s (psi:(real^1->real^N)->bool)` THEN
      REWRITE_TAC[moi_s33_char] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2) THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC TAUT);;

(* ========================================================================= *)
(* Part 6: at most four characters; finite unions of closed convex sets are *)
(* path-connected when connected; the theorem Z2_TORUS_BOUND.               *)
(* ========================================================================= *)

let MOI_S3Z2_CHARS_LE_4 = prove
 (`!(s:real^N->bool) g.
     moi_s3z2_inj s g /\ path_connected s /\ ~(s = {}) /\
     FINITE {phi | moi_s33_char s phi}
     ==> CARD {phi | moi_s33_char s phi} <= 4`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `g:real^N->real^(2,2)finite_sum`; `a:real^N`]
    MOI_S3Z2_TWO_LOOPS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p1:real^1->real^N`
    (X_CHOOSE_THEN `p2:real^1->real^N` (LABEL_TAC "inj"))) THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD(IMAGE (\phi:(real^1->real^N)->bool. (phi p1:bool,phi p2:bool))
                         {phi | moi_s33_char s phi})` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    BETA_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
    MAP_EVERY X_GEN_TAC [`phi:(real^1->real^N)->bool`;
                         `phi':(real^1->real^N)->bool`] THEN
    STRIP_TAC THEN USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD {(T,T),(T,F),(F,T),(F,F)}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `phi:(real^1->real^N)->bool` THEN DISCH_TAC THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; PAIR_EQ] THEN CONV_TAC TAUT;
    SIMP_TAC[FINITE_INSERT; FINITE_EMPTY; CARD_CLAUSES] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; PAIR_EQ] THEN
    CONV_TAC NUM_REDUCE_CONV]);;

let MOI_S3Z2_EXP_LE_4 = prove
 (`!n. 2 EXP n <= 4 <=> n <= 2`,
  GEN_TAC THEN SUBGOAL_THEN `4 = 2 EXP 2` SUBST1_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV; REWRITE_TAC[LE_EXP; ARITH_EQ]]);;

(* The statement MOI_S33_POLY_PC of pc_moi_s33_stmt.ml, proved here. *)

let MOI_S3Z2_POLY_PC = prove
 (MOI_S33_POLY_PC,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `UNIONS c:real^N->bool` PATH_CONNECTED_EQ_CONNECTED_LPC) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC ANR_IMP_LOCALLY_PATH_CONNECTED THEN
    MATCH_MP_TAC ANR_FINITE_UNIONS_CONVEX_CLOSED THEN ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

let MOI_S3Z2_COMPLEX_PC = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ lf_simplicial_complex c /\ connected (UNIONS c)
     ==> path_connected (UNIONS c)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S3Z2_POLY_PC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `lf_simplicial_complex (c:(real^N->bool)->bool)` THEN
  REWRITE_TAC[lf_simplicial_complex] THEN
  MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_CLOSED]);;

let Z2_TORUS_BOUND = prove
 (MOI_S30_Z2_TORUS_BOUND,
  DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`m:(real^N->bool)->bool`;
                       `g:real^N->real^(2,2)finite_sum`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:(real^N->bool)->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `path_connected (UNIONS m:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3Z2_COMPLEX_PC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[combinatorial_manifold];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s3z2_inj (UNIONS m:real^N->bool)
                             (g:real^N->real^(2,2)finite_sum)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[moi_s3z2_inj]; ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS m:real^N->bool`; `g:real^N->real^(2,2)finite_sum`]
    MOI_S3Z2_CHARS_LE_4) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[HAS_SIZE]; ALL_TAC] THEN
  SUBGOAL_THEN `CARD {phi | moi_s33_char (UNIONS m:real^N->bool) phi} = 2 EXP n`
    SUBST1_TAC THENL [ASM_MESON_TAC[HAS_SIZE]; ALL_TAC] THEN
  REWRITE_TAC[MOI_S3Z2_EXP_LE_4; GSYM REAL_OF_NUM_LE] THEN
  ASM_REAL_ARITH_TAC);;


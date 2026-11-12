(* ========================================================================= *)
(* pc_moi_s33_char: characters and 2D recognition for Sec 33 (Moise GTM 47,  *)
(* Sec 33, pp.230-238: the replacement of Lemma 11 and the 2D recognition    *)
(* used in Lemmas 3-4, 9 and on p.238).  Main theorems:                      *)
(*   CHAR_TRANSFER  |- MOI_S33_CHAR_TRANSFER                                 *)
(*   CHAR_HOMEO     |- MOI_S33_CHAR_HOMEO                                    *)
(*   CHAR_PRODUCT   |- MOI_S33_CHAR_PRODUCT                                  *)
(*   POLY_PC        |- MOI_S33_POLY_PC                                       *)
(*   DISK_RECOG     |- MOI_S33_DISK_RECOG                                    *)
(*   HOLED_RECOG    |- MOI_S33_HOLED_RECOG                                   *)
(* Characters: transport along maps that are inverse up to free homotopy of *)
(* loops (homeomorphisms; the product with an open interval); transfer      *)
(* along a pi_1 isomorphism (restriction and extension are inverse).        *)
(* Recognition: the local structure of triangulated surfaces comes from     *)
(* pc_moi_s28_trib / pc_moi_s30_tame (charts), the Euler characteristic     *)
(* from the character counts, the PL type from MOI_FND_SURFACE_PLANAR.      *)
(* ========================================================================= *)

needs "src/pc_moi_s33_stmt.ml";;
needs "src/pc_moi_s30_z2c.ml";;
needs "src/pc_moi_fnd_surfb.ml";;
needs "src/pc_moi_s30_tame.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Part 1: POLY_PC; transport of characters; CHAR_HOMEO, CHAR_PRODUCT.      *)
(* ------------------------------------------------------------------------- *)

let POLY_PC = prove
 (MOI_S33_POLY_PC,
  ACCEPT_TAC MOI_S3Z2_POLY_PC);;

(* A continuous map carries loops to loops. *)

let MOI_S3KC_LOOP_COMPOSE = prove
 (`!(g:real^N->real^M) s t q.
     g continuous_on t /\ IMAGE g t SUBSET s /\
     path q /\ path_image q SUBSET t /\ pathfinish q = pathstart q
     ==> path (g o q) /\ path_image (g o q) SUBSET s /\
         pathfinish (g o q) = pathstart (g o q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[PATH_IMAGE_COMPOSE; PATHSTART_COMPOSE; PATHFINISH_COMPOSE] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    ASM SET_TAC[]]);;

(* Pulling a character back along a continuous map. *)

let MOI_S3KC_CHAR_PULL = prove
 (`!(s:real^M->bool) (t:real^N->bool) g phi.
     g continuous_on t /\ IMAGE g t SUBSET s /\ moi_s33_char s phi
     ==> moi_s33_char t (\q. path q /\ path_image q SUBSET t /\
                             pathfinish q = pathstart q /\ phi (g o q))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s33_char] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "sup") (CONJUNCTS_THEN2 (LABEL_TAC "hom")
      (LABEL_TAC "add"))))) THEN
  REPEAT CONJ_TAC THENL
   [SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`p:real^1->real^N`; `q:real^1->real^N`] THEN DISCH_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_LOOP) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_PATH) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "hom" MATCH_MP_TAC THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`p:real^1->real^N`; `q:real^1->real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `pathfinish p = pathstart (q:real^1->real^N)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN;
                 UNION_SUBSET; PATH_COMPOSE_JOIN] THEN
    USE_THEN "add" MATCH_MP_TAC THEN
    REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MOI_S3KC_LOOP_COMPOSE]]);;

(* Maps inverse to each other up to free homotopy of loops give equal       *)
(* character counts.                                                        *)

let MOI_S3KC_CHAR_HEQ = prove
 (`!(s:real^M->bool) (t:real^N->bool) f g.
     f continuous_on s /\ IMAGE f s SUBSET t /\
     g continuous_on t /\ IMAGE g t SUBSET s /\
     (!p. path p /\ path_image p SUBSET s /\ pathfinish p = pathstart p
          ==> homotopic_loops s (g o f o p) p) /\
     (!q. path q /\ path_image q SUBSET t /\ pathfinish q = pathstart q
          ==> homotopic_loops t (f o g o q) q)
     ==> !n. {phi | moi_s33_char s phi} HAS_SIZE n <=>
             {phi | moi_s33_char t phi} HAS_SIZE n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC BIJECTIONS_HAS_SIZE_EQ THEN
  EXISTS_TAC `\phi (q:real^1->real^N). path q /\ path_image q SUBSET (t:real^N->bool) /\
                    pathfinish q = pathstart q /\ phi ((g:real^N->real^M) o q)` THEN
  EXISTS_TAC `\psi (p:real^1->real^M). path p /\ path_image p SUBSET (s:real^M->bool) /\
                    pathfinish p = pathstart p /\ psi ((f:real^M->real^N) o p)` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
   [X_GEN_TAC `phi:(real^1->real^M)->bool` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S3KC_CHAR_PULL THEN EXISTS_TAC `s:real^M->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `p:real^1->real^M` THEN
    EQ_TAC THENL
     [STRIP_TAC THEN
      SUBGOAL_THEN `homotopic_loops s ((g:real^N->real^M) o (f:real^M->real^N) o p) p`
      ASSUME_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `moi_s33_char s (phi:(real^1->real^M)->bool)` THEN
      REWRITE_TAC[moi_s33_char] THEN ASM_MESON_TAC[];
      DISCH_TAC THEN
      SUBGOAL_THEN `path (p:real^1->real^M) /\ path_image p SUBSET (s:real^M->bool) /\ pathfinish p = pathstart p`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `moi_s33_char s (phi:(real^1->real^M)->bool)` THEN
        REWRITE_TAC[moi_s33_char] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`f:real^M->real^N`; `t:real^N->bool`; `s:real^M->bool`;
                     `p:real^1->real^M`] MOI_S3KC_LOOP_COMPOSE) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `homotopic_loops s ((g:real^N->real^M) o (f:real^M->real^N) o p) p`
      ASSUME_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `moi_s33_char s (phi:(real^1->real^M)->bool)` THEN
      REWRITE_TAC[moi_s33_char] THEN ASM_MESON_TAC[]];
    X_GEN_TAC `psi:(real^1->real^N)->bool` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S3KC_CHAR_PULL THEN EXISTS_TAC `t:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `q:real^1->real^N` THEN
    EQ_TAC THENL
     [STRIP_TAC THEN
      SUBGOAL_THEN `homotopic_loops t ((f:real^M->real^N) o (g:real^N->real^M) o q) q`
      ASSUME_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `moi_s33_char t (psi:(real^1->real^N)->bool)` THEN
      REWRITE_TAC[moi_s33_char] THEN ASM_MESON_TAC[];
      DISCH_TAC THEN
      SUBGOAL_THEN `path (q:real^1->real^N) /\ path_image q SUBSET (t:real^N->bool) /\ pathfinish q = pathstart q`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `moi_s33_char t (psi:(real^1->real^N)->bool)` THEN
        REWRITE_TAC[moi_s33_char] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`g:real^N->real^M`; `s:real^M->bool`; `t:real^N->bool`;
                     `q:real^1->real^N`] MOI_S3KC_LOOP_COMPOSE) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `homotopic_loops t ((f:real^M->real^N) o (g:real^N->real^M) o q) q`
      ASSUME_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `moi_s33_char t (psi:(real^1->real^N)->bool)` THEN
      REWRITE_TAC[moi_s33_char] THEN ASM_MESON_TAC[]]]);;

(* CHAR_HOMEO: a homeomorphism is inverse to its inverse on the points of *)
(* the loops (the loops themselves are total maps, so only homotopic).     *)

let CHAR_HOMEO = prove
 (MOI_S33_CHAR_HOMEO,
  MAP_EVERY X_GEN_TAC [`s:real^M->bool`; `s':real^N->bool`; `f:real^M->real^N`;
                       `g:real^N->real^M`] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  MATCH_MP_TAC MOI_S3KC_CHAR_HEQ THEN
  MAP_EVERY EXISTS_TAC [`f:real^M->real^N`; `g:real^N->real^M`] THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN CONJ_TAC THENL
   [X_GEN_TAC `p:real^1->real^M` THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[HOMOTOPIC_LOOPS_SYM] THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_EQ THEN ASM_REWRITE_TAC[o_THM] THEN
    X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[path_image]) THEN ASM SET_TAC[];
    X_GEN_TAC `q:real^1->real^N` THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[HOMOTOPIC_LOOPS_SYM] THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_EQ THEN ASM_REWRITE_TAC[o_THM] THEN
    X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[path_image]) THEN ASM SET_TAC[]]);;

(* CHAR_PRODUCT: fstcart and the slice at 1/2 are inverse up to the        *)
(* straight-line homotopy in the convex second factor.                     *)

let CHAR_PRODUCT = prove
 (MOI_S33_CHAR_PRODUCT,
  X_GEN_TAC `s:real^N->bool` THEN
  ABBREV_TAC `i = {x:real^1 | &0 < drop x /\ drop x < &1}` THEN
  SUBGOAL_THEN `convex (i:real^1->bool) /\ lift(&1 / &2) IN i` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "i" THEN CONJ_TAC THENL
     [SUBGOAL_THEN `{x:real^1 | &0 < drop x /\ drop x < &1} = interval(vec 0,vec 1)`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_INTERVAL_1; IN_ELIM_THM; DROP_VEC]; ALL_TAC] THEN
      REWRITE_TAC[CONVEX_INTERVAL];
      REWRITE_TAC[IN_ELIM_THM; LIFT_DROP] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S3KC_CHAR_HEQ THEN
  MAP_EVERY EXISTS_TAC [`fstcart:real^(N,1)finite_sum->real^N`;
                        `\x:real^N. pastecart x (lift(&1 / &2))`] THEN
  SUBGOAL_THEN `fstcart continuous_on (s PCROSS (i:real^1->bool)) /\
                IMAGE fstcart (s PCROSS i) SUBSET (s:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; FSTCART_PASTECART] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x:real^N. pastecart x (lift(&1 / &2))) continuous_on s /\
    IMAGE (\x:real^N. pastecart x (lift(&1 / &2))) s SUBSET s PCROSS (i:real^1->bool)`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST] THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `p:real^1->real^(N,1)finite_sum` THEN STRIP_TAC THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_LINEAR THEN
    MP_TAC(ISPECL [`fstcart:real^(N,1)finite_sum->real^N`; `s:real^N->bool`;
                   `(s:real^N->bool) PCROSS (i:real^1->bool)`; `p:real^1->real^(N,1)finite_sum`]
      MOI_S3KC_LOOP_COMPOSE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`\x:real^N. pastecart x (lift(&1 / &2))`; `(s:real^N->bool) PCROSS (i:real^1->bool)`;
                   `s:real^N->bool`; `fstcart o (p:real^1->real^(N,1)finite_sum)`]
      MOI_S3KC_LOOP_COMPOSE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(p:real^1->real^(N,1)finite_sum) t IN s PCROSS i` MP_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[path_image]) THEN ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[o_THM] THEN
    SPEC_TAC(`(p:real^1->real^(N,1)finite_sum) t`, `z:real^(N,1)finite_sum`) THEN
    REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; FSTCART_PASTECART] THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^1`] THEN STRIP_TAC THEN
    REWRITE_TAC[SUBSET; IN_SEGMENT] THEN X_GEN_TAC `z:real^(N,1)finite_sum` THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[GSYM PASTECART_CMUL; PASTECART_ADD; PASTECART_IN_PCROSS] THEN
    REWRITE_TAC[VECTOR_ARITH `(&1 - u) % x + u % x = x:real^N`] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `convex (i:real^1->bool)` THEN REWRITE_TAC[CONVEX_ALT] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `q:real^1->real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `fstcart o (\x:real^N. pastecart x (lift(&1 / &2))) o (q:real^1->real^N) = q`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART];
      ASM_REWRITE_TAC[HOMOTOPIC_LOOPS_REFL]]]);;

(* ------------------------------------------------------------------------- *)
(* Part 2: path algebra.  Freely homotopic loops are conjugate by the       *)
(* track of the base point (the general form of the library's              *)
(* HOMOTOPIC_LOOPS_IMP_HOMOTOPIC_PATHS_NULL, with the same homotopy), and  *)
(* conjugation by a path distributes over the join of two loops.           *)
(* ------------------------------------------------------------------------- *)

let MOI_S3KC_HOMOTOPIC_LOOPS_CONJUGATE_PATH = prove
 (`!s p q:real^1->real^N.
        homotopic_loops s p q
        ==> ?r. path r /\ path_image r SUBSET s /\
                pathstart r = pathstart p /\ pathfinish r = pathstart q /\
                homotopic_paths s p (r ++ q ++ reversepath r)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_LOOP) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_PATH) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_SUBSET) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homotopic_loops]) THEN
  REWRITE_TAC[HOMOTOPIC_WITH_EUCLIDEAN; PCROSS; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `h:real^(1,1)finite_sum->real^N` THEN STRIP_TAC THEN
  EXISTS_TAC `\u. (h:real^(1,1)finite_sum->real^N) (pastecart u (vec 0))` THEN
  MATCH_MP_TAC(TAUT `(p /\ q) /\ r ==> p /\ q /\ r`) THEN CONJ_TAC THENL
   [REWRITE_TAC[path; path_image] THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_ID;
               CONTINUOUS_ON_CONST] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
      SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_PASTECART_THM;
               ENDS_IN_UNIT_INTERVAL];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
          SUBSET_TRANS)) THEN
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM o_DEF] THEN
      REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_PASTECART_THM;
               ENDS_IN_UNIT_INTERVAL]];
    ALL_TAC] THEN
  REWRITE_TAC[pathstart; pathfinish] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN EXISTS_TAC
   `(p:real^1->real^N) ++ linepath(pathfinish p,pathfinish p)` THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[HOMOTOPIC_PATHS_RID; HOMOTOPIC_PATHS_SYM]; ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN EXISTS_TAC
   `linepath(pathstart p,pathstart p) ++ (p:real^1->real^N) ++
    linepath(pathfinish p,pathfinish p)` THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN
    MP_TAC(ISPECL [`s:real^N->bool`;
       `(p:real^1->real^N) ++ linepath(pathfinish p,pathfinish p)`]
     HOMOTOPIC_PATHS_LID) THEN
    REWRITE_TAC[PATHSTART_JOIN] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[PATH_JOIN; PATH_LINEPATH; PATHSTART_LINEPATH] THEN
    MATCH_MP_TAC SUBSET_PATH_IMAGE_JOIN THEN
    ASM_REWRITE_TAC[PATH_IMAGE_LINEPATH; SEGMENT_REFL] THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
    ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[homotopic_paths; HOMOTOPIC_WITH_EUCLIDEAN; PCROSS] THEN
  EXISTS_TAC
   `\y:real^(1,1)finite_sum.
        (subpath (vec 0) (fstcart y) (\u. h(pastecart u (vec 0))) ++
         (\u. (h:real^(1,1)finite_sum->real^N) (pastecart (fstcart y) u)) ++
         subpath (fstcart y) (vec 0) (\u. h(pastecart u (vec 0))))
        (sndcart y)` THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; SUBPATH_TRIVIAL;
                  SUBPATH_REFL; SUBPATH_REVERSEPATH; ETA_AX;
                  PATHSTART_JOIN; PATHFINISH_JOIN;
                  PATHSTART_SUBPATH; PATHFINISH_SUBPATH;
                  PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
  ONCE_REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[pathstart]] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[PCROSS] HOMOTOPIC_JOIN_LEMMA) THEN
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC(REWRITE_RULE[PCROSS] HOMOTOPIC_JOIN_LEMMA) THEN
      ASM_REWRITE_TAC[PASTECART_FST_SND; ETA_AX] THEN CONJ_TAC THENL
       [ALL_TAC;
        RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
        REWRITE_TAC[PATHSTART_SUBPATH] THEN
        ASM_SIMP_TAC[pathstart; pathfinish]];
      RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
      REWRITE_TAC[PATHFINISH_SUBPATH; PATHSTART_JOIN] THEN
      ASM_SIMP_TAC[pathstart]] THEN
    REWRITE_TAC[subpath] THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    REWRITE_TAC[VECTOR_SUB_RZERO; VECTOR_SUB_LZERO; VECTOR_ADD_LID] THEN
    (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
       [CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_ADD; CONTINUOUS_ON_MUL;
        LIFT_DROP; CONTINUOUS_ON_NEG; DROP_NEG; CONTINUOUS_ON_CONST;
        CONTINUOUS_ON_ID; LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART;
        LIFT_NEG; o_DEF; ETA_AX] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
       CONTINUOUS_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
    REWRITE_TAC[IN_ELIM_PASTECART_THM] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; IN_INTERVAL_1] THEN
    REWRITE_TAC[DROP_ADD; DROP_NEG; DROP_VEC; DROP_CMUL; REAL_POS] THEN
    SIMP_TAC[REAL_LE_MUL; REAL_SUB_LE; REAL_ARITH
     `t + --t * x = t * (&1 - x)`] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH
     `t * x <= t * &1 /\ &1 * t <= &1 * &1 ==> t * x <= &1`) THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;

    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC; IMP_CONJ;
      RIGHT_FORALL_IMP_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    X_GEN_TAC `t:real^1` THEN STRIP_TAC THEN
    REWRITE_TAC[SET_RULE
     `(!x:real^1. x IN s ==> (f:real^1->real^N) x IN t) <=> IMAGE f s SUBSET t`] THEN
    REWRITE_TAC[GSYM path_image; ETA_AX] THEN
    REPEAT(MATCH_MP_TAC SUBSET_PATH_IMAGE_JOIN THEN CONJ_TAC) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
      SUBSET_TRANS)) THEN
    REWRITE_TAC[path_image; subpath] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM o_DEF] THEN
    REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_PASTECART_THM] THEN
    SIMP_TAC[IN_INTERVAL_1; DROP_SUB; DROP_VEC; DROP_CMUL; DROP_ADD] THEN
    REWRITE_TAC[REAL_ADD_LID; REAL_SUB_RZERO; REAL_POS] THEN
    REWRITE_TAC[REAL_ARITH `t + (&0 - t) * x = t * (&1 - x)`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_SUB_LE] THEN
    REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Part 3: CHAR_TRANSFER.  With s, w path connected and moi_s33_pi1 s       *)
(* w (kernel trivial; every loop of w at a homotopic rel a to a loop of s), *)
(* extension (a loop of w takes the value of any loop of s freely homotopic *)
(* to it in w) and restriction are inverse bijections between the          *)
(* characters of s and those of w.                                         *)
(* ------------------------------------------------------------------------- *)

(* Conjugation by a path distributes over the join of two loops. *)

let MOI_S3KC_CONJ_JOIN = prove
 (`!s g p q:real^1->real^N.
     path g /\ path_image g SUBSET s /\
     path p /\ path_image p SUBSET s /\ path q /\ path_image q SUBSET s /\
     pathstart p = pathfinish g /\ pathfinish p = pathfinish g /\
     pathstart q = pathfinish g /\ pathfinish q = pathfinish g
     ==> homotopic_paths s (g ++ (p ++ q) ++ reversepath g)
                           ((g ++ p ++ reversepath g) ++ (g ++ q ++ reversepath g))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `path (reversepath g:real^1->real^N) /\
                path_image (reversepath g) SUBSET s /\
                pathstart (reversepath g) = pathfinish g /\
                pathfinish (reversepath g) = pathstart g`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[PATH_REVERSEPATH; PATH_IMAGE_REVERSEPATH; PATHSTART_REVERSEPATH;
                    PATHFINISH_REVERSEPATH];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
  EXISTS_TAC `(g:real^1->real^N) ++ ((p ++ reversepath g) ++ (g ++ q ++ reversepath g))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC HOMOTOPIC_PATHS_ASSOC THEN
    ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN;
                 UNION_SUBSET]] THEN
  MP_TAC(ISPECL [`g:real^1->real^N`; `(p ++ q) ++ reversepath (g:real^1->real^N)`;
                 `(p ++ reversepath g) ++ ((g:real^1->real^N) ++ q ++ reversepath g)`;
                 `s:real^N->bool`] HOMOTOPIC_PATHS_LCANCEL_EQ) THEN
  ASM_REWRITE_TAC[PATHSTART_JOIN] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
  EXISTS_TAC `(p:real^1->real^N) ++ (q ++ reversepath g)` THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN MATCH_MP_TAC HOMOTOPIC_PATHS_ASSOC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
  EXISTS_TAC `(p:real^1->real^N) ++ (reversepath g ++ (g ++ q ++ reversepath g))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC HOMOTOPIC_PATHS_ASSOC THEN
    ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN;
                 UNION_SUBSET]] THEN
  MP_TAC(ISPECL [`p:real^1->real^N`; `q ++ reversepath (g:real^1->real^N)`;
                 `reversepath g ++ ((g:real^1->real^N) ++ q ++ reversepath g)`;
                 `s:real^N->bool`] HOMOTOPIC_PATHS_LCANCEL_EQ) THEN
  ASM_REWRITE_TAC[PATHSTART_JOIN] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
  EXISTS_TAC `(reversepath g ++ g) ++ (q ++ reversepath (g:real^1->real^N))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN MATCH_MP_TAC HOMOTOPIC_PATHS_ASSOC THEN
    ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN;
                 UNION_SUBSET]] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
  EXISTS_TAC `linepath(pathfinish g,pathfinish g) ++ (q ++ reversepath (g:real^1->real^N))` THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `q ++ reversepath (g:real^1->real^N)`]
      HOMOTOPIC_PATHS_LID) THEN
    ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; PATHSTART_JOIN; UNION_SUBSET];
    MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
    ASM_SIMP_TAC[PATHFINISH_LINEPATH; PATHSTART_JOIN; HOMOTOPIC_PATHS_REFL; PATH_JOIN;
                 PATH_IMAGE_JOIN; UNION_SUBSET] THEN
    ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_LINV THEN ASM_REWRITE_TAC[]]);;

(* Conjugating a loop to a base point. *)

let MOI_S3KC_LOOP_REBASE = prove
 (`!s p (a:real^N).
     path_connected s /\ a IN s /\
     path p /\ path_image p SUBSET s /\ pathfinish p = pathstart p
     ==> ?g. path g /\ path_image g SUBSET s /\
             pathstart g = a /\ pathfinish g = pathstart p /\
             path (g ++ p ++ reversepath g) /\
             path_image (g ++ p ++ reversepath g) SUBSET s /\
             pathstart (g ++ p ++ reversepath g) = a /\
             pathfinish (g ++ p ++ reversepath g) = a /\
             homotopic_loops s (g ++ p ++ reversepath g) p`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^N`; `pathstart p:real^N`] o
    GEN_REWRITE_RULE I [path_connected]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; SUBSET];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^1->real^N` THEN STRIP_TAC] THEN
  ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN; UNION_SUBSET;
               PATH_REVERSEPATH; PATH_IMAGE_REVERSEPATH; PATHSTART_REVERSEPATH;
               PATHFINISH_REVERSEPATH] THEN
  MATCH_MP_TAC HOMOTOPIC_LOOPS_CONJUGATE THEN ASM_REWRITE_TAC[]);;

(* W1: every loop of w is freely homotopic in w to a loop of s at a. *)

let MOI_S3KC_TR_W1 = prove
 (`!s w (a:real^N).
     s SUBSET w /\ path_connected w /\ a IN s /\
     (!p. path p /\ path_image p SUBSET w /\ pathstart p = a /\ pathfinish p = a
          ==> ?q. path q /\ path_image q SUBSET s /\ pathstart q = a /\
                  pathfinish q = a /\ homotopic_paths w p q)
     ==> !p. path p /\ path_image p SUBSET w /\ pathfinish p = pathstart p
             ==> ?q. path q /\ path_image q SUBSET s /\ pathfinish q = pathstart q /\
                     pathstart q = a /\ homotopic_loops w p q`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "surj")))) THEN
  X_GEN_TAC `p:real^1->real^N` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`w:real^N->bool`; `p:real^1->real^N`; `a:real^N`] MOI_S3KC_LOOP_REBASE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^N` STRIP_ASSUME_TAC) THEN
  USE_THEN "surj" (MP_TAC o SPEC `(g:real^1->real^N) ++ p ++ reversepath g`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^1->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `q:real^1->real^N` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
  EXISTS_TAC `(g:real^1->real^N) ++ p ++ reversepath g` THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[HOMOTOPIC_LOOPS_SYM] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC HOMOTOPIC_PATHS_IMP_HOMOTOPIC_LOOPS THEN ASM_REWRITE_TAC[]]);;

(* W2 at the base point: loops of s at a that are freely homotopic in w    *)
(* have the same value.  They are conjugate in w by a loop at a, which is  *)
(* homotopic rel a to a loop of s; the difference is null in w, hence in s. *)

let MOI_S3KC_TR_W2A = prove
 (`!s w (a:real^N) phi.
     s SUBSET w /\ a IN s /\
     (!p. path p /\ path_image p SUBSET s /\ pathfinish p = pathstart p /\
          homotopic_loops w p (linepath(pathstart p,pathstart p))
          ==> homotopic_loops s p (linepath(pathstart p,pathstart p))) /\
     (!p. path p /\ path_image p SUBSET w /\ pathstart p = a /\ pathfinish p = a
          ==> ?q. path q /\ path_image q SUBSET s /\ pathstart q = a /\
                  pathfinish q = a /\ homotopic_paths w p q) /\
     moi_s33_char s phi
     ==> !q1 q2. path q1 /\ path_image q1 SUBSET s /\ pathstart q1 = a /\
                 pathfinish q1 = a /\
                 path q2 /\ path_image q2 SUBSET s /\ pathstart q2 = a /\
                 pathfinish q2 = a /\
                 homotopic_loops w q1 q2
                 ==> (phi q1 <=> phi q2)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "inj") (CONJUNCTS_THEN2 (LABEL_TAC "surj")
      ASSUME_TAC)))) THEN
  MAP_EVERY X_GEN_TAC [`q1:real^1->real^N`; `q2:real^1->real^N`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`w:real^N->bool`; `q1:real^1->real^N`; `q2:real^1->real^N`]
    MOI_S3KC_HOMOTOPIC_LOOPS_CONJUGATE_PATH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^1->real^N` STRIP_ASSUME_TAC) THEN
  USE_THEN "surj" (MP_TAC o SPEC `r:real^1->real^N`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r':real^1->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `path_image q1 SUBSET (w:real^N->bool) /\ path_image q2 SUBSET w /\
                path_image r' SUBSET w`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  (* x = r' ++ q2 ++ reversepath r', a loop of s at a *)
  SUBGOAL_THEN
   `path ((r':real^1->real^N) ++ q2 ++ reversepath r') /\
    path_image (r' ++ q2 ++ reversepath r') SUBSET s /\
    pathstart (r' ++ q2 ++ reversepath r') = a /\
    pathfinish (r' ++ q2 ++ reversepath r') = a`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN;
                 UNION_SUBSET; PATH_REVERSEPATH; PATH_IMAGE_REVERSEPATH;
                 PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH];
    ALL_TAC] THEN
  SUBGOAL_THEN `path_image ((r':real^1->real^N) ++ q2 ++ reversepath r') SUBSET w`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  (* q1 is homotopic rel a in w to x *)
  SUBGOAL_THEN `homotopic_paths w q1 ((r':real^1->real^N) ++ q2 ++ reversepath r')`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
    EXISTS_TAC `(r:real^1->real^N) ++ q2 ++ reversepath r` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN ASM_REWRITE_TAC[PATHSTART_JOIN] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
    ASM_REWRITE_TAC[HOMOTOPIC_PATHS_REVERSEPATH; HOMOTOPIC_PATHS_REFL;
                    PATHSTART_REVERSEPATH];
    ALL_TAC] THEN
  (* the difference q1 ++ reversepath x is null in w, hence in s *)
  SUBGOAL_THEN
   `homotopic_loops s (q1 ++ reversepath ((r':real^1->real^N) ++ q2 ++ reversepath r'))
                      (linepath(pathstart (q1 ++ reversepath (r' ++ q2 ++ reversepath r')),
                                pathstart (q1 ++ reversepath (r' ++ q2 ++ reversepath r'))))`
  ASSUME_TAC THENL
   [USE_THEN "inj" MATCH_MP_TAC THEN
    ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN;
                 UNION_SUBSET; PATH_REVERSEPATH; PATH_IMAGE_REVERSEPATH;
                 PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_IMP_HOMOTOPIC_LOOPS THEN
    ASM_SIMP_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_REVERSEPATH;
                 PATHFINISH_REVERSEPATH; PATHFINISH_LINEPATH] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
    EXISTS_TAC `((r':real^1->real^N) ++ q2 ++ reversepath r') ++
                reversepath (r' ++ q2 ++ reversepath r')` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
      ASM_REWRITE_TAC[HOMOTOPIC_PATHS_REFL; PATH_REVERSEPATH; PATH_IMAGE_REVERSEPATH;
                      PATHSTART_REVERSEPATH];
      MP_TAC(ISPECL [`w:real^N->bool`; `(r':real^1->real^N) ++ q2 ++ reversepath r'`]
        HOMOTOPIC_PATHS_RINV) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `phi:(real^1->real^N)->bool`;
    `q1 ++ reversepath ((r':real^1->real^N) ++ q2 ++ reversepath r')`]
    MOI_S3Z2_CHAR_NULL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN;
                 UNION_SUBSET; PATH_REVERSEPATH; PATH_IMAGE_REVERSEPATH;
                 PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `phi:(real^1->real^N)->bool`;
    `(r':real^1->real^N) ++ q2 ++ reversepath r'`] MOI_S3Z2_CHAR_REV) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `homotopic_loops s ((r':real^1->real^N) ++ q2 ++ reversepath r') q2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_LOOPS_CONJUGATE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `moi_s33_char s (phi:(real^1->real^N)->bool)` THEN
  REWRITE_TAC[moi_s33_char] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "hom")
    (LABEL_TAC "add"))) THEN
  REMOVE_THEN "hom" (fun th -> MP_TAC(MATCH_MP th (ASSUME
    `homotopic_loops s ((r':real^1->real^N) ++ q2 ++ reversepath r') q2`))) THEN
  USE_THEN "add" (MP_TAC o SPECL [`q1:real^1->real^N`;
    `reversepath ((r':real^1->real^N) ++ q2 ++ reversepath r')`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[PATH_REVERSEPATH; PATH_IMAGE_REVERSEPATH; PATHSTART_REVERSEPATH;
                    PATHFINISH_REVERSEPATH];
    ALL_TAC] THEN
  MESON_TAC[]);;

(* W2: loops of s freely homotopic in w have the same value. *)

let MOI_S3KC_TR_W2 = prove
 (`!s w (a:real^N) phi.
     s SUBSET w /\ path_connected s /\ a IN s /\
     (!p. path p /\ path_image p SUBSET s /\ pathfinish p = pathstart p /\
          homotopic_loops w p (linepath(pathstart p,pathstart p))
          ==> homotopic_loops s p (linepath(pathstart p,pathstart p))) /\
     (!p. path p /\ path_image p SUBSET w /\ pathstart p = a /\ pathfinish p = a
          ==> ?q. path q /\ path_image q SUBSET s /\ pathstart q = a /\
                  pathfinish q = a /\ homotopic_paths w p q) /\
     moi_s33_char s phi
     ==> !q1 q2. path q1 /\ path_image q1 SUBSET s /\ pathfinish q1 = pathstart q1 /\
                 path q2 /\ path_image q2 SUBSET s /\ pathfinish q2 = pathstart q2 /\
                 homotopic_loops w q1 q2
                 ==> (phi q1 <=> phi q2)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "inj")
      (CONJUNCTS_THEN2 (LABEL_TAC "surj") ASSUME_TAC))))) THEN
  MAP_EVERY X_GEN_TAC [`q1:real^1->real^N`; `q2:real^1->real^N`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `q1:real^1->real^N`; `a:real^N`]
    MOI_S3KC_LOOP_REBASE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g1:real^1->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `q2:real^1->real^N`; `a:real^N`]
    MOI_S3KC_LOOP_REBASE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g2:real^1->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `w:real^N->bool`; `a:real^N`;
                 `phi:(real^1->real^N)->bool`] MOI_S3KC_TR_W2A) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`(g1:real^1->real^N) ++ q1 ++ reversepath g1`;
                             `(g2:real^1->real^N) ++ q2 ++ reversepath g2`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN EXISTS_TAC `q1:real^1->real^N` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_LOOPS_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN EXISTS_TAC `q2:real^1->real^N` THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[HOMOTOPIC_LOOPS_SYM] THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_s33_char s (phi:(real^1->real^N)->bool)` THEN
  REWRITE_TAC[moi_s33_char] THEN ASM_MESON_TAC[]);;

(* The extension of phi takes on a loop p of w the value of phi on any     *)
(* loop of s freely homotopic to p in w.                                   *)

let MOI_S3KC_TR_EXT_EQ = prove
 (`!s w (a:real^N) phi.
     s SUBSET w /\ path_connected s /\ a IN s /\
     (!p. path p /\ path_image p SUBSET s /\ pathfinish p = pathstart p /\
          homotopic_loops w p (linepath(pathstart p,pathstart p))
          ==> homotopic_loops s p (linepath(pathstart p,pathstart p))) /\
     (!p. path p /\ path_image p SUBSET w /\ pathstart p = a /\ pathfinish p = a
          ==> ?q. path q /\ path_image q SUBSET s /\ pathstart q = a /\
                  pathfinish q = a /\ homotopic_paths w p q) /\
     moi_s33_char s phi
     ==> !p q. path q /\ path_image q SUBSET s /\ pathfinish q = pathstart q /\
               homotopic_loops w p q
               ==> ((?q'. path q' /\ path_image q' SUBSET s /\
                          pathfinish q' = pathstart q' /\
                          homotopic_loops w p q' /\ phi q') <=> phi q)`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    ASSUME_TAC(MATCH_MP MOI_S3KC_TR_W2 th) THEN ASSUME_TAC th) THEN
  MAP_EVERY X_GEN_TAC [`p:real^1->real^N`; `q:real^1->real^N`] THEN STRIP_TAC THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `q':real^1->real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `homotopic_loops w (q':real^1->real^N) q` ASSUME_TAC THENL
     [ASM_MESON_TAC[HOMOTOPIC_LOOPS_SYM; HOMOTOPIC_LOOPS_TRANS]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    DISCH_TAC THEN EXISTS_TAC `q:real^1->real^N` THEN ASM_REWRITE_TAC[]]);;

(* The restriction of a character of w is a character of s. *)

let MOI_S3KC_TR_RES = prove
 (`!s w:real^N->bool psi.
     s SUBSET w /\ moi_s33_char w psi
     ==> moi_s33_char s (\p. path p /\ path_image p SUBSET s /\
                             pathfinish p = pathstart p /\ psi p)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s33_char] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "hom") (LABEL_TAC "add")))) THEN
  REPEAT CONJ_TAC THENL
   [SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`p:real^1->real^N`; `q:real^1->real^N`] THEN DISCH_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_LOOP) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_PATH) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "hom" MATCH_MP_TAC THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`p:real^1->real^N`; `q:real^1->real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `pathfinish p = pathstart (q:real^1->real^N)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN;
                 UNION_SUBSET] THEN
    USE_THEN "add" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* The extension of a character of s is a character of w. *)

let MOI_S3KC_TR_EXT = prove
 (`!s w (a:real^N) phi.
     s SUBSET w /\ path_connected s /\ path_connected w /\ a IN s /\
     (!p. path p /\ path_image p SUBSET s /\ pathfinish p = pathstart p /\
          homotopic_loops w p (linepath(pathstart p,pathstart p))
          ==> homotopic_loops s p (linepath(pathstart p,pathstart p))) /\
     (!p. path p /\ path_image p SUBSET w /\ pathstart p = a /\ pathfinish p = a
          ==> ?q. path q /\ path_image q SUBSET s /\ pathstart q = a /\
                  pathfinish q = a /\ homotopic_paths w p q) /\
     moi_s33_char s phi
     ==> moi_s33_char w
           (\p. path p /\ path_image p SUBSET w /\ pathfinish p = pathstart p /\
                ?q. path q /\ path_image q SUBSET s /\ pathfinish q = pathstart q /\
                    homotopic_loops w p q /\ phi q)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "inj") (CONJUNCTS_THEN2 (LABEL_TAC "surj")
        ASSUME_TAC)))))) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `w:real^N->bool`; `a:real^N`;
                 `phi:(real^1->real^N)->bool`] MOI_S3KC_TR_EXT_EQ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "eq")] THEN
  GEN_REWRITE_TAC I [moi_s33_char] THEN BETA_TAC THEN REPEAT CONJ_TAC THENL
   [SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`p:real^1->real^N`; `q:real^1->real^N`] THEN DISCH_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_LOOP) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_PATH) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[HOMOTOPIC_LOOPS_SYM; HOMOTOPIC_LOOPS_TRANS];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`p:real^1->real^N`; `p':real^1->real^N`] THEN STRIP_TAC THEN
  (* conjugate both loops to a *)
  MP_TAC(ISPECL [`w:real^N->bool`; `p:real^1->real^N`; `a:real^N`]
    MOI_S3KC_LOOP_REBASE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `path ((g:real^1->real^N) ++ p' ++ reversepath g) /\
    path_image (g ++ p' ++ reversepath g) SUBSET w /\
    pathstart (g ++ p' ++ reversepath g) = a /\
    pathfinish (g ++ p' ++ reversepath g) = a /\
    homotopic_loops w (g ++ p' ++ reversepath g) p'`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN;
                 UNION_SUBSET; PATH_REVERSEPATH; PATH_IMAGE_REVERSEPATH;
                 PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH] THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_CONJUGATE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "surj" (MP_TAC o SPEC `(g:real^1->real^N) ++ p ++ reversepath g`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^1->real^N` STRIP_ASSUME_TAC) THEN
  USE_THEN "surj" (MP_TAC o SPEC `(g:real^1->real^N) ++ p' ++ reversepath g`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q':real^1->real^N` STRIP_ASSUME_TAC) THEN
  (* the three free homotopies *)
  SUBGOAL_THEN `homotopic_loops w p (q:real^1->real^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
    EXISTS_TAC `(g:real^1->real^N) ++ p ++ reversepath g` THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[HOMOTOPIC_LOOPS_SYM] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC HOMOTOPIC_PATHS_IMP_HOMOTOPIC_LOOPS THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `homotopic_loops w p' (q':real^1->real^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
    EXISTS_TAC `(g:real^1->real^N) ++ p' ++ reversepath g` THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[HOMOTOPIC_LOOPS_SYM] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC HOMOTOPIC_PATHS_IMP_HOMOTOPIC_LOOPS THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pathfinish p = pathstart (p':real^1->real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `homotopic_loops w (p ++ p') ((q:real^1->real^N) ++ q')` ASSUME_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
    EXISTS_TAC `(g:real^1->real^N) ++ (p ++ p') ++ reversepath g` THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[HOMOTOPIC_LOOPS_SYM] THEN
      MATCH_MP_TAC HOMOTOPIC_LOOPS_CONJUGATE THEN
      ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN;
                   UNION_SUBSET];
      ALL_TAC] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_IMP_HOMOTOPIC_LOOPS THEN
    ASM_SIMP_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHFINISH_REVERSEPATH] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
    EXISTS_TAC `((g:real^1->real^N) ++ p ++ reversepath g) ++ (g ++ p' ++ reversepath g)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S3KC_CONJ_JOIN THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* evaluate *)
  SUBGOAL_THEN
   `path ((q:real^1->real^N) ++ q') /\ path_image (q ++ q') SUBSET s /\
    pathfinish (q ++ q') = pathstart (q ++ q')`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN;
                 UNION_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `path ((p:real^1->real^N) ++ p') /\ path_image (p ++ p') SUBSET w /\
    pathfinish (p ++ p') = pathstart (p ++ p')`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN;
                 UNION_SUBSET];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "eq" (fun th ->
    MP_TAC(SPECL [`(p:real^1->real^N) ++ p'`; `(q:real^1->real^N) ++ q'`] th) THEN
    MP_TAC(SPECL [`p:real^1->real^N`; `q:real^1->real^N`] th) THEN
    MP_TAC(SPECL [`p':real^1->real^N`; `q':real^1->real^N`] th)) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN(fun th -> REWRITE_TAC[th])) THEN
  UNDISCH_TAC `moi_s33_char s (phi:(real^1->real^N)->bool)` THEN
  REWRITE_TAC[moi_s33_char] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[]);;

(* CHAR_TRANSFER. *)

let CHAR_TRANSFER = prove
 (MOI_S33_CHAR_TRANSFER,
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `w:real^N->bool`] THEN
  REWRITE_TAC[moi_s33_pi1] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "inj")
      (X_CHOOSE_THEN `a:real^N` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "surj"))))))) THEN
  MATCH_MP_TAC BIJECTIONS_HAS_SIZE_EQ THEN
  EXISTS_TAC `\phi (p:real^1->real^N).
                path p /\ path_image p SUBSET w /\ pathfinish p = pathstart p /\
                ?q. path q /\ path_image q SUBSET s /\ pathfinish q = pathstart q /\
                    homotopic_loops w p q /\ phi q` THEN
  EXISTS_TAC `\psi (p:real^1->real^N).
                path p /\ path_image p SUBSET s /\ pathfinish p = pathstart p /\ psi p` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
   [X_GEN_TAC `phi:(real^1->real^N)->bool` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S3KC_TR_EXT THEN EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `w:real^N->bool`; `a:real^N`;
                   `phi:(real^1->real^N)->bool`] MOI_S3KC_TR_EXT_EQ) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `p:real^1->real^N` THEN EQ_TAC THENL
     [STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`p:real^1->real^N`; `p:real^1->real^N`]) THEN
      ASM_REWRITE_TAC[HOMOTOPIC_LOOPS_REFL] THEN ASM_MESON_TAC[];
      DISCH_TAC THEN
      SUBGOAL_THEN `path (p:real^1->real^N) /\ path_image p SUBSET (s:real^N->bool) /\ pathfinish p = pathstart p`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `moi_s33_char s (phi:(real^1->real^N)->bool)` THEN
        REWRITE_TAC[moi_s33_char] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `path_image (p:real^1->real^N) SUBSET (w:real^N->bool)` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `p:real^1->real^N` THEN
      ASM_REWRITE_TAC[HOMOTOPIC_LOOPS_REFL]];
    X_GEN_TAC `psi:(real^1->real^N)->bool` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S3KC_TR_RES THEN EXISTS_TAC `w:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `p:real^1->real^N` THEN EQ_TAC THENL
     [STRIP_TAC THEN
      UNDISCH_TAC `moi_s33_char w (psi:(real^1->real^N)->bool)` THEN
      REWRITE_TAC[moi_s33_char] THEN ASM_MESON_TAC[];
      DISCH_TAC THEN
      SUBGOAL_THEN `path (p:real^1->real^N) /\ path_image p SUBSET (w:real^N->bool) /\ pathfinish p = pathstart p`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `moi_s33_char w (psi:(real^1->real^N)->bool)` THEN
        REWRITE_TAC[moi_s33_char] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `w:real^N->bool`; `a:real^N`] MOI_S3KC_TR_W1) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `p:real^1->real^N`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `q:real^1->real^N` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `q:real^1->real^N` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `moi_s33_char w (psi:(real^1->real^N)->bool)` THEN
      REWRITE_TAC[moi_s33_char] THEN ASM_MESON_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Part 4: DISK_RECOG.  The body is POLY_DISK of pc_moi_s30_tame: its       *)
(* antecedents are SURFACE_TRIANG on SURF_LOCAL, Z2_SC_BOUNDARY on the      *)
(* antecedent CHAR_COUNT_BD, and SURFACE_EULER_PLANAR.                      *)
(* ------------------------------------------------------------------------- *)

let DISK_RECOG = prove
 (MOI_S33_DISK_RECOG,
  DISCH_TAC THEN
  MP_TAC(MP POLY_DISK (end_itlist CONJ
    [MP SURFACE_TRIANG SURF_LOCAL;
     MP Z2_SC_BOUNDARY (ASSUME MOI_S33_CHAR_COUNT_BD);
     SURFACE_EULER_PLANAR])) THEN
  DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`d:real^N->bool`; `j:real^N->bool`] THEN
  REWRITE_TAC[disk_with_boundary] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `f:real^2->real^N` (X_CHOOSE_THEN `g:real^N->real^2`
      STRIP_ASSUME_TAC))
    ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `g:real^N->real^2` THEN
  ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON]);;

(* ------------------------------------------------------------------------- *)
(* Part 5: charts of the holed disk model.  Interior points have plane      *)
(* charts (balls).  Frontier points have half-plane charts: on the outer    *)
(* rectangle from a triangulation of the convex rectangle (MOI_S3TM_DISK_TRI *)
(* and SURF_CHARTS), on a hole from the translated square annulus           *)
(* (ANNULUS_COMPLEX and SURF_CHARTS), moved to the model through an open    *)
(* set on which the two sets agree (MOI_S3TM_CHART_TRANSFER).               *)
(* ------------------------------------------------------------------------- *)

let MOI_S3KC_INTERIOR_R2 = prove
 (`!(x:real^2->bool) y. y IN interior x ==> moi_s28_locally_r2 x y`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERIOR]) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[moi_s28_locally_r2] THEN EXISTS_TAC `ball(y:real^2,e)` THEN
  ASM_SIMP_TAC[CENTRE_IN_BALL; HOMEOMORPHIC_BALL_UNIV] THEN
  MATCH_MP_TAC OPEN_SUBSET THEN ASM_REWRITE_TAC[OPEN_BALL]);;

(* A polytope in the plane with nonempty interior is a disk bounded by its  *)
(* frontier, and has half-plane charts at its frontier points.              *)

let MOI_S3KC_POLYTOPE_DISK = prove
 (`!x:real^2->bool.
     polytope x /\ ~(interior x = {})
     ==> ?(f:real^2->real^2) g. homeomorphism (cball(vec 0,&1),x) (f,g) /\
               IMAGE f (sphere(vec 0,&1)) = frontier x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `convex (x:real^2->bool) /\ compact x` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX; POLYTOPE_IMP_COMPACT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`x:real^2->bool`; `vec 0:real^2`; `&1`]
    HOMEOMORPHIC_CONVEX_COMPACT_CBALL) THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN
  ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:real^2->real^2` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^2->real^2` THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM FRONTIER_CBALL] THEN MATCH_MP_TAC MOI_S3TM_HOMEO_FRONTIER THEN
  EXISTS_TAC `g:real^2->real^2` THEN
  ASM_SIMP_TAC[CLOSED_CBALL; COMPACT_IMP_CLOSED]);;

let MOI_S3KC_POLYTOPE_HALF = prove
 (`!(x:real^2->bool) y.
     polytope x /\ ~(interior x = {}) /\ y IN frontier x
     ==> moi_s28_locally_half x y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `x:real^2->bool` MOI_S3KC_POLYTOPE_DISK) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^2` (X_CHOOSE_THEN `g:real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `pl_polyhedron (x:real^2->bool)` MP_TAC THENL
   [ASM_SIMP_TAC[POLYTOPE_IMP_PL_POLYHEDRON]; ALL_TAC] THEN
  REWRITE_TAC[PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:(real^2->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`m:(real^2->bool)->bool`; `f:real^2->real^2`; `g:real^2->real^2`]
    MOI_S3TM_DISK_TRI) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `m:(real^2->bool)->bool` SURF_CHARTS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MOI_SCF_SC_FINITE]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^2` o CONJUNCT1 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* The translated square annulus has half-plane charts at its inner square. *)

let MOI_S3KC_ANN_HALF = prove
 (`!(c:real^2) y.
     y IN relative_frontier
            (IMAGE (\x. c + x) (interval[--vector[&1;&1],vector[&1;&1]]))
     ==> moi_s28_locally_half (IMAGE (\x. c + x) moi_fps_ann) y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[RELATIVE_FRONTIER_TRANSLATION] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `pl_annulus_with_ends (IMAGE (\x:real^2. c + x) moi_fps_ann)
      (IMAGE (\x:real^2. c + x)
        (relative_frontier (interval[--vector[&1;&1],vector[&1;&1]])))
      (IMAGE (\x:real^2. c + x)
        (relative_frontier (interval[--vector[&2;&2],vector[&2;&2]])))`
  MP_TAC THENL
   [REWRITE_TAC[pl_annulus_with_ends; GSYM moi_fps_ann] THEN
    MAP_EVERY EXISTS_TAC [`\x:real^2. c + x`; `\x:real^2. --c + x`] THEN
    REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`IMAGE (\x:real^2. c + x) moi_fps_ann`; `c:real^2`]
      MOI_CMB_TRANSLATION_PL_HOMEOMORPHISM) THEN
    SIMP_TAC[PL_POLYHEDRON_TRANSLATION; MOI_FPS_ANN_PL_POLYHEDRON] THEN
    REWRITE_TAC[GSYM IMAGE_o; o_DEF; VECTOR_ARITH `--c + c + x:real^2 = x`; IMAGE_ID];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP ANNULUS_COMPLEX) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:(real^2->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `d:(real^2->bool)->bool` SURF_CHARTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^2` o CONJUNCT1 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[IN_UNION] THEN SIMP_TAC[]);;

(* Coordinates of the model and of the translated annulus. *)

let MOI_S3KC_IN_HD = prove
 (`!k z:real^2.
     z IN holed_disk_model k <=>
     (&0 <= z$1 /\ z$1 <= &4 * &k + &4 /\ &0 <= z$2 /\ z$2 <= &4) /\
     ~(?j. j < k /\ &4 * &j + &2 < z$1 /\ z$1 < &4 * &j + &4 /\
           &1 < z$2 /\ z$2 < &3)`,
  REWRITE_TAC[holed_disk_model; IN_DIFF; IN_INTERVAL; UNIONS_GSPEC; IN_ELIM_THM;
              DIMINDEX_2; FORALL_2; VECTOR_2; VEC_COMPONENT] THEN
  REWRITE_TAC[CONJ_ACI]);;

let MOI_S3KC_IN_ANN = prove
 (`!c z:real^2.
     z IN IMAGE (\x. c + x) moi_fps_ann <=>
     (abs(z$1 - c$1) <= &2 /\ abs(z$2 - c$2) <= &2) /\
     ~(abs(z$1 - c$1) < &1 /\ abs(z$2 - c$2) < &1)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `z IN IMAGE (\x:real^2. c + x) moi_fps_ann <=> (z - c) IN moi_fps_ann`
  SUBST1_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[VECTOR_ARITH `z:real^2 = c + x <=> x = z - c`];
    ALL_TAC] THEN
  REWRITE_TAC[moi_fps_ann; IN_DIFF; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2;
              VECTOR_NEG_COMPONENT; VECTOR_SUB_COMPONENT] THEN
  REAL_ARITH_TAC);;

let MOI_S3KC_HC_TRANSLATE = prove
 (`!i. moi_fsb_hc i =
       IMAGE (\x. vector[&4 * &i + &3; &2] + x) (interval[--vector[&1;&1],vector[&1;&1]])`,
  GEN_TAC THEN REWRITE_TAC[GSYM(CONJUNCT1 INTERVAL_TRANSLATION); moi_fsb_hc] THEN
  SUBGOAL_THEN `vector[&4 * &i + &3; &2] + --vector[&1;&1] = vector[&4 * &i + &2; &1]:real^2 /\
                vector[&4 * &i + &3; &2] + vector[&1;&1] = vector[&4 * &i + &4; &3]:real^2`
  (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_ADD_COMPONENT;
              VECTOR_NEG_COMPONENT] THEN
  REAL_ARITH_TAC);;

(* Near hole i the model agrees with the annulus around it. *)

let MOI_S3KC_HOLE_AGREE = prove
 (`!k i. i < k
         ==> IMAGE (\x. vector[&4 * &i + &3; &2] + x) moi_fps_ann INTER
             interval(vector[&4 * &i + &1; &0],vector[&4 * &i + &5; &4]) =
             holed_disk_model k INTER
             interval(vector[&4 * &i + &1; &0],vector[&4 * &i + &5; &4]) /\
             moi_fsb_hc i SUBSET
             interval(vector[&4 * &i + &1; &0],vector[&4 * &i + &5; &4])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= &i /\ &i + &1 <= &k` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POS; REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[moi_fsb_hc; SUBSET_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
    ASM_REAL_ARITH_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_INTER] THEN X_GEN_TAC `z:real^2` THEN
  REWRITE_TAC[MOI_S3KC_IN_ANN; MOI_S3KC_IN_HD; IN_INTERVAL; DIMINDEX_2; FORALL_2;
              VECTOR_2] THEN
  ASM_CASES_TAC `(&4 * &i + &1 < (z:real^2)$1 /\ z$1 < &4 * &i + &5) /\
                 (&0 < z$2 /\ z$2 < &4)` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  SUBGOAL_THEN
   `(?j. j < k /\ &4 * &j + &2 < (z:real^2)$1 /\ z$1 < &4 * &j + &4 /\
         &1 < z$2 /\ z$2 < &3) <=>
    (&4 * &i + &2 < z$1 /\ z$1 < &4 * &i + &4 /\ &1 < z$2 /\ z$2 < &3)`
  SUBST1_TAC THENL
   [EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
      REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (ARITH_RULE `(j:num) < i \/ j = i \/ i < j`) THENL
       [SUBGOAL_THEN `&j + &1 <= &i` MP_TAC THENL
         [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
          UNDISCH_TAC `j:num < i` THEN ARITH_TAC; ALL_TAC] THEN
        ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[];
        SUBGOAL_THEN `&i + &1 <= &j` MP_TAC THENL
         [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
          UNDISCH_TAC `i:num < j` THEN ARITH_TAC; ALL_TAC] THEN
        ASM_REAL_ARITH_TAC];
      STRIP_TAC THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The charts of the model. *)

let MOI_S3KC_HD_CHARTS = prove
 (`!k y. y IN holed_disk_model k
         ==> (y IN frontier (holed_disk_model k)
              ==> moi_s28_locally_half (holed_disk_model k) y) /\
             (~(y IN frontier (holed_disk_model k))
              ==> moi_s28_locally_r2 (holed_disk_model k) y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [ALL_TAC;
    DISCH_TAC THEN MATCH_MP_TAC MOI_S3KC_INTERIOR_R2 THEN
    UNDISCH_TAC `~((y:real^2) IN frontier (holed_disk_model k))` THEN
    UNDISCH_TAC `(y:real^2) IN holed_disk_model k` THEN
    MP_TAC(SPEC `k:num` MOI_FSB_HD_POLY) THEN
    SIMP_TAC[frontier; CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN SET_TAC[]] THEN
  MP_TAC(SPEC `k:num` MOI_FSB_HD_FACTS) THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(interior (moi_fsb_hq k) = {})` ASSUME_TAC THENL
   [MP_TAC(ISPEC `moi_fsb_hr k` INTERIOR_SUBSET) THEN ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MOI_FSB_HD_FRONTIER; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
  STRIP_TAC THENL
   [(* the outer rectangle *)
    MP_TAC(ISPECL [`moi_fsb_hq k`; `holed_disk_model k`;
                   `moi_fsb_hq k INTER ((:real^2) DIFF UNIONS {moi_fsb_hc i | i < k})`;
                   `y:real^2`] MOI_S3TM_CHART_TRANSFER) THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN `open ((:real^2) DIFF UNIONS {moi_fsb_hc i | i < k})` ASSUME_TAC THENL
       [MATCH_MP_TAC OPEN_DIFF THEN REWRITE_TAC[OPEN_UNIV] THEN
        MATCH_MP_TAC CLOSED_UNIONS THEN
        ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
        SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT; FORALL_IN_IMAGE; moi_fsb_hc;
                 CLOSED_INTERVAL];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `moi_fsb_hq k INTER ((:real^2) DIFF UNIONS {moi_fsb_hc i | i < k}) =
        holed_disk_model k INTER ((:real^2) DIFF UNIONS {moi_fsb_hc i | i < k})`
      ASSUME_TAC THENL
       [REWRITE_TAC[MOI_FSB_HD_EQ; EXTENSION; IN_INTER; IN_DIFF; IN_UNIV; UNIONS_GSPEC;
                    IN_ELIM_THM] THEN
        MESON_TAC[INTERIOR_SUBSET; SUBSET];
        ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[OPEN_IN_OPEN_INTER];
        ALL_TAC] THEN
      SUBGOAL_THEN `(y:real^2) IN frontier (moi_fsb_hq k)` MP_TAC THENL
       [UNDISCH_TAC `(y:real^2) IN relative_frontier (moi_fsb_hq k)` THEN
        ASM_SIMP_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR];
        ALL_TAC] THEN
      SIMP_TAC[frontier; CLOSURE_CLOSED; COMPACT_IMP_CLOSED; POLYTOPE_IMP_COMPACT;
               ASSUME `polytope (moi_fsb_hq k)`] THEN
      REWRITE_TAC[IN_DIFF; IN_INTER; IN_UNIV; UNIONS_GSPEC; IN_ELIM_THM] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      MP_TAC(ISPEC `moi_fsb_hr k` INTERIOR_SUBSET) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
        can (find_term (fun t -> t = `moi_fsb_hc`)) (concl th) &&
        is_forall (concl th) && length(fst(strip_forall(concl th))) = 1)) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~((y:real^2) IN interior (moi_fsb_hq k))` THEN
      UNDISCH_TAC `moi_fsb_hr k SUBSET interior (moi_fsb_hq k)` THEN
      UNDISCH_TAC `(y:real^2) IN moi_fsb_hc i` THEN SET_TAC[];
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2)] THEN
    MATCH_MP_TAC MOI_S3KC_POLYTOPE_HALF THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:real^2) IN relative_frontier (moi_fsb_hq k)` THEN
    ASM_SIMP_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR];
    (* hole i *)
    MP_TAC(SPECL [`k:num`; `i:num`] MOI_S3KC_HOLE_AGREE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`IMAGE (\x. vector[&4 * &i + &3; &2] + x) moi_fps_ann`;
                   `holed_disk_model k`;
                   `IMAGE (\x. vector[&4 * &i + &3; &2] + x) moi_fps_ann INTER
                    interval(vector[&4 * &i + &1; &0],vector[&4 * &i + &5; &4])`;
                   `y:real^2`] MOI_S3TM_CHART_TRANSFER) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [SIMP_TAC[OPEN_IN_OPEN_INTER; OPEN_INTERVAL];
        ASM_REWRITE_TAC[] THEN SIMP_TAC[OPEN_IN_OPEN_INTER; OPEN_INTERVAL];
        ASM_REWRITE_TAC[IN_INTER] THEN
        SUBGOAL_THEN `relative_frontier (moi_fsb_hc i) SUBSET moi_fsb_hc i` MP_TAC THENL
         [REWRITE_TAC[relative_frontier] THEN
          SIMP_TAC[moi_fsb_hc; CLOSURE_CLOSED; CLOSED_INTERVAL] THEN SET_TAC[];
          ASM SET_TAC[]]];
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2)] THEN
    MATCH_MP_TAC MOI_S3KC_ANN_HALF THEN
    ASM_REWRITE_TAC[GSYM MOI_S3KC_HC_TRANSLATE]]);;

(* ------------------------------------------------------------------------- *)
(* Part 6: HOLED_RECOG.  A triangulation c0 of the model is a               *)
(* combinatorial surface with boundary the frontier (charts of Part 5 and  *)
(* SURF_LOCAL); a triangulation d of a is one with boundary the image of    *)
(* the frontier (SURF_INVARIANT); the character counts give chi d = 1 - k;  *)
(* the frontier has k + 1 components; MOI_FSB_PLANAR_EQ.                    *)
(* ------------------------------------------------------------------------- *)

(* The relative frontier of a planar polytope with interior is a compact     *)
(* connected nonempty set, its frontier.                                     *)

let MOI_S3KC_POLYTOPE_RF = prove
 (`!x:real^2->bool.
     polytope x /\ ~(interior x = {})
     ==> compact (relative_frontier x) /\ connected (relative_frontier x) /\
         ~(relative_frontier x = {}) /\ relative_frontier x = frontier x`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR] THEN
  MP_TAC(ISPEC `x:real^2->bool` MOI_S3KC_POLYTOPE_DISK) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^2` (X_CHOOSE_THEN `g:real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `IMAGE (f:real^2->real^2) (sphere(vec 0,&1)) = frontier x` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `(f:real^2->real^2) continuous_on sphere(vec 0,&1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SPHERE_SUBSET_CBALL]; ALL_TAC] THEN
  ASM_SIMP_TAC[COMPACT_CONTINUOUS_IMAGE; COMPACT_SPHERE; CONNECTED_CONTINUOUS_IMAGE;
               CONNECTED_SPHERE; DIMINDEX_2; LE_REFL; IMAGE_EQ_EMPTY; SPHERE_EQ_EMPTY] THEN
  REAL_ARITH_TAC);;

(* The boundary circles of the model: k + 1 disjoint compact connected sets. *)

let MOI_S3KC_HD_BD_FAMILY = prove
 (`!k. ?u. FINITE u /\ CARD u = k + 1 /\ UNIONS u = frontier (holed_disk_model k) /\
           (!c. c IN u ==> compact c /\ connected c /\ ~(c = {})) /\
           (!c c'. c IN u /\ c' IN u /\ ~(c = c') ==> DISJOINT c c')`,
  GEN_TAC THEN
  MP_TAC(SPEC `k:num` MOI_FSB_HD_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "hc") (LABEL_TAC "dis")))))) THEN
  SUBGOAL_THEN `~(interior (moi_fsb_hq k) = {})` ASSUME_TAC THENL
   [MP_TAC(ISPEC `moi_fsb_hr k` INTERIOR_SUBSET) THEN ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `moi_fsb_hq k` MOI_S3KC_POLYTOPE_RF) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `DISJOINT (relative_frontier (moi_fsb_hq k)) (interior (moi_fsb_hq k))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[frontier] THEN SET_TAC[]; ALL_TAC] THEN
  UNDISCH_THEN `relative_frontier (moi_fsb_hq k) = frontier (moi_fsb_hq k)` (K ALL_TAC) THEN
  SUBGOAL_THEN
   `!i. i < k
        ==> compact (relative_frontier (moi_fsb_hc i)) /\
            connected (relative_frontier (moi_fsb_hc i)) /\
            ~(relative_frontier (moi_fsb_hc i) = {}) /\
            relative_frontier (moi_fsb_hc i) SUBSET moi_fsb_hc i /\
            relative_frontier (moi_fsb_hc i) SUBSET interior (moi_fsb_hq k)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "hc" (fun th -> MP_TAC(MATCH_MP th (ASSUME `i:num < k`))) THEN STRIP_TAC THEN
    MP_TAC(ISPEC `moi_fsb_hc i` MOI_S3KC_POLYTOPE_RF) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `frontier (moi_fsb_hc i) SUBSET moi_fsb_hc i` ASSUME_TAC THENL
     [REWRITE_TAC[frontier] THEN
      SIMP_TAC[moi_fsb_hc; CLOSURE_CLOSED; CLOSED_INTERVAL] THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `moi_fsb_hr k` INTERIOR_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `relative_frontier (moi_fsb_hq k) INSERT
              IMAGE (\i. relative_frontier (moi_fsb_hc i)) {i | i < k}` THEN
  SUBGOAL_THEN `UNIONS (relative_frontier (moi_fsb_hq k) INSERT
                        IMAGE (\i. relative_frontier (moi_fsb_hc i)) {i | i < k}) =
                frontier (holed_disk_model k)` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[UNIONS_INSERT; MOI_FSB_HD_FRONTIER] THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[FINITE_INSERT; FINITE_IMAGE; FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[FORALL_IN_INSERT; FORALL_IN_IMAGE; IN_INSERT; IN_IMAGE; IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!i j. i < k /\ j < k /\ ~(i = j)
          ==> DISJOINT (relative_frontier (moi_fsb_hc i)) (relative_frontier (moi_fsb_hc j))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "dis" (fun th -> MP_TAC(MATCH_MP th (ASSUME `~(i:num = j)`))) THEN
    FIRST_X_ASSUM((fun th -> MP_TAC(SPEC `i:num` th) THEN MP_TAC(SPEC `j:num` th)) o
      check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> t = `relative_frontier (moi_fsb_hc i)`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* the count *)
    SUBGOAL_THEN `CARD (IMAGE (\i. relative_frontier (moi_fsb_hc i)) {i | i < k}) = k`
    ASSUME_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `CARD {i:num | i < k}` THEN CONJ_TAC THENL
       [MATCH_MP_TAC CARD_IMAGE_INJ THEN REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
        MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
        MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`] o check (fun th ->
          is_forall (concl th) && length(fst(strip_forall(concl th))) = 2 &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "relative_frontier")) (concl th))) THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
          is_forall (concl th) && length(fst(strip_forall(concl th))) = 1 &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "relative_frontier")) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        REWRITE_TAC[CARD_NUMSEG_LT]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[CARD_CLAUSES; FINITE_IMAGE; FINITE_NUMSEG_LT] THEN
    COND_CASES_TAC THENL [ALL_TAC; ARITH_TAC] THEN
    MATCH_MP_TAC(TAUT `F ==> p`) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb (concl th) &&
      can (find_term (fun t -> aconv t `IMAGE (\i. relative_frontier (moi_fsb_hc i)) {i | i < k}`))
          (concl th))) THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      is_forall (concl th) && length(fst(strip_forall(concl th))) = 1 &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "relative_frontier")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `DISJOINT (relative_frontier (moi_fsb_hq k)) (interior (moi_fsb_hq k))` THEN
    UNDISCH_TAC `~(relative_frontier (moi_fsb_hq k) = {})` THEN ASM_REWRITE_TAC[] THEN
    SET_TAC[];
    (* the members *)
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      is_forall (concl th) && length(fst(strip_forall(concl th))) = 1 &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "relative_frontier")) (concl th))) THEN
    ASM_SIMP_TAC[];
    (* disjointness *)
    MAP_EVERY X_GEN_TAC [`c:real^2->bool`; `c':real^2->bool`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (DISJ_CASES_THEN STRIP_ASSUME_TAC)
      (CONJUNCTS_THEN2 (DISJ_CASES_THEN STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    TRY(UNDISCH_TAC `~(c:real^2->bool = c')` THEN ASM_REWRITE_TAC[] THEN NO_TAC) THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `x:num` o check (fun th ->
        is_forall (concl th) && length(fst(strip_forall(concl th))) = 1 &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "relative_frontier")) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `DISJOINT (relative_frontier (moi_fsb_hq k)) (interior (moi_fsb_hq k))` THEN
      SET_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `x:num` o check (fun th ->
        is_forall (concl th) && length(fst(strip_forall(concl th))) = 1 &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "relative_frontier")) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `DISJOINT (relative_frontier (moi_fsb_hq k)) (interior (moi_fsb_hq k))` THEN
      SET_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `~(c:real^2->bool = c')` THEN ASM_REWRITE_TAC[]]]);;

(* A homeomorphism carries such a family to one of the same kind. *)

let MOI_S3KC_IMAGE_FAMILY = prove
 (`!(f:real^M->real^N) g s t u.
     homeomorphism (s,t) (f,g) /\ UNIONS u SUBSET s /\ FINITE u /\
     (!c. c IN u ==> compact c /\ connected c /\ ~(c = {})) /\
     (!c c'. c IN u /\ c' IN u /\ ~(c = c') ==> DISJOINT c c')
     ==> FINITE (IMAGE (IMAGE f) u) /\ CARD (IMAGE (IMAGE f) u) = CARD u /\
         UNIONS (IMAGE (IMAGE f) u) = IMAGE f (UNIONS u) /\
         (!c. c IN IMAGE (IMAGE f) u ==> compact c /\ connected c /\ ~(c = {})) /\
         (!c c'. c IN IMAGE (IMAGE f) u /\ c' IN IMAGE (IMAGE f) u /\ ~(c = c')
                 ==> DISJOINT c c')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `!c. c IN u ==> c SUBSET (s:real^M->bool)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!c c'. c IN u /\ c' IN u /\ IMAGE (f:real^M->real^N) c = IMAGE f c' ==> c = c'`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `IMAGE (g:real^N->real^M) (IMAGE f c) = c /\
                  IMAGE (g:real^N->real^M) (IMAGE f c') = c'` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC(SET_RULE
       `(!x. x IN s ==> (g:real^N->real^M) ((f:real^M->real^N) x) = x) /\ c SUBSET s
        ==> IMAGE g (IMAGE f c) = c`) THEN
      ASM_SIMP_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_UNIONS] THEN
  CONJ_TAC THENL [MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN CONJ_TAC THENL
   [X_GEN_TAC `c:real^M->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(f:real^M->real^N) continuous_on c` ASSUME_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
    ASM_SIMP_TAC[COMPACT_CONTINUOUS_IMAGE; CONNECTED_CONTINUOUS_IMAGE; IMAGE_EQ_EMPTY];
    X_GEN_TAC `c:real^M->bool` THEN DISCH_TAC THEN
    X_GEN_TAC `c':real^M->bool` THEN DISCH_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `DISJOINT (c:real^M->bool) c'` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> t = `DISJOINT:(real^M->bool)->(real^M->bool)->bool`))
            (concl th) && is_forall (concl th))) THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `c SUBSET (s:real^M->bool) /\ c' SUBSET s` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `!x:real^M. x IN s ==> (g:real^N->real^M) (f x) = x` THEN
    SET_TAC[]]);;

(* The model is connected: a union of rectangles that all meet a connected *)
(* frame.                                                                   *)

let MOI_S3KC_HD_CONNECTED = prove
 (`!k. connected (holed_disk_model k)`,
  GEN_TAC THEN REWRITE_TAC[MOI_FSB_HD_UNION] THEN
  REWRITE_TAC[UNIONS_UNION; UNIONS_INSERT; UNIONS_0; UNION_EMPTY] THEN
  ABBREV_TAC `s0 = interval[vec 0:real^2,vector[&4 * &k + &4; &1]] UNION
                   interval[vector[&0; &3]:real^2,vector[&4 * &k + &4; &4]] UNION
                   interval[vector[&4 * &k; &1]:real^2,vector[&4 * &k + &4; &3]]` THEN
  SUBGOAL_THEN `&0 <= &k` ASSUME_TAC THENL [REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `connected (s0:real^2->bool) /\ vec 0 IN s0 /\
                !i. i < k ==> vector[&4 * &i; &1] IN s0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s0" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_UNION THEN REWRITE_TAC[CONNECTED_INTERVAL] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONNECTED_UNION THEN REWRITE_TAC[CONNECTED_INTERVAL] THEN
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
        EXISTS_TAC `vector[&4 * &k; &3]:real^2`;
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_UNION] THEN
        EXISTS_TAC `vector[&4 * &k; &1]:real^2`] THEN
      REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2; VEC_COMPONENT] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[IN_UNION; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2; VEC_COMPONENT] THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `&i + &1 <= &k` MP_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= &i` MP_TAC THENL [REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
      REWRITE_TAC[IN_UNION; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2; VEC_COMPONENT] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `s0 UNION UNIONS {interval[vector[&4 * &i; &1]:real^2,vector[&4 * &i + &2; &3]] | i | i < k} =
    UNIONS ((s0:real^2->bool) INSERT
            IMAGE (\i. s0 UNION interval[vector[&4 * &i; &1],vector[&4 * &i + &2; &3]])
                  {i | i < k})`
  SUBST1_TAC THENL
   [REWRITE_TAC[UNIONS_INSERT; UNIONS_IMAGE; UNIONS_GSPEC; EXTENSION; IN_UNION;
                IN_ELIM_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_UNIONS THEN
  REWRITE_TAC[FORALL_IN_INSERT; FORALL_IN_IMAGE; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN MATCH_MP_TAC CONNECTED_UNION THEN
    ASM_REWRITE_TAC[CONNECTED_INTERVAL; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `vector[&4 * &i; &1]:real^2` THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `&0 <= &i` MP_TAC THENL [REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
    REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2] THEN REAL_ARITH_TAC;
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTERS; FORALL_IN_INSERT; FORALL_IN_IMAGE;
                IN_ELIM_THM] THEN
    EXISTS_TAC `vec 0:real^2` THEN ASM_SIMP_TAC[IN_UNION]]);;

(* A triangulation of the model is a combinatorial surface bounded by the  *)
(* frontier.                                                                *)

let MOI_S3KC_HD_COMPLEX = prove
 (`!k (c0:(real^2->bool)->bool).
     simplicial_complex c0 /\ UNIONS c0 = holed_disk_model k
     ==> FINITE c0 /\ combinatorial_manifold_with_boundary 2 c0 /\
         surface_boundary c0 = frontier (holed_disk_model k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (c0:(real^2->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SCF_SC_FINITE]; ALL_TAC] THEN
  MP_TAC(ISPEC `c0:(real^2->bool)->bool` SURF_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`k:num`; `y:real^2`] MOI_S3KC_HD_CHARTS) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^2` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_CASES_TAC `(y:real^2) IN holed_disk_model k` THEN ASM_REWRITE_TAC[] THENL
   [MP_TAC(SPECL [`k:num`; `y:real^2`] MOI_S3KC_HD_CHARTS) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[MOI_S8TA_HALF_NOT_R2];
    UNDISCH_TAC `~((y:real^2) IN holed_disk_model k)` THEN
    MP_TAC(SPEC `k:num` MOI_FSB_HD_POLY) THEN
    SIMP_TAC[frontier; CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN SET_TAC[]]);;

(* The frontier of the model is nonempty. *)

let MOI_S3KC_HD_FRONTIER_NE = prove
 (`!k. ~(frontier (holed_disk_model k) = {})`,
  GEN_TAC THEN MP_TAC(SPEC `k:num` MOI_S3KC_HD_BD_FAMILY) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:(real^2->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(u:(real^2->bool)->bool = {})` MP_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `CARD (u:(real^2->bool)->bool) = k + 1` THEN
    ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `c:real^2->bool`) THEN
  SUBGOAL_THEN `~(c:real^2->bool = {})` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `y:real^2`) THEN EXISTS_TAC `y:real^2` THEN
  UNDISCH_TAC `UNIONS u = frontier (holed_disk_model k)` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[]);;

(* HOLED_RECOG. *)

let HOLED_RECOG = prove
 (MOI_S33_HOLED_RECOG,
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "cbN") (CONJUNCTS_THEN2 (LABEL_TAC "cb2")
    (LABEL_TAC "homeo"))) THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `a:real^N->bool`; `f:real^2->real^N`;
                       `g:real^N->real^2`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  (* the model complex *)
  MP_TAC(CONJUNCT1(SPEC `k:num` MOI_FSB_HD_POLY)) THEN
  REWRITE_TAC[PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX] THEN
  DISCH_THEN(X_CHOOSE_THEN `c0:(real^2->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`k:num`; `c0:(real^2->bool)->bool`] MOI_S3KC_HD_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* a triangulation of a *)
  UNDISCH_TAC `pl_polyhedron (a:real^N->bool)` THEN
  REWRITE_TAC[PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `FINITE (d:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SCF_SC_FINITE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c0:(real^2->bool)->bool`; `d:(real^N->bool)->bool`;
                 `f:real^2->real^N`; `g:real^N->real^2`]
    (MP SURF_INVARIANT (CONJ (INST_TYPE [`:M`,`:N`] SURF_CHARTS) SURF_LOCAL))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* basic facts *)
  MP_TAC(SPEC `k:num` MOI_S3KC_HD_CONNECTED) THEN
  MP_TAC(SPEC `k:num` MOI_S3KC_HD_FRONTIER_NE) THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `connected (a:real^N->bool) /\ ~(surface_boundary d = {}:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (f:real^2->real^N) (holed_disk_model k) = a` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq (concl th) && rand(concl th) = `surface_boundary (d:(real^N->bool)->bool)`)) THEN
      ASM_REWRITE_TAC[IMAGE_EQ_EMPTY]];
    ALL_TAC] THEN
  (* the Euler characteristic of d *)
  SUBGOAL_THEN `complex_euler (c0:(real^2->bool)->bool) = &1 - &k` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FEU_COMPLEX_EULER_EQ_EULER THEN
    ASM_REWRITE_TAC[MOI_FEU_EULER_HOLED_DISK_MODEL];
    ALL_TAC] THEN
  REMOVE_THEN "cb2" (MP_TAC o SPEC `c0:(real^2->bool)->bool`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n0:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `n0:num = k` SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_THEN `&k = &1 - (&1 - &k)` (K ALL_TAC) THEN
  REMOVE_THEN "homeo" (MP_TAC o SPECL [`holed_disk_model k`; `a:real^N->bool`;
                                    `f:real^2->real^N`; `g:real^N->real^2`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `2 EXP k`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REMOVE_THEN "cbN" (MP_TAC o SPEC `d:(real^N->bool)->bool`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `n:num = k` SUBST_ALL_TAC THENL
   [SUBGOAL_THEN `2 EXP n = 2 EXP k` MP_TAC THENL
     [UNDISCH_TAC `{phi | moi_s33_char (a:real^N->bool) phi} HAS_SIZE 2 EXP n` THEN
      UNDISCH_TAC `{phi | moi_s33_char (a:real^N->bool) phi} HAS_SIZE 2 EXP k` THEN
      REWRITE_TAC[HAS_SIZE] THEN MESON_TAC[];
      REWRITE_TAC[EQ_EXP] THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `complex_euler (d:(real^N->bool)->bool) = &1 - &k` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_THEN `&k = &1 - complex_euler (d:(real^N->bool)->bool)` (K ALL_TAC) THEN
  (* k + 1 boundary components *)
  MP_TAC(SPEC `k:num` MOI_S3KC_HD_BD_FAMILY) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:(real^2->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`f:real^2->real^N`; `g:real^N->real^2`; `holed_disk_model k`;
                 `a:real^N->bool`; `u:(real^2->bool)->bool`] MOI_S3KC_IMAGE_FAMILY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `k:num` MOI_FSB_HD_POLY) THEN
    SIMP_TAC[frontier; CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN SET_TAC[];
    STRIP_TAC] THEN
  SUBGOAL_THEN `CARD (components (surface_boundary (d:(real^N->bool)->bool))) = k + 1`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq (concl th) && rand(concl th) = `surface_boundary (d:(real^N->bool)->bool)`)) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq (concl th) && rand(concl th) = `frontier (holed_disk_model k)`)) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq (concl th) && rand(concl th) = `IMAGE (f:real^2->real^N) (UNIONS u)`)) THEN
    MP_TAC(ISPEC `IMAGE (IMAGE (f:real^2->real^N)) u` MOI_S5C_COMPONENTS_PARTITION) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the planar classification *)
  MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `k:num`] MOI_FSB_PLANAR_EQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (f:real^2->real^N) (holed_disk_model k) = a` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `vec 0:real^2` THEN
    REWRITE_TAC[MOI_S3KC_IN_HD; VEC_COMPONENT; NOT_EXISTS_THM] THEN
    SIMP_TAC[REAL_POS; REAL_LE_REFL] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; GEN_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^2->real^N` (X_CHOOSE_THEN `g':real^N->real^2`
    MP_TAC)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`f':real^2->real^N`; `g':real^N->real^2`] THEN
  ASM_REWRITE_TAC[]);;


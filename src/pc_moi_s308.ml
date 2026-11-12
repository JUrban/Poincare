(* ========================================================================= *)
(* pc_moi_s308: Moise 30.8 (GTM 47, p.217 printed): a spine of the inner     *)
(* solid torus carries the loops of every solid torus between it and an    *)
(* outer one, when a toroidal shell lies between the inner and outer tori. *)
(* Route: an integer degree (the winding number of the circle coordinate   *)
(* of the model) classifies loops in a solid torus up to free homotopy and *)
(* is additive along powers of a loop; the toroidal shell collapses the     *)
(* outer torus onto the inner one, so the spine of the inner torus has      *)
(* degree +1 or -1 in the outer one, hence also in the middle one.          *)
(*                                                                           *)
(* First, powers of loops and their winding numbers.                       *)
(* ========================================================================= *)

needs "src/pc_moi_core_stmt.ml";;
needs "src/pc_moi_fnd_h1.ml";;

prioritize_real();;
type_invention_error := true;;

let moi_s38_looppow = define
 `moi_s38_looppow (c:real^1->real^N) 0 = linepath(pathstart c,pathstart c) /\
  (!n. moi_s38_looppow c (SUC n) = moi_s38_looppow c n ++ c)`;;

let MOI_S38_LOOPPOW_LOOP = prove
 (`!(c:real^1->real^N) n.
      path c /\ pathfinish c = pathstart c
      ==> path (moi_s38_looppow c n) /\
          pathstart (moi_s38_looppow c n) = pathstart c /\
          pathfinish (moi_s38_looppow c n) = pathstart c /\
          path_image (moi_s38_looppow c n) SUBSET path_image c`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN STRIP_TAC THEN
  INDUCT_TAC THEN REWRITE_TAC[moi_s38_looppow] THENL
   [REWRITE_TAC[PATH_LINEPATH; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                PATH_IMAGE_LINEPATH; SEGMENT_REFL; SING_SUBSET;
                PATHSTART_IN_PATH_IMAGE];
    ASM_SIMP_TAC[PATH_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN; PATH_IMAGE_JOIN;
                 UNION_SUBSET; SUBSET_REFL]]);;

let MOI_S38_WINDING_LOOPPOW = prove
 (`!(h:real^N->real^2) (c:real^1->real^N) n.
      path c /\ pathfinish c = pathstart c /\
      h continuous_on path_image c /\ ~(vec 0 IN IMAGE h (path_image c))
      ==> winding_number(h o moi_s38_looppow c n,vec 0) =
          Cx(&n) * winding_number(h o c,vec 0)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN STRIP_TAC THEN
  INDUCT_TAC THEN REWRITE_TAC[moi_s38_looppow] THENL
   [REWRITE_TAC[MOI_FH1_COMPOSE_LINEPATH_REFL; COMPLEX_MUL_LZERO] THEN
    MATCH_MP_TAC WINDING_NUMBER_TRIVIAL THEN
    UNDISCH_TAC `~((vec 0:real^2) IN IMAGE (h:real^N->real^2) (path_image c))` THEN
    MP_TAC(ISPEC `c:real^1->real^N` PATHSTART_IN_PATH_IMAGE) THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`c:real^1->real^N`; `n:num`] MOI_S38_LOOPPOW_LOOP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[PATH_COMPOSE_JOIN] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WINDING_NUMBER_JOIN o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATH_IMAGE_COMPOSE] THEN
    REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[CONTINUOUS_ON_SUBSET] THEN NO_TAC) THEN
    ASM SET_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_SUC; CX_ADD] THEN
  CONV_TAC COMPLEX_RING);;

let MOI_S38_WINDING_REVERSEPATH_COMPOSE = prove
 (`!(h:real^N->real^2) (c:real^1->real^N).
      path c /\ h continuous_on path_image c /\ ~(vec 0 IN IMAGE h (path_image c))
      ==> winding_number(h o reversepath c,vec 0) =
          --(winding_number(h o c,vec 0))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PATH_COMPOSE_REVERSEPATH] THEN
  MATCH_MP_TAC WINDING_NUMBER_REVERSEPATH THEN
  ASM_REWRITE_TAC[PATH_IMAGE_COMPOSE] THEN
  MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The degree of a loop in a solid torus.  For a model                      *)
(* homeomorphism (f,g) from cball x circle onto x, the degree of a loop c   *)
(* in x is the winding number of sndcart o g o c about the origin; it is an *)
(* integer, it classifies loops in x up to free homotopy, it is additive    *)
(* along powers of a loop, and the spine loops have degree one.             *)
(* ------------------------------------------------------------------------- *)

let MOI_S38_MODEL_HOMOTOPIC_LOOPS_EQ = prove
 (`!p q:real^1->real^(2,2)finite_sum.
      path p /\ pathfinish p = pathstart p /\
      path_image p SUBSET cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1) /\
      path q /\ pathfinish q = pathstart q /\
      path_image q SUBSET cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)
      ==> (homotopic_loops (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) p q <=>
           winding_number(sndcart o p,vec 0) = winding_number(sndcart o q,vec 0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p:real^1->real^(2,2)finite_sum`; `cball(vec 0:real^2,&1)`;
                 `sphere(vec 0:real^2,&1)`] MOI_FH1_LOOP_COMPONENTS) THEN
  MP_TAC(ISPECL [`q:real^1->real^(2,2)finite_sum`; `cball(vec 0:real^2,&1)`;
                 `sphere(vec 0:real^2,&1)`] MOI_FH1_LOOP_COMPONENTS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`sndcart o (p:real^1->real^(2,2)finite_sum)`;
                 `sndcart o (q:real^1->real^(2,2)finite_sum)`]
                MOI_FH1_CIRCLE_HOMOTOPIC_LOOPS_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  EQ_TAC THENL
   [DISCH_THEN(MP_TAC o CONJUNCT2 o MATCH_MP MOI_FH1_HOMOTOPIC_LOOPS_PROJ) THEN
    REWRITE_TAC[];
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `homotopic_loops (cball(vec 0:real^2,&1))
      (fstcart o (p:real^1->real^(2,2)finite_sum))
      (fstcart o (q:real^1->real^(2,2)finite_sum))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_LOOPS_LINEAR THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[CONVEX_CONTAINS_SEGMENT] CONVEX_CBALL) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[path_image]) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`cball(vec 0:real^2,&1)`; `sphere(vec 0:real^2,&1)`;
                 `fstcart o (p:real^1->real^(2,2)finite_sum)`;
                 `sndcart o (p:real^1->real^(2,2)finite_sum)`;
                 `fstcart o (q:real^1->real^(2,2)finite_sum)`;
                 `sndcart o (q:real^1->real^(2,2)finite_sum)`]
                MOI_FH1_HOMOTOPIC_LOOPS_PASTECART) THEN
  ASM_REWRITE_TAC[o_THM; PASTECART_FST_SND; ETA_AX]);;

let MOI_S38_HOMEO_LOOP = prove
 (`!(m:real^M->bool) (x:real^N->bool) f g c.
      homeomorphism (m,x) (f,g) /\
      path c /\ pathfinish c = pathstart c /\ path_image c SUBSET x
      ==> path (g o c) /\ pathfinish (g o c) = pathstart (g o c) /\
          path_image (g o c) SUBSET m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HOMEOMORPHISM] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATH_IMAGE_COMPOSE] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    ASM SET_TAC[]]);;

let MOI_S38_HOMEO_HOMOTOPIC_LOOPS_EQ = prove
 (`!(m:real^M->bool) (x:real^N->bool) f g c d.
      homeomorphism (m,x) (f,g) /\
      path c /\ pathfinish c = pathstart c /\ path_image c SUBSET x /\
      path d /\ pathfinish d = pathstart d /\ path_image d SUBSET x
      ==> (homotopic_loops x c d <=> homotopic_loops m (g o c) (g o d))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HOMEOMORPHISM] THEN STRIP_TAC THEN
  EQ_TAC THEN DISCH_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE THEN
    EXISTS_TAC `x:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `homotopic_loops x ((f:real^M->real^N) o (g:real^N->real^M) o (c:real^1->real^N))
                      (f o g o (d:real^1->real^N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE THEN
    EXISTS_TAC `m:real^M->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `homotopic_loops x (c:real^1->real^N) ((f:real^M->real^N) o (g:real^N->real^M) o c) /\
    homotopic_loops x (d:real^1->real^N) ((f:real^M->real^N) o (g:real^N->real^M) o d)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC HOMOTOPIC_LOOPS_EQ THEN ASM_REWRITE_TAC[o_THM] THEN
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[path_image]) THEN ASM SET_TAC[];
    ASM_MESON_TAC[HOMOTOPIC_LOOPS_TRANS; HOMOTOPIC_LOOPS_SYM]]);;

let MOI_S38_SOLID_TORUS_HOMOTOPIC_LOOPS_EQ = prove
 (`!(x:real^N->bool) f g c d.
      homeomorphism (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1),x) (f,g) /\
      path c /\ pathfinish c = pathstart c /\ path_image c SUBSET x /\
      path d /\ pathfinish d = pathstart d /\ path_image d SUBSET x
      ==> (homotopic_loops x c d <=>
           winding_number(sndcart o g o c,vec 0) =
           winding_number(sndcart o g o d,vec 0))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)`;
                 `x:real^N->bool`; `f:real^(2,2)finite_sum->real^N`;
                 `g:real^N->real^(2,2)finite_sum`; `c:real^1->real^N`;
                 `d:real^1->real^N`] MOI_S38_HOMEO_HOMOTOPIC_LOOPS_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC MOI_S38_MODEL_HOMOTOPIC_LOOPS_EQ THEN
  ASM_MESON_TAC[MOI_S38_HOMEO_LOOP]);;

let MOI_S38_SOLID_TORUS_COORD = prove
 (`!(x:real^N->bool) f g.
      homeomorphism (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1),x) (f,g)
      ==> (sndcart o g) continuous_on x /\
          IMAGE (sndcart o g) x SUBSET sphere(vec 0:real^2,&1) /\
          ~(vec 0 IN IMAGE (sndcart o g) x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HOMEOMORPHISM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (sndcart o (g:real^N->real^(2,2)finite_sum)) x SUBSET
                sphere(vec 0:real^2,&1)` ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_o] THEN
    UNDISCH_TAC `IMAGE (g:real^N->real^(2,2)finite_sum) x SUBSET
                 cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; MOI_FH1_IN_PCROSS] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART];
    MP_TAC MOI_FH1_ORIGIN_NOT_IN_CIRCLE THEN ASM SET_TAC[]]);;

let MOI_S38_SOLID_TORUS_DEGREE_INTEGER = prove
 (`!(x:real^N->bool) f g c.
      homeomorphism (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1),x) (f,g) /\
      path c /\ pathfinish c = pathstart c /\ path_image c SUBSET x
      ==> complex_integer(winding_number(sndcart o g o c,vec 0))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)`;
                 `x:real^N->bool`; `f:real^(2,2)finite_sum->real^N`;
                 `g:real^N->real^(2,2)finite_sum`; `c:real^1->real^N`]
                MOI_S38_HOMEO_LOOP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(g:real^N->real^(2,2)finite_sum) o (c:real^1->real^N)`;
                 `cball(vec 0:real^2,&1)`; `sphere(vec 0:real^2,&1)`]
                MOI_FH1_LOOP_COMPONENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC INTEGER_WINDING_NUMBER THEN ASM_REWRITE_TAC[] THEN
  MP_TAC MOI_FH1_ORIGIN_NOT_IN_CIRCLE THEN ASM SET_TAC[]);;

let MOI_S38_SOLID_TORUS_DEGREE_LOOPPOW = prove
 (`!(x:real^N->bool) f g c n.
      homeomorphism (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1),x) (f,g) /\
      path c /\ pathfinish c = pathstart c /\ path_image c SUBSET x
      ==> winding_number(sndcart o g o moi_s38_looppow c n,vec 0) =
          Cx(&n) * winding_number(sndcart o g o c,vec 0) /\
          winding_number(sndcart o g o reversepath(moi_s38_looppow c n),vec 0) =
          --(Cx(&n) * winding_number(sndcart o g o c,vec 0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S38_SOLID_TORUS_COORD) THEN
  MP_TAC(SPECL [`c:real^1->real^N`; `n:num`] MOI_S38_LOOPPOW_LOOP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`sndcart o (g:real^N->real^(2,2)finite_sum)`; `c:real^1->real^N`;
                 `n:num`] MOI_S38_WINDING_LOOPPOW) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ASM SET_TAC[]];
    REWRITE_TAC[GSYM o_ASSOC] THEN DISCH_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`sndcart o (g:real^N->real^(2,2)finite_sum)`;
                 `moi_s38_looppow (c:real^1->real^N) n`]
                MOI_S38_WINDING_REVERSEPATH_COMPOSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_TRANS]; ASM SET_TAC[]];
    ASM_REWRITE_TAC[GSYM o_ASSOC]]);;

(* ------------------------------------------------------------------------- *)
(* Spine loops, loops as powers of a degree-one loop, and the               *)
(* comparison of degrees in two nested solid tori.                          *)
(* ------------------------------------------------------------------------- *)

let MOI_S38_SOLID_TORUS_HOMEO = prove
 (`!x:real^N->bool.
      solid_torus x
      ==> ?f g. homeomorphism
                  (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1),x) (f,g)`,
  GEN_TAC THEN REWRITE_TAC[solid_torus; homeomorphic] THEN
  MESON_TAC[HOMEOMORPHISM_SYM]);;

let MOI_S38_MODEL_SPINE_LOOP = prove
 (`!p:real^2.
      p IN cball(vec 0,&1)
      ==> path (\t. pastecart p (circlepath(vec 0,&1) t)) /\
          pathfinish (\t. pastecart p (circlepath(vec 0,&1) t)) =
          pathstart (\t. pastecart p (circlepath(vec 0,&1) t)) /\
          path_image (\t. pastecart p (circlepath(vec 0,&1) t)) SUBSET
          {p} PCROSS sphere(vec 0:real^2,&1) /\
          {p} PCROSS sphere(vec 0:real^2,&1) SUBSET
          cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)`,
  GEN_TAC THEN DISCH_TAC THEN STRIP_ASSUME_TAC MOI_FH1_CIRCLEPATH_FACTS THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[path] THEN MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST; ETA_AX; GSYM path] THEN ASM_REWRITE_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
    ASM_REWRITE_TAC[pathstart; pathfinish];
    REWRITE_TAC[path_image; SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS; IN_SING] THEN
    UNDISCH_TAC `path_image (circlepath(vec 0,&1)) = sphere(vec 0:real^2,&1)` THEN
    REWRITE_TAC[path_image] THEN SET_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_PCROSS; PASTECART_IN_PCROSS; IN_SING] THEN
    ASM_MESON_TAC[]]);;

let MOI_S38_SPINE_LOOP = prove
 (`!(x:real^N->bool) f g (p:real^2).
      homeomorphism (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1),x) (f,g) /\
      p IN cball(vec 0,&1)
      ==> path (f o (\t. pastecart p (circlepath(vec 0,&1) t))) /\
          pathfinish (f o (\t. pastecart p (circlepath(vec 0,&1) t))) =
          pathstart (f o (\t. pastecart p (circlepath(vec 0,&1) t))) /\
          path_image (f o (\t. pastecart p (circlepath(vec 0,&1) t))) SUBSET
          IMAGE f ({p} PCROSS sphere(vec 0:real^2,&1)) /\
          path_image (f o (\t. pastecart p (circlepath(vec 0,&1) t))) SUBSET x /\
          winding_number(sndcart o g o f o (\t. pastecart p (circlepath(vec 0,&1) t)),
                         vec 0) = Cx(&1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HOMEOMORPHISM] THEN STRIP_TAC THEN
  STRIP_ASSUME_TAC MOI_FH1_CIRCLEPATH_FACTS THEN
  MP_TAC(SPEC `p:real^2` MOI_S38_MODEL_SPINE_LOOP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATH_IMAGE_COMPOSE] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_TRANS];
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `winding_number(circlepath(vec 0,&1),vec 0)` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC WINDING_NUMBER_HOMOTOPIC_LOOPS THEN
  MATCH_MP_TAC HOMOTOPIC_LOOPS_EQ THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC MOI_FH1_ORIGIN_NOT_IN_CIRCLE THEN SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
  SUBGOAL_THEN
   `pastecart (p:real^2) (circlepath(vec 0,&1) t) IN
    cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)`
  (fun th -> ASM_SIMP_TAC[th; SNDCART_PASTECART]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[path_image]) THEN ASM SET_TAC[]);;

let MOI_S38_SIGN_SWAP = prove
 (`!a b:complex.
      (a = b \/ a = --b)
      ==> ((a = Cx(&1) \/ a = --Cx(&1)) <=> (b = Cx(&1) \/ b = --Cx(&1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MESON_TAC[COMPLEX_NEG_NEG]);;

let MOI_S38_UNIT_CASES = prove
 (`!n z. complex_integer z /\ (Cx(&n) * z = Cx(&1) \/ Cx(&n) * z = --Cx(&1))
         ==> n = 1 /\ (z = Cx(&1) \/ z = --Cx(&1))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_TAC `m:num` o MATCH_MP MOI_FH1_COMPLEX_INTEGER_CASES) MP_TAC) THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[COMPLEX_MUL_RNEG; GSYM CX_MUL; GSYM CX_NEG; CX_INJ; COMPLEX_EQ_NEG2;
              REAL_EQ_NEG2; REAL_OF_NUM_MUL; REAL_OF_NUM_EQ; MULT_EQ_1] THEN
  MP_TAC(SPEC `n * m:num` REAL_POS) THEN MP_TAC(SPEC `m:num` REAL_POS) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  ASM_CASES_TAC `n = 1` THEN ASM_REWRITE_TAC[REAL_MUL_LID] THEN
  REAL_ARITH_TAC);;

let MOI_S38_LOOP_AS_POWER = prove
 (`!(x:real^N->bool) f g c gam.
      homeomorphism (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1),x) (f,g) /\
      path c /\ pathfinish c = pathstart c /\ path_image c SUBSET x /\
      (winding_number(sndcart o g o c,vec 0) = Cx(&1) \/
       winding_number(sndcart o g o c,vec 0) = --Cx(&1)) /\
      path gam /\ pathfinish gam = pathstart gam /\ path_image gam SUBSET x
      ==> ?n. homotopic_loops x gam (moi_s38_looppow c n) \/
              homotopic_loops x gam (reversepath(moi_s38_looppow c n))`,
  REPEAT GEN_TAC THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  MP_TAC(ISPECL [`x:real^N->bool`; `f:real^(2,2)finite_sum->real^N`;
                 `g:real^N->real^(2,2)finite_sum`; `gam:real^1->real^N`]
                MOI_S38_SOLID_TORUS_DEGREE_INTEGER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num` o MATCH_MP MOI_FH1_COMPLEX_INTEGER_CASES) THEN
  EXISTS_TAC `n:num` THEN
  MP_TAC(ISPECL [`x:real^N->bool`; `f:real^(2,2)finite_sum->real^N`;
                 `g:real^N->real^(2,2)finite_sum`; `c:real^1->real^N`; `n:num`]
                MOI_S38_SOLID_TORUS_DEGREE_LOOPPOW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real^1->real^N`; `n:num`] MOI_S38_LOOPPOW_LOOP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `path_image (moi_s38_looppow (c:real^1->real^N) n) SUBSET x`
  ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`x:real^N->bool`; `f:real^(2,2)finite_sum->real^N`;
                 `g:real^N->real^(2,2)finite_sum`; `gam:real^1->real^N`;
                 `moi_s38_looppow (c:real^1->real^N) n`]
                MOI_S38_SOLID_TORUS_HOMOTOPIC_LOOPS_EQ) THEN
  MP_TAC(ISPECL [`x:real^N->bool`; `f:real^(2,2)finite_sum->real^N`;
                 `g:real^N->real^(2,2)finite_sum`; `gam:real^1->real^N`;
                 `reversepath(moi_s38_looppow (c:real^1->real^N) n)`]
                MOI_S38_SOLID_TORUS_HOMOTOPIC_LOOPS_EQ) THEN
  ASM_REWRITE_TAC[PATH_REVERSEPATH; PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH;
                  PATH_IMAGE_REVERSEPATH] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  MAP_EVERY UNDISCH_TAC
   [`winding_number(sndcart o (g:real^N->real^(2,2)finite_sum) o (c:real^1->real^N),
                    vec 0) = Cx(&1) \/
     winding_number(sndcart o g o c,vec 0) = --Cx(&1)`;
    `winding_number(sndcart o (g:real^N->real^(2,2)finite_sum) o (gam:real^1->real^N),
                    vec 0) = Cx(&n) \/
     winding_number(sndcart o g o gam,vec 0) = --Cx(&n)`] THEN
  REPEAT(DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC)) THEN
  REWRITE_TAC[COMPLEX_MUL_RID; COMPLEX_MUL_RNEG; COMPLEX_NEG_NEG]);;

let MOI_S38_HOMOTOPIC_POWER_DEGREE = prove
 (`!(x:real^N->bool) f g c d n.
      homeomorphism (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1),x) (f,g) /\
      path c /\ pathfinish c = pathstart c /\ path_image c SUBSET x /\
      (homotopic_loops x d (moi_s38_looppow c n) \/
       homotopic_loops x d (reversepath(moi_s38_looppow c n)))
      ==> winding_number(sndcart o g o d,vec 0) =
          Cx(&n) * winding_number(sndcart o g o c,vec 0) \/
          winding_number(sndcart o g o d,vec 0) =
          --(Cx(&n) * winding_number(sndcart o g o c,vec 0))`,
  REPEAT GEN_TAC THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  MP_TAC(ISPECL [`x:real^N->bool`; `f:real^(2,2)finite_sum->real^N`;
                 `g:real^N->real^(2,2)finite_sum`; `c:real^1->real^N`; `n:num`]
                MOI_S38_SOLID_TORUS_DEGREE_LOOPPOW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real^1->real^N`; `n:num`] MOI_S38_LOOPPOW_LOOP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `path_image (moi_s38_looppow (c:real^1->real^N) n) SUBSET x`
  ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [DISJ1_TAC; DISJ2_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_LOOP) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_PATH) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_SUBSET) THENL
   [MP_TAC(ISPECL [`x:real^N->bool`; `f:real^(2,2)finite_sum->real^N`;
                   `g:real^N->real^(2,2)finite_sum`; `d:real^1->real^N`;
                   `moi_s38_looppow (c:real^1->real^N) n`]
                  MOI_S38_SOLID_TORUS_HOMOTOPIC_LOOPS_EQ);
    MP_TAC(ISPECL [`x:real^N->bool`; `f:real^(2,2)finite_sum->real^N`;
                   `g:real^N->real^(2,2)finite_sum`; `d:real^1->real^N`;
                   `reversepath(moi_s38_looppow (c:real^1->real^N) n)`]
                  MOI_S38_SOLID_TORUS_HOMOTOPIC_LOOPS_EQ)] THEN
  ASM_REWRITE_TAC[PATH_REVERSEPATH; PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH;
                  PATH_IMAGE_REVERSEPATH] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]);;

let MOI_S38_DEGREE_COMPARE = prove
 (`!(x:real^N->bool) z fx gx fz gz c d.
      homeomorphism (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1),x) (fx,gx) /\
      homeomorphism (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1),z) (fz,gz) /\
      x SUBSET z /\
      path c /\ pathfinish c = pathstart c /\ path_image c SUBSET x /\
      (winding_number(sndcart o gx o c,vec 0) = Cx(&1) \/
       winding_number(sndcart o gx o c,vec 0) = --Cx(&1)) /\
      path d /\ pathfinish d = pathstart d /\ path_image d SUBSET x /\
      (winding_number(sndcart o gz o d,vec 0) = Cx(&1) \/
       winding_number(sndcart o gz o d,vec 0) = --Cx(&1))
      ==> (winding_number(sndcart o gx o d,vec 0) = Cx(&1) \/
           winding_number(sndcart o gx o d,vec 0) = --Cx(&1)) /\
          (winding_number(sndcart o gz o c,vec 0) = Cx(&1) \/
           winding_number(sndcart o gz o c,vec 0) = --Cx(&1))`,
  REPEAT GEN_TAC THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  MP_TAC(ISPECL [`x:real^N->bool`; `fx:real^(2,2)finite_sum->real^N`;
                 `gx:real^N->real^(2,2)finite_sum`; `c:real^1->real^N`;
                 `d:real^1->real^N`] MOI_S38_LOOP_AS_POWER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  SUBGOAL_THEN `path_image (c:real^1->real^N) SUBSET z` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `homotopic_loops z (d:real^1->real^N) (moi_s38_looppow c n) \/
    homotopic_loops z d (reversepath(moi_s38_looppow c n))`
  ASSUME_TAC THENL [ASM_MESON_TAC[HOMOTOPIC_LOOPS_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`x:real^N->bool`; `fx:real^(2,2)finite_sum->real^N`;
                 `gx:real^N->real^(2,2)finite_sum`; `c:real^1->real^N`;
                 `d:real^1->real^N`; `n:num`] MOI_S38_HOMOTOPIC_POWER_DEGREE) THEN
  MP_TAC(ISPECL [`z:real^N->bool`; `fz:real^(2,2)finite_sum->real^N`;
                 `gz:real^N->real^(2,2)finite_sum`; `c:real^1->real^N`;
                 `d:real^1->real^N`; `n:num`] MOI_S38_HOMOTOPIC_POWER_DEGREE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `n = 1 /\
    (winding_number(sndcart o (gz:real^N->real^(2,2)finite_sum) o (c:real^1->real^N),
                    vec 0) = Cx(&1) \/
     winding_number(sndcart o gz o c,vec 0) = --Cx(&1))`
  (CONJUNCTS_THEN ASSUME_TAC) THENL
   [MATCH_MP_TAC MOI_S38_UNIT_CASES THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S38_SOLID_TORUS_DEGREE_INTEGER THEN
      EXISTS_TAC `z:real^N->bool` THEN EXISTS_TAC `fz:real^(2,2)finite_sum->real^N` THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL
       [`winding_number(sndcart o (gz:real^N->real^(2,2)finite_sum) o (d:real^1->real^N),
                        vec 0)`;
        `Cx(&n) * winding_number(sndcart o (gz:real^N->real^(2,2)finite_sum) o
                                 (c:real^1->real^N),vec 0)`] MOI_S38_SIGN_SWAP) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL
   [`winding_number(sndcart o (gx:real^N->real^(2,2)finite_sum) o (d:real^1->real^N),
                    vec 0)`;
    `winding_number(sndcart o (gx:real^N->real^(2,2)finite_sum) o
                    (c:real^1->real^N),vec 0)`] MOI_S38_SIGN_SWAP) THEN
  UNDISCH_TAC
   `winding_number(sndcart o (gx:real^N->real^(2,2)finite_sum) o (d:real^1->real^N),
                   vec 0) =
    Cx(&n) * winding_number(sndcart o gx o c,vec 0) \/
    winding_number(sndcart o gx o d,vec 0) =
    --(Cx(&n) * winding_number(sndcart o gx o c,vec 0))` THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_LID] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A collar b x [0,1] attached to a closed set a along b x 0                *)
(* collapses onto a: the identity of a UNION y is homotopic in a UNION y to *)
(* a map into a (squash the collar coordinate to 0, pasting on the closed   *)
(* sets a and y).  For nested solid tori with a toroidal shell between      *)
(* them, every loop of the outer torus is freely homotopic in it to a loop *)
(* of the inner torus.                                                      *)
(* ------------------------------------------------------------------------- *)

let MOI_S38_COLLAR_MAP = prove
 (`!(y:real^N->bool) (b:real^M->bool) fy gy.
      homeomorphism (b PCROSS interval[vec 0:real^1,vec 1],y) (fy,gy)
      ==> (\z:real^(1,N)finite_sum.
             fy(pastecart (fstcart((gy:real^N->real^(M,1)finite_sum)(sndcart z)))
                          ((&1 - drop(fstcart z)) % sndcart(gy(sndcart z)))))
          continuous_on (interval[vec 0:real^1,vec 1] PCROSS y) /\
          IMAGE (\z:real^(1,N)finite_sum.
             fy(pastecart (fstcart((gy:real^N->real^(M,1)finite_sum)(sndcart z)))
                          ((&1 - drop(fstcart z)) % sndcart(gy(sndcart z)))))
                (interval[vec 0:real^1,vec 1] PCROSS y) SUBSET y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HOMEOMORPHISM] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!z:real^(1,N)finite_sum.
      z IN interval[vec 0:real^1,vec 1] PCROSS y
      ==> pastecart (fstcart((gy:real^N->real^(M,1)finite_sum)(sndcart z)))
                    ((&1 - drop(fstcart z)) % sndcart(gy(sndcart z))) IN
          (b:real^M->bool) PCROSS interval[vec 0:real^1,vec 1]`
  ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART;
                PASTECART_IN_PCROSS] THEN
    MAP_EVERY X_GEN_TAC [`t:real^1`; `w:real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(gy:real^N->real^(M,1)finite_sum) w IN
                  (b:real^M->bool) PCROSS interval[vec 0:real^1,vec 1]`
    MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[MOI_FH1_IN_PCROSS] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `sndcart((gy:real^N->real^(M,1)finite_sum) w) IN
                 interval[vec 0:real^1,vec 1]` THEN
    UNDISCH_TAC `(t:real^1) IN interval[vec 0,vec 1]` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_CMUL; DROP_VEC] THEN
    REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MP_TAC(SPECL [`drop t`; `drop(sndcart((gy:real^N->real^(M,1)finite_sum) w))`]
                   REAL_LE_MUL) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z:real^(1,N)finite_sum. (gy:real^N->real^(M,1)finite_sum)(sndcart z))
    continuous_on (interval[vec 0:real^1,vec 1] PCROSS y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_COMPOSE) THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `y:real^N->bool` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; SNDCART_PASTECART] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^(1,N)finite_sum` THEN
    DISCH_TAC THEN
    UNDISCH_TAC `IMAGE (fy:real^(M,1)finite_sum->real^N)
                   ((b:real^M->bool) PCROSS interval[vec 0:real^1,vec 1]) SUBSET y` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[]] THEN
  MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_COMPOSE) THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(b:real^M->bool) PCROSS interval[vec 0:real^1,vec 1]` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[]] THEN
  MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_COMPOSE) THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART];
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC[o_DEF; LIFT_SUB; LIFT_DROP; LIFT_NUM] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
      SIMP_TAC[CONTINUOUS_ON_CONST; LINEAR_CONTINUOUS_ON; LINEAR_FSTCART];
      MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_COMPOSE) THEN
      ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART]]]);;

let MOI_S38_COLLAR_COLLAPSE = prove
 (`!(a:real^N->bool) (y:real^N->bool) (b:real^M->bool) fy gy.
      closed a /\ closed y /\
      homeomorphism (b PCROSS interval[vec 0:real^1,vec 1],y) (fy,gy) /\
      a INTER y SUBSET IMAGE fy (b PCROSS {vec 0:real^1}) /\
      IMAGE fy (b PCROSS {vec 0:real^1}) SUBSET a
      ==> ?r. homotopic_with (\h. T)
                (subtopology euclidean (a UNION y),subtopology euclidean (a UNION y))
                (\x. x) r /\
              IMAGE r (a UNION y) SUBSET a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S38_COLLAR_MAP) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [HOMEOMORPHISM]) THEN
  EXISTS_TAC `\x:real^N. if x IN a then x
                         else (fy:real^(M,1)finite_sum->real^N)
                                (pastecart (fstcart((gy:real^N->real^(M,1)finite_sum) x))
                                           (vec 0))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNION] THEN X_GEN_TAC `x:real^N` THEN
    DISCH_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(x:real^N) IN y` ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^N) IN a \/ x IN y` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `IMAGE (fy:real^(M,1)finite_sum->real^N)
                   ((b:real^M->bool) PCROSS {vec 0:real^1}) SUBSET a` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; IN_SING] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(gy:real^N->real^(M,1)finite_sum) x IN
                  (b:real^M->bool) PCROSS interval[vec 0:real^1,vec 1]`
    MP_TAC THENL [ASM SET_TAC[]; SIMP_TAC[MOI_FH1_IN_PCROSS]]] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) HOMOTOPIC_WITH_EUCLIDEAN_ALT o snd) THEN
  ANTS_TAC THENL [REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  EXISTS_TAC `\z:real^(1,N)finite_sum.
                 if sndcart z IN a then sndcart z
                 else (fy:real^(M,1)finite_sum->real^N)
                       (pastecart (fstcart((gy:real^N->real^(M,1)finite_sum)(sndcart z)))
                          ((&1 - drop(fstcart z)) % sndcart(gy(sndcart z))))` THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; DROP_VEC; REAL_SUB_RZERO;
              REAL_SUB_REFL; VECTOR_MUL_LID; VECTOR_MUL_LZERO; PASTECART_FST_SND] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[PCROSS_UNION] THEN MATCH_MP_TAC CONTINUOUS_ON_CASES THEN
    ASM_SIMP_TAC[CLOSED_PCROSS; CLOSED_INTERVAL; LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
    X_GEN_TAC `z:real^(1,N)finite_sum` THEN REWRITE_TAC[MOI_FH1_IN_PCROSS] THEN
    STRIP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `?u:real^M. u IN b /\
                 sndcart (z:real^(1,N)finite_sum) =
                 (fy:real^(M,1)finite_sum->real^N) (pastecart u (vec 0))`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(a:real^N->bool) INTER y SUBSET
                   IMAGE (fy:real^(M,1)finite_sum->real^N)
                         ((b:real^M->bool) PCROSS {vec 0:real^1})` THEN
      REWRITE_TAC[SUBSET; IN_INTER; IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS;
                  IN_SING] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `pastecart (u:real^M) (vec 0:real^1) IN
                  (b:real^M->bool) PCROSS interval[vec 0:real^1,vec 1]`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[PASTECART_IN_PCROSS; ENDS_IN_UNIT_INTERVAL]; ALL_TAC] THEN
    ASM_SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART; VECTOR_MUL_RZERO];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; FSTCART_PASTECART;
                SNDCART_PASTECART] THEN
    MAP_EVERY X_GEN_TAC [`t:real^1`; `x:real^N`] THEN REWRITE_TAC[IN_UNION] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
    UNDISCH_TAC
     `IMAGE (\z:real^(1,N)finite_sum.
             (fy:real^(M,1)finite_sum->real^N)
             (pastecart (fstcart((gy:real^N->real^(M,1)finite_sum)(sndcart z)))
             ((&1 - drop (fstcart z)) % sndcart (gy (sndcart z)))))
      (interval [vec 0:real^1,vec 1] PCROSS (y:real^N->bool)) SUBSET y` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; FSTCART_PASTECART;
                SNDCART_PASTECART] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `(x:real^N) IN a \/ x IN y` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_UNION] THEN DISCH_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^N) IN a \/ x IN y` THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN ASM_SIMP_TAC[]]);;

let MOI_S38_DEFORM_LOOPS = prove
 (`!(x:real^N->bool) u r gam.
      homotopic_with (\h. T) (subtopology euclidean x,subtopology euclidean x)
                     (\x. x) r /\
      IMAGE r x SUBSET u /\
      path gam /\ pathfinish gam = pathstart gam /\ path_image gam SUBSET x
      ==> homotopic_loops x gam (r o gam) /\
          path (r o gam) /\ pathfinish (r o gam) = pathstart (r o gam) /\
          path_image (r o gam) SUBSET u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `homotopic_loops x (gam:real^1->real^N) ((r:real^N->real^N) o gam)`
  ASSUME_TAC THENL
   [REWRITE_TAC[homotopic_loops] THEN
    MP_TAC(ISPECL [`\k:real^1->real^N. pathfinish k = pathstart k`;
                   `\x:real^N. x`; `r:real^N->real^N`; `gam:real^1->real^N`;
                   `interval[vec 0:real^1,vec 1]`; `x:real^N->bool`;
                   `x:real^N->bool`] HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT) THEN
    SUBGOAL_THEN `(\x:real^N. x) o (gam:real^1->real^N) = gam` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[path; path_image]) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_MONO THEN
    EXISTS_TAC `\h:real^N->real^N. T` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_LOOP) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_PATH) THEN
  ASM_REWRITE_TAC[PATH_IMAGE_COMPOSE] THEN ASM SET_TAC[]);;

let MOI_S38_SOLID_TORUS_COMPACT = prove
 (`!x:real^N->bool. solid_torus x ==> compact x`,
  GEN_TAC THEN REWRITE_TAC[solid_torus] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP HOMEOMORPHIC_COMPACTNESS th]) THEN
  SIMP_TAC[COMPACT_PCROSS; COMPACT_CBALL; COMPACT_SPHERE]);;

let MOI_S38_SHELL_LOOPS = prove
 (`!(s1:real^N->bool) s2.
      solid_torus s1 /\ solid_torus s2 /\ s1 SUBSET s2 /\
      toroidal_shell (closure(s2 DIFF s1)) (frontier s1) (frontier s2)
      ==> !gam. path gam /\ pathfinish gam = pathstart gam /\ path_image gam SUBSET s2
                ==> ?q. path q /\ pathfinish q = pathstart q /\ path_image q SUBSET s1 /\
                        homotopic_loops s2 gam q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[toroidal_shell] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`fy:real^((2,2)finite_sum,1)finite_sum->real^N`;
                       `gy:real^N->real^((2,2)finite_sum,1)finite_sum`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `closed (s1:real^N->bool) /\ closed (s2:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S38_SOLID_TORUS_COMPACT; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `(s2:real^N->bool) DIFF s1 SUBSET closure(s2 DIFF s1) /\
                closure(s2 DIFF s1) SUBSET s2`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[CLOSURE_SUBSET] THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s1:real^N->bool) UNION closure(s2 DIFF s1) = s2` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(s1:real^N->bool) INTER closure(s2 DIFF s1) SUBSET frontier s1`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `closure((s2:real^N->bool) DIFF s1) SUBSET (:real^N) DIFF interior s1`
    MP_TAC THENL
     [REWRITE_TAC[GSYM CLOSURE_COMPLEMENT] THEN MATCH_MP_TAC SUBSET_CLOSURE THEN
      SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier(s1:real^N->bool) SUBSET s1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FRONTIER_SUBSET_CLOSED]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s1:real^N->bool`; `closure((s2:real^N->bool) DIFF s1)`;
                 `sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)`;
                 `fy:real^((2,2)finite_sum,1)finite_sum->real^N`;
                 `gy:real^N->real^((2,2)finite_sum,1)finite_sum`]
                MOI_S38_COLLAR_COLLAPSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CLOSED_CLOSURE] THEN
    UNDISCH_TAC `frontier(s1:real^N->bool) SUBSET s1` THEN
    UNDISCH_TAC `(s1:real^N->bool) INTER closure(s2 DIFF s1) SUBSET frontier s1` THEN
    FIRST_X_ASSUM(fun th ->
      if lhs(concl th) = `frontier(s1:real^N->bool)` then REWRITE_TAC[th]
      else NO_TAC) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->real^N` STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `gam:real^1->real^N` THEN STRIP_TAC THEN
  EXISTS_TAC `(r:real^N->real^N) o (gam:real^1->real^N)` THEN
  MP_TAC(ISPECL [`s2:real^N->bool`; `s1:real^N->bool`; `r:real^N->real^N`;
                 `gam:real^1->real^N`] MOI_S38_DEFORM_LOOPS) THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Moise 30.8.  If every loop of s2 is homotopic in s2 to a                  *)
(* loop of s1 (toroidal shell, see above), the spine loop of s1 has          *)
(* degree +1 or -1 in s2, hence in s (compare with the spine loop of s),   *)
(* so every loop of s is homotopic in s to a power of the spine loop of s1. *)
(* ------------------------------------------------------------------------- *)

let MOI_S38_CORE = prove
 (`!(s1:real^N->bool) s s2 j.
      solid_torus s /\ solid_torus s2 /\ s1 SUBSET s /\ s SUBSET s2 /\
      (!gam. path gam /\ pathfinish gam = pathstart gam /\ path_image gam SUBSET s2
             ==> ?q. path q /\ pathfinish q = pathstart q /\ path_image q SUBSET s1 /\
                     homotopic_loops s2 gam q) /\
      spine j s1
      ==> loops_carried j s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[spine] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "shell") MP_TAC))))) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`f1:real^(2,2)finite_sum->real^N`;
                       `g1:real^N->real^(2,2)finite_sum`; `p1:real^2`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^N->bool` MOI_S38_SOLID_TORUS_HOMEO) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `fs:real^(2,2)finite_sum->real^N`
   (X_CHOOSE_TAC `gs:real^N->real^(2,2)finite_sum`)) THEN
  MP_TAC(ISPEC `s2:real^N->bool` MOI_S38_SOLID_TORUS_HOMEO) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f2:real^(2,2)finite_sum->real^N`
   (X_CHOOSE_TAC `g2:real^N->real^(2,2)finite_sum`)) THEN
  SUBGOAL_THEN `(vec 0:real^2) IN cball(vec 0,&1) /\ (p1:real^2) IN cball(vec 0,&1)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[CENTRE_IN_CBALL; REAL_POS] THEN
    ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?c1:real^1->real^N.
      path c1 /\ pathfinish c1 = pathstart c1 /\ path_image c1 SUBSET j /\
      path_image c1 SUBSET s1 /\
      winding_number(sndcart o (g1:real^N->real^(2,2)finite_sum) o c1,vec 0) = Cx(&1)`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `(f1:real^(2,2)finite_sum->real^N) o
                (\t. pastecart (p1:real^2) (circlepath(vec 0,&1) t))` THEN
    MP_TAC(ISPECL [`s1:real^N->bool`; `f1:real^(2,2)finite_sum->real^N`;
                   `g1:real^N->real^(2,2)finite_sum`; `p1:real^2`]
                  MOI_S38_SPINE_LOOP) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?cs:real^1->real^N.
      path cs /\ pathfinish cs = pathstart cs /\ path_image cs SUBSET s /\
      winding_number(sndcart o (gs:real^N->real^(2,2)finite_sum) o cs,vec 0) = Cx(&1)`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `(fs:real^(2,2)finite_sum->real^N) o
                (\t. pastecart (vec 0:real^2) (circlepath(vec 0,&1) t))` THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `fs:real^(2,2)finite_sum->real^N`;
                   `gs:real^N->real^(2,2)finite_sum`; `vec 0:real^2`]
                  MOI_S38_SPINE_LOOP) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?c2:real^1->real^N.
      path c2 /\ pathfinish c2 = pathstart c2 /\ path_image c2 SUBSET s2 /\
      winding_number(sndcart o (g2:real^N->real^(2,2)finite_sum) o c2,vec 0) = Cx(&1)`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `(f2:real^(2,2)finite_sum->real^N) o
                (\t. pastecart (vec 0:real^2) (circlepath(vec 0,&1) t))` THEN
    MP_TAC(ISPECL [`s2:real^N->bool`; `f2:real^(2,2)finite_sum->real^N`;
                   `g2:real^N->real^(2,2)finite_sum`; `vec 0:real^2`]
                  MOI_S38_SPINE_LOOP) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s1:real^N->bool) SUBSET s2 /\ path_image (c1:real^1->real^N) SUBSET s /\
                path_image (c1:real^1->real^N) SUBSET s2`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  (* Step A: the spine loop of s1 has degree +1 or -1 in s2 *)
  SUBGOAL_THEN
   `winding_number(sndcart o (g2:real^N->real^(2,2)finite_sum) o (c1:real^1->real^N),
                   vec 0) = Cx(&1) \/
    winding_number(sndcart o g2 o c1,vec 0) = --Cx(&1)`
  ASSUME_TAC THENL
   [REMOVE_THEN "shell" (MP_TAC o SPEC `c2:real^1->real^N`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `q0:real^1->real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `path_image (q0:real^1->real^N) SUBSET s2` ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
    SUBGOAL_THEN
     `winding_number(sndcart o (g2:real^N->real^(2,2)finite_sum) o (q0:real^1->real^N),
                     vec 0) = Cx(&1)`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`s2:real^N->bool`; `f2:real^(2,2)finite_sum->real^N`;
                     `g2:real^N->real^(2,2)finite_sum`; `c2:real^1->real^N`;
                     `q0:real^1->real^N`] MOI_S38_SOLID_TORUS_HOMOTOPIC_LOOPS_EQ) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o SYM);
      ALL_TAC] THEN
    MP_TAC(ISPECL [`s1:real^N->bool`; `s2:real^N->bool`;
                   `f1:real^(2,2)finite_sum->real^N`; `g1:real^N->real^(2,2)finite_sum`;
                   `f2:real^(2,2)finite_sum->real^N`; `g2:real^N->real^(2,2)finite_sum`;
                   `c1:real^1->real^N`; `q0:real^1->real^N`]
                  MOI_S38_DEGREE_COMPARE) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* Step B: hence degree +1 or -1 in s *)
  SUBGOAL_THEN
   `winding_number(sndcart o (gs:real^N->real^(2,2)finite_sum) o (c1:real^1->real^N),
                   vec 0) = Cx(&1) \/
    winding_number(sndcart o gs o c1,vec 0) = --Cx(&1)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^N->bool`; `s2:real^N->bool`;
                   `fs:real^(2,2)finite_sum->real^N`; `gs:real^N->real^(2,2)finite_sum`;
                   `f2:real^(2,2)finite_sum->real^N`; `g2:real^N->real^(2,2)finite_sum`;
                   `cs:real^1->real^N`; `c1:real^1->real^N`]
                  MOI_S38_DEGREE_COMPARE) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* Step C: every loop of s is homotopic in s to a power of c1 *)
  REWRITE_TAC[loops_carried] THEN X_GEN_TAC `gam:real^1->real^N` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `fs:real^(2,2)finite_sum->real^N`;
                 `gs:real^N->real^(2,2)finite_sum`; `c1:real^1->real^N`;
                 `gam:real^1->real^N`] MOI_S38_LOOP_AS_POWER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  MP_TAC(SPECL [`c1:real^1->real^N`; `n:num`] MOI_S38_LOOPPOW_LOOP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl) o
    check (can (find_term ((=) `moi_s38_looppow:(real^1->real^N)->num->real^1->real^N`))
           o concl)) THENL
   [EXISTS_TAC `moi_s38_looppow (c1:real^1->real^N) n`;
    EXISTS_TAC `reversepath(moi_s38_looppow (c1:real^1->real^N) n)`] THEN
  ASM_REWRITE_TAC[PATH_REVERSEPATH; PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH;
                  PATH_IMAGE_REVERSEPATH] THEN
  ASM_MESON_TAC[SUBSET_TRANS]);;

let MOISE_308 = prove
 (`MOISE_308_STATEMENT`,
  REWRITE_TAC[MOISE_308_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`s1:real^3->bool`; `s:real^3->bool`; `s2:real^3->bool`;
                       `j:real^3->bool`] THEN
  STRIP_TAC THEN MATCH_MP_TAC MOI_S38_CORE THEN
  EXISTS_TAC `s1:real^3->bool` THEN EXISTS_TAC `s2:real^3->bool` THEN
  SUBGOAL_THEN `(s1:real^3->bool) SUBSET s /\ (s:real^3->bool) SUBSET s2`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET_TRANS]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S38_SHELL_LOOPS THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET_TRANS]);;


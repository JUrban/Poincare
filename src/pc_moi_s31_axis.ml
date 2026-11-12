(* ========================================================================= *)
(* pc_moi_s31_axis: spines and transfer in a canonical configuration (Moise *)
(* GTM 47, 31.2-31.3, printed p.221).  Main theorems SPINES and TRANSFER    *)
(* (the statements MOI_S31_SPINES and MOI_S31_TRANSFER of                   *)
(* pc_moi_s3032_stmt).  Route: the angle around the x2 axis pulled back by  *)
(* h detects the loops of each solid torus s2 k (MOI_S4S_CARRIED_BY_DEGREE  *)
(* of pc_moi_s34_shell, MOI_S4T_CARRIES_UNIT of pc_moi_s34_trace).          *)
(* ========================================================================= *)

needs "src/pc_moi_s3032_stmt.ml";;
needs "src/pc_moi_s34_shell.ml";;   (* MOI_S4S_MAP_DEGREE, CARRIED_BY_DEGREE *)
needs "src/pc_moi_s34_trace.ml";;   (* MOI_S4T_CARRIES_UNIT *)
needs "src/pc_moi_s34_torus.ml";;   (* MOI_S4U_PL_SPHERE1_CIRCLE *)

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Part 1: revolutions and the angle around the x2 axis.  The circle        *)
(* of a point q of the open half-plane {q$3 = 0, q$1 > 0} is the image of   *)
(* the unit circle under moi_s3ax_circ q; the revolution of a compact       *)
(* subset of the half-plane is compact and misses the x2 axis; the angle    *)
(* moi_s3ax_ang (w$1,w$3)/|(w$1,w$3)| is continuous off the axis, takes     *)
(* values in the unit circle and inverts moi_s3ax_circ q.                   *)
(* ========================================================================= *)

let moi_s3ax_circ = new_definition
 `moi_s3ax_circ (q:real^3) (u:real^2) = vector[q$1 * u$1; q$2; q$1 * u$2]:real^3`;;

let moi_s3ax_ang = new_definition
 `moi_s3ax_ang (w:real^3) =
    inv(norm(vector[w$1; w$3]:real^2)) % vector[w$1; w$3]:real^2`;;

let MOI_S3AX_UNIT_SQUARES = prove
 (`!u:real^2. norm u = &1 ==> u$1 pow 2 + u$2 pow 2 = &1`,
  GEN_TAC THEN REWRITE_TAC[NORM_EQ_1; DOT_2] THEN CONV_TAC REAL_RING);;

let MOI_S3AX_REV_IMAGE = prove
 (`!x:real^3->bool.
     x SUBSET {q | q$3 = &0 /\ &0 < q$1}
     ==> revolution x =
         IMAGE (\z. moi_s3ax_circ (fstcart z) (sndcart z))
               (x PCROSS sphere(vec 0:real^2,&1))`,
  GEN_TAC THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_TAC THEN
  REWRITE_TAC[revolution; EXTENSION; IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS;
              FSTCART_PASTECART; SNDCART_PASTECART; IN_SPHERE_0; IN_ELIM_THM] THEN
  X_GEN_TAC `w:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `q:real^3`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`q:real^3`; `vector[(w:real^3)$1 / (q:real^3)$1; w$3 / q$1]:real^2`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[moi_s3ax_circ; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_2] THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < (q:real^3)$1` THEN CONV_TAC REAL_FIELD;
      REWRITE_TAC[NORM_EQ_1; DOT_2; VECTOR_2] THEN
      UNDISCH_TAC `(q:real^3)$1 pow 2 = (w:real^3)$1 pow 2 + w$3 pow 2` THEN
      UNDISCH_TAC `&0 < (q:real^3)$1` THEN CONV_TAC REAL_FIELD];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`q:real^3`; `u:real^2`] THEN STRIP_TAC THEN
    EXISTS_TAC `q:real^3` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `q:real^3`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[moi_s3ax_circ; VECTOR_3] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3AX_UNIT_SQUARES) THEN CONV_TAC REAL_RING]);;

let MOI_S3AX_REV_SING = prove
 (`!q:real^3.
     q$3 = &0 /\ &0 < q$1
     ==> revolution {q} = IMAGE (moi_s3ax_circ q) (sphere(vec 0:real^2,&1))`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `{q:real^3}` MOI_S3AX_REV_IMAGE) THEN
  ASM_REWRITE_TAC[SING_SUBSET; IN_ELIM_THM] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS; IN_SING;
              FSTCART_PASTECART; SNDCART_PASTECART] THEN
  MESON_TAC[]);;

let MOI_S3AX_RV_CONTINUOUS = prove
 (`!s. (\z:real^(3,2)finite_sum. moi_s3ax_circ (fstcart z) (sndcart z)) continuous_on s`,
  GEN_TAC THEN REWRITE_TAC[moi_s3ax_circ] THEN
  GEN_REWRITE_TAC I [CONTINUOUS_ON_COMPONENTWISE_LIFT] THEN
  REWRITE_TAC[DIMINDEX_3; ARITH_RULE `1 <= i /\ i <= 3 <=> i = 1 \/ i = 2 \/ i = 3`] THEN
  X_GEN_TAC `i:num` THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN REWRITE_TAC[VECTOR_3] THEN
  TRY(REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
      REWRITE_TAC[o_DEF] THEN CONJ_TAC) THEN
  MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN
  SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART; ETA_AX]);;

let MOI_S3AX_REV_COMPACT = prove
 (`!x:real^3->bool.
     compact x /\ x SUBSET {q | q$3 = &0 /\ &0 < q$1}
     ==> compact(revolution x) /\
         !w. w IN revolution x ==> ~(vector[w$1; w$3]:real^2 = vec 0)`,
  GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o MATCH_MP MOI_S3AX_REV_IMAGE) THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_SIMP_TAC[MOI_S3AX_RV_CONTINUOUS; COMPACT_PCROSS; COMPACT_SPHERE];
    REWRITE_TAC[revolution; IN_ELIM_THM] THEN X_GEN_TAC `w:real^3` THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(x:real^3->bool) SUBSET {q | q$3 = &0 /\ &0 < q$1}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN(MP_TAC o SPEC `q:real^3`) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VEC_COMPONENT] THEN
    STRIP_TAC THEN
    UNDISCH_TAC `(q:real^3)$1 pow 2 = (w:real^3)$1 pow 2 + w$3 pow 2` THEN
    ASM_REWRITE_TAC[REAL_ARITH `&0 pow 2 + &0 pow 2 = &0`; REAL_POW_EQ_0; ARITH_EQ] THEN
    ASM_REAL_ARITH_TAC]);;

(* The angle map. *)

let MOI_S3AX_ANG_CONTINUOUS = prove
 (`!s. (!w:real^3. w IN s ==> ~(vector[w$1; w$3]:real^2 = vec 0))
       ==> moi_s3ax_ang continuous_on s`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(\w:real^3. vector[w$1; w$3]:real^2) continuous_on s` ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [CONTINUOUS_ON_COMPONENTWISE_LIFT] THEN
    REWRITE_TAC[DIMINDEX_2; ARITH_RULE `1 <= i /\ i <= 2 <=> i = 1 \/ i = 2`] THEN
    X_GEN_TAC `i:num` THEN DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
    REWRITE_TAC[VECTOR_2] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT THEN
    REWRITE_TAC[DIMINDEX_3] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_s3ax_ang = (\w:real^3. inv(norm(vector[w$1; w$3]:real^2)) % vector[w$1; w$3])`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; moi_s3ax_ang]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\w:real^3. inv(norm(vector[w$1; w$3]:real^2))) =
                inv o (\w. norm(vector[w$1; w$3]:real^2))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_INV THEN ASM_SIMP_TAC[NORM_EQ_0] THEN
  REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
  ASM_REWRITE_TAC[]);;

let MOI_S3AX_ANG_SPHERE = prove
 (`!w:real^3. ~(vector[w$1; w$3]:real^2 = vec 0)
              ==> moi_s3ax_ang w IN sphere(vec 0:real^2,&1)`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[moi_s3ax_ang; IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
  MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[NORM_EQ_0]);;

let MOI_S3AX_ANG_CIRC = prove
 (`!(q:real^3) (u:real^2).
     &0 < q$1 /\ norm u = &1 ==> moi_s3ax_ang (moi_s3ax_circ q u) = u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s3ax_ang; moi_s3ax_circ; VECTOR_3] THEN
  SUBGOAL_THEN `vector[q$1 * (u:real^2)$1; q$1 * u$2]:real^2 = (q:real^3)$1 % u`
  SUBST1_TAC THENL
   [REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_MUL_COMPONENT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[NORM_MUL; REAL_MUL_RID; VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; REAL_MUL_LINV; REAL_LT_IMP_NZ;
               VECTOR_MUL_LID]);;

let MOI_S3AX_CIRC_CONTINUOUS = prove
 (`!(q:real^3) s. moi_s3ax_circ q continuous_on s`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `moi_s3ax_circ q = (\z:real^(3,2)finite_sum.
                  moi_s3ax_circ (fstcart z) (sndcart z)) o (\u:real^2. pastecart q u)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC[MOI_S3AX_RV_CONTINUOUS] THEN
  MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
  REWRITE_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID]);;

let MOI_S3AX_CIRC_INJ = prove
 (`!(q:real^3) (u:real^2) v.
     &0 < q$1 /\ moi_s3ax_circ q u = moi_s3ax_circ q v ==> u = v`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[moi_s3ax_circ; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; DIMINDEX_2;
              FORALL_2; REAL_EQ_MUL_LCANCEL] THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Part 2: a canonical configuration.  The points p j, p (j+1) lie in       *)
(* the open half-plane; the union U of the revolutions of dd j (j < 3) is   *)
(* compact and misses the x2 axis; the angle pulled back by the inverse of  *)
(* h on U is a continuous map r of IMAGE h U (which contains every s2 k)    *)
(* into the unit circle with r (h w) = ang w; the circle loop of a point q, *)
(* pushed forward by h, winds once under r.                                  *)
(* ========================================================================= *)

let MOI_S3AX_CC_POINTS = prove
 (`!(p:num->real^3) dd (h:real^3->real^3) s2 j.
     canonical_configuration p dd h s2 /\ j < 3
     ==> (p j)$3 = &0 /\ &0 < (p j)$1 /\ (p (j + 1))$3 = &0 /\ &0 < (p (j + 1))$1 /\
         revolution {p j} SUBSET revolution (segment[p j,p (j + 1)]) /\
         revolution {p (j + 1)} SUBSET revolution (segment[p j,p (j + 1)]) /\
         revolution (segment[p j,p (j + 1)]) SUBSET revolution (dd j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[canonical_configuration; planar_cell_chain] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
    can (find_term ((=) `relative_interior:(real^3->bool)->real^3->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `segment[(p:num->real^3) j,p (j + 1)] SUBSET dd (j:num)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `relative_interior((dd:num->real^3->bool) j)` THEN
    ASM_REWRITE_TAC[RELATIVE_INTERIOR_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:num->real^3) j IN dd (j:num) /\ p (j + 1) IN dd j` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(p:num->real^3) j`; `(p:num->real^3) (j + 1)`] ENDS_IN_SEGMENT) THEN
    UNDISCH_TAC `segment[(p:num->real^3) j,p (j + 1)] SUBSET dd (j:num)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!q:real^3. q IN (dd:num->real^3->bool) j ==> q$3 = &0 /\ &0 < q$1`
  (fun th -> MP_TAC(SPEC `(p:num->real^3) j` th) THEN
             MP_TAC(SPEC `(p:num->real^3) (j + 1)` th)) THENL
   [UNDISCH_TAC `(dd:num->real^3->bool) j SUBSET {q:real^3 | q$3 = &0 /\ &0 < q$1}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN MATCH_MP_TAC MOI_STD_REV_MONO THEN
  ASM_REWRITE_TAC[SING_SUBSET; ENDS_IN_SEGMENT]);;

let MOI_S3AX_CC_U = prove
 (`!(p:num->real^3) dd (h:real^3->real^3) s2.
     canonical_configuration p dd h s2
     ==> compact (UNIONS {revolution (dd j) | j < 3}) /\
         (!w. w IN UNIONS {revolution (dd j) | j < 3}
              ==> ~(vector[w$1; w$3]:real^2 = vec 0)) /\
         (!k. k < 3 ==> revolution (dd k) SUBSET UNIONS {revolution (dd j) | j < 3} /\
                        s2 k SUBSET IMAGE h (UNIONS {revolution (dd j) | j < 3}))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [canonical_configuration]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [planar_cell_chain]) THEN
  SUBGOAL_THEN
   `!j. j < 3 ==> compact(revolution ((dd:num->real^3->bool) j)) /\
                  !w. w IN revolution (dd j) ==> ~(vector[w$1; w$3]:real^2 = vec 0)`
  (LABEL_TAC "rj") THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_S3AX_REV_COMPACT THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
      can (find_term ((=) `relative_interior:(real^3->bool)->real^3->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[disk_with_boundary] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC (K ALL_TAC))) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`ff:real^2->real^3`; `gg:real^3->real^2`] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      can (term_match [] `IMAGE (ff:real^2->real^3) (cball(vec 0,&1)) = x`) (concl th))) THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[COMPACT_CBALL];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC COMPACT_UNIONS THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT; FORALL_IN_IMAGE; IN_ELIM_THM];
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `revolution ((dd:num->real^3->bool) k) SUBSET
                  UNIONS {revolution (dd j) | j < 3}` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
      can (find_term ((=) `pl_solid_torus:(real^3->bool)->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `interior(IMAGE (h:real^3->real^3) (revolution ((dd:num->real^3->bool) k)))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (h:real^3->real^3) (revolution ((dd:num->real^3->bool) k))` THEN
    REWRITE_TAC[INTERIOR_SUBSET] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]]);;

(* The pulled-back angle. *)

let MOI_S3AX_CC_ANGLE = prove
 (`!(p:num->real^3) dd (h:real^3->real^3) s2.
     canonical_configuration p dd h s2
     ==> ?r:real^3->real^2.
           r continuous_on IMAGE h (UNIONS {revolution (dd j) | j < 3}) /\
           IMAGE r (IMAGE h (UNIONS {revolution (dd j) | j < 3})) SUBSET
           sphere(vec 0:real^2,&1) /\
           (!w. w IN UNIONS {revolution (dd j) | j < 3} ==> r(h w) = moi_s3ax_ang w)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3AX_CC_U) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [canonical_configuration]) THEN
  ABBREV_TAC `U = UNIONS {revolution ((dd:num->real^3->bool) j) | j < 3}` THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `h:real^3->real^3`; `IMAGE (h:real^3->real^3) U`]
                HOMEOMORPHISM_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `hinv:real^3->real^3` MP_TAC) THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  EXISTS_TAC `moi_s3ax_ang o (hinv:real^3->real^3)` THEN
  ASM_SIMP_TAC[o_THM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S3AX_ANG_CONTINUOUS THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN ASM_SIMP_TAC[MOI_S3AX_ANG_SPHERE]]);;

(* The circle loop of a point, pushed forward by h. *)

let MOI_S3AX_CIRCLE_LOOP = prove
 (`!(h:real^3->real^3) (r:real^3->real^2) u q.
     q$3 = &0 /\ &0 < q$1 /\ revolution {q} SUBSET u /\ h continuous_on u /\
     (!w. w IN u ==> r(h w) = moi_s3ax_ang w)
     ==> path (h o moi_s3ax_circ q o circlepath(vec 0,&1)) /\
         pathfinish (h o moi_s3ax_circ q o circlepath(vec 0,&1)) =
         pathstart (h o moi_s3ax_circ q o circlepath(vec 0,&1)) /\
         path_image (h o moi_s3ax_circ q o circlepath(vec 0,&1)) =
         IMAGE h (revolution {q}) /\
         winding_number(r o h o moi_s3ax_circ q o circlepath(vec 0,&1),vec 0) = Cx(&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_ASSUME_TAC MOI_FH1_CIRCLEPATH_FACTS THEN
  SUBGOAL_THEN `!t. moi_s3ax_circ q (circlepath(vec 0,&1) t) IN revolution {q:real^3}`
  ASSUME_TAC THENL
   [GEN_TAC THEN ASM_SIMP_TAC[MOI_S3AX_REV_SING] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    REWRITE_TAC[MOI_S4S_CIRCLEPATH_SPHERE];
    ALL_TAC] THEN
  SUBGOAL_THEN `path_image (moi_s3ax_circ q o circlepath(vec 0,&1)) = revolution {q:real^3}`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_S3AX_REV_SING; PATH_IMAGE_COMPOSE]; ALL_TAC] THEN
  SUBGOAL_THEN `path (moi_s3ax_circ q o circlepath(vec 0,&1))` ASSUME_TAC THENL
   [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[MOI_S3AX_CIRC_CONTINUOUS];
    ALL_TAC] THEN
  REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `u:real^3->bool` THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[PATH_IMAGE_COMPOSE; MOI_S3AX_REV_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN `(r:real^3->real^2) o h o moi_s3ax_circ q o circlepath(vec 0,&1) =
                circlepath(vec 0,&1)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `t:real^1` THEN
    SUBGOAL_THEN `moi_s3ax_circ q (circlepath(vec 0,&1) t) IN (u:real^3->bool)`
    (fun th -> ASM_SIMP_TAC[th]) THENL
     [UNDISCH_TAC `revolution {q:real^3} SUBSET u` THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real^1` o check (fun th ->
        can (find_term ((=) `circlepath:complex#real->real^1->complex`)) (concl th) &&
        is_forall(concl th))) THEN
      SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_S3AX_ANG_CIRC THEN
    ASM_REWRITE_TAC[GSYM IN_SPHERE_0; MOI_S4S_CIRCLEPATH_SPHERE];
    ASM_REWRITE_TAC[]]);;

(* The circles of the end points of segment j. *)

let MOI_S3AX_CC_CIRCLES = prove
 (`!(p:num->real^3) dd (h:real^3->real^3) s2 j (r:real^3->real^2) k.
     canonical_configuration p dd h s2 /\ j < 3 /\ (k = j \/ k = j + 1) /\
     (!w. w IN UNIONS {revolution (dd i) | i < 3} ==> r(h w) = moi_s3ax_ang w)
     ==> IMAGE h (revolution {p k}) SUBSET interior (s2 j) /\
         path (h o moi_s3ax_circ (p k) o circlepath(vec 0,&1)) /\
         pathfinish (h o moi_s3ax_circ (p k) o circlepath(vec 0,&1)) =
         pathstart (h o moi_s3ax_circ (p k) o circlepath(vec 0,&1)) /\
         path_image (h o moi_s3ax_circ (p k) o circlepath(vec 0,&1)) =
         IMAGE h (revolution {p k}) /\
         winding_number(r o h o moi_s3ax_circ (p k) o circlepath(vec 0,&1),vec 0) =
         Cx(&1) /\
         IMAGE h (revolution {p k}) homeomorphic sphere(vec 0:real^2,&1)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "k") ASSUME_TAC))) THEN
  MP_TAC(SPECL [`p:num->real^3`; `dd:num->real^3->bool`; `h:real^3->real^3`;
                `s2:num->real^3->bool`; `j:num`] MOI_S3AX_CC_POINTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `((p:num->real^3) k)$3 = &0 /\ &0 < (p k)$1 /\
    revolution {p k} SUBSET revolution (segment[p j,p (j + 1)])`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "k" (DISJ_CASES_THEN SUBST1_TAC) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`p:num->real^3`; `dd:num->real^3->bool`; `h:real^3->real^3`;
                `s2:num->real^3->bool`] MOI_S3AX_CC_U) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [canonical_configuration]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
    can (find_term ((=) `pl_solid_torus:(real^3->bool)->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
    is_forall(concl th) &&
    can (find_term ((=) `IMAGE:(real^3->real^3)->(real^3->bool)->real^3->bool`)) (concl th) &&
    not(can (find_term ((=) `interior:(real^3->bool)->real^3->bool`)) (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `U = UNIONS {revolution ((dd:num->real^3->bool) i) | i < 3}` THEN
  SUBGOAL_THEN `revolution {(p:num->real^3) k} SUBSET U` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`revolution {(p:num->real^3) k} SUBSET revolution (segment[p j,p (j + 1)])`;
      `revolution (segment[(p:num->real^3) j,p (j + 1)]) SUBSET revolution (dd j)`;
      `revolution ((dd:num->real^3->bool) j) SUBSET U`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:real^3->real^3`; `r:real^3->real^2`; `U:real^3->bool`;
                 `(p:num->real^3) k`] MOI_S3AX_CIRCLE_LOOP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (h:real^3->real^3) (revolution (segment[(p:num->real^3) j,p (j + 1)]))` THEN
    ASM_SIMP_TAC[IMAGE_SUBSET];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_S3AX_REV_SING; GSYM IMAGE_o] THEN
  ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
  EXISTS_TAC `(h:real^3->real^3) o moi_s3ax_circ ((p:num->real^3) k)` THEN
  MATCH_MP_TAC HOMEOMORPHISM_COMPACT THEN REWRITE_TAC[COMPACT_SPHERE] THEN
  SUBGOAL_THEN `IMAGE (moi_s3ax_circ ((p:num->real^3) k)) (sphere(vec 0:real^2,&1)) SUBSET U`
  ASSUME_TAC THENL
   [MP_TAC(SPEC `(p:num->real^3) k` MOI_S3AX_REV_SING) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC[MOI_S3AX_CIRC_CONTINUOUS] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `U:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[o_THM] THEN MAP_EVERY X_GEN_TAC [`a:real^2`; `b:real^2`] THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_S3AX_CIRC_INJ THEN EXISTS_TAC `(p:num->real^3) k` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!x y. x IN (U:real^3->bool) /\ y IN U /\ (h:real^3->real^3) x = h y
                               ==> x = y`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (moi_s3ax_circ ((p:num->real^3) k)) (sphere(vec 0:real^2,&1)) SUBSET U` THEN
    UNDISCH_TAC `(a:real^2) IN sphere(vec 0,&1)` THEN
    UNDISCH_TAC `(b:real^2) IN sphere(vec 0,&1)` THEN SET_TAC[]]);;

(* ========================================================================= *)
(* Part 3: the theorem SPINES.  The circle h(rev{p k}) lies in the          *)
(* interior of s2 j and is homeomorphic to S1 (Part 2); its loop winds once *)
(* under the pulled-back angle r, and s2 j is a solid torus                  *)
(* (PL_SOLID_TORUS_BASIC), so the circle carries the loops of s2 j          *)
(* (MOI_S4S_CARRIED_BY_DEGREE).                                              *)
(* ========================================================================= *)

let MOI_S3AX_CC_SOLID_TORUS = prove
 (`!(p:num->real^3) dd (h:real^3->real^3) s2 j.
     (!s:real^3->bool. pl_solid_torus s ==> solid_torus s /\ ?j. spine j s /\ pl_sphere 1 j) /\
     canonical_configuration p dd h s2 /\ j < 3
     ==> ?f g. homeomorphism
                 (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1),s2 j) (f,g)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "basic") STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC MOI_S38_SOLID_TORUS_HOMEO THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [canonical_configuration]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
    can (find_term ((=) `pl_solid_torus:(real^3->bool)->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "basic" (fun th ->
    MP_TAC(MATCH_MP th (ASSUME `pl_solid_torus((s2:num->real^3->bool) j)`))) THEN
  SIMP_TAC[]);;

let SPINES = prove
 (MOI_S31_SPINES,
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "basic") (K ALL_TAC)))) THEN
  MAP_EVERY X_GEN_TAC [`p:num->real^3`; `dd:num->real^3->bool`; `h:real^3->real^3`;
                       `s2:num->real^3->bool`; `j:num`; `k:num`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  MP_TAC(MATCH_MP MOI_S3AX_CC_ANGLE
    (ASSUME `canonical_configuration (p:num->real^3) dd (h:real^3->real^3) s2`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^3->real^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`p:num->real^3`; `dd:num->real^3->bool`; `h:real^3->real^3`;
                `s2:num->real^3->bool`; `j:num`; `r:real^3->real^2`; `k:num`]
               MOI_S3AX_CC_CIRCLES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`p:num->real^3`; `dd:num->real^3->bool`; `h:real^3->real^3`;
                `s2:num->real^3->bool`] MOI_S3AX_CC_U) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
    is_forall(concl th) &&
    can (find_term ((=) `IMAGE:(real^3->real^3)->(real^3->bool)->real^3->bool`)) (concl th) &&
    not(can (find_term ((=) `interior:(real^3->bool)->real^3->bool`)) (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:num->real^3`; `dd:num->real^3->bool`; `h:real^3->real^3`;
                `s2:num->real^3->bool`; `j:num`] MOI_S3AX_CC_SOLID_TORUS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^(2,2)finite_sum->real^3`
    (X_CHOOSE_TAC `g:real^3->real^(2,2)finite_sum`)) THEN
  MATCH_MP_TAC MOI_S4S_CARRIED_BY_DEGREE THEN
  MAP_EVERY EXISTS_TAC
   [`f:real^(2,2)finite_sum->real^3`; `g:real^3->real^(2,2)finite_sum`;
    `r:real^3->real^2`;
    `(h:real^3->real^3) o moi_s3ax_circ ((p:num->real^3) k) o circlepath(vec 0,&1)`] THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (h:real^3->real^3) (UNIONS {revolution ((dd:num->real^3->bool) j) | j < 3})` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (r:real^3->real^2)
                  (IMAGE (h:real^3->real^3) (UNIONS {revolution ((dd:num->real^3->bool) j) | j < 3}))` THEN
    ASM_SIMP_TAC[IMAGE_SUBSET];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `interior((s2:num->real^3->bool) j)` THEN
    ASM_REWRITE_TAC[INTERIOR_SUBSET]]);;

(* ========================================================================= *)
(* Part 4: the theorem TRANSFER.  In a solid torus x with a map r into      *)
(* the circle and a loop of r-winding 1, a loop is null-homotopic iff its   *)
(* r-winding is 0 (the powers of the s308 degree tools); the inclusion of a *)
(* circle gg = ff(S1) is null-homotopic iff the loop ff o circlepath is     *)
(* (HOMOTOPIC_CIRCLEMAPS_IMP_HOMOTOPIC_LOOPS and the converse).  For s2 j   *)
(* and s2 (j+1) the common circle h(rev{p (j+1)}) provides the loop of      *)
(* winding 1, so both conditions become winding(r o l) = 0, and carrying    *)
(* H_1 forces winding +-1 (MOI_S4T_CARRIES_UNIT), hence loops in both.      *)
(* ========================================================================= *)

let MOI_S3AX_NULL_BY_WINDING = prove
 (`!(x:real^N->bool) f g (r:real^N->real^2) c q.
     homeomorphism (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1),x) (f,g) /\
     r continuous_on x /\ IMAGE r x SUBSET sphere(vec 0:real^2,&1) /\
     path c /\ pathfinish c = pathstart c /\ path_image c SUBSET x /\
     winding_number(r o c,vec 0) = Cx(&1) /\
     path q /\ pathfinish q = pathstart q /\ path_image q SUBSET x
     ==> ((?z. homotopic_loops x q (linepath(z,z))) <=>
          winding_number(r o q,vec 0) = Cx(&0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (r:real^N->real^2) x SUBSET (:complex) DELETE vec 0` ASSUME_TAC THENL
   [MP_TAC MOI_FH1_ORIGIN_NOT_IN_CIRCLE THEN
    UNDISCH_TAC `IMAGE (r:real^N->real^2) x SUBSET sphere(vec 0:real^2,&1)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. homotopic_loops x a b
          ==> winding_number((r:real^N->real^2) o a,vec 0) = winding_number(r o b,vec 0)`
  (LABEL_TAC "hw") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WINDING_NUMBER_HOMOTOPIC_LOOPS THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE THEN EXISTS_TAC `x:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(r:real^N->real^2) continuous_on path_image c /\
    ~(vec 0 IN IMAGE r (path_image (c:real^1->real^N)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `x:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `IMAGE (r:real^N->real^2) x SUBSET (:complex) DELETE vec 0` THEN
      UNDISCH_TAC `path_image (c:real^1->real^N) SUBSET x` THEN SET_TAC[]];
    ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `z:real^N` ASSUME_TAC) THEN
    SUBGOAL_THEN `(z:real^N) IN x` ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o CONJUNCT2 o MATCH_MP HOMOTOPIC_LOOPS_IMP_SUBSET) THEN
      REWRITE_TAC[PATH_IMAGE_LINEPATH; SEGMENT_REFL; SING_SUBSET];
      ALL_TAC] THEN
    USE_THEN "hw" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `homotopic_loops x (q:real^1->real^N) (linepath(z,z))`))) THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MOI_FH1_COMPOSE_LINEPATH_REFL] THEN
    MATCH_MP_TAC WINDING_NUMBER_TRIVIAL THEN
    UNDISCH_TAC `IMAGE (r:real^N->real^2) x SUBSET (:complex) DELETE vec 0` THEN
    UNDISCH_TAC `(z:real^N) IN x` THEN SET_TAC[];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`x:real^N->bool`; `f:real^(2,2)finite_sum->real^N`;
                 `g:real^N->real^(2,2)finite_sum`; `r:real^N->real^2`;
                 `c:real^1->real^N`] MOI_S4S_MAP_DEGREE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`x:real^N->bool`; `f:real^(2,2)finite_sum->real^N`;
                 `g:real^N->real^(2,2)finite_sum`; `c:real^1->real^N`;
                 `q:real^1->real^N`] MOI_S38_LOOP_AS_POWER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `n:num` (LABEL_TAC "pow")) THEN
  MP_TAC(ISPECL [`c:real^1->real^N`; `n:num`] MOI_S38_LOOPPOW_LOOP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`r:real^N->real^2`; `c:real^1->real^N`; `n:num`] MOI_S38_WINDING_LOOPPOW) THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_RID] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`r:real^N->real^2`; `moi_s38_looppow (c:real^1->real^N) n`]
                MOI_S38_WINDING_REVERSEPATH_COMPOSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `path_image (c:real^1->real^N)` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `~(vec 0 IN IMAGE (r:real^N->real^2) (path_image (c:real^1->real^N)))` THEN
      UNDISCH_TAC `path_image (moi_s38_looppow (c:real^1->real^N) n) SUBSET path_image c` THEN
      SET_TAC[]];
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  SUBGOAL_THEN `n = 0` SUBST_ALL_TAC THENL
   [USE_THEN "pow" (DISJ_CASES_THEN (fun th -> USE_THEN "hw" (fun hw ->
      MP_TAC(MATCH_MP hw th)))) THEN
    ASM_REWRITE_TAC[GSYM CX_NEG; CX_INJ; REAL_ARITH `!x. &0 = --x <=> x = &0`;
                    REAL_OF_NUM_EQ] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `pathstart (c:real^1->real^N)` THEN
  USE_THEN "pow" (DISJ_CASES_THEN MP_TAC) THEN
  REWRITE_TAC[moi_s38_looppow; REVERSEPATH_LINEPATH]);;

(* The inclusion of a circle and the loop around it. *)

let MOI_S3AX_CIRCLEPATH_CEXP = prove
 (`!t. circlepath(vec 0,&1) t = cexp(Cx(&2 * pi * drop t) * ii)`,
  GEN_TAC THEN REWRITE_TAC[CIRCLEPATH; COMPLEX_VEC_0; COMPLEX_ADD_LID; COMPLEX_MUL_LID] THEN
  AP_TERM_TAC THEN REWRITE_TAC[CX_MUL] THEN CONV_TAC COMPLEX_RING);;

let MOI_S3AX_INCLUSION_NULL = prove
 (`!(s:real^N->bool) gg (ff:real^2->real^N) gf.
     homeomorphism (sphere(vec 0:real^2,&1),gg) (ff,gf) /\ gg SUBSET s
     ==> ((?z. homotopic_with (\f. T)
                 (subtopology euclidean gg,subtopology euclidean s) (\x. x) (\x. z)) <=>
          (?z. homotopic_loops s (ff o circlepath(vec 0,&1)) (linepath(z,z))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `(ff:real^2->real^N) o circlepath(vec 0,&1) =
                ff o cexp o (\t. Cx(&2 * pi * drop t) * ii)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; MOI_S3AX_CIRCLEPATH_CEXP]; ALL_TAC] THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_TAC `z:real^N`) THEN EXISTS_TAC `z:real^N` THENL
   [MP_TAC(ISPECL [`\f:real^2->real^N. T`; `\x:real^N. x`; `\x:real^N. (z:real^N)`;
                   `ff:real^2->real^N`; `sphere(vec 0:real^2,&1)`; `gg:real^N->bool`;
                   `s:real^N->bool`] HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT) THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN
    DISCH_THEN(MP_TAC o MATCH_MP HOMOTOPIC_CIRCLEMAPS_IMP_HOMOTOPIC_LOOPS) THEN
    MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM; LINEPATH_REFL];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_HOMOTOPIC_CIRCLEMAPS) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `homotopic_with (\h. T)
      (subtopology euclidean (sphere(vec 0:real^2,&1)),subtopology euclidean s)
      (ff:real^2->real^N) (\w. z)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP] o
                  MATCH_MP (REWRITE_RULE[IMP_CONJ] HOMOTOPIC_WITH_EQ)) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; o_THM; LINEPATH_REFL; LIFT_DROP] THEN
    X_GEN_TAC `w:real^2` THEN REWRITE_TAC[IN_SPHERE_0] THEN DISCH_TAC THEN
    AP_TERM_TAC THEN
    SUBGOAL_THEN `&2 * pi * Arg w / (&2 * pi) = Arg w` SUBST1_TAC THENL
     [MP_TAC PI_POS THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MP_TAC(last(CONJUNCTS(SPEC `w:complex` ARG))) THEN
    ASM_REWRITE_TAC[COMPLEX_MUL_LID] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
    AP_TERM_TAC THEN MATCH_ACCEPT_TAC COMPLEX_MUL_SYM;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\h:real^N->real^N. T`; `ff:real^2->real^N`; `\w:real^2. (z:real^N)`;
                 `gf:real^N->real^2`; `gg:real^N->bool`; `sphere(vec 0:real^2,&1)`;
                 `s:real^N->bool`] HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  DISCH_THEN(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP] o
             MATCH_MP (REWRITE_RULE[IMP_CONJ] HOMOTOPIC_WITH_EQ)) THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; o_THM] THEN ASM_SIMP_TAC[]);;

(* The theorem TRANSFER. *)

let TRANSFER = prove
 (MOI_S31_TRANSFER,
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (LABEL_TAC "basic") (K ALL_TAC)) (K ALL_TAC)))) THEN
  MAP_EVERY X_GEN_TAC [`p:num->real^3`; `dd:num->real^3->bool`; `h:real^3->real^3`;
                       `s2:num->real^3->bool`; `j:num`; `gg:real^3->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `j + 1 < 3` ASSUME_TAC THENL [UNDISCH_TAC `j < 2` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `j < 3` ASSUME_TAC THENL [UNDISCH_TAC `j < 2` THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(MATCH_MP MOI_S3AX_CC_ANGLE
    (ASSUME `canonical_configuration (p:num->real^3) dd (h:real^3->real^3) s2`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^3->real^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`p:num->real^3`; `dd:num->real^3->bool`; `h:real^3->real^3`;
                `s2:num->real^3->bool`] MOI_S3AX_CC_U) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the common circle and the two solid tori *)
  ABBREV_TAC `c = (h:real^3->real^3) o moi_s3ax_circ ((p:num->real^3) (j + 1)) o
                  circlepath(vec 0,&1)` THEN
  SUBGOAL_THEN
   `!k. (k = j \/ k = j + 1)
        ==> (?f g. homeomorphism
                     (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1),s2 k) (f,g)) /\
            (r:real^3->real^2) continuous_on s2 k /\
            IMAGE r (s2 k) SUBSET sphere(vec 0:real^2,&1) /\
            path (c:real^1->real^3) /\ pathfinish c = pathstart c /\
            path_image c SUBSET s2 k /\ winding_number(r o c,vec 0) = Cx(&1)`
  (LABEL_TAC "tori") THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `k < 3` ASSUME_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(j + 1 = k) \/ (j + 1 = k + 1)` ASSUME_TAC THENL
     [UNDISCH_TAC `k = j \/ k = j + 1` THEN ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`p:num->real^3`; `dd:num->real^3->bool`; `h:real^3->real^3`;
                  `s2:num->real^3->bool`; `k:num`; `r:real^3->real^2`; `j + 1`]
                 MOI_S3AX_CC_CIRCLES) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(j + 1 = k) \/ (j + 1 = k + 1)` THEN MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`p:num->real^3`; `dd:num->real^3->bool`; `h:real^3->real^3`;
                  `s2:num->real^3->bool`; `k:num`] MOI_S3AX_CC_SOLID_TORUS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `IMAGE:(real^3->real^3)->(real^3->bool)->real^3->bool`)) (concl th) &&
      not(can (find_term ((=) `interior:(real^3->bool)->real^3->bool`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (h:real^3->real^3)
                    (UNIONS {revolution ((dd:num->real^3->bool) i) | i < 3})` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (r:real^3->real^2)
                    (IMAGE (h:real^3->real^3)
                       (UNIONS {revolution ((dd:num->real^3->bool) i) | i < 3}))` THEN
      ASM_SIMP_TAC[IMAGE_SUBSET];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `interior((s2:num->real^3->bool) k)` THEN
      ASM_REWRITE_TAC[INTERIOR_SUBSET]];
    ALL_TAC] THEN
  (* the circle gg and its loop *)
  MP_TAC(MATCH_MP MOI_S4U_PL_SPHERE1_CIRCLE (ASSUME `pl_sphere 1 (gg:real^3->bool)`)) THEN
  ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
  DISCH_THEN(X_CHOOSE_THEN `ff:real^2->real^3` (X_CHOOSE_TAC `gf:real^3->real^2`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
    can (find_term ((=) `ff:real^2->real^3`)) (concl th))) THEN
  SUBGOAL_THEN
   `simple_path ((ff:real^2->real^3) o circlepath(vec 0,&1)) /\
    path (ff o circlepath(vec 0,&1)) /\
    pathfinish (ff o circlepath(vec 0,&1)) = pathstart (ff o circlepath(vec 0,&1)) /\
    path_image (ff o circlepath(vec 0,&1)) = gg`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATH_IMAGE_COMPOSE;
                MOI_FH1_CIRCLEPATH_FACTS] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN
    REWRITE_TAC[SIMPLE_PATH_IMP_PATH] THEN
    MATCH_MP_TAC SIMPLE_PATH_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[SIMPLE_PATH_CIRCLEPATH; MOI_FH1_CIRCLEPATH_FACTS; REAL_OF_NUM_EQ;
                    ARITH_EQ] THEN
    UNDISCH_TAC `!x. x IN sphere(vec 0,&1)
                     ==> (gf:real^3->real^2)((ff:real^2->real^3) x) = x` THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `l = (ff:real^2->real^3) o circlepath(vec 0,&1)` THEN
  SUBGOAL_THEN `(gg:real^3->bool) SUBSET s2 j /\ gg SUBSET s2 (j + 1)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(gg:real^3->bool) SUBSET s2 j INTER s2 (j + 1)` THEN SET_TAC[];
    ALL_TAC] THEN
  (* null-homotopy in either torus means winding 0 *)
  SUBGOAL_THEN
   `!k. (k = j \/ k = j + 1)
        ==> ((?z. homotopic_with (\f. T)
                    (subtopology euclidean (gg:real^3->bool),
                     subtopology euclidean ((s2:num->real^3->bool) k)) (\x. x) (\x. z)) <=>
             winding_number((r:real^3->real^2) o l,vec 0) = Cx(&0))`
  (LABEL_TAC "null") THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "tori" (fun th -> MP_TAC(MATCH_MP th (ASSUME `k = j \/ k = j + 1`))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `f:real^(2,2)finite_sum->real^3`
      (X_CHOOSE_TAC `g:real^3->real^(2,2)finite_sum`)) STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(gg:real^3->bool) SUBSET s2 (k:num)` ASSUME_TAC THENL
     [UNDISCH_TAC `k = j \/ k = j + 1` THEN STRIP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`(s2:num->real^3->bool) k`; `gg:real^3->bool`; `ff:real^2->real^3`;
                   `gf:real^3->real^2`] MOI_S3AX_INCLUSION_NULL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC MOI_S3AX_NULL_BY_WINDING THEN
    MAP_EVERY EXISTS_TAC [`f:real^(2,2)finite_sum->real^3`; `g:real^3->real^(2,2)finite_sum`;
                          `c:real^1->real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    USE_THEN "null" (MP_TAC o SPEC `j:num`) THEN
    USE_THEN "null" (MP_TAC o SPEC `j + 1`) THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[]] THEN
  (* carrying H_1 gives winding +-1 *)
  DISCH_TAC THEN
  SUBGOAL_THEN
   `winding_number((r:real^3->real^2) o l,vec 0) = Cx(&1) \/
    winding_number(r o l,vec 0) = --Cx(&1)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `?k. (k = j \/ k = j + 1) /\ carries_h1 gg ((s2:num->real^3->bool) k)`
    (X_CHOOSE_THEN `k:num` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THENL
     [UNDISCH_TAC `carries_h1 (gg:real^3->bool) (s2 j) \/ carries_h1 gg (s2 (j + 1))` THEN
      MESON_TAC[];
      ALL_TAC] THEN
    USE_THEN "tori" (fun th -> MP_TAC(MATCH_MP th (ASSUME `k = j \/ k = j + 1`))) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(gg:real^3->bool) SUBSET s2 (k:num)` ASSUME_TAC THENL
     [UNDISCH_TAC `k = j \/ k = j + 1` THEN STRIP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`(s2:num->real^3->bool) k`; `r:real^3->real^2`;
                   `l:real^1->real^3`; `c:real^1->real^3`] MOI_S4T_CARRIES_UNIT) THEN
    ASM_REWRITE_TAC[GSYM COMPLEX_VEC_0];
    ALL_TAC] THEN
  (* hence the loops of both solid tori *)
  SUBGOAL_THEN
   `!k. (k = j \/ k = j + 1) ==> loops_carried gg ((s2:num->real^3->bool) k)`
  (fun th -> CONJ_TAC THEN MATCH_MP_TAC th THEN REWRITE_TAC[]) THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  USE_THEN "tori" (fun th -> MP_TAC(MATCH_MP th (ASSUME `k = j \/ k = j + 1`))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `f:real^(2,2)finite_sum->real^3`
    (X_CHOOSE_TAC `g:real^3->real^(2,2)finite_sum`)) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(gg:real^3->bool) SUBSET s2 (k:num)` ASSUME_TAC THENL
   [UNDISCH_TAC `k = j \/ k = j + 1` THEN STRIP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_S4S_CARRIED_BY_DEGREE THEN
  MAP_EVERY EXISTS_TAC [`f:real^(2,2)finite_sum->real^3`; `g:real^3->real^(2,2)finite_sum`;
                        `r:real^3->real^2`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th ->
    is_disj(concl th) && can (find_term ((=) `l:real^1->real^3`)) (concl th))) THENL
   [EXISTS_TAC `l:real^1->real^3` THEN ASM_REWRITE_TAC[SUBSET_REFL];
    EXISTS_TAC `reversepath(l:real^1->real^3)` THEN
    ASM_REWRITE_TAC[PATH_REVERSEPATH; PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH;
                    PATH_IMAGE_REVERSEPATH; SUBSET_REFL] THEN
    MP_TAC(ISPECL [`r:real^3->real^2`; `l:real^1->real^3`]
                  MOI_S38_WINDING_REVERSEPATH_COMPOSE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(s2:num->real^3->bool) k` THEN
        ASM_REWRITE_TAC[];
        MP_TAC MOI_FH1_ORIGIN_NOT_IN_CIRCLE THEN
        UNDISCH_TAC `IMAGE (r:real^3->real^2) ((s2:num->real^3->bool) k) SUBSET
                     sphere(vec 0:real^2,&1)` THEN
        UNDISCH_TAC `(gg:real^3->bool) SUBSET s2 (k:num)` THEN SET_TAC[]];
      ASM_REWRITE_TAC[COMPLEX_NEG_NEG]]]);;


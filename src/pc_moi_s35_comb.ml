(* ========================================================================= *)
(* pc_moi_s35_comb: Moise GTM 47, Sec 35.1, the circle removal at all edges *)
(* at once (main theorem COMBINE = MOI_S35_COMBINE_R1 of                    *)
(* pc_moi_s35_stmt_r1.ml: COMBINE of pc_moi_s35_stmt.ml with                *)
(* graph_in_complex and the charts as antecedents, so that the ends of an   *)
(* edge are vertices and a vertex has finitely many B-side edges).  Per     *)
(* vertex, the per-edge removal MOI_S35_REMOVAL is applied in turn at its   *)
(* finitely many B-side edges; the changes lie in disjoint tubes.           *)
(* ========================================================================= *)

needs "src/pc_moi_s35_stmt_r1.ml";;
needs "src/pc_moi_s35_cells.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Closure, interior and frontier off a closed set; the parts of the        *)
(* slab; the two cells of an edge configuration meet and differ.            *)
(* ------------------------------------------------------------------------- *)

let MOI_S5K_CLOSURE_OFF = prove
 (`!x m:real^N->bool. closed m ==> closure x DIFF m = closure (x DIFF m) DIFF m`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^N) DIFF m`; `x:real^N->bool`] OPEN_INTER_CLOSURE_SUBSET) THEN
  ASM_REWRITE_TAC[GSYM closed] THEN
  MP_TAC(ISPECL [`x DIFF m:real^N->bool`; `x:real^N->bool`] SUBSET_CLOSURE) THEN
  REWRITE_TAC[SUBSET_DIFF] THEN
  SUBGOAL_THEN `((:real^N) DIFF m) INTER x = x DIFF m` SUBST1_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  SET_TAC[]);;

let MOI_S5K_INTERIOR_OFF = prove
 (`!x m:real^N->bool. closed m ==> interior x DIFF m = interior (x DIFF m) DIFF m`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [SUBGOAL_THEN `interior x DIFF m = interior x INTER ((:real^N) DIFF m)` SUBST1_TAC THENL
     [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE
     `!a b:real^N->bool. a SUBSET b /\ a SUBSET (:real^N) DIFF m ==> a SUBSET b DIFF m`) THEN
    CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
    MATCH_MP_TAC INTERIOR_MAXIMAL THEN
    ASM_SIMP_TAC[OPEN_INTER; OPEN_INTERIOR; GSYM closed] THEN
    MP_TAC(ISPEC `x:real^N->bool` INTERIOR_SUBSET) THEN SET_TAC[];
    MP_TAC(ISPECL [`x DIFF m:real^N->bool`; `x:real^N->bool`] SUBSET_INTERIOR) THEN
    REWRITE_TAC[SUBSET_DIFF] THEN SET_TAC[]]);;

let MOI_S5K_LOCAL_OFF = prove
 (`!s s' m:real^N->bool.
     closed m /\ s' DIFF m = s DIFF m
     ==> closure s' DIFF m = closure s DIFF m /\
         interior s' DIFF m = interior s DIFF m /\
         frontier s' DIFF m = frontier s DIFF m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `m:real^N->bool`] MOI_S5K_CLOSURE_OFF) THEN
  MP_TAC(ISPECL [`s':real^N->bool`; `m:real^N->bool`] MOI_S5K_CLOSURE_OFF) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `m:real^N->bool`] MOI_S5K_INTERIOR_OFF) THEN
  MP_TAC(ISPECL [`s':real^N->bool`; `m:real^N->bool`] MOI_S5K_INTERIOR_OFF) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `closure s' DIFF m = closure s DIFF m /\
                interior s' DIFF m = interior (s:real^N->bool) DIFF m`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[frontier] THEN
  MAP_EVERY UNDISCH_TAC
   [`closure s' DIFF m = closure s DIFF (m:real^N->bool)`;
    `interior s' DIFF m = interior s DIFF (m:real^N->bool)`] THEN
  SET_TAC[]);;

(* The tube, the thin tube and the squares at the level c lie in the slab.  *)

let MOI_S5K_SLAB_PARTS = prove
 (`!c. abs c <= &1 / &512
       ==> interior moi_s35_stube SUBSET moi_s35_slab /\
           moi_s35_stube SUBSET moi_s35_slab /\ moi_s35_ttube SUBSET moi_s35_slab /\
           moi_s35_sq (&3 / &16) c SUBSET moi_s35_slab /\
           moi_s35_sq (&5 / &16) c SUBSET moi_s35_slab`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `moi_s35_stube SUBSET moi_s35_slab` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s35_stube; moi_s35_slab; moi_s35_cube; SUBSET; IN_ELIM_THM;
      IN_INTERVAL; moi_s35_n; DIMINDEX_3; FORALL_3; VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `moi_s35_stube` THEN
    ASM_REWRITE_TAC[INTERIOR_SUBSET];
    REWRITE_TAC[moi_s35_ttube; moi_s35_slab; moi_s35_cube; SUBSET; IN_ELIM_THM;
      IN_INTERVAL; moi_s35_n; DIMINDEX_3; FORALL_3; VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
    REAL_ARITH_TAC;
    UNDISCH_TAC `abs c <= &1 / &512` THEN
    REWRITE_TAC[moi_s35_sq; moi_s35_slab; moi_s35_cube; SUBSET; IN_ELIM_THM;
      IN_INTERVAL; moi_s35_n; DIMINDEX_3; FORALL_3; VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
    REAL_ARITH_TAC;
    UNDISCH_TAC `abs c <= &1 / &512` THEN
    REWRITE_TAC[moi_s35_sq; moi_s35_slab; moi_s35_cube; SUBSET; IN_ELIM_THM;
      IN_INTERVAL; moi_s35_n; DIMINDEX_3; FORALL_3; VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
    REAL_ARITH_TAC]);;

let MOI_S5K_SLAB_IMAGES = prove
 (`!(phi:real^3->real^3) c.
     abs c <= &1 / &512
     ==> IMAGE phi (interior moi_s35_stube) SUBSET IMAGE phi moi_s35_slab /\
         IMAGE phi moi_s35_stube SUBSET IMAGE phi moi_s35_slab /\
         IMAGE phi moi_s35_ttube SUBSET IMAGE phi moi_s35_slab /\
         IMAGE phi (moi_s35_sq (&3 / &16) c) SUBSET IMAGE phi moi_s35_slab /\
         IMAGE phi (moi_s35_sq (&5 / &16) c) SUBSET IMAGE phi moi_s35_slab`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MOI_S5K_SLAB_PARTS) THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN FIRST_ASSUM ACCEPT_TAC);;

(* The two cells of an edge configuration meet and are different.          *)

let MOI_S5K_EDGE_MEET = prove
 (`!phi xa xb ww b b0 b1 c.
     moi_s35_edge_conf phi xa xb ww b b0 b1 c
     ==> ~(xa INTER xb = {}) /\ ~(xa = xb)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s35_edge_conf] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!r. &0 <= r /\ r <= &5 / &16
        ==> (phi:real^3->real^3) (vector[r; &0; c]) IN xa /\
            phi (vector[r; &0; c]) IN IMAGE phi (moi_s35_sq r c)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THENL
     [SUBGOAL_THEN `(phi:real^3->real^3) (vector[r; &0; c]) IN
                    IMAGE phi {x | x IN moi_s35_slab /\ x$3 <= c}` MP_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN
        REWRITE_TAC[IN_ELIM_THM; moi_s35_slab; moi_s35_cube; IN_INTERVAL; DIMINDEX_3;
          FORALL_3; VECTOR_NEG_COMPONENT; VEC_COMPONENT; VECTOR_3] THEN
        UNDISCH_TAC `abs c <= &1 / &512` THEN
        MAP_EVERY UNDISCH_TAC [`&0 <= r`; `r <= &5 / &16`] THEN REAL_ARITH_TAC;
        UNDISCH_TAC `xa INTER IMAGE (phi:real^3->real^3) moi_s35_slab =
                     IMAGE phi {x | x IN moi_s35_slab /\ x$3 <= c}` THEN
        SET_TAC[]];
      MATCH_MP_TAC FUN_IN_IMAGE THEN
      REWRITE_TAC[moi_s35_sq; IN_ELIM_THM; moi_s35_n; VECTOR_3] THEN
      UNDISCH_TAC `&0 <= r` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `&3 / &16`) THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; STRIP_TAC] THEN
    MP_TAC(ISPEC `xb:real^3->bool` INTERIOR_SUBSET) THEN
    MAP_EVERY UNDISCH_TAC
     [`IMAGE (phi:real^3->real^3) (moi_s35_sq (&3 / &16) c) SUBSET interior xb`;
      `(phi:real^3->real^3) (vector[&3 / &16; &0; c]) IN xa`;
      `(phi:real^3->real^3) (vector[&3 / &16; &0; c]) IN
       IMAGE phi (moi_s35_sq (&3 / &16) c)`] THEN
    SET_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `&5 / &16`) THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; STRIP_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`DISJOINT (IMAGE (phi:real^3->real^3) (moi_s35_sq (&5 / &16) c)) xb`;
      `(phi:real^3->real^3) (vector[&5 / &16; &0; c]) IN xa`;
      `(phi:real^3->real^3) (vector[&5 / &16; &0; c]) IN
       IMAGE phi (moi_s35_sq (&5 / &16) c)`] THEN
    SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* An edge configuration and the single-circle outcome survive a change     *)
(* of the B-cell (PRES_B) or of the A-cell (PRES_A) off a closed set m that *)
(* misses the slab image and the other cell.                                *)
(* ------------------------------------------------------------------------- *)

let MOI_S5K_PRES_B = prove
 (`!phi xa xb xb' ww b b0 b1 c (m:real^3->bool).
     moi_s35_edge_conf phi xa xb ww b b0 b1 c /\
     closed m /\ DISJOINT m (IMAGE phi moi_s35_slab) /\ DISJOINT m xa /\
     xb' DIFF m = xb DIFF m /\ pl_ball 3 xb' /\
     xb' UNION IMAGE phi moi_s35_stube UNION
     inside (xb' UNION IMAGE phi moi_s35_stube) SUBSET ww
     ==> moi_s35_edge_conf phi xa xb' ww b b0 b1 c /\
         (moi_s35_single phi xa xb c ==> moi_s35_single phi xa xb' c)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> MAP_EVERY ASSUME_TAC
    (CONJUNCTS(REWRITE_RULE[moi_s35_edge_conf] th))) STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`xb:real^3->bool`; `xb':real^3->bool`; `m:real^3->bool`]
    MOI_S5K_LOCAL_OFF) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`phi:real^3->real^3`; `c:real`] MOI_S5K_SLAB_IMAGES) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `frontier xa SUBSET (xa:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FRONTIER_SUBSET_CLOSED THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    MATCH_MP_TAC MOI_S4D_PL_BALL_COMPACT THEN EXISTS_TAC `3` THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frontier xa INTER xb' = frontier xa INTER (xb:real^3->bool) /\
    frontier xa INTER frontier xb' = frontier xa INTER frontier (xb:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`frontier xa SUBSET (xa:real^3->bool)`; `DISJOINT m (xa:real^3->bool)`;
      `xb' DIFF m = xb DIFF (m:real^3->bool)`;
      `frontier xb' DIFF m = frontier xb DIFF (m:real^3->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s35_edge_conf] THEN REPEAT CONJ_TAC THEN
  TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MAP_EVERY UNDISCH_TAC
     [`b SUBSET frontier (xb:real^3->bool)`;
      `b SUBSET IMAGE (phi:real^3->real^3) (interior moi_s35_stube)`;
      `IMAGE (phi:real^3->real^3) (interior moi_s35_stube) SUBSET IMAGE phi moi_s35_slab`;
      `DISJOINT m (IMAGE (phi:real^3->real^3) moi_s35_slab)`;
      `frontier xb' DIFF m = frontier xb DIFF (m:real^3->bool)`] THEN
    SET_TAC[];
    MAP_EVERY UNDISCH_TAC
     [`frontier xb INTER IMAGE (phi:real^3->real^3) moi_s35_ttube SUBSET b`;
      `IMAGE (phi:real^3->real^3) moi_s35_ttube SUBSET IMAGE phi moi_s35_slab`;
      `DISJOINT m (IMAGE (phi:real^3->real^3) moi_s35_slab)`;
      `frontier xb' DIFF m = frontier xb DIFF (m:real^3->bool)`] THEN
    SET_TAC[];
    MAP_EVERY UNDISCH_TAC
     [`IMAGE (phi:real^3->real^3) (moi_s35_sq (&3 / &16) c) SUBSET interior xb`;
      `IMAGE (phi:real^3->real^3) (moi_s35_sq (&3 / &16) c) SUBSET
       IMAGE phi moi_s35_slab`;
      `DISJOINT m (IMAGE (phi:real^3->real^3) moi_s35_slab)`;
      `interior xb' DIFF m = interior xb DIFF (m:real^3->bool)`] THEN
    SET_TAC[];
    MAP_EVERY UNDISCH_TAC
     [`DISJOINT (IMAGE (phi:real^3->real^3) (moi_s35_sq (&5 / &16) c)) xb`;
      `IMAGE (phi:real^3->real^3) (moi_s35_sq (&5 / &16) c) SUBSET
       IMAGE phi moi_s35_slab`;
      `DISJOINT m (IMAGE (phi:real^3->real^3) moi_s35_slab)`;
      `xb' DIFF m = xb DIFF (m:real^3->bool)`] THEN
    SET_TAC[];
    REWRITE_TAC[moi_s35_single] THEN ASM_REWRITE_TAC[]]);;

let MOI_S5K_PRES_A = prove
 (`!phi xa xa' xb ww b b0 b1 c (m:real^3->bool).
     moi_s35_edge_conf phi xa xb ww b b0 b1 c /\
     closed m /\ DISJOINT m (IMAGE phi moi_s35_slab) /\ DISJOINT m xb /\
     xa' DIFF m = xa DIFF m /\ pl_ball 3 xa'
     ==> moi_s35_edge_conf phi xa' xb ww b b0 b1 c /\
         (moi_s35_single phi xa xb c ==> moi_s35_single phi xa' xb c)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> MAP_EVERY ASSUME_TAC
    (CONJUNCTS(REWRITE_RULE[moi_s35_edge_conf] th))) STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`xa:real^3->bool`; `xa':real^3->bool`; `m:real^3->bool`]
    MOI_S5K_LOCAL_OFF) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `frontier xb SUBSET (xb:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FRONTIER_SUBSET_CLOSED THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    MATCH_MP_TAC MOI_S4D_PL_BALL_COMPACT THEN EXISTS_TAC `3` THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frontier xa' INTER xb = frontier xa INTER (xb:real^3->bool) /\
    frontier xa' INTER frontier xb = frontier xa INTER frontier (xb:real^3->bool) /\
    xa' INTER IMAGE (phi:real^3->real^3) moi_s35_slab = xa INTER IMAGE phi moi_s35_slab`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`frontier xb SUBSET (xb:real^3->bool)`; `DISJOINT m (xb:real^3->bool)`;
      `DISJOINT m (IMAGE (phi:real^3->real^3) moi_s35_slab)`;
      `xa' DIFF m = xa DIFF (m:real^3->bool)`;
      `frontier xa' DIFF m = frontier xa DIFF (m:real^3->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s35_edge_conf] THEN REPEAT CONJ_TAC THEN
  TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    REWRITE_TAC[moi_s35_single] THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The frame clauses used, chart facts at the ends of an edge, and the      *)
(* separation of change sets lying in tubes of given edges.                  *)
(* ------------------------------------------------------------------------- *)

let MOI_S5K_STUBE_SLAB = prove
 (`moi_s35_stube SUBSET moi_s35_slab`,
  REWRITE_TAC[moi_s35_stube; moi_s35_slab; moi_s35_cube; SUBSET; IN_ELIM_THM;
    IN_INTERVAL; moi_s35_n; DIMINDEX_3; FORALL_3; VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
  REAL_ARITH_TAC);;

let MOI_S5K_TUBE_MISS = prove
 (`!(ff:real^N->real^N->real^3) av psi d (m:real^3->bool) s.
     m SUBSET UNIONS {IMAGE (moi_s35_ach ff av psi e) moi_s35_stube | e | e IN d} /\
     (!e. e IN d ==> DISJOINT s (IMAGE (moi_s35_ach ff av psi e) moi_s35_slab))
     ==> DISJOINT s m`,
  REPEAT GEN_TAC THEN MP_TAC MOI_S5K_STUBE_SLAB THEN
  REWRITE_TAC[UNIONS_GSPEC] THEN
  REWRITE_TAC[SUBSET; DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_ELIM_THM;
              IN_IMAGE] THEN
  MESON_TAC[]);;

let MOI_S5K_TUBE_MISS2 = prove
 (`!(ff:real^N->real^N->real^3) av psi d1 d2 (m1:real^3->bool) m2.
     m1 SUBSET UNIONS {IMAGE (moi_s35_ach ff av psi e) moi_s35_stube | e | e IN d1} /\
     m2 SUBSET UNIONS {IMAGE (moi_s35_ach ff av psi e) moi_s35_stube | e | e IN d2} /\
     (!e1 e2. e1 IN d1 /\ e2 IN d2
              ==> DISJOINT (IMAGE (moi_s35_ach ff av psi e1) moi_s35_slab)
                           (IMAGE (moi_s35_ach ff av psi e2) moi_s35_slab))
     ==> DISJOINT m1 m2`,
  REPEAT GEN_TAC THEN MP_TAC MOI_S5K_STUBE_SLAB THEN
  REWRITE_TAC[UNIONS_GSPEC] THEN
  REWRITE_TAC[SUBSET; DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_ELIM_THM;
              IN_IMAGE] THEN
  MESON_TAC[]);;

let MOI_S5K_TUBE_SUB = prove
 (`!(ff:real^N->real^N->real^3) av psi d d' (m:real^3->bool).
     m SUBSET UNIONS {IMAGE (moi_s35_ach ff av psi e) moi_s35_stube | e | e IN d} /\
     d SUBSET d'
     ==> m SUBSET UNIONS {IMAGE (moi_s35_ach ff av psi e) moi_s35_stube | e | e IN d'}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[]);;

(* Frame clauses.                                                           *)

let MOI_S5K_MENTIONS (s:string) (th:thm) =
  can (find_term (fun t -> is_const t && fst(dest_const t) = s)) (concl th);;

let MOI_S5K_HEAD (s:string) (th:thm) =
  try fst(dest_const(fst(strip_comb(concl th)))) = s with Failure _ -> false;;

(* Apply an implicational assumption chosen by pred to the assumed instance  *)
(* tm of its antecedent (avoids the collapse of MP_TAC'd instances under     *)
(* ASM_REWRITE_TAC).                                                         *)

let MOI_S5K_AT (pred:thm->bool) (tm:term) (ttac:thm_tactic) : tactic =
  FIRST_ASSUM(fun th -> if pred th then ttac (MATCH_MP th (ASSUME tm))
                        else failwith "MOI_S5K_AT");;

let MOI_S5K_FRAME_CELL = prove
 (`!(t:(real^N->bool)->bool) (l:(real^N->bool)->bool) (h:real^N->real^3) (w:real^N->real^3->bool) (av:(real^N->bool)->real^N) (bv:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N) (ff:real^N->real^N->real^3) (xx:real^N->real^3->bool) (cc:(real^N->bool)->real).
     moi_s35_frame t l h w av bv psi ff xx cc
     ==> !v. {v} IN l
             ==> pl_ball 3 (xx v) /\ xx v SUBSET w v /\
                 xx v UNION
                 UNIONS {IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) moi_s35_stube | e |
                         moi_s35_edge l e /\ bv e = v} UNION
                 inside (xx v UNION
                         UNIONS {IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) moi_s35_stube | e |
                                 moi_s35_edge l e /\ bv e = v}) SUBSET w v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s35_frame] THEN STRIP_TAC THEN
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N` o check (fun th ->
    is_forall(concl th) && MOI_S5K_MENTIONS "pl_ball" th)) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let MOI_S5K_FRAME_EDGE = prove
 (`!(t:(real^N->bool)->bool) (l:(real^N->bool)->bool) (h:real^N->real^3) (w:real^N->real^3->bool) (av:(real^N->bool)->real^N) (bv:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N) (ff:real^N->real^N->real^3) (xx:real^N->real^3->bool) (cc:(real^N->bool)->real).
     moi_s35_frame t l h w av bv psi ff xx cc
     ==> !e. moi_s35_edge l e
             ==> abs(cc e) <= &1 / &512 /\
                 xx (av e) INTER xx (bv e) SUBSET IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) moi_s35_slab /\
                 DISJOINT (IMAGE ((moi_s35_bch (ff:real^N->real^N->real^3) (bv:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) (moi_s35_level (&1 / &8))) (xx (av e))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s35_frame] THEN STRIP_TAC THEN
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real^N->bool` o check (fun th ->
    is_forall(concl th) && MOI_S5K_MENTIONS "moi_s35_same_orient" th)) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let MOI_S5K_FRAME_SEP = prove
 (`!(t:(real^N->bool)->bool) (l:(real^N->bool)->bool) (h:real^N->real^3) (w:real^N->real^3->bool) (av:(real^N->bool)->real^N) (bv:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N) (ff:real^N->real^N->real^3) (xx:real^N->real^3->bool) (cc:(real^N->bool)->real).
     moi_s35_frame t l h w av bv psi ff xx cc
     ==> (!e v. moi_s35_edge l e /\ {v} IN l /\ ~(v = av e) /\ ~(v = bv e)
                ==> DISJOINT (xx v) (IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) moi_s35_slab)) /\
         (!e e'. moi_s35_edge l e /\ moi_s35_edge l e' /\ ~(e = e')
                 ==> DISJOINT (IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) moi_s35_slab)
                              (IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e') moi_s35_slab) /\
                     DISJOINT (IMAGE ((moi_s35_bch (ff:real^N->real^N->real^3) (bv:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) (moi_s35_level (&1 / &8)))
                              (IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e') moi_s35_slab)) /\
         (!u v. {u} IN l /\ {v} IN l /\ ~(u = v) /\ ~(segment[u,v] IN l)
                ==> DISJOINT (xx u) (xx v))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s35_frame] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* Chart facts at the ends of an edge.                                      *)

let MOI_S5K_CHART_ENDS = prove
 (`!(t:(real^N->bool)->bool) l g av bv psi e.
     moi_s35_charts t l g av bv psi /\ moi_s35_edge l e
     ==> {av e} IN l /\ {bv e} IN l /\ ~(av e = bv e) /\ e = segment[av e,bv e] /\
         e IN l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s35_charts] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `e:real^N->bool` o CONJUNCT1) ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REPEAT CONJ_TAC THEN
  TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  UNDISCH_TAC `moi_s35_edge l (e:real^N->bool)` THEN SIMP_TAC[moi_s35_edge]);;

let MOI_S5K_CHART_SAME = prove
 (`!(t:(real^N->bool)->bool) l g av bv psi e e'.
     moi_s35_charts t l g av bv psi /\ moi_s35_edge l e /\ moi_s35_edge l e' /\
     ((av e = av e' /\ bv e = bv e') \/ (av e = bv e' /\ bv e = av e'))
     ==> e = e'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `e:real^N->bool`] MOI_S5K_CHART_ENDS) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `e':real^N->bool`] MOI_S5K_CHART_ENDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[SEGMENT_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Separation at the ends of edges; the per-vertex process: the removal      *)
(* at the B-side edges of one vertex applied in turn (finite induction).     *)
(* ------------------------------------------------------------------------- *)

let MOI_S5K_FILL_GEN = prove
 (`!a b za zb ww:real^N->bool.
     a UNION b SUBSET za UNION zb /\
     za UNION zb UNION inside (za UNION zb) SUBSET ww
     ==> a UNION b UNION inside (a UNION b) SUBSET ww`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a UNION b:real^N->bool`; `za UNION zb:real^N->bool`]
    INSIDE_MONO_ALT) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `za UNION zb UNION inside (za UNION zb) SUBSET (ww:real^N->bool)` THEN
  UNDISCH_TAC `a UNION b SUBSET za UNION (zb:real^N->bool)` THEN SET_TAC[]);;

let MOI_S5K_STUBE_DOM = prove
 (`interior moi_s35_stube SUBSET moi_s35_dom`,
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `moi_s35_stube` THEN
  REWRITE_TAC[INTERIOR_SUBSET] THEN
  REWRITE_TAC[moi_s35_stube; moi_s35_dom; moi_s35_cube; SUBSET; IN_ELIM_THM;
    IN_INTERVAL; moi_s35_n; DIMINDEX_3; FORALL_3; VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
  REAL_ARITH_TAC);;

(* The A-cell of a B-side edge e at v misses the slab of every other B-side *)
(* edge at v; the B-cell of e misses the slabs of the B-side edges of the   *)
(* A-end of e; a cell misses the slab of an edge to a non-adjacent vertex.  *)

let MOI_S5K_SEP_A = prove
 (`!(t:(real^N->bool)->bool) (l:(real^N->bool)->bool) (h:real^N->real^3) (w:real^N->real^3->bool) (av:(real^N->bool)->real^N) (bv:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N) (ff:real^N->real^N->real^3) (xx:real^N->real^3->bool) (cc:(real^N->bool)->real) (g:real^N->real^N->bool) e e''.
     moi_s35_charts t l g av bv psi /\ moi_s35_frame t l h w av bv psi ff xx cc /\
     moi_s35_edge l e /\ moi_s35_edge l e'' /\ bv e'' = bv e /\ ~(e'' = e)
     ==> DISJOINT (xx (av e)) (IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e'') moi_s35_slab)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP MOI_S5K_FRAME_SEP) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`; `e:real^N->bool`] MOI_S5K_CHART_ENDS) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    DISCH_TAC THEN UNDISCH_TAC `~(e'':real^N->bool = e)` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S5K_CHART_SAME THEN
    MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`] THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[]]);;

let MOI_S5K_SEP_B = prove
 (`!(t:(real^N->bool)->bool) (l:(real^N->bool)->bool) (h:real^N->real^3) (w:real^N->real^3->bool) (av:(real^N->bool)->real^N) (bv:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N) (ff:real^N->real^N->real^3) (xx:real^N->real^3->bool) (cc:(real^N->bool)->real) (g:real^N->real^N->bool) e e'.
     moi_s35_charts t l g av bv psi /\ moi_s35_frame t l h w av bv psi ff xx cc /\
     moi_s35_edge l e /\ moi_s35_edge l e' /\ bv e' = av e
     ==> DISJOINT (xx (bv e)) (IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e') moi_s35_slab)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP MOI_S5K_FRAME_SEP) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`; `e:real^N->bool`] MOI_S5K_CHART_ENDS) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    DISCH_TAC THEN
    SUBGOAL_THEN `e':real^N->bool = e` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_S5K_CHART_SAME THEN MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`] THEN
      ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN ASM_MESON_TAC[];
      UNDISCH_TAC `(bv:(real^N->bool)->real^N) e' = (av:(real^N->bool)->real^N) e` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[]];
    ASM_MESON_TAC[]]);;

let MOI_S5K_SEP_C = prove
 (`!(t:(real^N->bool)->bool) (l:(real^N->bool)->bool) (h:real^N->real^3) (w:real^N->real^3->bool) (av:(real^N->bool)->real^N) (bv:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N) (ff:real^N->real^N->real^3) (xx:real^N->real^3->bool) (cc:(real^N->bool)->real) (g:real^N->real^N->bool) u e''.
     moi_s35_charts t l g av bv psi /\ moi_s35_frame t l h w av bv psi ff xx cc /\
     {u} IN l /\ moi_s35_edge l e'' /\ ~(u = bv e'') /\ ~(segment[u,bv e''] IN l)
     ==> DISJOINT (xx u) (IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e'') moi_s35_slab)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP MOI_S5K_FRAME_SEP) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`; `e'':real^N->bool`] MOI_S5K_CHART_ENDS) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    DISCH_TAC THEN
    UNDISCH_TAC `~(segment[u:real^N,bv(e'':real^N->bool)] IN l)` THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `segment[u:real^N,bv(e'':real^N->bool)] = e''` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; FIRST_ASSUM ACCEPT_TAC];
    FIRST_ASSUM ACCEPT_TAC]);;

let MOI_S5K_SEP_D = prove
 (`!(t:(real^N->bool)->bool) (l:(real^N->bool)->bool) (h:real^N->real^3) (w:real^N->real^3->bool) (av:(real^N->bool)->real^N) (bv:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N) (ff:real^N->real^N->real^3) (xx:real^N->real^3->bool) (cc:(real^N->bool)->real) e1 e2.
     moi_s35_frame t l h w av bv psi ff xx cc /\
     moi_s35_edge l e1 /\ moi_s35_edge l e2 /\ ~(bv e1 = bv e2)
     ==> DISJOINT (IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e1) moi_s35_slab) (IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e2) moi_s35_slab) /\
         DISJOINT (IMAGE ((moi_s35_bch (ff:real^N->real^N->real^3) (bv:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e1) (moi_s35_level (&1 / &8)))
                  (IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e2) moi_s35_slab)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o MATCH_MP MOI_S5K_FRAME_SEP) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN UNDISCH_TAC `~((bv:(real^N->bool)->real^N) e1 = bv e2)` THEN
  ASM_REWRITE_TAC[]);;

(* The invariant of the per-vertex process: after doing the edges d at the *)
(* vertex v the cell y differs from xx v only in m (a closed set inside the *)
(* tubes of d); done edges carry an edge configuration and a single circle, *)
(* the other B-side edges of v keep their configuration of p.250.          *)

let moi_s5k_inv = new_definition
 `moi_s5k_inv (l:(real^N->bool)->bool) (w:real^N->real^3->bool)
              (av:(real^N->bool)->real^N) (bv:(real^N->bool)->real^N)
              (psi:(real^N->bool)->real^3->real^N) (ff:real^N->real^N->real^3)
              (xx:real^N->real^3->bool) (cc:(real^N->bool)->real) (v:real^N)
              (d:(real^N->bool)->bool) (y:real^3->bool) (m:real^3->bool) <=>
    closed m /\
    m SUBSET UNIONS {IMAGE (moi_s35_ach ff av psi e) moi_s35_stube | e | e IN d} /\
    y DIFF m = xx v DIFF m /\ pl_ball 3 y /\
    (!e. e IN d
         ==> (?b. moi_s35_edge_conf (moi_s35_ach ff av psi e) (xx (av e)) y (w v) b
                    (IMAGE (moi_s35_bch ff bv psi e) (moi_s35_sq (&5 / &32) (--(&3) / &256)))
                    (IMAGE (moi_s35_bch ff bv psi e) (moi_s35_sq (&11 / &32) (&3 / &256)))
                    (cc e)) /\
             moi_s35_single (moi_s35_ach ff av psi e) (xx (av e)) y (cc e)) /\
    (!e. moi_s35_edge l e /\ bv e = v /\ ~(e IN d)
         ==> moi_s35_edge_conf (moi_s35_ach ff av psi e) (xx (av e)) y (w v)
               (IMAGE (moi_s35_bch ff bv psi e) moi_s35_bann)
               (IMAGE (moi_s35_bch ff bv psi e) (moi_s35_sq (&5 / &32) (--(&3) / &256)))
               (IMAGE (moi_s35_bch ff bv psi e) (moi_s35_sq (&11 / &32) (&3 / &256)))
               (cc e))`;;
(* The per-vertex process.                                                  *)

let MOI_S5K_PROCESS = prove
 (mk_imp(MOI_S35_REMOVAL,
  `!(t:(real^N->bool)->bool) (l:(real^N->bool)->bool) (h:real^N->real^3) (w:real^N->real^3->bool) (av:(real^N->bool)->real^N) (bv:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N) (ff:real^N->real^N->real^3) (xx:real^N->real^3->bool) (cc:(real^N->bool)->real) (g:real^N->real^N->bool) (v:real^N).
     moi_s35_charts t l g av bv psi /\ moi_s35_pre t l h w av bv psi ff xx cc /\
     {v} IN l
     ==> !d. FINITE d /\ d SUBSET {e':real^N->bool | moi_s35_edge l e' /\ (bv:(real^N->bool)->real^N) e' = v}
             ==> ?y m. moi_s5k_inv l w av bv psi ff xx cc v d y m`),
  DISCH_THEN(LABEL_TAC "rem") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_s35_pre] o check
    (MOI_S5K_HEAD "moi_s35_pre")) THEN
  FIRST_ASSUM(MP_TAC o SPEC `v:real^N` o MATCH_MP MOI_S5K_FRAME_CELL) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`(xx:real^N->real^3->bool) v`; `{}:real^3->bool`] THEN
    REWRITE_TAC[moi_s5k_inv; CLOSED_EMPTY; EMPTY_SUBSET; NOT_IN_EMPTY] THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real^N->bool` o check (fun th ->
      is_forall(concl th) && MOI_S5K_MENTIONS "moi_s35_bann" th)) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `(bv:(real^N->bool)->real^N) e`)) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`e1:real^N->bool`; `d:(real^N->bool)->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[INSERT_SUBSET; IN_ELIM_THM] THEN STRIP_TAC THEN
  USE_THEN "ih" (fun th -> MP_TAC(MP th (ASSUME `d SUBSET {e':real^N->bool | moi_s35_edge l e' /\ (bv:(real^N->bool)->real^N) e' = v}`))) THEN
  REWRITE_TAC[moi_s5k_inv; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`y:real^3->bool`; `m:real^3->bool`] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `e1:real^N->bool` o check (fun th ->
    is_forall(concl th) && MOI_S5K_MENTIONS "moi_s35_bann" th &&
    can (find_term ((=) `y:real^3->bool`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    USE_THEN "rem" (fun rem -> MP_TAC(MATCH_MP rem th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `y':real^3->bool` (X_CHOOSE_THEN `b':real^3->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `kk:real^3->bool` STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN `pl_ball 3 (y':real^3->bool) /\
                abs(cc(e1:real^N->bool)) <= &1 / &512 /\
                pl_map_on moi_s35_dom ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e1)`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o REWRITE_RULE[moi_s35_edge_conf] o check (fun th ->
      MOI_S5K_MENTIONS "moi_s35_edge_conf" th &&
      can (find_term ((=) `y':real^3->bool`)) (concl th))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e1) kk) /\ IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e1) kk SUBSET IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e1) moi_s35_stube`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `moi_s35_dom` THEN ASM_SIMP_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON] THEN
      MP_TAC MOI_S5K_STUBE_DOM THEN
      UNDISCH_TAC `kk SUBSET interior moi_s35_stube` THEN SET_TAC[];
      MATCH_MP_TAC IMAGE_SUBSET THEN MP_TAC(ISPEC `moi_s35_stube` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `kk SUBSET interior moi_s35_stube` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y':real^3->bool) SUBSET (xx:real^N->real^3->bool) v UNION UNIONS {IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e') moi_s35_stube | e' | moi_s35_edge l e' /\ (bv:(real^N->bool)->real^N) e' = v}`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `m UNION IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e1) kk SUBSET UNIONS {IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e') moi_s35_stube | e' | moi_s35_edge l e' /\ (bv:(real^N->bool)->real^N) e' = v}` MP_TAC THENL
     [REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `UNIONS {IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) moi_s35_stube | e | e IN d}` THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[UNIONS_GSPEC] THEN
        UNDISCH_TAC `d SUBSET {e':real^N->bool | moi_s35_edge l e' /\ (bv:(real^N->bool)->real^N) e' = v}` THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
        MESON_TAC[];
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e1) moi_s35_stube` THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[UNIONS_GSPEC] THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
        EXISTS_TAC `e1:real^N->bool` THEN ASM_REWRITE_TAC[]];
      MAP_EVERY UNDISCH_TAC
       [`y' DIFF IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e1) kk = y DIFF IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e1) kk`;
        `y DIFF m = (xx:real^N->real^3->bool) v DIFF m`] THEN
      SPEC_TAC(`UNIONS {IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e') moi_s35_stube | e' | moi_s35_edge l e' /\ (bv:(real^N->bool)->real^N) e' = v}`,`uu:real^3->bool`) THEN SPEC_TAC(`IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e1) kk`,`k1:real^3->bool`) THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e bb. moi_s35_edge l e /\ bv e = v /\ ~(e = e1) /\
           moi_s35_edge_conf ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) (xx (av e)) y (w v) bb
             (IMAGE ((moi_s35_bch (ff:real^N->real^N->real^3) (bv:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) (moi_s35_sq (&5 / &32) (--(&3) / &256))) (IMAGE ((moi_s35_bch (ff:real^N->real^N->real^3) (bv:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) (moi_s35_sq (&11 / &32) (&3 / &256))) (cc e)
           ==> moi_s35_edge_conf ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) (xx (av e)) y' (w v) bb
                 (IMAGE ((moi_s35_bch (ff:real^N->real^N->real^3) (bv:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) (moi_s35_sq (&5 / &32) (--(&3) / &256))) (IMAGE ((moi_s35_bch (ff:real^N->real^N->real^3) (bv:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) (moi_s35_sq (&11 / &32) (&3 / &256))) (cc e) /\
               (moi_s35_single ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) (xx (av e)) y (cc e)
                ==> moi_s35_single ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) (xx (av e)) y' (cc e))`
  (LABEL_TAC "keep") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MOI_S5K_PRES_B THEN
    EXISTS_TAC `IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e1) kk` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!s t u:real^3->bool. s SUBSET t /\ DISJOINT t u
                                                  ==> DISJOINT s u`) THEN
      EXISTS_TAC `IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e1) moi_s35_slab` THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e1) moi_s35_stube` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
        REWRITE_TAC[MOI_S5K_STUBE_SLAB];
        FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o MATCH_MP MOI_S5K_FRAME_SEP) THEN
        DISCH_THEN(MP_TAC o SPECL [`e1:real^N->bool`; `e:real^N->bool`]) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(e:real^N->bool = e1)` THEN MESON_TAC[];
          SIMP_TAC[]]];
      MATCH_MP_TAC(SET_RULE `!s t u:real^3->bool. s SUBSET t /\ DISJOINT u t
                                                  ==> DISJOINT s u`) THEN
      EXISTS_TAC `IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e1) moi_s35_slab` THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e1) moi_s35_stube` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
        REWRITE_TAC[MOI_S5K_STUBE_SLAB];
        MATCH_MP_TAC MOI_S5K_SEP_A THEN MAP_EVERY EXISTS_TAC
         [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `h:real^N->real^3`;
          `w:real^N->real^3->bool`; `bv:(real^N->bool)->real^N`;
          `cc:(real^N->bool)->real`; `g:real^N->real^N->bool`] THEN
        ASM_REWRITE_TAC[]];
      MATCH_MP_TAC MOI_S5K_FILL_GEN THEN
      MAP_EVERY EXISTS_TAC [`(xx:real^N->real^3->bool) v`; `UNIONS {IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e') moi_s35_stube | e' | moi_s35_edge l e' /\ (bv:(real^N->bool)->real^N) e' = v}`] THEN
      ASM_REWRITE_TAC[UNION_SUBSET] THEN
      REWRITE_TAC[UNIONS_GSPEC] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNION] THEN
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN DISJ2_TAC THEN
      EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`y':real^3->bool`; `m UNION IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e1) kk`] THEN
  REWRITE_TAC[moi_s5k_inv] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[CLOSED_UNION];
    REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S5K_TUBE_SUB THEN EXISTS_TAC `d:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e1) moi_s35_stube` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[UNIONS_GSPEC] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INSERT] THEN MESON_TAC[]];
    MAP_EVERY UNDISCH_TAC
     [`y' DIFF IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e1) kk = y DIFF IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e1) kk`;
      `y DIFF m = (xx:real^N->real^3->bool) v DIFF m`] THEN
    SPEC_TAC(`IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e1) kk`,`k1:real^3->bool`) THEN SET_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[IN_INSERT] THEN X_GEN_TAC `e:real^N->bool` THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC) THENL
     [CONJ_TAC THENL
       [EXISTS_TAC `b':real^3->bool` THEN FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC];
      FIRST_X_ASSUM(MP_TAC o SPEC `e:real^N->bool` o check (fun th ->
        is_forall(concl th) && MOI_S5K_MENTIONS "moi_s35_single" th &&
        can (find_term ((=) `d:(real^N->bool)->bool`)) (concl th))) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `bb:real^3->bool`) ASSUME_TAC) THEN
      SUBGOAL_THEN `moi_s35_edge l (e:real^N->bool) /\ bv e = (v:real^N) /\ ~(e = e1)`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `d SUBSET {e':real^N->bool | moi_s35_edge l e' /\ (bv:(real^N->bool)->real^N) e' = v}` THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
        DISCH_THEN(MP_TAC o SPEC `e:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
        SIMP_TAC[] THEN DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
        UNDISCH_TAC `~((e1:real^N->bool) IN d)` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      USE_THEN "keep" (MP_TAC o SPECL [`e:real^N->bool`; `bb:real^3->bool`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(fun th -> CONJ_TAC THENL
       [EXISTS_TAC `bb:real^3->bool` THEN ACCEPT_TAC(CONJUNCT1 th);
        MATCH_MP_TAC(CONJUNCT2 th) THEN FIRST_ASSUM ACCEPT_TAC])];
    X_GEN_TAC `e:real^N->bool` THEN REWRITE_TAC[IN_INSERT; DE_MORGAN_THM] THEN
    STRIP_TAC THEN
    USE_THEN "keep" (MP_TAC o SPECL [`e:real^N->bool`;
      `IMAGE ((moi_s35_bch (ff:real^N->real^N->real^3) (bv:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) moi_s35_bann`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `e:real^N->bool` o check (fun th ->
        is_forall(concl th) && MOI_S5K_MENTIONS "moi_s35_bann" th &&
        can (find_term ((=) `d:(real^N->bool)->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      SIMP_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The combined cells (the results of the per-vertex processes) satisfy      *)
(* the frame and the post state.                                             *)
(* ------------------------------------------------------------------------- *)

let MOI_S5K_TUBE_EXCEPT = prove
 (`!(ff:real^N->real^N->real^3) av psi d e0 (m:real^3->bool) s.
     m SUBSET UNIONS {IMAGE (moi_s35_ach ff av psi e) moi_s35_stube | e | e IN d} /\
     (!e. e IN d /\ ~(e = e0)
          ==> DISJOINT s (IMAGE (moi_s35_ach ff av psi e) moi_s35_slab))
     ==> s INTER m SUBSET IMAGE (moi_s35_ach ff av psi e0) moi_s35_slab`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o
    REWRITE_RULE[UNIONS_GSPEC; SUBSET; IN_ELIM_THM] o
    check (MOI_S5K_MENTIONS "UNIONS")) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:real^3) IN IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) moi_s35_slab`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!s t x:real^3. s SUBSET t /\ x IN s ==> x IN t`) THEN
    EXISTS_TAC `IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) moi_s35_stube` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[MOI_S5K_STUBE_SLAB];
    ALL_TAC] THEN
  ASM_CASES_TAC `e:real^N->bool = e0` THENL
   [UNDISCH_TAC `(x:real^3) IN IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) moi_s35_slab` THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^3) IN (s:real^3->bool)` THEN
    UNDISCH_TAC `(x:real^3) IN IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) moi_s35_slab` THEN
    SET_TAC[]]);;

let MOI_S5K_INV_V = prove
 (`!l w av bv psi ff xx cc (v:real^N) y m.
     moi_s5k_inv l w av bv psi ff xx cc v {e:real^N->bool | moi_s35_edge l e /\ (bv:(real^N->bool)->real^N) e = v} y m
     ==> closed m /\ m SUBSET UNIONS {IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) moi_s35_stube | e | e IN {e:real^N->bool | moi_s35_edge l e /\ (bv:(real^N->bool)->real^N) e = v}} /\
         m SUBSET UNIONS {IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) moi_s35_stube | e |
                          moi_s35_edge l e /\ bv e = v} /\
         y DIFF m = xx v DIFF m /\ pl_ball 3 y /\ y SUBSET xx v UNION m /\
         (!e. moi_s35_edge l e /\ bv e = v
              ==> (?b. moi_s35_edge_conf ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) (xx (av e)) y (w v) b
                         (IMAGE ((moi_s35_bch (ff:real^N->real^N->real^3) (bv:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) (moi_s35_sq (&5 / &32) (--(&3) / &256))) (IMAGE ((moi_s35_bch (ff:real^N->real^N->real^3) (bv:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) (moi_s35_sq (&11 / &32) (&3 / &256))) (cc e)) /\
                  moi_s35_single ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) (xx (av e)) y (cc e))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s5k_inv; IN_ELIM_THM] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `y DIFF m = (xx:real^N->real^3->bool) v DIFF m` THEN SET_TAC[]);;

(* Separation of the change sets of the combined cells.                     *)

let MOI_S5K_MSEP = prove
 (`!(t:(real^N->bool)->bool) (l:(real^N->bool)->bool) (h:real^N->real^3) (w:real^N->real^3->bool) (av:(real^N->bool)->real^N) (bv:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N) (ff:real^N->real^N->real^3) (xx:real^N->real^3->bool) (cc:(real^N->bool)->real) (g:real^N->real^N->bool) (M:real^N->real^3->bool).
     moi_s35_charts t l g av bv psi /\ moi_s35_frame t l h w av bv psi ff xx cc /\
     (!v. {v} IN l ==> M v SUBSET UNIONS {IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) moi_s35_stube | e | e IN {e:real^N->bool | moi_s35_edge l e /\ (bv:(real^N->bool)->real^N) e = v}})
     ==> (!e. moi_s35_edge l e
              ==> xx (av e) INTER M (bv e) SUBSET IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) moi_s35_slab /\
                  DISJOINT (xx (bv e)) (M (av e)) /\
                  DISJOINT (M (av e)) (M (bv e)) /\
                  DISJOINT (IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) moi_s35_slab) (M (av e)) /\
                  DISJOINT (IMAGE ((moi_s35_bch (ff:real^N->real^N->real^3) (bv:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) (moi_s35_level (&1 / &8))) (M (av e))) /\
         (!e v. moi_s35_edge l e /\ {v} IN l /\ ~(v = bv e)
                ==> DISJOINT (IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) moi_s35_slab) (M v)) /\
         (!u v. {u} IN l /\ {v} IN l /\ ~(u = v) /\ ~(segment[u,v] IN l)
                ==> DISJOINT (xx u) (M v) /\ DISJOINT (M u) (M v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!u v. {u} IN l /\ {v} IN l /\ ~(u = v)
          ==> DISJOINT ((M:real^N->real^3->bool) u) (M (v:real^N))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S5K_TUBE_MISS2 THEN
    MAP_EVERY EXISTS_TAC
     [`ff:real^N->real^N->real^3`; `av:(real^N->bool)->real^N`;
      `psi:(real^N->bool)->real^3->real^N`; `{e:real^N->bool | moi_s35_edge l e /\ (bv:(real^N->bool)->real^N) e = u}`; `{e:real^N->bool | moi_s35_edge l e /\ (bv:(real^N->bool)->real^N) e = v}`] THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`e1:real^N->bool`; `e2:real^N->bool`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `h:real^N->real^3`; `w:real^N->real^3->bool`; `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`; `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`; `e1:real^N->bool`; `e2:real^N->bool`] MOI_S5K_SEP_D) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e v. moi_s35_edge l e /\ {v} IN l /\ ~(v = bv e)
          ==> DISJOINT (IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) moi_s35_slab) (M v) /\
              DISJOINT (IMAGE ((moi_s35_bch (ff:real^N->real^N->real^3) (bv:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) (moi_s35_level (&1 / &8))) (M (v:real^N))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN
    MATCH_MP_TAC MOI_S5K_TUBE_MISS THEN
    MAP_EVERY EXISTS_TAC
     [`ff:real^N->real^N->real^3`; `av:(real^N->bool)->real^N`;
      `psi:(real^N->bool)->real^3->real^N`; `{e:real^N->bool | moi_s35_edge l e /\ (bv:(real^N->bool)->real^N) e = v}`] THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `e'':real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `h:real^N->real^3`; `w:real^N->real^3->bool`; `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`; `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`; `e:real^N->bool`; `e'':real^N->bool`] MOI_S5K_SEP_D) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`; `e:real^N->bool`] MOI_S5K_CHART_ENDS) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S5K_TUBE_EXCEPT THEN
      EXISTS_TAC `{e'':real^N->bool | moi_s35_edge l e'' /\
                                     bv e'' = (bv:(real^N->bool)->real^N) e}` THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `(bv:(real^N->bool)->real^N) e` o check (fun th ->
          is_forall(concl th) && MOI_S5K_MENTIONS "UNIONS" th)) THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
        MATCH_MP_TAC MOI_S5K_SEP_A THEN
        MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
          `h:real^N->real^3`; `w:real^N->real^3->bool`; `bv:(real^N->bool)->real^N`;
          `cc:(real^N->bool)->real`; `g:real^N->real^N->bool`] THEN
        ASM_REWRITE_TAC[]];
      MATCH_MP_TAC MOI_S5K_TUBE_MISS THEN
      MAP_EVERY EXISTS_TAC
       [`ff:real^N->real^N->real^3`; `av:(real^N->bool)->real^N`;
        `psi:(real^N->bool)->real^3->real^N`;
        `{e':real^N->bool | moi_s35_edge l e' /\ bv e' = (av:(real^N->bool)->real^N) e}`] THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `(av:(real^N->bool)->real^N) e` o check (fun th ->
          is_forall(concl th) && MOI_S5K_MENTIONS "UNIONS" th)) THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
        MATCH_MP_TAC MOI_S5K_SEP_B THEN
        MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
          `h:real^N->real^3`; `w:real^N->real^3->bool`; `cc:(real^N->bool)->real`;
          `g:real^N->real^N->bool`] THEN
        ASM_REWRITE_TAC[]];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && not (MOI_S5K_MENTIONS "moi_s35_level" th) &&
        length(fst(strip_forall(concl th))) = 2 &&
        can (find_term ((=) `M:real^N->real^3->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPECL [`e:real^N->bool`; `(av:(real^N->bool)->real^N) e`] o
        check (fun th -> MOI_S5K_MENTIONS "moi_s35_level" th)) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPECL [`e:real^N->bool`; `(av:(real^N->bool)->real^N) e`] o
        check (fun th -> MOI_S5K_MENTIONS "moi_s35_level" th)) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`e:real^N->bool`; `v:real^N`] o
      check (fun th -> MOI_S5K_MENTIONS "moi_s35_level" th)) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S5K_TUBE_MISS THEN
      MAP_EVERY EXISTS_TAC
       [`ff:real^N->real^N->real^3`; `av:(real^N->bool)->real^N`;
        `psi:(real^N->bool)->real^3->real^N`; `{e:real^N->bool | moi_s35_edge l e /\ (bv:(real^N->bool)->real^N) e = v}`] THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N` o check (fun th ->
          is_forall(concl th) && MOI_S5K_MENTIONS "UNIONS" th)) THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
        MATCH_MP_TAC MOI_S5K_SEP_C THEN
        MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
          `h:real^N->real^3`; `w:real^N->real^3->bool`; `bv:(real^N->bool)->real^N`;
          `cc:(real^N->bool)->real`; `g:real^N->real^N->bool`] THEN
        ASM_REWRITE_TAC[]];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && not (MOI_S5K_MENTIONS "moi_s35_level" th) &&
        length(fst(strip_forall(concl th))) = 2 &&
        can (find_term ((=) `M:real^N->real^3->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[]]]);;
(* The frame for the combined cells.                                        *)

let MOI_S5K_POST_FRAME = prove
 (`!(t:(real^N->bool)->bool) (l:(real^N->bool)->bool) (h:real^N->real^3) (w:real^N->real^3->bool) (av:(real^N->bool)->real^N) (bv:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N) (ff:real^N->real^N->real^3) (xx:real^N->real^3->bool) (cc:(real^N->bool)->real) (g:real^N->real^N->bool) (Y:real^N->real^3->bool) (M:real^N->real^3->bool).
     moi_s35_charts t l g av bv psi /\ moi_s35_frame t l h w av bv psi ff xx cc /\
     (!v. {v} IN l
          ==> closed (M v) /\ M v SUBSET UNIONS {IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) moi_s35_stube | e | e IN {e:real^N->bool | moi_s35_edge l e /\ (bv:(real^N->bool)->real^N) e = v}} /\ M v SUBSET UNIONS {IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) moi_s35_stube | e | moi_s35_edge l e /\ (bv:(real^N->bool)->real^N) e = v} /\
              Y v DIFF M v = xx v DIFF M v /\ pl_ball 3 (Y v) /\
              Y v SUBSET xx v UNION M v)
     ==> moi_s35_frame t l h w av bv psi ff Y cc`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `h:real^N->real^3`; `w:real^N->real^3->bool`; `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`; `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`; `g:real^N->real^N->bool`; `M:real^N->real^3->bool`]
    MOI_S5K_MSEP) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_s35_frame] o check
    (MOI_S5K_HEAD "moi_s35_frame")) THEN
  SUBGOAL_THEN
   `!v. {v} IN l
        ==> pl_ball 3 ((Y:real^N->real^3->bool) v) /\ Y v SUBSET w v /\
            Y v UNION UNIONS {IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) moi_s35_stube | e | moi_s35_edge l e /\ (bv:(real^N->bool)->real^N) e = v} UNION inside (Y v UNION UNIONS {IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) moi_s35_stube | e | moi_s35_edge l e /\ (bv:(real^N->bool)->real^N) e = v}) SUBSET w v`
  (LABEL_TAC "c1") THENL
   [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    MOI_S5K_AT (fun th ->
      is_forall(concl th) && MOI_S5K_MENTIONS "pl_map_on" th) `{v:real^N} IN l` STRIP_ASSUME_TAC THEN
    MOI_S5K_AT (fun th ->
      is_forall(concl th) && MOI_S5K_MENTIONS "closed" th) `{v:real^N} IN l` STRIP_ASSUME_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(Y:real^N->real^3->bool) v SUBSET xx v UNION M v`;
        `(M:real^N->real^3->bool) v SUBSET UNIONS {IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) moi_s35_stube | e | moi_s35_edge l e /\ (bv:(real^N->bool)->real^N) e = v}`;
        `(xx:real^N->real^3->bool) v UNION UNIONS {IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) moi_s35_stube | e | moi_s35_edge l e /\ (bv:(real^N->bool)->real^N) e = v} UNION inside (xx v UNION UNIONS {IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) moi_s35_stube | e | moi_s35_edge l e /\ (bv:(real^N->bool)->real^N) e = v})
         SUBSET w v`] THEN
      SPEC_TAC(`inside ((xx:real^N->real^3->bool) v UNION UNIONS {IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) moi_s35_stube | e | moi_s35_edge l e /\ (bv:(real^N->bool)->real^N) e = v})`,`iin:real^3->bool`) THEN
      SPEC_TAC(`UNIONS {IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) moi_s35_stube | e | moi_s35_edge l e /\ (bv:(real^N->bool)->real^N) e = v}`,`uu:real^3->bool`) THEN SET_TAC[];
      MATCH_MP_TAC MOI_S5K_FILL_GEN THEN
      MAP_EVERY EXISTS_TAC [`(xx:real^N->real^3->bool) v`; `UNIONS {IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) moi_s35_stube | e | moi_s35_edge l e /\ (bv:(real^N->bool)->real^N) e = v}`] THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC
       [`(Y:real^N->real^3->bool) v SUBSET xx v UNION M v`;
        `(M:real^N->real^3->bool) v SUBSET UNIONS {IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) moi_s35_stube | e | moi_s35_edge l e /\ (bv:(real^N->bool)->real^N) e = v}`] THEN
      SPEC_TAC(`UNIONS {IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) moi_s35_stube | e | moi_s35_edge l e /\ (bv:(real^N->bool)->real^N) e = v}`,`uu:real^3->bool`) THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. moi_s35_edge l e
        ==> (Y:real^N->real^3->bool) (av e) INTER Y (bv e) SUBSET
            IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) moi_s35_slab /\
            DISJOINT (IMAGE ((moi_s35_bch (ff:real^N->real^N->real^3) (bv:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) (moi_s35_level (&1 / &8))) (Y (av e))`
  (LABEL_TAC "c2") THENL
   [X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`; `e:real^N->bool`] MOI_S5K_CHART_ENDS) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    MOI_S5K_AT (fun th ->
      is_forall(concl th) && MOI_S5K_MENTIONS "moi_s35_same_orient" th) `moi_s35_edge l (e:real^N->bool)` STRIP_ASSUME_TAC THEN
    MOI_S5K_AT (fun th ->
      is_forall(concl th) && MOI_S5K_MENTIONS "closed" th) `{(av:(real^N->bool)->real^N) e} IN l` STRIP_ASSUME_TAC THEN
    MOI_S5K_AT (fun th ->
      is_forall(concl th) && MOI_S5K_MENTIONS "closed" th) `{(bv:(real^N->bool)->real^N) e} IN l` STRIP_ASSUME_TAC THEN
    MOI_S5K_AT (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
      MOI_S5K_MENTIONS "moi_s35_level" th &&
      can (find_term ((=) `M:real^N->real^3->bool`)) (concl th)) `moi_s35_edge l (e:real^N->bool)` STRIP_ASSUME_TAC THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(Y:real^N->real^3->bool) ((av:(real^N->bool)->real^N) e) SUBSET
         xx (av e) UNION M (av e)`;
        `(Y:real^N->real^3->bool) ((bv:(real^N->bool)->real^N) e) SUBSET
         xx (bv e) UNION M (bv e)`;
        `(xx:real^N->real^3->bool) ((av:(real^N->bool)->real^N) e) INTER
         xx ((bv:(real^N->bool)->real^N) e) SUBSET IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) moi_s35_slab`;
        `(xx:real^N->real^3->bool) ((av:(real^N->bool)->real^N) e) INTER
         (M:real^N->real^3->bool) ((bv:(real^N->bool)->real^N) e) SUBSET
         IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) moi_s35_slab`;
        `DISJOINT ((xx:real^N->real^3->bool) ((bv:(real^N->bool)->real^N) e))
                  ((M:real^N->real^3->bool) ((av:(real^N->bool)->real^N) e))`;
        `DISJOINT ((M:real^N->real^3->bool) ((av:(real^N->bool)->real^N) e))
                  (M ((bv:(real^N->bool)->real^N) e))`] THEN
      SPEC_TAC(`IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) moi_s35_slab`,`ss:real^3->bool`) THEN SET_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`(Y:real^N->real^3->bool) ((av:(real^N->bool)->real^N) e) SUBSET
         xx (av e) UNION M (av e)`;
        `DISJOINT (IMAGE ((moi_s35_bch (ff:real^N->real^N->real^3) (bv:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) (moi_s35_level (&1 / &8)))
                  ((xx:real^N->real^3->bool) ((av:(real^N->bool)->real^N) e))`;
        `DISJOINT (IMAGE ((moi_s35_bch (ff:real^N->real^N->real^3) (bv:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) (moi_s35_level (&1 / &8)))
                  ((M:real^N->real^3->bool) ((av:(real^N->bool)->real^N) e))`] THEN
      SPEC_TAC(`IMAGE ((moi_s35_bch (ff:real^N->real^N->real^3) (bv:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) (moi_s35_level (&1 / &8))`,`ss:real^3->bool`) THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e v. moi_s35_edge l e /\ {v} IN l /\ ~(v = av e) /\ ~(v = bv e)
          ==> DISJOINT ((Y:real^N->real^3->bool) v) (IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) moi_s35_slab)`
  (LABEL_TAC "c3") THENL
   [MAP_EVERY X_GEN_TAC [`e:real^N->bool`; `v:real^N`] THEN STRIP_TAC THEN
    MOI_S5K_AT (fun th ->
      is_forall(concl th) && MOI_S5K_MENTIONS "closed" th) `{v:real^N} IN l` STRIP_ASSUME_TAC THEN
    SUBGOAL_THEN `DISJOINT ((xx:real^N->real^3->bool) v) (IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) moi_s35_slab) /\
                  DISJOINT (IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) moi_s35_slab) ((M:real^N->real^3->bool) v)`
    MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(Y:real^N->real^3->bool) v SUBSET xx v UNION M v` THEN
    SPEC_TAC(`IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) moi_s35_slab`,`ss:real^3->bool`) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u v. {u} IN l /\ {v} IN l /\ ~(u = v) /\ ~(segment[u,v] IN l)
          ==> DISJOINT ((Y:real^N->real^3->bool) u) (Y v)`
  (LABEL_TAC "c5") THENL
   [MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN STRIP_TAC THEN
    MOI_S5K_AT (fun th ->
      is_forall(concl th) && MOI_S5K_MENTIONS "closed" th) `{u:real^N} IN l` STRIP_ASSUME_TAC THEN
    MOI_S5K_AT (fun th ->
      is_forall(concl th) && MOI_S5K_MENTIONS "closed" th) `{v:real^N} IN l` STRIP_ASSUME_TAC THEN
    SUBGOAL_THEN `~(segment[v:real^N,u] IN l)` ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[SEGMENT_SYM] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `DISJOINT ((xx:real^N->real^3->bool) u) (xx v) /\
      DISJOINT ((xx:real^N->real^3->bool) u) ((M:real^N->real^3->bool) v) /\
      DISJOINT ((xx:real^N->real^3->bool) v) ((M:real^N->real^3->bool) u) /\
      DISJOINT ((M:real^N->real^3->bool) u) (M v)`
    MP_TAC THENL
     [ASM_SIMP_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`(Y:real^N->real^3->bool) u SUBSET xx u UNION M u`;
        `(Y:real^N->real^3->bool) v SUBSET xx v UNION M v`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN IMAGE h (UNIONS l)
        ==> ?v. {v} IN l /\ y IN interior ((Y:real^N->real^3->bool) v) /\
                !e. moi_s35_edge l e ==> ~(y IN IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) moi_s35_stube)`
  (LABEL_TAC "c6") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MOI_S5K_AT (fun th ->
      is_forall(concl th) && MOI_S5K_MENTIONS "interior" th &&
      can (find_term ((=) `h:real^N->real^3`)) (concl th))
      `(y:real^3) IN IMAGE (h:real^N->real^3) (UNIONS l)`
      (X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[] THEN
    MOI_S5K_AT (fun th ->
      is_forall(concl th) && MOI_S5K_MENTIONS "closed" th) `{v:real^N} IN l` STRIP_ASSUME_TAC THEN
    SUBGOAL_THEN `~((y:real^3) IN (M:real^N->real^3->bool) v)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `(y:real^3) IN UNIONS {IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) moi_s35_stube | e | moi_s35_edge l e /\ (bv:(real^N->bool)->real^N) e = v}` MP_TAC THENL
       [MATCH_MP_TAC(SET_RULE `!s t x:real^3. s SUBSET t /\ x IN s ==> x IN t`) THEN
        EXISTS_TAC `(M:real^N->real^3->bool) v` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `e:real^N->bool` o check (fun th ->
        is_forall(concl th) && is_neg(snd(dest_imp(snd(dest_forall(concl th))))))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`(xx:real^N->real^3->bool) v`; `(Y:real^N->real^3->bool) v`;
                   `(M:real^N->real^3->bool) v`] MOI_S5K_LOCAL_OFF) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`interior ((Y:real^N->real^3->bool) v) DIFF M v = interior (xx v) DIFF M v`;
      `(y:real^3) IN interior ((xx:real^N->real^3->bool) v)`;
      `~((y:real^3) IN (M:real^N->real^3->bool) v)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s35_frame] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    MOI_S5K_AT (fun th ->
      is_forall(concl th) && MOI_S5K_MENTIONS "pl_map_on" th)
      `{v:real^N} IN l` STRIP_ASSUME_TAC THEN
    USE_THEN "c1" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `{v:real^N} IN l`))) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
    MOI_S5K_AT (fun th ->
      is_forall(concl th) && MOI_S5K_MENTIONS "moi_s35_same_orient" th)
      `moi_s35_edge l (e:real^N->bool)` STRIP_ASSUME_TAC THEN
    USE_THEN "c2" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
      (ASSUME `moi_s35_edge l (e:real^N->bool)`))) THEN
    ASM_REWRITE_TAC[];
    USE_THEN "c3" ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    USE_THEN "c5" ACCEPT_TAC;
    USE_THEN "c6" ACCEPT_TAC]);;
(* The post state for the combined cells.                                   *)

let MOI_S5K_POST = prove
 (`!(t:(real^N->bool)->bool) (l:(real^N->bool)->bool) (h:real^N->real^3) (w:real^N->real^3->bool) (av:(real^N->bool)->real^N) (bv:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N) (ff:real^N->real^N->real^3) (xx:real^N->real^3->bool) (cc:(real^N->bool)->real) (g:real^N->real^N->bool) (Y:real^N->real^3->bool) (M:real^N->real^3->bool).
     moi_s35_charts t l g av bv psi /\ moi_s35_pre t l h w av bv psi ff xx cc /\
     (!v. {v} IN l ==> moi_s5k_inv l w av bv psi ff xx cc v {e:real^N->bool | moi_s35_edge l e /\ (bv:(real^N->bool)->real^N) e = v} (Y v) (M v))
     ==> moi_s35_post t l h w av bv psi ff Y cc`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_s35_pre] o check
    (MOI_S5K_HEAD "moi_s35_pre")) THEN
  SUBGOAL_THEN
   `!v. {v} IN l
        ==> closed ((M:real^N->real^3->bool) v) /\ M v SUBSET UNIONS {IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) moi_s35_stube | e | e IN {e:real^N->bool | moi_s35_edge l e /\ (bv:(real^N->bool)->real^N) e = v}} /\
            M v SUBSET UNIONS {IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) moi_s35_stube | e | moi_s35_edge l e /\ (bv:(real^N->bool)->real^N) e = v} /\
            (Y:real^N->real^3->bool) v DIFF M v = xx v DIFF M v /\ pl_ball 3 (Y v) /\
            Y v SUBSET xx v UNION M v /\
            (!e. moi_s35_edge l e /\ bv e = v
                 ==> (?b. moi_s35_edge_conf ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) (xx (av e)) (Y v) (w v) b
                            (IMAGE ((moi_s35_bch (ff:real^N->real^N->real^3) (bv:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) (moi_s35_sq (&5 / &32) (--(&3) / &256))) (IMAGE ((moi_s35_bch (ff:real^N->real^N->real^3) (bv:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) (moi_s35_sq (&11 / &32) (&3 / &256))) (cc e)) /\
                     moi_s35_single ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) (xx (av e)) (Y v) (cc e))`
  (LABEL_TAC "iv") THENL
   [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_S5K_INV_V THEN
    MOI_S5K_AT (fun th -> is_forall(concl th) && MOI_S5K_MENTIONS "moi_s5k_inv" th)
      `{v:real^N} IN l` ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s35_frame t l h w av bv psi ff (Y:real^N->real^3->bool) cc`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S5K_POST_FRAME THEN
    MAP_EVERY EXISTS_TAC [`xx:real^N->real^3->bool`; `g:real^N->real^N->bool`;
                          `M:real^N->real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    USE_THEN "iv" (fun th -> MP_TAC(MATCH_MP th (ASSUME `{v:real^N} IN l`))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `h:real^N->real^3`; `w:real^N->real^3->bool`; `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`; `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`; `g:real^N->real^N->bool`; `M:real^N->real^3->bool`]
    MOI_S5K_MSEP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    USE_THEN "iv" (fun th -> MP_TAC(MATCH_MP th (ASSUME `{v:real^N} IN l`))) THEN
    SIMP_TAC[];
    STRIP_TAC] THEN
  ASM_REWRITE_TAC[moi_s35_post] THEN CONJ_TAC THENL
   [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    USE_THEN "iv" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `{v:real^N} IN l`))) THEN
    MOI_S5K_AT (fun th -> is_forall(concl th) && MOI_S5K_MENTIONS "moi_s35_csrc" th)
      `{v:real^N} IN l` (SUBST1_TAC o SYM) THEN
    MAP_EVERY UNDISCH_TAC
     [`(M:real^N->real^3->bool) v SUBSET UNIONS {IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) moi_s35_stube | e | moi_s35_edge l e /\ (bv:(real^N->bool)->real^N) e = v}`;
      `(Y:real^N->real^3->bool) v DIFF M v = xx v DIFF M v`] THEN
    SPEC_TAC(`UNIONS {IMAGE ((moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) moi_s35_stube | e | moi_s35_edge l e /\ (bv:(real^N->bool)->real^N) e = v}`,`uu:real^3->bool`) THEN SET_TAC[];
    X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`; `e:real^N->bool`] MOI_S5K_CHART_ENDS) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    USE_THEN "iv" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `{(bv:(real^N->bool)->real^N) e} IN l`))) THEN
    DISCH_THEN(MP_TAC o SPEC `e:real^N->bool` o last o CONJUNCTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `bb:real^3->bool`) ASSUME_TAC) THEN
    USE_THEN "iv" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
      (ASSUME `{(av:(real^N->bool)->real^N) e} IN l`))) THEN
    USE_THEN "iv" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
      (ASSUME `{(bv:(real^N->bool)->real^N) e} IN l`))) THEN
    MOI_S5K_AT (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
      MOI_S5K_MENTIONS "moi_s35_level" th &&
      can (find_term ((=) `M:real^N->real^3->bool`)) (concl th))
      `moi_s35_edge l (e:real^N->bool)` STRIP_ASSUME_TAC THEN
    MP_TAC(ISPECL [`(moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e`; `(xx:real^N->real^3->bool) ((av:(real^N->bool)->real^N) e)`;
                   `(Y:real^N->real^3->bool) ((av:(real^N->bool)->real^N) e)`;
                   `(Y:real^N->real^3->bool) ((bv:(real^N->bool)->real^N) e)`;
                   `(w:real^N->real^3->bool) ((bv:(real^N->bool)->real^N) e)`;
                   `bb:real^3->bool`; `IMAGE ((moi_s35_bch (ff:real^N->real^N->real^3) (bv:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) (moi_s35_sq (&5 / &32) (--(&3) / &256))`; `IMAGE ((moi_s35_bch (ff:real^N->real^N->real^3) (bv:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)) e) (moi_s35_sq (&11 / &32) (&3 / &256))`;
                   `(cc:(real^N->bool)->real) e`;
                   `(M:real^N->real^3->bool) ((av:(real^N->bool)->real^N) e)`]
      MOI_S5K_PRES_A) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[DISJOINT_SYM] THEN FIRST_ASSUM ACCEPT_TAC;
        MAP_EVERY UNDISCH_TAC
         [`(Y:real^N->real^3->bool) ((bv:(real^N->bool)->real^N) e) SUBSET
           xx (bv e) UNION M (bv e)`;
          `DISJOINT ((xx:real^N->real^3->bool) ((bv:(real^N->bool)->real^N) e))
                    ((M:real^N->real^3->bool) ((av:(real^N->bool)->real^N) e))`;
          `DISJOINT ((M:real^N->real^3->bool) ((av:(real^N->bool)->real^N) e))
                    (M ((bv:(real^N->bool)->real^N) e))`] THEN
        SET_TAC[]];
      DISCH_THEN(fun th -> CONJ_TAC THENL
       [EXISTS_TAC `bb:real^3->bool` THEN ACCEPT_TAC(CONJUNCT1 th);
        MATCH_MP_TAC(CONJUNCT2 th) THEN FIRST_ASSUM ACCEPT_TAC])]]);;

(* The main theorem COMBINE.                                                 *)

let COMBINE = prove
 (MOI_S35_COMBINE_R1,
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!v. ?y m. {v} IN l ==> moi_s5k_inv l w av bv psi ff xx cc v {e:real^N->bool | moi_s35_edge l e /\ (bv:(real^N->bool)->real^N) e = v} y m`
  MP_TAC THENL
   [X_GEN_TAC `v:real^N` THEN ASM_CASES_TAC `{v:real^N} IN l` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `h:real^N->real^3`; `w:real^N->real^3->bool`; `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`; `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`; `g:real^N->real^N->bool`; `v:real^N`]
      (MATCH_MP MOI_S5K_PROCESS (ASSUME MOI_S35_REMOVAL))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[SUBSET_REFL] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{e:real^N->bool | moi_s35_edge l e /\
                                  ((av:(real^N->bool)->real^N) e = v \/ bv e = v)}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S5V_EDGES_FINITE THEN EXISTS_TAC `t:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`; `e:real^N->bool`] MOI_S5K_CHART_ENDS) THEN
      ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; MESON_TAC[]];
      SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `Y:real^N->real^3->bool` (X_CHOOSE_TAC `M:real^N->real^3->bool`)) THEN
  EXISTS_TAC `Y:real^N->real^3->bool` THEN
  MATCH_MP_TAC MOI_S5K_POST THEN
  MAP_EVERY EXISTS_TAC [`xx:real^N->real^3->bool`; `g:real^N->real^N->bool`;
                        `M:real^N->real^3->bool`] THEN
  ASM_REWRITE_TAC[]);;


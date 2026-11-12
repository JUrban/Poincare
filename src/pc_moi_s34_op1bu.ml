(* ========================================================================= *)
(* pc_moi_s34_op1bu: Operation 1 of Sec 34 (p.241) with the compressing    *)
(* disk outside the face ball and an unclean pocket: DG's shell and tunnel  *)
(* (Section34CompressionOutsideTube), with the tunnel routed outside the     *)
(* tube N along the outer side of the face torus.  Main theorem UNCLEAN :    *)
(* |- MOI_S4V_UNCLEAN of pc_moi_s34_op1bstmt.ml.                             *)
(* The tube lemma is MOI_TB3_TUBE of pc_moi_tube3.                          *)
(* ========================================================================= *)

needs "src/pc_moi_s34_stmt.ml";;
needs "src/pc_moi_s34_op1bstmt.ml";;
needs "src/pc_moi_s34_op1b.ml";;
needs "src/pc_moi_s34_tinf.ml";;
needs "src/pc_moi_s34_l910.ml";;
needs "src/pc_moi_s34_outer.ml";;
needs "src/pc_moi_s34_h1.ml";;
needs "src/pc_moi_s35_cells.ml";;
needs "src/pc_moi_sch3_stmt.ml";;
needs "src/pc_moi_sch3_s2.ml";;
needs "src/pc_moi_tube3.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Generic part (no Sec 34 vocabulary).  A connected set minus finitely many *)
(* pairwise disjoint closed pieces, each meeting the rest in a nonempty      *)
(* connected set, stays connected (used for A_v = frontier T_v minus its      *)
(* splitting disks): a separation of the rest extends piece by piece.        *)
(* ------------------------------------------------------------------------- *)

let MOI_S4VU_HOLES_CONNECTED = prove
 (`!sg a (dd:(real^N->bool)->bool) (bd:(real^N->bool)->real^N->bool).
     connected sg /\ closed a /\ FINITE dd /\ sg = a UNION UNIONS dd /\
     (!D. D IN dd ==> closed D /\ connected (bd D) /\ ~(bd D = {}) /\ D INTER a = bd D) /\
     (!D D'. D IN dd /\ D' IN dd /\ ~(D = D') ==> DISJOINT D D')
     ==> connected a`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "pc") (LABEL_TAC "dj")))))) THEN
  REWRITE_TAC[CONNECTED_CLOSED; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`e1:real^N->bool`; `e2:real^N->bool`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!D:real^N->bool. D IN dd
                  ==> ((bd:(real^N->bool)->real^N->bool) D SUBSET e1 \/ bd D SUBSET e2) /\
                      ~(bd D SUBSET e1 /\ bd D SUBSET e2) /\
                      (bd D SUBSET e1 ==> D INTER e2 INTER a = {}) /\
                      (bd D SUBSET e2 ==> D INTER e1 INTER a = {})`
  (LABEL_TAC "side") THENL
   [X_GEN_TAC `D:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "pc" (MP_TAC o SPEC `D:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `(bd:(real^N->bool)->real^N->bool) D SUBSET a` ASSUME_TAC THENL
     [UNDISCH_TAC `D INTER a = (bd:(real^N->bool)->real^N->bool) D` THEN SET_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_CASES_TAC `e1 INTER (bd:(real^N->bool)->real^N->bool) D = {}` THENL
       [DISJ2_TAC THEN
        UNDISCH_TAC `e1 INTER (bd:(real^N->bool)->real^N->bool) D = {}` THEN
        UNDISCH_TAC `(a:real^N->bool) SUBSET e1 UNION e2` THEN
        UNDISCH_TAC `(bd:(real^N->bool)->real^N->bool) D SUBSET a` THEN SET_TAC[];
        ALL_TAC] THEN
      ASM_CASES_TAC `e2 INTER (bd:(real^N->bool)->real^N->bool) D = {}` THENL
       [DISJ1_TAC THEN
        UNDISCH_TAC `e2 INTER (bd:(real^N->bool)->real^N->bool) D = {}` THEN
        UNDISCH_TAC `(a:real^N->bool) SUBSET e1 UNION e2` THEN
        UNDISCH_TAC `(bd:(real^N->bool)->real^N->bool) D SUBSET a` THEN SET_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC(TAUT `F ==> p`) THEN
      UNDISCH_TAC `connected ((bd:(real^N->bool)->real^N->bool) D)` THEN
      REWRITE_TAC[CONNECTED_CLOSED] THEN
      MAP_EVERY EXISTS_TAC [`e1:real^N->bool`; `e2:real^N->bool`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `(a:real^N->bool) SUBSET e1 UNION e2` THEN
        UNDISCH_TAC `(bd:(real^N->bool)->real^N->bool) D SUBSET a` THEN SET_TAC[];
        UNDISCH_TAC `e1 INTER e2 INTER (a:real^N->bool) = {}` THEN
        UNDISCH_TAC `(bd:(real^N->bool)->real^N->bool) D SUBSET a` THEN SET_TAC[]];
      UNDISCH_TAC `~((bd:(real^N->bool)->real^N->bool) D = {})` THEN
      UNDISCH_TAC `e1 INTER e2 INTER (a:real^N->bool) = {}` THEN
      UNDISCH_TAC `(bd:(real^N->bool)->real^N->bool) D SUBSET a` THEN SET_TAC[];
      UNDISCH_TAC `D INTER a = (bd:(real^N->bool)->real^N->bool) D` THEN
      UNDISCH_TAC `e1 INTER e2 INTER (a:real^N->bool) = {}` THEN SET_TAC[];
      UNDISCH_TAC `D INTER a = (bd:(real^N->bool)->real^N->bool) D` THEN
      UNDISCH_TAC `e1 INTER e2 INTER (a:real^N->bool) = {}` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i:real^N->bool. closed i
      ==> closed ((i INTER a) UNION
                  UNIONS {D | D IN dd /\ (bd:(real^N->bool)->real^N->bool) D SUBSET i})`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSED_UNION THEN ASM_SIMP_TAC[CLOSED_INTER] THEN
    MATCH_MP_TAC CLOSED_UNIONS THEN ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN USE_THEN "pc" (MP_TAC o SPEC `t:real^N->bool`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `connected (sg:real^N->bool)` THEN
  REWRITE_TAC[CONNECTED_CLOSED] THEN
  MAP_EVERY EXISTS_TAC
   [`(e1 INTER a) UNION
     UNIONS {D | D IN dd /\ (bd:(real^N->bool)->real^N->bool) D SUBSET e1}`;
    `(e2 INTER a) UNION
     UNIONS {D | D IN dd /\ (bd:(real^N->bool)->real^N->bool) D SUBSET e2}`] THEN
  ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THENL
   [GEN_REWRITE_TAC I [SUBSET] THEN
    REWRITE_TAC[IN_UNION; IN_UNIONS; IN_INTER; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN STRIP_TAC THENL
     [UNDISCH_TAC `(a:real^N->bool) SUBSET e1 UNION e2` THEN
      UNDISCH_TAC `(x:real^N) IN a` THEN SET_TAC[];
      USE_THEN "side" (MP_TAC o C MATCH_MP (ASSUME `(t:real^N->bool) IN dd`)) THEN
      DISCH_THEN(DISJ_CASES_TAC o CONJUNCT1) THENL
       [DISJ1_TAC THEN DISJ2_TAC THEN EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[];
        DISJ2_TAC THEN DISJ2_TAC THEN EXISTS_TAC `t:real^N->bool` THEN
        ASM_REWRITE_TAC[]]];
    REWRITE_TAC[EXTENSION; IN_UNION; IN_UNIONS; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
    DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN
    DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
     [UNDISCH_TAC `e1 INTER e2 INTER (a:real^N->bool) = {}` THEN
      UNDISCH_TAC `(x:real^N) IN e1` THEN UNDISCH_TAC `(x:real^N) IN e2` THEN
      UNDISCH_TAC `(x:real^N) IN a` THEN SET_TAC[];
      USE_THEN "side" (MP_TAC o C MATCH_MP (ASSUME `(t:real^N->bool) IN dd`)) THEN
      DISCH_THEN(MP_TAC o C MATCH_MP
        (ASSUME `(bd:(real^N->bool)->real^N->bool) t SUBSET e1`) o
        CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
      UNDISCH_TAC `(x:real^N) IN e2` THEN UNDISCH_TAC `(x:real^N) IN t` THEN
      UNDISCH_TAC `(x:real^N) IN a` THEN SET_TAC[];
      USE_THEN "side" (MP_TAC o C MATCH_MP (ASSUME `(t:real^N->bool) IN dd`)) THEN
      DISCH_THEN(MP_TAC o C MATCH_MP
        (ASSUME `(bd:(real^N->bool)->real^N->bool) t SUBSET e2`) o
        CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
      UNDISCH_TAC `(x:real^N) IN e1` THEN UNDISCH_TAC `(x:real^N) IN t` THEN
      UNDISCH_TAC `(x:real^N) IN a` THEN SET_TAC[];
      ASM_CASES_TAC `t:real^N->bool = t'` THENL
       [UNDISCH_TAC `t:real^N->bool = t'` THEN DISCH_THEN SUBST_ALL_TAC THEN
        USE_THEN "side" (MP_TAC o C MATCH_MP (ASSUME `(t':real^N->bool) IN dd`)) THEN
        ASM_REWRITE_TAC[];
        USE_THEN "dj" (MP_TAC o SPECL [`t:real^N->bool`; `t':real^N->bool`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        UNDISCH_TAC `(x:real^N) IN t` THEN UNDISCH_TAC `(x:real^N) IN t'` THEN
        SET_TAC[]]];
    MATCH_MP_TAC(SET_RULE `!e a u w:real^N->bool.
       ~(e INTER a = {}) ==> ~((e INTER a UNION u) INTER (a UNION w) = {})`) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC(SET_RULE `!e a u w:real^N->bool.
       ~(e INTER a = {}) ==> ~((e INTER a UNION u) INTER (a UNION w) = {})`) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Sec 34, the unclean pocket.  A vertex of tt in kk has its h-image in its  *)
(* own vertex ball (h(1-skeleton) SUBSET int f1(N), carriers of the other    *)
(* vertices miss h of the vertex).                                           *)
(* ------------------------------------------------------------------------- *)

let MOI_S4VU_H_VERTEX = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car w.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\ {w} IN kk
     ==> h w IN IMAGE f1 (moi_s34_vb tt kk w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  LABEL_TAC "fr" (REWRITE_RULE[moi_s34_frame]
    (ASSUME `moi_s34_frame tt kk h ep (f1:real^N->real^3) car`)) THEN
  SUBGOAL_THEN `(h:real^N->real^3) w IN IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)` MP_TAC THENL
   [USE_THEN "fr" (MP_TAC o el 2 o CONJUNCTS) THEN
    MP_TAC(ISPEC `IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)` INTERIOR_SUBSET) THEN
    SUBGOAL_THEN `(w:real^N) IN UNIONS (skeleton 1 kk)` MP_TAC THENL
     [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{w:real^N}` THEN
      ASM_REWRITE_TAC[MOI_S4L_SKEL_VERTEX; IN_SING];
      ALL_TAC] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`]
    MOI_S4L_GRAPH_TUBE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  REWRITE_TAC[IN_IMAGE; IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `t:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)))) THEN
  ASM_CASES_TAC `x:real^N = w` THENL
   [EXISTS_TAC `p:real^N` THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN
  SUBGOAL_THEN `(h:real^N->real^3) w IN car {x:real^N}` MP_TAC THENL
   [USE_THEN "fr" (MP_TAC o SPEC `x:real^N` o el 6 o CONJUNCTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
    UNDISCH_TAC `(h:real^N->real^3) w = f1 (p:real^N)` THEN
    UNDISCH_TAC `(p:real^N) IN t` THEN
    UNDISCH_TAC `t = moi_s34_vb (tt:(real^N->bool)->bool) kk x` THEN SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "fr" (MP_TAC o SPECL [`x:real^N`; `{w:real^N}`] o el 8 o CONJUNCTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_SING]; ALL_TAC] THEN
  REWRITE_TAC[IMAGE_CLAUSES] THEN SET_TAC[]);;

(* A foreign vertex ball meeting the pocket lies in its interior: it misses  *)
(* d (op1w) and e (fb1, e SUBSET frontier cb s).                             *)

let MOI_S4VU_FOREIGN_IN_Q = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v d j q e e' w.
     moi_s34_tube tt kk /\ moi_s34_emb h (UNIONS tt) /\
     moi_s34_frame tt kk h ep f1 car /\ moi_s34_fbinv tt kk h f1 car cb /\
     s IN moi_s34_simp kk (&2) /\
     moi_s34_op1w tt kk f1 cb s v d j /\ DISJOINT (d DIFF j) (cb s) /\
     moi_s4v_pocket (cb s) d j q e e' /\
     {w} IN kk /\ ~(w IN s) /\ ~DISJOINT q (IMAGE f1 (moi_s34_vb tt kk w))
     ==> IMAGE f1 (moi_s34_vb tt kk w) SUBSET interior q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`;
                 `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`;
                 `v:real^N`; `d:real^3->bool`; `j:real^3->bool`] MOI_S4V_SETUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `DISJOINT ((cb:(real^N->bool)->real^3->bool) s)
                         (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`;
                   `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`]
      MOI_S4L_TRACE_COMP_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `w:real^N` o el 3 o CONJUNCTS o
      REWRITE_RULE[moi_s34_fb1] o CONJUNCT1) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_s4v_pocket] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "moi_s4v_pocket"
                     with Failure _ -> false)) THEN
  MP_TAC(ISPEC `(cb:(real^N->bool)->real^3->bool) s` MOI_S4V_BALL_SIDES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPEC `q:real^3->bool` MOI_S4V_BALL_SIDES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `connected (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `w:real^N`] MOI_S4L_AV_BASIC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    DISCH_THEN(MP_TAC o MATCH_MP MOI_S4L_PL_BALL_COMPACT) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w) INTER frontier q = {}`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `DISJOINT ((cb:(real^N->bool)->real^3->bool) s)
                          (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w))` THEN
    UNDISCH_TAC `e UNION e' = frontier ((cb:(real^N->bool)->real^3->bool) s)` THEN
    UNDISCH_TAC `frontier ((cb:(real^N->bool)->real^3->bool) s) SUBSET cb s` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^N` o check (fun th ->
      try let v,bd = dest_forall(concl th) in fst(dest_var v) = "w" &&
              is_imp bd && can (find_term (fun t -> try fst(dest_const t) = "DISJOINT"
                                                    with Failure _ -> false)) bd &&
              can (find_term (fun t -> t = `d:real^3->bool`)) bd
      with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w) SUBSET q` MP_TAC THENL
   [MP_TAC(ISPECL [`IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w)`; `q:real^3->bool`]
      CONNECTED_INTER_FRONTIER) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~DISJOINT q (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w) INTER frontier q = {}` THEN
  MP_TAC(ISPEC `q:real^3->bool` frontier) THEN
  ASM_SIMP_TAC[CLOSURE_CLOSED] THEN SET_TAC[]);;

(* A foreign vertex ball meeting the pocket yields a point of int q on some *)
(* A_u, u a vertex of s: a rim of a splitting disk at s if the foreign      *)
(* vertex is adjacent to s; otherwise frame clause (7) for a 3-simplex      *)
(* containing s keeps h w (which lies in its own vertex ball) out of q.     *)

let MOI_S4VU_FOREIGN_POINT = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v d j q e e' w.
     moi_s34_tube tt kk /\ moi_s34_emb h (UNIONS tt) /\
     moi_s34_frame tt kk h ep f1 car /\ moi_s34_fbinv tt kk h f1 car cb /\
     s IN moi_s34_simp kk (&2) /\
     moi_s34_op1w tt kk f1 cb s v d j /\ DISJOINT (d DIFF j) (cb s) /\
     moi_s4v_pocket (cb s) d j q e e' /\
     {w} IN kk /\ ~(w IN s) /\ ~DISJOINT q (IMAGE f1 (moi_s34_vb tt kk w))
     ==> ?u y. {u} IN kk /\ u IN s /\ y IN interior q /\
               y IN IMAGE f1 (moi_s34_vb tt kk u INTER moi_s34_bd tt kk)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`;
                 `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`;
                 `v:real^N`; `d:real^3->bool`; `j:real^3->bool`; `q:real^3->bool`;
                 `e:real^3->bool`; `e':real^3->bool`; `w:real^N`] MOI_S4VU_FOREIGN_IN_Q) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  LABEL_TAC "fr" (REWRITE_RULE[moi_s34_frame]
    (ASSUME `moi_s34_frame tt kk h ep (f1:real^N->real^3) car`)) THEN
  ASM_CASES_TAC `?u:real^N. u IN s /\ {u} IN kk /\ segment[u,w] IN kk` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `~(u:real^N = w)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~((w:real^N) IN s)` THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `u:real^N`; `w:real^N`] MOI_S4L_EDGE_SD) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "fr" (MP_TAC o SPEC `segment[u:real^N,w]` o el 7 o CONJUNCTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o MATCH_MP MOI_S4L_PL_CELL2_TOPO) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `y:real^3`) THEN
    MAP_EVERY EXISTS_TAC [`u:real^N`; `y:real^3`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!a b (y:real^3). y IN a /\ a SUBSET b ==> y IN b`) THEN
      EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w)` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y:real^3) IN IMAGE (f1:real^N->real^3)
                     ((moi_s34_vb tt kk u INTER moi_s34_vb tt kk w) INTER moi_s34_bd tt kk)` THEN
      SET_TAC[];
      UNDISCH_TAC `(y:real^3) IN IMAGE (f1:real^N->real^3)
                     ((moi_s34_vb tt kk u INTER moi_s34_vb tt kk w) INTER moi_s34_bd tt kk)` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`;
                 `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`;
                 `v:real^N`; `d:real^3->bool`; `j:real^3->bool`] MOI_S4V_SETUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(s:real^N->bool) IN kk /\ aff_dim s = &2` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(s:real^N->bool) IN moi_s34_simp kk (&2)` THEN
    SIMP_TAC[moi_s34_simp; IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `v:real^N`; `s:real^N->bool`] MOI_S4O_KK_PURE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`]
    MOI_S4L_TUBE_TUBE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `~((w:real^N) IN r)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) &&
      is_exists(rand(concl th)))) THEN
    REWRITE_TAC[] THEN EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `lf_simplicial_complex (kk:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sx") (CONJUNCTS_THEN2 (LABEL_TAC "fc")
      (CONJUNCTS_THEN2 (LABEL_TAC "it") (K ALL_TAC)))) THEN
    USE_THEN "fc" MATCH_MP_TAC THEN EXISTS_TAC `r:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S4L_SIMPLEX_EDGE_FACE THEN
    CONJ_TAC THENL [USE_THEN "sx" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM FACE_OF_SING] THEN CONJ_TAC THENL
     [USE_THEN "it" (MP_TAC o SPECL [`{v:real^N}`; `r:real^N->bool`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `{v:real^N} INTER r = {v}` (fun th -> SIMP_TAC[th]) THEN
      UNDISCH_TAC `(v:real^N) IN s` THEN UNDISCH_TAC `(s:real^N->bool) SUBSET r` THEN
      SET_TAC[];
      USE_THEN "it" (MP_TAC o SPECL [`{w:real^N}`; `r:real^N->bool`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `{w:real^N} INTER r = {w}` (fun th -> SIMP_TAC[th]) THEN
      UNDISCH_TAC `(w:real^N) IN r` THEN SET_TAC[]];
    ALL_TAC] THEN
  USE_THEN "fr" (MP_TAC o SPECL [`r:real^N->bool`; `w:real^N`] o el 10 o CONJUNCTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[moi_s34_simp; IN_ELIM_THM]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `frontier q SUBSET
                UNIONS {(car:(real^N->bool)->real^3->bool) q' | q' |
                        q' IN kk /\ ~(q' = {}) /\ q' SUBSET r /\ ~(q' = r)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `(car:(real^N->bool)->real^3->bool) s` THEN CONJ_TAC THENL
     [FIRST_ASSUM(SUBST1_TAC o el 5 o CONJUNCTS o REWRITE_RULE[moi_s4v_pocket] o
        check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
                             "moi_s4v_pocket" with Failure _ -> false)) THEN
      FIRST_ASSUM(MP_TAC o el 2 o CONJUNCTS o REWRITE_RULE[moi_s4v_pocket] o
        check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
                             "moi_s4v_pocket" with Failure _ -> false)) THEN
      UNDISCH_TAC `(d:real^3->bool) SUBSET (car:(real^N->bool)->real^3->bool) s` THEN
      UNDISCH_TAC `frontier ((cb:(real^N->bool)->real^3->bool) s) SUBSET car s` THEN
      SET_TAC[];
      GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      X_GEN_TAC `y:real^3` THEN
      DISCH_TAC THEN EXISTS_TAC `(car:(real^N->bool)->real^3->bool) s` THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [DISCH_TAC THEN UNDISCH_TAC `aff_dim(s:real^N->bool) = &2` THEN
        ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
        DISCH_TAC THEN UNDISCH_TAC `aff_dim(s:real^N->bool) = &2` THEN
        ASM_REWRITE_TAC[] THEN INT_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `w:real^N`] MOI_S4VU_H_VERTEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `bounded (q:real^3->bool)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o el 4 o CONJUNCTS o REWRITE_RULE[moi_s4v_pocket] o
      check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
                           "moi_s4v_pocket" with Failure _ -> false)) THEN
    DISCH_THEN(MP_TAC o MATCH_MP MOI_S4V_BALL_SIDES) THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `q:real^3->bool` OUTSIDE_FRONTIER_MISSES_CLOSURE) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`frontier q:real^3->bool`;
                 `UNIONS {(car:(real^N->bool)->real^3->bool) q' | q' |
                          q' IN kk /\ ~(q' = {}) /\ q' SUBSET r /\ ~(q' = r)}`]
    OUTSIDE_MONO) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `q:real^3->bool` INTERIOR_SUBSET) THEN
  MP_TAC(ISPEC `q:real^3->bool` CLOSURE_SUBSET) THEN
  UNDISCH_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w) SUBSET interior q` THEN
  UNDISCH_TAC `(h:real^N->real^3) w IN IMAGE f1 (moi_s34_vb tt kk w)` THEN
  UNDISCH_TAC `(h:real^N->real^3) w IN
                outside (UNIONS {(car:(real^N->bool)->real^3->bool) q' | q' |
                                 q' IN kk /\ ~(q' = {}) /\ q' SUBSET r /\ ~(q' = r)})` THEN
  SET_TAC[]);;

(* An unclean pocket contains a point of some A_u, u a vertex of s, in its  *)
(* interior.                                                                 *)

let MOI_S4VU_UNCLEAN_POINT = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v d j q e e'.
     moi_s34_tube tt kk /\ moi_s34_emb h (UNIONS tt) /\
     moi_s34_frame tt kk h ep f1 car /\ moi_s34_fbinv tt kk h f1 car cb /\
     s IN moi_s34_simp kk (&2) /\
     moi_s34_op1w tt kk f1 cb s v d j /\ DISJOINT (d DIFF j) (cb s) /\
     moi_s4v_pocket (cb s) d j q e e' /\ ~moi_s4v_clean tt kk f1 s q
     ==> ?u y. {u} IN kk /\ u IN s /\ y IN interior q /\
               y IN IMAGE f1 (moi_s34_vb tt kk u INTER moi_s34_bd tt kk)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!w. {w} IN kk /\ ~(w IN s) /\
        ~DISJOINT q (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w))
        ==> ?u y. {u} IN kk /\ u IN s /\ y IN interior q /\
                  y IN IMAGE f1 (moi_s34_vb tt kk u INTER moi_s34_bd tt kk)`
  (LABEL_TAC "fp") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S4VU_FOREIGN_POINT THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`;
                          `car:(real^N->bool)->real^3->bool`;
                          `cb:(real^N->bool)->real^3->bool`; `v:real^N`;
                          `d:real^3->bool`; `j:real^3->bool`; `e:real^3->bool`;
                          `e':real^3->bool`; `w:real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `~moi_s4v_clean tt kk (f1:real^N->real^3) s q` THEN
  REWRITE_TAC[moi_s4v_clean; DE_MORGAN_THM; NOT_FORALL_THM; NOT_IMP] THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
   [ALL_TAC;
    DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    USE_THEN "fp" MATCH_MP_TAC THEN EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `s:real^N->bool`] MOI_S4J_T_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  SUBGOAL_THEN `(z:real^3) IN IMAGE f1 (moi_s34_ft tt kk (s:real^N->bool))` ASSUME_TAC THENL
   [MP_TAC(ISPEC `IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)` FRONTIER_SUBSET_CLOSED) THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
    UNDISCH_TAC `(z:real^3) IN frontier (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?u:real^N. u IN s /\ {u} IN kk /\
                           (z:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^3) IN IMAGE f1 (moi_s34_ft tt kk (s:real^N->bool))` THEN
    REWRITE_TAC[moi_s34_ft; IN_IMAGE; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`]
    MOI_S4L_GRAPH_TUBE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> LABEL_TAC "nbu" (CONJUNCT1 th) THEN
                       LABEL_TAC "bdn" (CONJUNCT1(CONJUNCT2 th)) THEN
                       LABEL_TAC "vbn" (CONJUNCT1(CONJUNCT2(CONJUNCT2 th)))) THEN
  SUBGOAL_THEN `moi_s34_vb tt kk (u:real^N) SUBSET moi_s34_nb tt kk` ASSUME_TAC THENL
   [USE_THEN "vbn" (MP_TAC o SPEC `u:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `(z:real^3) IN IMAGE f1 (moi_s34_bd (tt:(real^N->bool)->bool) kk)` THENL
   [MAP_EVERY EXISTS_TAC [`u:real^N`; `z:real^3`] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`] MOI_S4L_IMAGES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`moi_s34_vb tt kk (u:real^N)`;
                               `moi_s34_bd (tt:(real^N->bool)->bool) kk`] o
               el 2 o CONJUNCTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "bdn" ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3) IN interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk))`
  ASSUME_TAC THENL
   [MP_TAC(el 3 (CONJUNCTS (REWRITE_RULE[moi_s34_frame]
      (ASSUME `moi_s34_frame tt kk h ep (f1:real^N->real^3) car`)))) THEN
    SUBGOAL_THEN `(z:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)` MP_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!a b (z:A). z IN a /\ a SUBSET b ==> z IN b`) THEN
      EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u)` THEN
      ASM_SIMP_TAC[IMAGE_SUBSET];
      ALL_TAC] THEN
    UNDISCH_TAC `~((z:real^3) IN IMAGE f1 (moi_s34_bd (tt:(real^N->bool)->bool) kk))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?p0. p0 IN interior q /\
         p0 IN interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)) /\
         ~(p0 IN IMAGE f1 (moi_s34_ft tt kk (s:real^N->bool)))`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `interior q INTER interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)) SUBSET
      interior (IMAGE f1 (moi_s34_ft tt kk (s:real^N->bool)))`
    MP_TAC THENL
     [MATCH_MP_TAC INTERIOR_MAXIMAL THEN SIMP_TAC[OPEN_INTER; OPEN_INTERIOR] THEN
      UNDISCH_TAC `~(?p0. p0 IN interior q /\
                         p0 IN interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)) /\
                         ~(p0 IN IMAGE f1 (moi_s34_ft tt kk (s:real^N->bool))))` THEN
      SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPEC `IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)` frontier) THEN
    UNDISCH_TAC `(z:real^3) IN frontier (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s))` THEN
    UNDISCH_TAC `(z:real^3) IN interior q` THEN
    UNDISCH_TAC `(z:real^3) IN interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?x:real^N. {x} IN kk /\ (p0:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk x)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(p0:real^3) IN interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk))` THEN
    MP_TAC(ISPEC `IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)` INTERIOR_SUBSET) THEN
    USE_THEN "nbu" SUBST1_TAC THEN
    REWRITE_TAC[SUBSET; IN_IMAGE; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  USE_THEN "fp" MATCH_MP_TAC THEN EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~((p0:real^3) IN IMAGE f1 (moi_s34_ft tt kk (s:real^N->bool)))` THEN
    REWRITE_TAC[moi_s34_ft] THEN
    UNDISCH_TAC `(p0:real^3) IN IMAGE f1 (moi_s34_vb tt kk (x:real^N))` THEN
    REWRITE_TAC[IN_IMAGE; IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    MP_TAC(ISPEC `q:real^3->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(p0:real^3) IN interior q` THEN
    UNDISCH_TAC `(p0:real^3) IN IMAGE f1 (moi_s34_vb tt kk (x:real^N))` THEN
    SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The outer route.  Near a point of the carriers                            *)
(* only the vertex balls containing it are present (local finiteness).      *)
(* ------------------------------------------------------------------------- *)

let MOI_S4VU_LOCAL_BALLS = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car x.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     x IN UNIONS {car q | q | q IN kk /\ ~(q = {})}
     ==> ?u. open u /\ x IN u /\
             !w. {w} IN kk /\ ~(x IN IMAGE f1 (moi_s34_vb tt kk w))
                 ==> DISJOINT u (IMAGE f1 (moi_s34_vb tt kk w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  LABEL_TAC "fr" (REWRITE_RULE[moi_s34_frame]
    (ASSUME `moi_s34_frame tt kk h ep (f1:real^N->real^3) car`)) THEN
  USE_THEN "fr" (MP_TAC o SPEC `x:real^3` o el 11 o CONJUNCTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u0:real^3->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `W0 = {w:real^N | {w} IN kk /\
                               ~((x:real^3) IN IMAGE f1 (moi_s34_vb tt kk w)) /\
                               ~(IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w) INTER
                                 u0 = {})}` THEN
  SUBGOAL_THEN `FINITE (W0:real^N->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `FINITE (IMAGE (\w:real^N. {w}) W0)` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] FINITE_SUBSET) o
        check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "FINITE"
                         with Failure _ -> false)) THEN
      EXPAND_TAC "W0" THEN REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `g:real^N->bool` THEN
      DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN
      USE_THEN "fr" (MP_TAC o SPEC `w:real^N` o el 6 o CONJUNCTS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
      UNDISCH_TAC `~(IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w) INTER u0 = {})` THEN
      SET_TAC[];
      MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC FINITE_IMAGE_INJ_EQ THEN SET_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `u0 DIFF UNIONS (IMAGE (\w:real^N. IMAGE (f1:real^N->real^3)
                                                  (moi_s34_vb tt kk w)) W0)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_DIFF THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CLOSED_UNIONS THEN ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `w:real^N` THEN EXPAND_TAC "W0" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `w:real^N`] MOI_S4L_AV_BASIC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    REWRITE_TAC[IN_DIFF; IN_UNIONS; IN_IMAGE] THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "W0" THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
    X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
    ASM_CASES_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w) INTER u0 = {}` THENL
     [UNDISCH_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w) INTER u0 = {}` THEN
      SET_TAC[];
      SUBGOAL_THEN `(w:real^N) IN W0` MP_TAC THENL
       [EXPAND_TAC "W0" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
      SET_TAC[]]]);;

(* Two adjacent vertex balls form a PL ball (MOI_S5V_CELL_UNION along their  *)
(* splitting disk), with the expected frontier.                              *)

let MOI_S4VU_TWO_BALLS = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car a b.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     {a} IN kk /\ ~(b = a) /\ segment[a,b] IN kk
     ==> pl_ball 3 (IMAGE f1 (moi_s34_vb tt kk a) UNION IMAGE f1 (moi_s34_vb tt kk b)) /\
         frontier (IMAGE f1 (moi_s34_vb tt kk a) UNION IMAGE f1 (moi_s34_vb tt kk b)) =
         (frontier (IMAGE f1 (moi_s34_vb tt kk a)) UNION
          frontier (IMAGE f1 (moi_s34_vb tt kk b))) DIFF
         (IMAGE f1 (moi_s34_vb tt kk a INTER moi_s34_vb tt kk b) DIFF
          IMAGE f1 (moi_s34_vb tt kk a INTER moi_s34_vb tt kk b INTER moi_s34_bd tt kk))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!c:real^3->bool. pl_ball 3 c ==> pl_cell_with_boundary 3 c (frontier c)`
  (LABEL_TAC "bc") THENL
   [GEN_TAC THEN REWRITE_TAC[pl_ball; pl_cell_with_boundary] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
      (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_SCD_BALL_FRONTIER THEN
    EXISTS_TAC `g:real^3->real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `a:real^N`] MOI_S4L_SIGMA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "fa")
    (CONJUNCTS_THEN2 (MP_TAC o SPEC `b:real^N`) (K ALL_TAC)))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `b:real^N`] MOI_S4L_SIGMA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "fb") (K ALL_TAC))) THEN
  SUBGOAL_THEN `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk a INTER moi_s34_vb tt kk b)
                SUBSET frontier (IMAGE f1 (moi_s34_vb tt kk a)) /\
                IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk a INTER moi_s34_vb tt kk b)
                SUBSET frontier (IMAGE f1 (moi_s34_vb tt kk b))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "fa" SUBST1_TAC THEN
      MATCH_MP_TAC(SET_RULE `!a b u:real^3->bool. b SUBSET u ==> b SUBSET a UNION u`) THEN
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN
      DISCH_TAC THEN
      EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk a INTER moi_s34_vb tt kk b)` THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `b:real^N` THEN ASM_REWRITE_TAC[];
      USE_THEN "fb" SUBST1_TAC THEN
      MATCH_MP_TAC(SET_RULE `!a b u:real^3->bool. b SUBSET u ==> b SUBSET a UNION u`) THEN
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN
      DISCH_TAC THEN
      EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk b INTER moi_s34_vb tt kk a)` THEN
      CONJ_TAC THENL
       [EXISTS_TAC `a:real^N` THEN ONCE_REWRITE_TAC[SEGMENT_SYM] THEN ASM_REWRITE_TAC[];
        ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  REMOVE_THEN "fa" (K ALL_TAC) THEN REMOVE_THEN "fb" (K ALL_TAC) THEN
  SUBGOAL_THEN `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk a) INTER
                IMAGE f1 (moi_s34_vb tt kk b) =
                IMAGE f1 (moi_s34_vb tt kk a INTER moi_s34_vb tt kk b)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`] MOI_S4L_IMAGES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`moi_s34_vb tt kk (a:real^N)`;
                               `moi_s34_vb tt kk (b:real^N)`] o el 2 o CONJUNCTS) THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`]
      MOI_S4L_GRAPH_TUBE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `a:real^N` th) THEN MP_TAC(SPEC `b:real^N` th)) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[] THEN REPEAT DISCH_TAC THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk a)`;
                 `frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk a))`;
                 `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk b)`;
                 `frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk b))`;
                 `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk a INTER moi_s34_vb tt kk b)`;
                 `IMAGE (f1:real^N->real^3)
                    (moi_s34_vb tt kk a INTER moi_s34_vb tt kk b INTER moi_s34_bd tt kk)`]
    MOI_S5V_CELL_UNION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN USE_THEN "bc" MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`] MOI_S4L_AV_BASIC) THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `a:real^N` th) THEN MP_TAC(SPEC `b:real^N` th)) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [UNDISCH_TAC `pl_cell_with_boundary 3
      (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk a) UNION IMAGE f1 (moi_s34_vb tt kk b))
      ((frontier (IMAGE f1 (moi_s34_vb tt kk a)) UNION frontier (IMAGE f1 (moi_s34_vb tt kk b)))
       DIFF (IMAGE f1 (moi_s34_vb tt kk a INTER moi_s34_vb tt kk b) DIFF
             IMAGE f1 (moi_s34_vb tt kk a INTER moi_s34_vb tt kk b INTER moi_s34_bd tt kk)))` THEN
    REWRITE_TAC[pl_cell_with_boundary; pl_ball] THEN MESON_TAC[];
    UNDISCH_TAC `pl_cell_with_boundary 3
      (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk a) UNION IMAGE f1 (moi_s34_vb tt kk b))
      ((frontier (IMAGE f1 (moi_s34_vb tt kk a)) UNION frontier (IMAGE f1 (moi_s34_vb tt kk b)))
       DIFF (IMAGE f1 (moi_s34_vb tt kk a INTER moi_s34_vb tt kk b) DIFF
             IMAGE f1 (moi_s34_vb tt kk a INTER moi_s34_vb tt kk b INTER moi_s34_bd tt kk)))` THEN
    REWRITE_TAC[pl_cell_with_boundary] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
      (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_SCD_BALL_FRONTIER THEN
    EXISTS_TAC `g:real^3->real^3` THEN ASM_REWRITE_TAC[]]);;

(* The complement of the tube inside a carrier is open.                      *)

let MOI_S4VU_O_OPEN = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car q.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\ q IN kk /\ ~(q = {})
     ==> open (car q DIFF IMAGE f1 (moi_s34_nb tt kk))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open ((car:(real^N->bool)->real^3->bool) q)` ASSUME_TAC THENL
   [MP_TAC(SPEC `q:real^N->bool` (el 4 (CONJUNCTS (REWRITE_RULE[moi_s34_frame]
      (ASSUME `moi_s34_frame tt kk h ep (f1:real^N->real^3) car`))))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[OPEN_SUBOPEN] THEN X_GEN_TAC `x:real^3` THEN
  REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `x:real^3`] MOI_S4VU_LOCAL_BALLS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `(car:(real^N->bool)->real^3->bool) q` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `q:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `u INTER (car:(real^N->bool)->real^3->bool) q` THEN
  ASM_SIMP_TAC[OPEN_INTER; IN_INTER] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_DIFF] THEN X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`]
    MOI_S4L_GRAPH_TUBE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  SUBGOAL_THEN `?w:real^N. {w} IN kk /\ (z:real^3) IN IMAGE f1 (moi_s34_vb tt kk w)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_IMAGE; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^N` (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `t:real^N->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)))) THEN
    EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `p:real^N` THEN
    UNDISCH_TAC `(p:real^N) IN t` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `w:real^N` o check (is_forall o concl)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `~((x:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk))` THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `!a b (x:A). x IN a /\ a SUBSET b ==> x IN b`) THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `p:real^N` THEN
    DISCH_TAC THEN EXISTS_TAC `moi_s34_vb tt kk (w:real^N)` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(z:real^3) IN IMAGE f1 (moi_s34_vb tt kk (w:real^N))` THEN
  UNDISCH_TAC `(z:real^3) IN u` THEN SET_TAC[]);;

(* Points of the tube image are points of some vertex ball.                  *)

let MOI_S4VU_IN_TUBE = prove
 (`!(tt:(real^N->bool)->bool) kk (f1:real^N->real^3) z.
     moi_s34_tube tt kk
     ==> (z IN IMAGE f1 (moi_s34_nb tt kk) <=>
          ?w. {w} IN kk /\ z IN IMAGE f1 (moi_s34_vb tt kk w))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`]
    MOI_S4L_GRAPH_TUBE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o CONJUNCT1)] THEN
  REWRITE_TAC[IN_IMAGE; IN_UNIONS; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `p:real^N` (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `t:real^N->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)))) THEN
    EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `p:real^N` THEN
    UNDISCH_TAC `(p:real^N) IN t` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `w:real^N` (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `p:real^N` STRIP_ASSUME_TAC))) THEN
    EXISTS_TAC `p:real^N` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `moi_s34_vb tt kk (w:real^N)` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[]]);;

(* Local outer pieces at points of A_vi, vi a vertex of s:                   *)
(* near y only the vertex balls through y are present; their union B is a  *)
(* PL ball with y on its frontier; the local outside of frontier B           *)
(* (MOI_S4V_SPHERE_OUT_LOCAL) is a connected set outside the tube.           *)

let MOI_S4VU_LOCAL_PIECE = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car s vi y u.
     PL_SCHOENFLIES_3_AMBIENT_STATEMENT /\
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     s IN moi_s34_simp kk (&2) /\ {vi} IN kk /\ vi IN s /\
     y IN IMAGE f1 (moi_s34_vb tt kk vi INTER moi_s34_bd tt kk) /\ open u /\ y IN u
     ==> ?v cc. open v /\ y IN v /\ v SUBSET u /\ connected cc /\
                v DIFF IMAGE f1 (moi_s34_nb tt kk) SUBSET cc /\
                cc SUBSET u INTER (car s DIFF IMAGE f1 (moi_s34_nb tt kk))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  LABEL_TAC "fr" (REWRITE_RULE[moi_s34_frame]
    (ASSUME `moi_s34_frame tt kk h ep (f1:real^N->real^3) car`)) THEN
  SUBGOAL_THEN `(s:real^N->bool) IN kk /\ ~(s = {})` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(s:real^N->bool) IN moi_s34_simp kk (&2)` THEN
    REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN UNDISCH_TAC `aff_dim(s:real^N->bool) = &2` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN IMAGE f1 (moi_s34_vb tt kk (vi:real^N))` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN IMAGE (f1:real^N->real^3)
                   (moi_s34_vb tt kk vi INTER moi_s34_bd tt kk)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN (car:(real^N->bool)->real^3->bool) {vi}` ASSUME_TAC THENL
   [USE_THEN "fr" (MP_TAC o SPEC `vi:real^N` o el 6 o CONJUNCTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
    UNDISCH_TAC `(y:real^3) IN IMAGE f1 (moi_s34_vb tt kk (vi:real^N))` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(car:(real^N->bool)->real^3->bool) {vi} SUBSET car s /\ open (car s)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "fr" (MP_TAC o SPECL [`{vi:real^N}`; `s:real^N->bool`] o el 5 o CONJUNCTS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[NOT_INSERT_EMPTY; SING_SUBSET]; SIMP_TAC[]];
      USE_THEN "fr" (MP_TAC o SPEC `s:real^N->bool` o el 4 o CONJUNCTS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `y:real^3`] MOI_S4VU_LOCAL_BALLS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `(car:(real^N->bool)->real^3->bool) {vi}` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `{vi:real^N}` THEN ASM_REWRITE_TAC[NOT_INSERT_EMPTY];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?B. pl_ball 3 B /\ y IN frontier B /\ B SUBSET IMAGE f1 (moi_s34_nb tt kk) /\
        (!w:real^N. {w} IN kk /\ (y:real^3) IN IMAGE f1 (moi_s34_vb tt kk w)
                    ==> IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w) SUBSET B)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `vi:real^N`] MOI_S4L_SIGMA) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "fvi") (K ALL_TAC))) THEN
    SUBGOAL_THEN `(y:real^3) IN frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk vi))`
    ASSUME_TAC THENL
     [USE_THEN "fvi" SUBST1_TAC THEN
      UNDISCH_TAC `(y:real^3) IN IMAGE (f1:real^N->real^3)
                     (moi_s34_vb tt kk vi INTER moi_s34_bd tt kk)` THEN SET_TAC[];
      ALL_TAC] THEN
    REMOVE_THEN "fvi" (K ALL_TAC) THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`]
      MOI_S4L_GRAPH_TUBE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(LABEL_TAC "vbn" o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    SUBGOAL_THEN `!w:real^N. {w} IN kk
                    ==> IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w) SUBSET
                        IMAGE f1 (moi_s34_nb tt kk)` (LABEL_TAC "vbi") THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      USE_THEN "vbn" (MP_TAC o SPEC `w:real^N`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      ALL_TAC] THEN
    ASM_CASES_TAC `?x:real^N. {x} IN kk /\ ~(x = vi) /\
                              (y:real^3) IN IMAGE f1 (moi_s34_vb tt kk x)` THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                     `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                     `car:(real^N->bool)->real^3->bool`; `vi:real^N`; `x:real^N`;
                     `y:real^3`] MOI_S4L_AV_NO_OTHER) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                     `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                     `car:(real^N->bool)->real^3->bool`; `vi:real^N`; `x:real^N`]
        MOI_S4VU_TWO_BALLS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk vi) UNION
                  IMAGE f1 (moi_s34_vb tt kk x)` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `(y:real^3) IN IMAGE (f1:real^N->real^3)
                       (moi_s34_vb tt kk vi INTER moi_s34_vb tt kk x INTER
                        moi_s34_bd tt kk)` THEN
        UNDISCH_TAC `(y:real^3) IN frontier (IMAGE (f1:real^N->real^3)
                                               (moi_s34_vb tt kk vi))` THEN
        SET_TAC[];
        MATCH_MP_TAC(SET_RULE `!a b c:real^3->bool. a SUBSET c /\ b SUBSET c
                                                    ==> a UNION b SUBSET c`) THEN
        CONJ_TAC THEN USE_THEN "vbi" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
        ASM_CASES_TAC `w:real^N = vi` THENL
         [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
        ASM_CASES_TAC `w:real^N = x` THENL
         [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
        MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                       `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                       `car:(real^N->bool)->real^3->bool`] MOI_S4L_IMAGES) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o SPECL [`vi:real^N`; `x:real^N`; `w:real^N`] o
                   el 3 o CONJUNCTS) THEN
        ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        UNDISCH_TAC `(y:real^3) IN IMAGE f1 (moi_s34_vb tt kk (vi:real^N))` THEN
        UNDISCH_TAC `(y:real^3) IN IMAGE f1 (moi_s34_vb tt kk (x:real^N))` THEN
        UNDISCH_TAC `(y:real^3) IN IMAGE f1 (moi_s34_vb tt kk (w:real^N))` THEN
        SET_TAC[]];
      EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk vi)` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                       `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                       `car:(real^N->bool)->real^3->bool`; `vi:real^N`] MOI_S4L_AV_BASIC) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
        USE_THEN "vbi" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
        ASM_CASES_TAC `w:real^N = vi` THENL
         [ASM_REWRITE_TAC[SUBSET_REFL]; ALL_TAC] THEN
        MATCH_MP_TAC(TAUT `F ==> p`) THEN
        UNDISCH_TAC `~(?x:real^N. {x} IN kk /\ ~(x = vi) /\
                              (y:real^3) IN IMAGE f1 (moi_s34_vb tt kk x))` THEN
        REWRITE_TAC[] THEN EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `B:real^3->bool` MOI_S4V_BALL_SIDES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`frontier B:real^3->bool`;
                 `u INTER u1 INTER (car:(real^N->bool)->real^3->bool) s`;
                 `y:real^3`] MOI_S4V_SPHERE_OUT_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[OPEN_INTER; IN_INTER] THEN
    UNDISCH_TAC `(car:(real^N->bool)->real^3->bool) {vi} SUBSET car s` THEN
    UNDISCH_TAC `(y:real^3) IN (car:(real^N->bool)->real^3->bool) {vi}` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^3->bool` (X_CHOOSE_THEN `cc:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(u INTER u1 INTER (car:(real^N->bool)->real^3->bool) s) INTER
                IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk) SUBSET B`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `f1:real^N->real^3`; `z:real^3`] MOI_S4VU_IN_TUBE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `(y:real^3) IN IMAGE f1 (moi_s34_vb tt kk (w:real^N))` THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `w:real^N` o check (fun th ->
        try fst(dest_var(fst(dest_forall(concl th)))) = "w" &&
            can (find_term (fun t -> t = `B:real^3->bool`)) (concl th)
        with Failure _ -> false)) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(z:real^3) IN IMAGE f1 (moi_s34_vb tt kk (w:real^N))` THEN SET_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `w:real^N` o check (fun th ->
        try fst(dest_var(fst(dest_forall(concl th)))) = "w" &&
            can (find_term (fun t -> t = `u1:real^3->bool`)) (concl th)
        with Failure _ -> false)) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(z:real^3) IN IMAGE f1 (moi_s34_vb tt kk (w:real^N))` THEN
      UNDISCH_TAC `(z:real^3) IN u1` THEN SET_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `cc:real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `v SUBSET u INTER u1 INTER (car:(real^N->bool)->real^3->bool) s` THEN
    SET_TAC[];
    UNDISCH_TAC `v INTER ((:real^3) DIFF B) SUBSET cc` THEN
    UNDISCH_TAC `B SUBSET IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)` THEN SET_TAC[];
    UNDISCH_TAC `cc SUBSET (u INTER u1 INTER (car:(real^N->bool)->real^3->bool) s) INTER
                           ((:real^3) DIFF B)` THEN
    UNDISCH_TAC `(u INTER u1 INTER (car:(real^N->bool)->real^3->bool) s) INTER
                 IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk) SUBSET B` THEN
    SET_TAC[]]);;

(* PL 2-spheres are connected (images of relative frontiers of 3-simplices). *)

let MOI_S4VU_SPHERE2_CONNECTED = prove
 (`!s:real^N->bool. pl_sphere 2 s ==> connected s`,
  GEN_TAC THEN REWRITE_TAC[pl_sphere; pl_homeomorphism; homeomorphism] THEN
  NUM_REDUCE_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    try rand(concl th) = `s:real^N->bool` with Failure _ -> false)) THEN
  MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONNECTED_SPHERE_GEN THEN
  ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT; COMPACT_IMP_BOUNDED;
                AFF_DIM_SIMPLEX; INT_ARITH `~(&3:int = &1)`]);;

(* A_u = frontier T_u minus the open splitting disks at u is connected       *)
(* (MOI_S4VU_HOLES_CONNECTED on the PL sphere frontier T_u, MOI_S4L_SIGMA). *)

let MOI_S4VU_AV_CONNECTED = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car u.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\ {u} IN kk
     ==> connected (IMAGE f1 (moi_s34_vb tt kk u INTER moi_s34_bd tt kk))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `u:real^N`] MOI_S4L_SIGMA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "dk") (LABEL_TAC "dj")))) THEN
  MATCH_MP_TAC MOI_S4VU_HOLES_CONNECTED THEN
  MAP_EVERY EXISTS_TAC
   [`frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u))`;
    `{IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u INTER moi_s34_vb tt kk w) | w |
      ~(w = u) /\ segment[u,w] IN kk}`;
    `\D:real^3->bool. D INTER IMAGE (f1:real^N->real^3)
                                (moi_s34_vb tt kk u INTER moi_s34_bd tt kk)`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S4VU_SPHERE2_CONNECTED THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `u:real^N`] MOI_S4L_AV_BASIC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `skeleton 1 (kk:(real^N->bool)->bool)`;
                   `u:real^N`] MOI_S5H_NBRS_FINITE) THEN
    REWRITE_TAC[MOI_S4L_SKEL_VERTEX; MOI_S4L_SKEL_SEGMENT] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`]
      MOI_S4L_TUBE_TUBE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ASM_REWRITE_TAC[];
    REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
    USE_THEN "dk" (MP_TAC o SPEC `w:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_PL_CELL2_TOPO o
      check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
                           "pl_cell_with_boundary" with Failure _ -> false)) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SLV_CIRCLE_CLOSED o
      MATCH_MP (REWRITE_RULE[ARITH_RULE `1 + 1 = 2`] (SPEC `1` MOI_S4O_CELL_SPHERE)) o
      check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
                           "pl_cell_with_boundary" with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC COMPACT_IMP_CLOSED THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN X_GEN_TAC `w:real^N` THEN
    REPEAT DISCH_TAC THEN X_GEN_TAC `w':real^N` THEN REPEAT DISCH_TAC THEN
    ASM_CASES_TAC `w':real^N = w` THENL
     [FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "dj" (MP_TAC o SPECL [`w:real^N`; `w':real^N`]) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[DISJOINT]]);;

(* Theta' = A_a UNION A_b UNION A_c (a, b, c the vertices of s) is connected: *)
(* each A_u is, and adjacent ones share the rim of their splitting disk.      *)

let MOI_S4VU_THETA_CONNECTED = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car s.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\ s IN moi_s34_simp kk (&2)
     ==> connected (UNIONS {IMAGE f1 (moi_s34_vb tt kk u INTER moi_s34_bd tt kk) | u |
                            u IN s /\ {u} IN kk})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `s:real^N->bool`] MOI_S4L_TRI_FORM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    (X_CHOOSE_THEN `c:real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `s = convex hull {a:real^N,b,c}`)) THEN
  SUBGOAL_THEN
   `UNIONS {IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u INTER moi_s34_bd tt kk) | u |
            u IN s /\ {u} IN kk} =
    (IMAGE f1 (moi_s34_vb tt kk a INTER moi_s34_bd tt kk) UNION
     IMAGE f1 (moi_s34_vb tt kk b INTER moi_s34_bd tt kk)) UNION
    IMAGE f1 (moi_s34_vb tt kk c INTER moi_s34_bd tt kk)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
      SUBGOAL_THEN `(u:real^N) IN {a,b,c}` MP_TAC THENL
       [UNDISCH_TAC `{v | v IN s /\ {v} IN kk} = {a:real^N,b,c}` THEN
        REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
        DISCH_THEN(MP_TAC o SPEC `u:real^N`) THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; IN_UNION] THEN
      STRIP_TAC THEN UNDISCH_TAC `(z:real^3) IN t` THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC[];
      MATCH_MP_TAC(SET_RULE `!x y z w:real^3->bool.
        x SUBSET w /\ y SUBSET w /\ z SUBSET w ==> (x UNION y) UNION z SUBSET w`) THEN
      SUBGOAL_THEN `(a:real^N) IN s /\ (b:real^N) IN s /\ (c:real^N) IN s`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `{v | v IN s /\ {v} IN kk} = {a:real^N,b,c}` THEN
        REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[];
        ALL_TAC] THEN
      REPEAT CONJ_TAC THEN GEN_REWRITE_TAC I [SUBSET] THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THENL
       [EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk a INTER moi_s34_bd tt kk)` THEN
        ASM_REWRITE_TAC[] THEN EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[];
        EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk b INTER moi_s34_bd tt kk)` THEN
        ASM_REWRITE_TAC[] THEN EXISTS_TAC `b:real^N` THEN ASM_REWRITE_TAC[];
        EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk c INTER moi_s34_bd tt kk)` THEN
        ASM_REWRITE_TAC[] THEN EXISTS_TAC `c:real^N` THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y:real^N. {x} IN kk /\ ~(y = x) /\ segment[x,y] IN kk
                 ==> ~(IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk x INTER moi_s34_bd tt kk) INTER
                       IMAGE f1 (moi_s34_vb tt kk y INTER moi_s34_bd tt kk) = {})`
  (LABEL_TAC "meet") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `x:real^N`] MOI_S4L_SIGMA) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o
      CONJUNCT1 o CONJUNCT2 o MATCH_MP MOI_S4L_PL_CELL2_TOPO o CONJUNCT1)) THEN
    UNDISCH_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk x INTER moi_s34_bd tt kk) INTER
                 IMAGE f1 (moi_s34_vb tt kk y INTER moi_s34_bd tt kk) = {}` THEN
    MP_TAC(ISPECL [`f1:real^N->real^3`;
                   `moi_s34_vb tt kk (x:real^N) INTER moi_s34_vb tt kk y INTER
                    moi_s34_bd tt kk`;
                   `moi_s34_vb tt kk (x:real^N) INTER moi_s34_bd tt kk`] IMAGE_SUBSET) THEN
    MP_TAC(ISPECL [`f1:real^N->real^3`;
                   `moi_s34_vb tt kk (x:real^N) INTER moi_s34_vb tt kk y INTER
                    moi_s34_bd tt kk`;
                   `moi_s34_vb tt kk (y:real^N) INTER moi_s34_bd tt kk`] IMAGE_SUBSET) THEN
    REWRITE_TAC[SET_RULE `(a:A->bool) INTER b INTER c SUBSET a INTER c`;
                SET_RULE `(a:A->bool) INTER b INTER c SUBSET b INTER c`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^N. {x} IN kk
                  ==> connected (IMAGE (f1:real^N->real^3)
                                   (moi_s34_vb tt kk x INTER moi_s34_bd tt kk))`
  (LABEL_TAC "ac") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S4VU_AV_CONNECTED THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`;
                          `car:(real^N->bool)->real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_UNION THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_UNION THEN REPEAT CONJ_TAC THENL
     [USE_THEN "ac" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "ac" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "meet" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    USE_THEN "ac" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC(SET_RULE `!x y z:real^3->bool. ~(x INTER z = {})
                             ==> ~((x UNION y) INTER z = {})`) THEN
    USE_THEN "meet" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The outer route, part 2: points of Bd N are limits of points outside the *)
(* tube; the face torus lies in the ball W = cb s UNION q once Theta' does; *)
(* the route itself.                                                         *)
(* ------------------------------------------------------------------------- *)

let MOI_S4VU_NOT_INT_TUBE = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car y v.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     y IN IMAGE f1 (moi_s34_bd tt kk) /\ open v /\ y IN v
     ==> ~(v DIFF IMAGE f1 (moi_s34_nb tt kk) = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`] MOI_S4L_FRAME_F1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
  REWRITE_TAC[SET_RULE `(v:A->bool) DIFF s = {} <=> v SUBSET s`] THEN
  REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)`; `v:real^3->bool`]
    INTERIOR_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) INTER
               interior (IMAGE f1 (moi_s34_nb tt kk)) = {}` THEN
  UNDISCH_TAC `(y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)` THEN
  UNDISCH_TAC `(y:real^3) IN v` THEN SET_TAC[]);;

(* If Theta' lies in W = cb s UNION q, so does the face torus: the foreign   *)
(* splitting disks miss frontier W = d UNION e' and their rims lie in W, so *)
(* frontier T SUBSET W; the outside of W is connected and unbounded.        *)

let MOI_S4VU_T_IN_W = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v d j q e e'.
     moi_s34_tube tt kk /\ moi_s34_emb h (UNIONS tt) /\
     moi_s34_frame tt kk h ep f1 car /\ moi_s34_fbinv tt kk h f1 car cb /\
     s IN moi_s34_simp kk (&2) /\
     moi_s34_op1w tt kk f1 cb s v d j /\ DISJOINT (d DIFF j) (cb s) /\
     moi_s4v_pocket (cb s) d j q e e' /\
     UNIONS {IMAGE f1 (moi_s34_vb tt kk u INTER moi_s34_bd tt kk) | u |
             u IN s /\ {u} IN kk} SUBSET cb s UNION q
     ==> IMAGE f1 (moi_s34_ft tt kk s) SUBSET cb s UNION q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`;
                 `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`;
                 `v:real^N`; `d:real^3->bool`; `j:real^3->bool`] MOI_S4V_SETUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_s4v_pocket] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "moi_s4v_pocket"
                     with Failure _ -> false)) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`;
                 `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`]
    MOI_S4L_TRACE_COMP_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `s:real^N->bool`] MOI_S4J_T_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  SUBGOAL_THEN `frontier (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)) SUBSET ((cb:(real^N->bool)->real^3->bool) s UNION q)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s))` ASSUME_TAC THENL
     [MP_TAC(ISPEC `(IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)):real^3->bool` FRONTIER_SUBSET_CLOSED) THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
      UNDISCH_TAC `(x:real^3) IN frontier (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s))` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `?u:real^N. u IN s /\ {u} IN kk /\
                             (x:real^3) IN IMAGE f1 (moi_s34_vb tt kk u)`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s))` THEN ALL_TAC THEN
      REWRITE_TAC[moi_s34_ft; IN_IMAGE; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`]
      MOI_S4L_GRAPH_TUBE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> LABEL_TAC "bdn" (CONJUNCT1(CONJUNCT2 th)) THEN
                         LABEL_TAC "vbn" (CONJUNCT1(CONJUNCT2(CONJUNCT2 th)))) THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`] MOI_S4L_IMAGES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> LABEL_TAC "nadj" (el 1 (CONJUNCTS th)) THEN
                         LABEL_TAC "imi" (el 2 (CONJUNCTS th))) THEN
    SUBGOAL_THEN `!w:real^N. {w} IN kk
                    ==> moi_s34_vb tt kk w SUBSET moi_s34_nb tt kk` (LABEL_TAC "vbs") THENL
     [REPEAT STRIP_TAC THEN USE_THEN "vbn" (MP_TAC o SPEC `w:real^N`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      ALL_TAC] THEN
    ASM_CASES_TAC `(x:real^3) IN IMAGE f1 (moi_s34_bd (tt:(real^N->bool)->bool) kk)` THENL
     [ALL_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
        `!a b (x:real^3). a SUBSET b ==> x IN a ==> x IN b`) o check (fun th ->
        try fst(dest_const(fst(strip_comb(rand(rator(concl th)))))) = "UNIONS"
        with Failure _ -> false)) THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u INTER moi_s34_bd tt kk)` THEN
      CONJ_TAC THENL [EXISTS_TAC `u:real^N` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "imi" (MP_TAC o SPECL [`moi_s34_vb tt kk (u:real^N)`;
                                      `moi_s34_bd (tt:(real^N->bool)->bool) kk`]) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL [USE_THEN "vbs" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
                        USE_THEN "bdn" ACCEPT_TAC];
        DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[IN_INTER]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^3) IN interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk))`
    ASSUME_TAC THENL
     [MP_TAC(el 3 (CONJUNCTS (REWRITE_RULE[moi_s34_frame]
        (ASSUME `moi_s34_frame tt kk h ep (f1:real^N->real^3) car`)))) THEN
      SUBGOAL_THEN `(x:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)` MP_TAC THENL
       [MATCH_MP_TAC(SET_RULE `!a b (z:A). z IN a /\ a SUBSET b ==> z IN b`) THEN
        EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u)` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
        USE_THEN "vbs" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `~((x:real^3) IN IMAGE f1 (moi_s34_bd (tt:(real^N->bool)->bool) kk))` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^3) IN (car:(real^N->bool)->real^3->bool) {u}` ASSUME_TAC THENL
     [MP_TAC(SPEC `u:real^N` (el 6 (CONJUNCTS (REWRITE_RULE[moi_s34_frame]
        (ASSUME `moi_s34_frame tt kk h ep (f1:real^N->real^3) car`))))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
      UNDISCH_TAC `(x:real^3) IN IMAGE f1 (moi_s34_vb tt kk (u:real^N))` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `x:real^3`] MOI_S4VU_LOCAL_BALLS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      EXISTS_TAC `(car:(real^N->bool)->real^3->bool) {u}` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `{u:real^N}` THEN ASM_REWRITE_TAC[NOT_INSERT_EMPTY];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u1:real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lb")))) THEN
    SUBGOAL_THEN `?p. p IN u1 /\
                      p IN interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)) /\
                      ~(p IN (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)))` STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      SUBGOAL_THEN `u1 INTER interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk))
                    SUBSET interior (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s))` MP_TAC THENL
       [MATCH_MP_TAC INTERIOR_MAXIMAL THEN ASM_SIMP_TAC[OPEN_INTER; OPEN_INTERIOR] THEN
        UNDISCH_TAC `~(?p. p IN u1 /\
                           p IN interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)) /\
                           ~(p IN (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s))))` THEN SET_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPEC `(IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)):real^3->bool` frontier) THEN
      UNDISCH_TAC `(x:real^3) IN frontier (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s))` THEN
      UNDISCH_TAC `(x:real^3) IN u1` THEN
      UNDISCH_TAC `(x:real^3) IN interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk))` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `?w:real^N. {w} IN kk /\ (p:real^3) IN IMAGE f1 (moi_s34_vb tt kk w)`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                     `f1:real^N->real^3`; `p:real^3`] MOI_S4VU_IN_TUBE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MP_TAC(ISPEC `IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(p:real^3) IN interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk))` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((w:real^N) IN s)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~((p:real^3) IN (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)))` THEN REWRITE_TAC[] THEN
      REWRITE_TAC[moi_s34_ft] THEN
      UNDISCH_TAC `(p:real^3) IN IMAGE f1 (moi_s34_vb tt kk (w:real^N))` THEN
      REWRITE_TAC[IN_IMAGE; IN_UNIONS; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `z:real^N` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `moi_s34_vb tt kk (w:real^N)` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^3) IN IMAGE f1 (moi_s34_vb tt kk (w:real^N))` ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      USE_THEN "lb" (MP_TAC o SPEC `w:real^N`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(p:real^3) IN IMAGE f1 (moi_s34_vb tt kk (w:real^N))` THEN
      UNDISCH_TAC `(p:real^3) IN u1` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(u:real^N = w)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~((w:real^N) IN s)` THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `segment[u:real^N,w] IN kk` ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      USE_THEN "nadj" (MP_TAC o SPECL [`u:real^N`; `w:real^N`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(x:real^3) IN IMAGE f1 (moi_s34_vb tt kk (w:real^N))` THEN
      UNDISCH_TAC `(x:real^3) IN IMAGE f1 (moi_s34_vb tt kk (u:real^N))` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `u:real^N`] MOI_S4L_SIGMA) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `w:real^N` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `(x:real^3) IN
                  IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u INTER moi_s34_vb tt kk w)`
    MP_TAC THENL
     [USE_THEN "imi" (MP_TAC o SPECL [`moi_s34_vb tt kk (u:real^N)`;
                                      `moi_s34_vb tt kk (w:real^N)`]) THEN
      ANTS_TAC THENL
       [CONJ_TAC THEN USE_THEN "vbs" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[IN_INTER]];
      ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `!a b (x:real^3). a SUBSET b ==> x IN a ==> x IN b`) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_PL_CELL2_TOPO o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "pl_cell_with_boundary"
      with Failure _ -> false)) THEN
    MP_TAC(ISPECL [`IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u INTER moi_s34_vb tt kk w)`;
                   `(cb:(real^N->bool)->real^3->bool) s UNION q`] CONNECTED_INTER_FRONTIER) THEN
    REWRITE_TAC[MATCH_MP PATH_CONNECTED_IMP_CONNECTED (ASSUME
      `path_connected (IMAGE (f1:real^N->real^3)
                         (moi_s34_vb tt kk u INTER moi_s34_vb tt kk w))`)] THEN
    REWRITE_TAC[SET_RULE `(s:real^3->bool) DIFF t = {} <=> s SUBSET t`] THEN
    MATCH_MP_TAC(TAUT `p /\ q ==> (p /\ ~r ==> ~q) ==> r`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!rim d w:real^3->bool. ~(rim = {}) /\ rim SUBSET d /\
                              rim SUBSET w ==> ~(d INTER w = {})`) THEN
      EXISTS_TAC `IMAGE (f1:real^N->real^3)
                    (moi_s34_vb tt kk u INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)` THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
        `!a b c:real^3->bool. a SUBSET b ==> c SUBSET a ==> c SUBSET b`) o check (fun th ->
        try fst(dest_const(fst(strip_comb(rand(rator(concl th)))))) = "UNIONS"
        with Failure _ -> false)) THEN
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN
      DISCH_TAC THEN
      EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u INTER moi_s34_bd tt kk)` THEN
      CONJ_TAC THENL [EXISTS_TAC `u:real^N` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(z:real^3) IN IMAGE (f1:real^N->real^3)
                     (moi_s34_vb tt kk u INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)` THEN
      SET_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(SUBST1_TAC o check (fun th ->
      try lhs(concl th) = `frontier ((cb:(real^N->bool)->real^3->bool) s UNION q)`
      with Failure _ -> false)) THEN
    SUBGOAL_THEN `DISJOINT ((cb:(real^N->bool)->real^3->bool) s)
                           (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w))` ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPEC `w:real^N` o el 3 o CONJUNCTS o REWRITE_RULE[moi_s34_fb1] o
        check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "moi_s34_fb1"
                         with Failure _ -> false)) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^N` o check (fun th ->
      try let v,bd = dest_forall(concl th) in fst(dest_var v) = "w" &&
              can (find_term (fun t -> t = `d:real^3->bool`)) bd &&
              can (find_term (fun t -> try fst(dest_const t) = "DISJOINT"
                                       with Failure _ -> false)) bd
      with Failure _ -> false)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `DISJOINT ((cb:(real^N->bool)->real^3->bool) s)
                          (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w))` THEN
    UNDISCH_TAC `e UNION e' = frontier ((cb:(real^N->bool)->real^3->bool) s)` THEN
    UNDISCH_TAC `frontier ((cb:(real^N->bool)->real^3->bool) s) SUBSET cb s` THEN
    MP_TAC(ISPECL [`f1:real^N->real^3`;
                   `moi_s34_vb tt kk (u:real^N) INTER moi_s34_vb tt kk w`;
                   `moi_s34_vb tt kk (w:real^N)`] IMAGE_SUBSET) THEN
    REWRITE_TAC[INTER_SUBSET] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `((cb:(real^N->bool)->real^3->bool) s UNION q):real^3->bool` MOI_S4V_BALL_SIDES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`frontier (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s))`; `(:real^3) DIFF ((cb:(real^N->bool)->real^3->bool) s UNION q)`]
    MOI_S4V_UNBOUNDED_OUTSIDE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `(IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)):real^3->bool` THEN
      ASM_SIMP_TAC[COMPACT_IMP_BOUNDED; FRONTIER_SUBSET_CLOSED; COMPACT_IMP_CLOSED];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        try lhs(concl th) = `outside (frontier ((cb:(real^N->bool)->real^3->bool) s UNION q))` with Failure _ -> false)) THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        try lhs(concl th) = `outside (frontier ((cb:(real^N->bool)->real^3->bool) s UNION q))` with Failure _ -> false)) THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `frontier (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)) SUBSET ((cb:(real^N->bool)->real^3->bool) s UNION q)` THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `(IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)):real^3->bool` OUTSIDE_FRONTIER_MISSES_CLOSURE) THEN
  ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN
  MP_TAC(ISPEC `(IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)):real^3->bool` CLOSURE_SUBSET) THEN SET_TAC[]);;

(* Points of Theta' all have neighbourhoods whose part outside the tube lies *)
(* in one component of car s DIFF f1(N) (open-closed argument on Theta').    *)

let MOI_S4VU_COMPONENT_CLAIM = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car s p0 y0 v0.
     PL_SCHOENFLIES_3_AMBIENT_STATEMENT /\
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     s IN moi_s34_simp kk (&2) /\
     y0 IN UNIONS {IMAGE f1 (moi_s34_vb tt kk u INTER moi_s34_bd tt kk) | u |
                   u IN s /\ {u} IN kk} /\
     open v0 /\ y0 IN v0 /\
     v0 DIFF IMAGE f1 (moi_s34_nb tt kk) SUBSET
     connected_component (car s DIFF IMAGE f1 (moi_s34_nb tt kk)) p0
     ==> !y. y IN UNIONS {IMAGE f1 (moi_s34_vb tt kk u INTER moi_s34_bd tt kk) | u |
                          u IN s /\ {u} IN kk}
             ==> ?w. open w /\ y IN w /\
                     w DIFF IMAGE f1 (moi_s34_nb tt kk) SUBSET
                     connected_component (car s DIFF IMAGE f1 (moi_s34_nb tt kk)) p0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!y. y IN UNIONS {IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u INTER moi_s34_bd tt kk) | u |
                     u IN s /\ {u} IN kk}
        ==> ?u. u IN s /\ {u} IN kk /\
                y IN IMAGE f1 (moi_s34_vb tt kk u INTER moi_s34_bd tt kk)`
  (LABEL_TAC "vx") THENL
   [GEN_TAC THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!(z:real^3) w. z IN IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) /\
                         open w /\ z IN w
                         ==> ~(w DIFF IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk) = {})`
  (LABEL_TAC "nit") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `z:real^3`; `w:real^3->bool`]
      MOI_S4VU_NOT_INT_TUBE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!cc z:real^3. connected cc /\
                  cc SUBSET (car:(real^N->bool)->real^3->bool) s DIFF
                            IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk) /\
                  z IN cc /\
                  z IN connected_component (car s DIFF IMAGE f1 (moi_s34_nb tt kk)) p0
                  ==> cc SUBSET
                      connected_component (car s DIFF IMAGE f1 (moi_s34_nb tt kk)) p0`
  (LABEL_TAC "cmp") THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP CONNECTED_COMPONENT_EQ o check (fun th ->
      try fst(dest_const(fst(strip_comb(rand(concl th))))) = "connected_component"
      with Failure _ -> false)) THEN
    MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `s:real^N->bool`]
    MOI_S4VU_THETA_CONNECTED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[CONNECTED_CLOPEN] THEN
  DISCH_THEN(MP_TAC o SPEC
   `{y | y IN UNIONS {IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u INTER moi_s34_bd tt kk) |
                      u | u IN s /\ {u} IN kk} /\
         ?w. open w /\ y IN w /\
             w DIFF IMAGE f1 (moi_s34_nb tt kk) SUBSET
             connected_component ((car:(real^N->bool)->real^3->bool) s DIFF
                                  IMAGE f1 (moi_s34_nb tt kk)) p0}`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [GEN_REWRITE_TAC I [OPEN_IN_SUBOPEN] THEN REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `y:real^3` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `w:real^3->bool`
        STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `UNIONS {IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u INTER moi_s34_bd tt kk) |
                         u | u IN s /\ {u} IN kk} INTER w` THEN
      ASM_SIMP_TAC[OPEN_IN_OPEN_INTER; IN_INTER] THEN
      GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
      X_GEN_TAC `z:real^3` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `w:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[closed_in; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN CONJ_TAC THENL
       [SET_TAC[]; ALL_TAC] THEN
      GEN_REWRITE_TAC I [OPEN_IN_SUBOPEN] THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN
      X_GEN_TAC `y:real^3` THEN
      STRIP_TAC THEN
      USE_THEN "vx" (MP_TAC o SPEC `y:real^3`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                     `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                     `car:(real^N->bool)->real^3->bool`; `s:real^N->bool`; `u:real^N`;
                     `y:real^3`; `(:real^3)`] MOI_S4VU_LOCAL_PIECE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `v:real^3->bool` (X_CHOOSE_THEN `cc:real^3->bool`
        STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `UNIONS {IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u INTER moi_s34_bd tt kk) |
                         u | u IN s /\ {u} IN kk} INTER v` THEN
      ASM_SIMP_TAC[OPEN_IN_OPEN_INTER; IN_INTER] THEN
      GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_INTER; IN_DIFF; IN_ELIM_THM] THEN
      X_GEN_TAC `z:real^3` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `w':real^3->bool` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) &&
        free_in `y:real^3` (concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "connected_component"
                                 with Failure _ -> false)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `v:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cc:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "vx" (MP_TAC o SPEC `z:real^3`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `u':real^N` STRIP_ASSUME_TAC) THEN
      USE_THEN "nit" (MP_TAC o SPECL [`z:real^3`; `v INTER w':real^3->bool`]) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[OPEN_INTER; IN_INTER] THEN
        UNDISCH_TAC `(z:real^3) IN IMAGE (f1:real^N->real^3)
                       (moi_s34_vb tt kk u' INTER moi_s34_bd tt kk)` THEN SET_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_DIFF; IN_INTER] THEN
      DISCH_THEN(X_CHOOSE_THEN `pz:real^3` STRIP_ASSUME_TAC) THEN
      USE_THEN "cmp" MATCH_MP_TAC THEN EXISTS_TAC `pz:real^3` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `cc SUBSET (:real^3) INTER
                     ((car:(real^N->bool)->real^3->bool) s DIFF
                      IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk))` THEN SET_TAC[];
        CONJ_TAC THENL
         [UNDISCH_TAC `v DIFF IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk) SUBSET cc` THEN
          ASM SET_TAC[];
          UNDISCH_TAC `w' DIFF IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk) SUBSET
                       connected_component ((car:(real^N->bool)->real^3->bool) s DIFF
                                            IMAGE f1 (moi_s34_nb tt kk)) p0` THEN
          ASM SET_TAC[]]]];
    ALL_TAC] THEN
  DISCH_THEN DISJ_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `{}:real^3->bool`)) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `y0:real^3`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
    EXISTS_TAC `v0:real^3->bool` THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
      (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "GSPEC"
       with Failure _ -> false))) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[]]);;

(* The exit point: the component C0 of the claim is not                      *)
(* inside W = cb s UNION q.  Either Theta' leaves W, or T SUBSET W, and then *)
(* the points of d (in frontier W) would be interior to W.                   *)

let MOI_S4VU_EXIT = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v d j q e e'
    (p0:real^3).
     moi_s34_tube tt kk /\ moi_s34_emb h (UNIONS tt) /\
     moi_s34_frame tt kk h ep f1 car /\ moi_s34_fbinv tt kk h f1 car cb /\
     s IN moi_s34_simp kk (&2) /\
     moi_s34_op1w tt kk f1 cb s v d j /\ DISJOINT (d DIFF j) (cb s) /\
     moi_s4v_pocket (cb s) d j q e e' /\
     (!y. y IN UNIONS {IMAGE f1 (moi_s34_vb tt kk u INTER moi_s34_bd tt kk) | u |
                       u IN s /\ {u} IN kk}
          ==> ?w. open w /\ y IN w /\
                  w DIFF IMAGE f1 (moi_s34_nb tt kk) SUBSET
                  connected_component (car s DIFF IMAGE f1 (moi_s34_nb tt kk)) p0)
     ==> ?p1. p1 IN connected_component (car s DIFF IMAGE f1 (moi_s34_nb tt kk)) p0 /\
              ~(p1 IN cb s UNION q)`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `C0 = connected_component ((car:(real^N->bool)->real^3->bool) s DIFF
                     IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)) p0` THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(LABEL_TAC "cl" o check (is_forall o concl)) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`;
                 `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`; `v:real^N`;
                 `d:real^3->bool`; `j:real^3->bool`] MOI_S4V_SETUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `pl_ball 3 ((cb:(real^N->bool)->real^3->bool) s UNION q) /\
                frontier ((cb:(real^N->bool)->real^3->bool) s UNION q) = d UNION e'`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s4v_pocket ((cb:(real^N->bool)->real^3->bool) s) d j q e e'` THEN
    REWRITE_TAC[moi_s4v_pocket] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed ((cb:(real^N->bool)->real^3->bool) s UNION q)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP MOI_S4L_PL_BALL_COMPACT) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `d SUBSET IMAGE (f1:real^N->real^3)
                  (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s34_op1w tt kk (f1:real^N->real^3) cb s v d j` THEN
    REWRITE_TAC[moi_s34_op1w] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?yd:real^3. yd IN d` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(C0 SUBSET (cb:(real^N->bool)->real^3->bool) s UNION q)` MP_TAC THENL
   [DISCH_TAC; SET_TAC[]] THEN
  ASM_CASES_TAC
   `UNIONS {IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u INTER moi_s34_bd tt kk) | u |
            u IN s /\ {u} IN kk} SUBSET (cb:(real^N->bool)->real^3->bool) s UNION q`
  THENL
   [ALL_TAC;
    SUBGOAL_THEN
     `?y1:real^3. y1 IN UNIONS {IMAGE (f1:real^N->real^3)
                                  (moi_s34_vb tt kk u INTER moi_s34_bd tt kk) | u |
                                u IN s /\ {u} IN kk} /\
                  ~(y1 IN (cb:(real^N->bool)->real^3->bool) s UNION q)`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!a b:real^3->bool. ~(a SUBSET b) ==> ?y. y IN a /\ ~(y IN b)`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "cl" (MP_TAC o SPEC `y1:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `w1:real^3->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `y1:real^3`;
                   `w1 DIFF ((cb:(real^N->bool)->real^3->bool) s UNION q)`]
      MOI_S4VU_NOT_INT_TUBE) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[OPEN_DIFF; IN_DIFF] THEN
      UNDISCH_TAC `(y1:real^3) IN UNIONS
         {IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u INTER moi_s34_bd tt kk) | u |
          u IN s /\ {u} IN kk}` THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
      UNDISCH_TAC `(y1:real^3) IN t` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      UNDISCH_TAC `w1 DIFF IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk) SUBSET C0` THEN
      UNDISCH_TAC `C0 SUBSET (cb:(real^N->bool)->real^3->bool) s UNION q` THEN
      SET_TAC[]]] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`;
                 `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`; `v:real^N`;
                 `d:real^3->bool`; `j:real^3->bool`; `q:real^3->bool`; `e:real^3->bool`;
                 `e':real^3->bool`] MOI_S4VU_T_IN_W) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `(yd:real^3) IN UNIONS {(car:(real^N->bool)->real^3->bool) q' | q' |
                                       q' IN kk /\ ~(q' = {})}` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `(car:(real^N->bool)->real^3->bool) {v}` THEN CONJ_TAC THENL
     [EXISTS_TAC `{v:real^N}` THEN ASM_REWRITE_TAC[NOT_INSERT_EMPTY]; ALL_TAC] THEN
    UNDISCH_TAC `moi_s34_frame tt kk h ep (f1:real^N->real^3) car` THEN
    REWRITE_TAC[moi_s34_frame] THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^N` o el 6 o CONJUNCTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `yd:real^3`] MOI_S4VU_LOCAL_BALLS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^3->bool` STRIP_ASSUME_TAC) THEN
  USE_THEN "cl" (MP_TAC o SPEC `yd:real^3`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
    CONJ_TAC THENL [EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[]; ASM SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `w0:real^3->bool` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `u1 INTER w0 SUBSET (cb:(real^N->bool)->real^3->bool) s UNION q`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    ASM_CASES_TAC `(z:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)` THENL
     [ALL_TAC;
      SUBGOAL_THEN `(z:real^3) IN C0` MP_TAC THENL
       [UNDISCH_TAC `w0 DIFF IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk) SUBSET C0` THEN
        REWRITE_TAC[SUBSET; IN_DIFF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `C0 SUBSET (cb:(real^N->bool)->real^3->bool) s UNION q` THEN
        REWRITE_TAC[SUBSET] THEN MESON_TAC[]]] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `f1:real^N->real^3`; `z:real^3`] MOI_S4VU_IN_TUBE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(yd:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w)`
    ASSUME_TAC THENL
     [ASM_CASES_TAC `(yd:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w)` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `!w. {w} IN kk /\
                       ~((yd:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w))
                       ==> DISJOINT u1 (IMAGE f1 (moi_s34_vb tt kk w))` THEN
      DISCH_THEN(MP_TAC o SPEC `w:real^N`) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(z:real^3) IN u1` THEN
      UNDISCH_TAC `(z:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w)` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(w:real^N) IN s` ASSUME_TAC THENL
     [ASM_CASES_TAC `(w:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `!w. {w} IN kk /\ ~(w IN s)
                       ==> DISJOINT d (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w))` THEN
      DISCH_THEN(MP_TAC o SPEC `w:real^N`) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(yd:real^3) IN d` THEN
      UNDISCH_TAC `(yd:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w)` THEN
      SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s) SUBSET
                 (cb:(real^N->bool)->real^3->bool) s UNION q` THEN
    MATCH_MP_TAC(SET_RULE `!a b c x:real^3. x IN a /\ a SUBSET b ==> b SUBSET c ==> x IN c`) THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[moi_s34_ft] THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    EXISTS_TAC `moi_s34_vb tt kk (w:real^N)` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(yd:real^3) IN interior((cb:(real^N->bool)->real^3->bool) s UNION q)`
  MP_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!x t u:real^3->bool. x IN t /\ t SUBSET u ==> x IN u`) THEN
    EXISTS_TAC `u1 INTER w0:real^3->bool` THEN ASM_REWRITE_TAC[IN_INTER] THEN
    MATCH_MP_TAC INTERIOR_MAXIMAL THEN ASM_SIMP_TAC[OPEN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN `(yd:real^3) IN frontier((cb:(real^N->bool)->real^3->bool) s UNION q)`
  MP_TAC THENL
   [ASM_REWRITE_TAC[IN_UNION]; REWRITE_TAC[frontier; IN_DIFF] THEN MESON_TAC[]]);;

(* The route: a path outside the tube and inside car s                       *)
(* from a point of int q to a point outside W = cb s UNION q.                *)

let MOI_S4VU_ROUTE = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v d j q e e'.
     PL_SCHOENFLIES_3_AMBIENT_STATEMENT /\
     moi_s34_tube tt kk /\ moi_s34_emb h (UNIONS tt) /\
     moi_s34_frame tt kk h ep f1 car /\ moi_s34_fbinv tt kk h f1 car cb /\
     s IN moi_s34_simp kk (&2) /\
     moi_s34_op1w tt kk f1 cb s v d j /\ DISJOINT (d DIFF j) (cb s) /\
     moi_s4v_pocket (cb s) d j q e e' /\ ~moi_s4v_clean tt kk f1 s q
     ==> ?p0 p1 g. p0 IN interior q /\ ~(p1 IN cb s UNION q) /\
                   path g /\ pathstart g = p0 /\ pathfinish g = p1 /\
                   path_image g SUBSET car s DIFF IMAGE f1 (moi_s34_nb tt kk)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(s:real^N->bool) IN kk /\ ~(s = {})` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(s:real^N->bool) IN moi_s34_simp kk (&2)` THEN
    REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN UNDISCH_TAC `aff_dim(s:real^N->bool) = &2` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `s:real^N->bool`] MOI_S4VU_O_OPEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`;
                 `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`; `v:real^N`;
                 `d:real^3->bool`; `j:real^3->bool`; `q:real^3->bool`; `e:real^3->bool`;
                 `e':real^3->bool`] MOI_S4VU_UNCLEAN_POINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u0:real^N` (X_CHOOSE_THEN `y0:real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `s:real^N->bool`; `u0:real^N`;
                 `y0:real^3`; `interior q:real^3->bool`] MOI_S4VU_LOCAL_PIECE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[OPEN_INTERIOR]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v0:real^3->bool` (X_CHOOSE_THEN `cc0:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `?p0. p0 IN v0 /\ ~(p0 IN IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `y0:real^3`; `v0:real^3->bool`]
      MOI_S4VU_NOT_INT_TUBE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y0:real^3) IN IMAGE (f1:real^N->real^3)
                     (moi_s34_vb tt kk u0 INTER moi_s34_bd tt kk)` THEN SET_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p0:real^3) IN cc0` ASSUME_TAC THENL
   [UNDISCH_TAC `v0 DIFF IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk) SUBSET cc0` THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `cc0 SUBSET connected_component
                  ((car:(real^N->bool)->real^3->bool) s DIFF
                   IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)) p0` ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `cc0 SUBSET interior q INTER
                 ((car:(real^N->bool)->real^3->bool) s DIFF
                  IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk))` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `s:real^N->bool`; `p0:real^3`;
                 `y0:real^3`; `v0:real^3->bool`] MOI_S4VU_COMPONENT_CLAIM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u0 INTER moi_s34_bd tt kk)` THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `u0:real^N` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cc0:real^3->bool` THEN
      ASM_REWRITE_TAC[]];
    DISCH_THEN(LABEL_TAC "cl")] THEN
  SUBGOAL_THEN `?p1. p1 IN connected_component
                       ((car:(real^N->bool)->real^3->bool) s DIFF
                        IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)) p0 /\
                     ~(p1 IN cb s UNION q)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`;
                   `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`; `v:real^N`;
                   `d:real^3->bool`; `j:real^3->bool`; `q:real^3->bool`; `e:real^3->bool`;
                   `e':real^3->bool`; `p0:real^3`] MOI_S4VU_EXIT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`p0:real^3`; `p1:real^3`] THEN
  SUBGOAL_THEN `(p0:real^3) IN interior q` ASSUME_TAC THENL
   [UNDISCH_TAC `cc0 SUBSET interior q INTER
                 ((car:(real^N->bool)->real^3->bool) s DIFF
                  IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk))` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(p1:real^3) IN connected_component
                 ((car:(real^N->bool)->real^3->bool) s DIFF
                  IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)) p0` THEN
  ASM_SIMP_TAC[GSYM OPEN_PATH_CONNECTED_COMPONENT] THEN
  REWRITE_TAC[IN; path_component] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The pocket core.  A PL ball x inside the ball w, missing the              *)
(* boundary disk dd, such that w DIFF x lies in a compact subset of a given  *)
(* open neighbourhood of dd.  Inward analogue of MOI_S4V_OUTWARD_PUSH of     *)
(* pc_moi_s34_op1b, with the same straightening MOI_S4V_STRAIGHTEN and the   *)
(* shrunk standard simplex (1 - t) k0.                                       *)
(* ------------------------------------------------------------------------- *)

let MOI_S4VU_K0_SCALE = prove
 (`!c x:real^3.
     &0 < c
     ==> (x IN IMAGE (\x. c % x) (convex hull {vec 0,basis 1,basis 2,basis 3}) <=>
          &0 <= x$1 /\ &0 <= x$2 /\ &0 <= x$3 /\ x$1 + x$2 + x$3 <= c)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MOI_SPU_K0; IN_IMAGE; IN_ELIM_THM] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN
    REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN
    REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC) THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC THEN EXISTS_TAC `inv(c) % x:real^3` THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC; VECTOR_MUL_COMPONENT] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
    REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN
    SUBGOAL_THEN `&0 < inv(c)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC) THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC]);;

let MOI_S4VU_K0_SCALE_SIMPLEX = prove
 (`!c. &0 < c
       ==> &3 simplex (IMAGE (\x:real^3. c % x)
                         (convex hull {vec 0,basis 1,basis 2,basis 3}))`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SIMPLEX_LINEAR_IMAGE_EQ o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LINEAR_SCALING] THEN
    ASM_SIMP_TAC[VECTOR_MUL_LCANCEL; REAL_LT_IMP_NZ];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MOI_SPU_STD_SIMPLEX]]);;

let MOI_S4VU_SHRINK = prove
 (`!w dd jd oo:real^3->bool.
     PL_SCHOENFLIES_3_AMBIENT_STATEMENT /\
     pl_ball 3 w /\ pl_cell_with_boundary 2 dd jd /\ dd SUBSET frontier w /\
     open oo /\ dd SUBSET oo
     ==> ?x z. pl_ball 3 x /\ x SUBSET w /\ DISJOINT x dd /\
               compact z /\ z SUBSET oo /\ w DIFF z SUBSET x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`w:real^3->bool`; `dd:real^3->bool`; `jd:real^3->bool`]
    MOI_S4V_STRAIGHTEN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k2:real^3->bool` (X_CHOOSE_THEN `chi:real^3->real^3`
    (X_CHOOSE_THEN `chi':real^3->real^3` STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `k0 = convex hull {vec 0:real^3,basis 1,basis 2,basis 3}` THEN
  ABBREV_TAC `f0 = convex hull {basis 1:real^3,basis 2,basis 3}` THEN
  SUBGOAL_THEN `homeomorphism (k2,IMAGE chi k2) (chi:real^3->real^3,chi')` ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (k2,IMAGE chi k2) (chi:real^3->real^3,chi')` THEN
    SIMP_TAC[pl_homeomorphism];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `compact (k0:real^3->bool) /\ compact (f0:real^3->bool) /\
                f0 SUBSET k0 /\ compact (k2:real^3->bool) /\ interior k2 SUBSET k2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "k0" THEN EXPAND_TAC "f0" THEN
    REWRITE_TAC[INTERIOR_SUBSET] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONVEX_HULL THEN
      MATCH_MP_TAC FINITE_IMP_COMPACT THEN REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
      MATCH_MP_TAC COMPACT_CONVEX_HULL THEN
      MATCH_MP_TAC FINITE_IMP_COMPACT THEN REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      ASM_SIMP_TAC[POLYTOPE_IMP_COMPACT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(k0:real^3->bool) SUBSET k2` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  (* the preimage of oo near f0 *)
  SUBGOAL_THEN `?e2. &0 < e2 /\
                     !x y. x IN f0 /\ y IN k2 /\ dist(x,y) < e2
                           ==> (chi:real^3->real^3) y IN oo` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`chi:real^3->real^3`; `k2:real^3->bool`; `oo:real^3->bool`]
      CONTINUOUS_OPEN_IN_PREIMAGE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_OPEN]) THEN
    DISCH_THEN(X_CHOOSE_THEN `vv:real^3->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`f0:real^3->bool`; `vv:real^3->bool`] MOI_S4Q_COMPACT_IN_OPEN) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(x:real^3) IN {z | z IN k2 /\ (chi:real^3->real^3) z IN oo}` MP_TAC THENL
       [REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
         [ASM SET_TAC[];
          UNDISCH_TAC `IMAGE (chi:real^3->real^3) f0 = dd` THEN
          UNDISCH_TAC `(dd:real^3->bool) SUBSET oo` THEN ASM SET_TAC[]];
        ASM SET_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN {z | z IN k2 /\ (chi:real^3->real^3) z IN oo}` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_INTER] THEN ASM_MESON_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `t = min (&1 / &2) (e2 / &2)` THEN
  SUBGOAL_THEN `&0 < t /\ t <= &1 / &2 /\ t < e2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN k0 <=>
                  &0 <= x$1 /\ &0 <= x$2 /\ &0 <= x$3 /\ x$1 + x$2 + x$3 <= &1`
  (LABEL_TAC "K0") THENL
   [EXPAND_TAC "k0" THEN REWRITE_TAC[MOI_SPU_K0; IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN f0 <=>
                  &0 <= x$1 /\ &0 <= x$2 /\ &0 <= x$3 /\ x$1 + x$2 + x$3 = &1`
  (LABEL_TAC "F0") THENL
   [EXPAND_TAC "f0" THEN REWRITE_TAC[MOI_S4V_F0_COORDS]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 - t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN IMAGE (\x. (&1 - t) % x) k0 <=>
                  &0 <= x$1 /\ &0 <= x$2 /\ &0 <= x$3 /\ x$1 + x$2 + x$3 <= &1 - t`
  (LABEL_TAC "KS") THENL
   [EXPAND_TAC "k0" THEN GEN_TAC THEN MATCH_MP_TAC MOI_S4VU_K0_SCALE THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&3 simplex (IMAGE (\x:real^3. (&1 - t) % x) k0)` ASSUME_TAC THENL
   [EXPAND_TAC "k0" THEN MATCH_MP_TAC MOI_S4VU_K0_SCALE_SIMPLEX THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `ks = IMAGE (\x:real^3. (&1 - t) % x) k0` THEN
  ABBREV_TAC `z0 = {x:real^3 | x IN k0 /\ &1 - t <= x$1 + x$2 + x$3}` THEN
  SUBGOAL_THEN `(ks:real^3->bool) SUBSET k0 /\ k0 SUBSET ks UNION z0 /\
                (z0:real^3->bool) SUBSET k0 /\ DISJOINT ks (f0:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "z0" THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM; DISJOINT; EXTENSION; IN_INTER;
                NOT_IN_EMPTY] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (z0:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "z0" THEN
    REWRITE_TAC[SET_RULE `{x:real^3 | x IN s /\ P x} = s INTER {x | P x}`] THEN
    MATCH_MP_TAC COMPACT_INTER_CLOSED THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`vector[&1;&1;&1]:real^3`; `&1 - t`] CLOSED_HALFSPACE_GE) THEN
    MATCH_MP_TAC(TAUT `p = q ==> p ==> q`) THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; DOT_3; VECTOR_3; real_ge] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (chi:real^3->real^3) ks`; `IMAGE (chi:real^3->real^3) z0`] THEN
  REPEAT CONJ_TAC THENL
   [(* a PL ball *)
    REWRITE_TAC[pl_ball] THEN
    MAP_EVERY EXISTS_TAC [`ks:real^3->bool`; `chi:real^3->real^3`; `chi':real^3->real^3`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_SCD_PLH_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`k2:real^3->bool`; `IMAGE (chi:real^3->real^3) k2`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `polytope (ks:real^3->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE]; ALL_TAC] THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_POLYTOPE] THEN
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN
    ASM_SIMP_TAC[POLYTOPE_IMP_PL_POLYHEDRON] THEN
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `k2:real^3->bool` THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_POLYTOPE] THEN CONJ_TAC THENL
     [UNDISCH_TAC `pl_homeomorphism (k2,IMAGE chi k2) (chi:real^3->real^3,chi')` THEN
      SIMP_TAC[pl_homeomorphism];
      ASM SET_TAC[]];
    (* inside w *)
    UNDISCH_TAC `IMAGE (chi:real^3->real^3) k0 = w` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN FIRST_ASSUM ACCEPT_TAC;
    (* misses dd *)
    UNDISCH_TAC `IMAGE (chi:real^3->real^3) f0 = dd` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `DISJOINT (ks:real^3->bool) f0` THEN
    MAP_EVERY UNDISCH_TAC [`(ks:real^3->bool) SUBSET k0`; `(f0:real^3->bool) SUBSET k0`;
                           `(k0:real^3->bool) SUBSET k2`] THEN
    UNDISCH_TAC `!x. x IN k2 ==> (chi':real^3->real^3) (chi x) = x` THEN
    SET_TAC[];
    (* compact *)
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `k2:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    (* inside oo *)
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN
    EXPAND_TAC "z0" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ABBREV_TAC `sx = (x:real^3)$1 + x$2 + x$3` THEN
    SUBGOAL_THEN `&0 < sx` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `e2:real`)) (concl th))) THEN
    EXISTS_TAC `inv(sx) % x:real^3` THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
      REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `(k0:real^3->bool) SUBSET k2` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[dist; VECTOR_ARITH `a % x - x:real^3 = (a - &1) % x`; NORM_MUL] THEN
    SUBGOAL_THEN `norm(x:real^3) <= sx` ASSUME_TAC THENL
     [MP_TAC(ISPEC `x:real^3` NORM_LE_L1) THEN
      REWRITE_TAC[DIMINDEX_3; SUM_3] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `abs(inv sx - &1) = (&1 - sx) / sx` SUBST1_TAC THENL
     [SUBGOAL_THEN `inv sx - &1 = (&1 - sx) / sx` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < sx` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < sx ==> abs sx = sx`;
                   REAL_ARITH `sx <= &1 ==> abs(&1 - sx) = &1 - sx`];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(&1 - sx) / sx * sx` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN ASM_REAL_ARITH_TAC];
    (* w minus the slab image lies in the shrunk ball *)
    UNDISCH_TAC `IMAGE (chi:real^3->real^3) k0 = w` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `(k0:real^3->bool) SUBSET ks UNION z0` THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The new face ball G = W'' DIFF interior (X UNION N), set                 *)
(* topology.  Generic: c the old ball, q the pocket, y the push              *)
(* layer (W'' = c UNION q UNION y), x the pocket core with slab z0, n the   *)
(* tube, b the set whose trace is computed, oo the neighbourhood of d.      *)
(* ------------------------------------------------------------------------- *)

let MOI_S4VU_G_LOCAL = prove
 (`!c q y x n z0 d e e' j b oo:real^3->bool.
     closed c /\ closed q /\ closed y /\ closed n /\ closed z0 /\ closed x /\ closed d /\
     frontier c = e UNION e' /\ e INTER e' = j /\ j SUBSET d /\
     frontier q = d UNION e /\ q INTER c = e /\ d INTER frontier c = j /\
     y SUBSET oo /\ z0 SUBSET oo /\ oo INTER b SUBSET d UNION interior c /\
     x SUBSET q /\ q DIFF z0 SUBSET x /\ DISJOINT x d /\
     d SUBSET interior (c UNION q UNION y) /\ DISJOINT n b
     ==> !z. z IN b
             ==> (z IN frontier c /\ ~(z IN j)
                  ==> ?u. open u /\ z IN u /\
                          ((c UNION q UNION y) DIFF interior (x UNION n)) INTER u =
                          c INTER u) /\
                 (~(z IN frontier c /\ ~(z IN j))
                  ==> ~(z IN frontier ((c UNION q UNION y) DIFF interior (x UNION n))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~((z:real^3) IN n)` ASSUME_TAC THENL
   [UNDISCH_TAC `DISJOINT (n:real^3->bool) b` THEN UNDISCH_TAC `(z:real^3) IN b` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier (c:real^3->bool) SUBSET c /\ frontier (q:real^3->bool) SUBSET q`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC FRONTIER_SUBSET_CLOSED THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier (c:real^3->bool) INTER interior c = {} /\
                frontier (q:real^3->bool) INTER interior q = {}` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[frontier] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^3->bool) = interior c UNION frontier c /\
                (q:real^3->bool) = interior q UNION frontier q` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[frontier] THEN
    SUBGOAL_THEN `closure (c:real^3->bool) = c /\ closure (q:real^3->bool) = q`
    (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN MATCH_MP_TAC CLOSURE_CLOSED THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MP_TAC(ISPEC `c:real^3->bool` INTERIOR_SUBSET) THEN
    MP_TAC(ISPEC `q:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(q:real^3->bool) INTER interior c = {} /\
                (c:real^3->bool) INTER interior q = {}` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(q:real^3->bool) INTER c = e`; `frontier (c:real^3->bool) = e UNION e'`;
      `frontier (q:real^3->bool) = d UNION e`;
      `frontier (c:real^3->bool) INTER interior c = {}`;
      `frontier (q:real^3->bool) INTER interior q = {}`] THEN
    MP_TAC(ISPEC `c:real^3->bool` INTERIOR_SUBSET) THEN
    MP_TAC(ISPEC `q:real^3->bool` INTERIOR_SUBSET) THEN
    SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `~((z:real^3) IN oo)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `(z:real^3) IN d UNION interior c` MP_TAC THENL
       [UNDISCH_TAC `oo INTER b SUBSET d UNION interior (c:real^3->bool)` THEN
        UNDISCH_TAC `(z:real^3) IN b` THEN UNDISCH_TAC `(z:real^3) IN oo` THEN SET_TAC[];
        ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC
       [`(d:real^3->bool) INTER frontier c = j`; `(z:real^3) IN frontier c`;
        `~((z:real^3) IN j)`; `frontier (c:real^3->bool) INTER interior c = {}`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((z:real^3) IN y) /\ ~(z IN z0) /\ ~(z IN d)` STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(y:real^3->bool) SUBSET oo`; `(z0:real^3->bool) SUBSET oo`;
        `(d:real^3->bool) INTER frontier c = j`; `~((z:real^3) IN oo)`;
        `(z:real^3) IN frontier c`; `~((z:real^3) IN j)`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^3) IN e \/ z IN e'` MP_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN frontier c` THEN ASM_REWRITE_TAC[IN_UNION]; ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
     [(* z on the pocket side *)
      EXISTS_TAC `(:real^3) DIFF (z0 UNION y UNION n UNION d)` THEN
      SUBGOAL_THEN `open ((:real^3) DIFF (z0 UNION y UNION n UNION d))` ASSUME_TAC THENL
       [MATCH_MP_TAC OPEN_DIFF THEN ASM_SIMP_TAC[OPEN_UNIV; CLOSED_UNION]; ALL_TAC] THEN
      SUBGOAL_THEN
       `interior (x UNION n) INTER ((:real^3) DIFF (z0 UNION y UNION n UNION d)) =
        interior q INTER ((:real^3) DIFF (z0 UNION y UNION n UNION d))`
      ASSUME_TAC THENL
       [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
         [REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
          ASM_REWRITE_TAC[] THEN
          SUBGOAL_THEN `~((w:real^3) IN n)` ASSUME_TAC THENL
           [UNDISCH_TAC `(w:real^3) IN (:real^3) DIFF (z0 UNION y UNION n UNION d)` THEN
            SET_TAC[];
            ALL_TAC] THEN
          MP_TAC(ISPECL [`x:real^3->bool`; `n:real^3->bool`; `w:real^3`]
            MOI_TB3_INTERIOR_UNION_OFF) THEN
          ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
          SUBGOAL_THEN `interior x SUBSET interior (q:real^3->bool)` MP_TAC THENL
           [MATCH_MP_TAC SUBSET_INTERIOR THEN FIRST_ASSUM ACCEPT_TAC;
            UNDISCH_TAC `(w:real^3) IN interior x` THEN SET_TAC[]];
          MATCH_MP_TAC(SET_RULE
           `!a b u:real^3->bool. a INTER u SUBSET b ==> a INTER u SUBSET b INTER u`) THEN
          MATCH_MP_TAC INTERIOR_MAXIMAL THEN CONJ_TAC THENL
           [MP_TAC(ISPEC `q:real^3->bool` INTERIOR_SUBSET) THEN
            UNDISCH_TAC `q DIFF z0 SUBSET (x:real^3->bool)` THEN SET_TAC[];
            MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[OPEN_INTERIOR]]];
        ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; IN_UNION];
        MAP_EVERY UNDISCH_TAC
         [`interior (x UNION n) INTER ((:real^3) DIFF (z0 UNION y UNION n UNION d)) =
           interior q INTER ((:real^3) DIFF (z0 UNION y UNION n UNION d))`;
          `(c:real^3->bool) INTER interior q = {}`;
          `(q:real^3->bool) = interior q UNION frontier q`;
          `frontier (q:real^3->bool) = d UNION e`;
          `frontier (c:real^3->bool) = e UNION e'`;
          `frontier (c:real^3->bool) SUBSET c`] THEN
        SET_TAC[]];
      (* z on the far side *)
      SUBGOAL_THEN `~((z:real^3) IN q)` ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`(q:real^3->bool) INTER c = e`; `(e:real^3->bool) INTER e' = j`;
          `frontier (c:real^3->bool) SUBSET c`; `frontier (c:real^3->bool) = e UNION e'`;
          `(z:real^3) IN e'`; `~((z:real^3) IN j)`] THEN
        SET_TAC[];
        ALL_TAC] THEN
      EXISTS_TAC `(:real^3) DIFF (q UNION y UNION n)` THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC OPEN_DIFF THEN ASM_SIMP_TAC[OPEN_UNIV; CLOSED_UNION];
        ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; IN_UNION];
        MP_TAC(ISPEC `x UNION n:real^3->bool` INTERIOR_SUBSET) THEN
        UNDISCH_TAC `(x:real^3->bool) SUBSET q` THEN SET_TAC[]]];
    ALL_TAC] THEN
  (* points off the old trace are not frontier points of G *)
  DISCH_TAC THEN
  SUBGOAL_THEN `closed ((c UNION q UNION y) DIFF interior (x UNION n):real^3->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_DIFF THEN ASM_SIMP_TAC[CLOSED_UNION; OPEN_INTERIOR]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(z:real^3) IN interior ((c UNION q UNION y) DIFF interior (x UNION n)) \/
    ~(z IN (c UNION q UNION y) DIFF interior (x UNION n))`
  MP_TAC THENL
   [ALL_TAC;
    SUBGOAL_THEN
     `frontier ((c UNION q UNION y) DIFF interior (x UNION n):real^3->bool) SUBSET
      (c UNION q UNION y) DIFF interior (x UNION n) /\
      frontier ((c UNION q UNION y) DIFF interior (x UNION n)) INTER
      interior ((c UNION q UNION y) DIFF interior (x UNION n)) = {}`
    MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC FRONTIER_SUBSET_CLOSED THEN FIRST_ASSUM ACCEPT_TAC;
        REWRITE_TAC[frontier] THEN SET_TAC[]];
      SET_TAC[]]] THEN
  ASM_CASES_TAC `(z:real^3) IN d` THENL
   [DISJ1_TAC THEN
    SUBGOAL_THEN `interior (c UNION q UNION y) DIFF (x UNION n) SUBSET
                  interior ((c UNION q UNION y) DIFF interior (x UNION n):real^3->bool)`
    MP_TAC THENL
     [MATCH_MP_TAC INTERIOR_MAXIMAL THEN CONJ_TAC THENL
       [MP_TAC(ISPEC `c UNION q UNION y:real^3->bool` INTERIOR_SUBSET) THEN
        MP_TAC(ISPEC `x UNION n:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[];
        MATCH_MP_TAC OPEN_DIFF THEN ASM_SIMP_TAC[OPEN_INTERIOR; CLOSED_UNION]];
      MAP_EVERY UNDISCH_TAC
       [`(d:real^3->bool) SUBSET interior (c UNION q UNION y)`;
        `DISJOINT (x:real^3->bool) d`; `(z:real^3) IN d`; `~((z:real^3) IN n)`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `(z:real^3) IN interior c` THENL
   [DISJ1_TAC THEN
    SUBGOAL_THEN `interior c DIFF n SUBSET
                  interior ((c UNION q UNION y) DIFF interior (x UNION n):real^3->bool)`
    MP_TAC THENL
     [MATCH_MP_TAC INTERIOR_MAXIMAL THEN CONJ_TAC THENL
       [MP_TAC(ISPEC `c:real^3->bool` INTERIOR_SUBSET) THEN
        MP_TAC(ISPEC `x UNION n:real^3->bool` INTERIOR_SUBSET) THEN
        MAP_EVERY UNDISCH_TAC
         [`(x:real^3->bool) SUBSET q`; `(q:real^3->bool) INTER interior c = {}`] THEN
        SET_TAC[];
        MATCH_MP_TAC OPEN_DIFF THEN ASM_REWRITE_TAC[OPEN_INTERIOR]];
      MAP_EVERY UNDISCH_TAC [`(z:real^3) IN interior c`; `~((z:real^3) IN n)`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  DISJ2_TAC THEN
  SUBGOAL_THEN `~((z:real^3) IN c)` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(c:real^3->bool) = interior c UNION frontier c`;
      `~((z:real^3) IN frontier c /\ ~(z IN j))`; `(j:real^3->bool) SUBSET d`;
      `~((z:real^3) IN d)`; `~((z:real^3) IN interior c)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((z:real^3) IN oo)` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`oo INTER b SUBSET d UNION interior (c:real^3->bool)`; `(z:real^3) IN b`;
      `~((z:real^3) IN d)`; `~((z:real^3) IN interior c)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(z:real^3) IN q` THENL
   [ALL_TAC;
    MAP_EVERY UNDISCH_TAC
     [`~((z:real^3) IN c)`; `~((z:real^3) IN q)`; `(y:real^3->bool) SUBSET oo`;
      `~((z:real^3) IN oo)`] THEN
    SET_TAC[]] THEN
  SUBGOAL_THEN `(z:real^3) IN interior q /\ ~(z IN z0)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(q:real^3->bool) = interior q UNION frontier q`;
      `frontier (q:real^3->bool) = d UNION e`; `frontier (c:real^3->bool) SUBSET c`;
      `frontier (c:real^3->bool) = e UNION e'`; `(z0:real^3->bool) SUBSET oo`;
      `(z:real^3) IN q`; `~((z:real^3) IN c)`; `~((z:real^3) IN d)`;
      `~((z:real^3) IN oo)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior q DIFF z0 SUBSET interior (x UNION n:real^3->bool)` MP_TAC THENL
   [MATCH_MP_TAC INTERIOR_MAXIMAL THEN CONJ_TAC THENL
     [MP_TAC(ISPEC `q:real^3->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `q DIFF z0 SUBSET (x:real^3->bool)` THEN SET_TAC[];
      MATCH_MP_TAC OPEN_DIFF THEN ASM_REWRITE_TAC[OPEN_INTERIOR]];
    MAP_EVERY UNDISCH_TAC [`(z:real^3) IN interior q`; `~((z:real^3) IN z0)`] THEN
    SET_TAC[]]);;

let MOI_S4VU_G_TRACE = prove
 (`!c q y x n z0 d e e' j b oo:real^3->bool.
     closed c /\ closed q /\ closed y /\ closed n /\ closed z0 /\ closed x /\ closed d /\
     frontier c = e UNION e' /\ e INTER e' = j /\ j SUBSET d /\
     frontier q = d UNION e /\ q INTER c = e /\ d INTER frontier c = j /\
     y SUBSET oo /\ z0 SUBSET oo /\ oo INTER b SUBSET d UNION interior c /\
     x SUBSET q /\ q DIFF z0 SUBSET x /\ DISJOINT x d /\
     d SUBSET interior (c UNION q UNION y) /\ DISJOINT n b
     ==> frontier ((c UNION q UNION y) DIFF interior (x UNION n)) INTER b =
         (frontier c INTER b) DIFF j /\
         (!z. z IN frontier ((c UNION q UNION y) DIFF interior (x UNION n)) INTER b
              ==> ?u. open u /\ z IN u /\
                      frontier ((c UNION q UNION y) DIFF interior (x UNION n)) INTER u =
                      frontier c INTER u)`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "loc" o MATCH_MP MOI_S4VU_G_LOCAL) THEN
  SUBGOAL_THEN
   `!z:real^3. z IN b /\ z IN frontier c /\ ~(z IN j)
               ==> ?u. open u /\ z IN u /\
                       frontier ((c UNION q UNION y) DIFF interior (x UNION n)) INTER u =
                       frontier c INTER u`
  (LABEL_TAC "fl") THENL
   [X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    REMOVE_THEN "loc" (MP_TAC o CONJUNCT1 o C MATCH_MP (ASSUME `(z:real^3) IN b`)) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^3->bool` THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC MOI_S4V_FRONTIER_LOCAL THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^3. z IN b /\
               z IN frontier ((c UNION q UNION y) DIFF interior (x UNION n))
               ==> z IN frontier c /\ ~(z IN j)`
  (LABEL_TAC "fc") THENL
   [X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    REMOVE_THEN "loc" (MP_TAC o CONJUNCT2 o C MATCH_MP (ASSUME `(z:real^3) IN b`)) THEN
    MATCH_MP_TAC(TAUT `r ==> (~p ==> ~r) ==> p`) THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_DIFF] THEN X_GEN_TAC `z:real^3` THEN
    EQ_TAC THENL
     [STRIP_TAC THEN
      SUBGOAL_THEN `(z:real^3) IN frontier c /\ ~(z IN j)` STRIP_ASSUME_TAC THENL
       [REMOVE_THEN "fc" MATCH_MP_TAC THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];
      STRIP_TAC THEN CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
      REMOVE_THEN "fl" (MP_TAC o SPEC `z:real^3`) THEN
      ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `frontier ((c UNION q UNION y) DIFF interior (x UNION n)) INTER u =
                   frontier c INTER (u:real^3->bool)` THEN
      MAP_EVERY UNDISCH_TAC [`(z:real^3) IN frontier c`; `(z:real^3) IN u`] THEN
      SET_TAC[]];
    X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN frontier c /\ ~(z IN j)` STRIP_ASSUME_TAC THENL
     [REMOVE_THEN "fc" MATCH_MP_TAC THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REMOVE_THEN "fl" MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

let MOI_S4VU_G_GLOBAL = prove
 (`!c q y x n z0 e e':real^3->bool.
     closed c /\ closed q /\ closed y /\ closed n /\ closed z0 /\ closed x /\
     frontier c = e UNION e' /\ q INTER c = e /\
     x SUBSET q /\ q DIFF z0 SUBSET x
     ==> (c UNION q UNION y) DIFF interior (x UNION n) SUBSET
         c UNION y UNION z0 UNION frontier q /\
         frontier ((c UNION q UNION y) DIFF interior (x UNION n)) SUBSET
         frontier (c UNION q) UNION y UNION z0 UNION frontier q UNION n /\
         interior c DIFF n SUBSET interior ((c UNION q UNION y) DIFF interior (x UNION n))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `q DIFF interior x SUBSET z0 UNION frontier (q:real^3->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `interior q DIFF z0 SUBSET interior (x:real^3->bool)` MP_TAC THENL
     [MATCH_MP_TAC INTERIOR_MAXIMAL THEN CONJ_TAC THENL
       [MP_TAC(ISPEC `q:real^3->bool` INTERIOR_SUBSET) THEN
        UNDISCH_TAC `q DIFF z0 SUBSET (x:real^3->bool)` THEN SET_TAC[];
        MATCH_MP_TAC OPEN_DIFF THEN ASM_REWRITE_TAC[OPEN_INTERIOR]];
      REWRITE_TAC[frontier] THEN
      SUBGOAL_THEN `closure (q:real^3->bool) = q` SUBST1_TAC THENL
       [MATCH_MP_TAC CLOSURE_CLOSED THEN FIRST_ASSUM ACCEPT_TAC; SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior (x:real^3->bool) SUBSET interior (x UNION n)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_INTERIOR THEN SET_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`q DIFF interior x SUBSET z0 UNION frontier (q:real^3->bool)`;
      `interior (x:real^3->bool) SUBSET interior (x UNION n)`] THEN
    SET_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `frontier ((c UNION q) UNION y:real^3->bool) UNION
                frontier (interior (x UNION n:real^3->bool))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SET_RULE `(c UNION q UNION y) DIFF i =
                            ((c UNION q) UNION y) INTER ((:real^3) DIFF i)`] THEN
      W(MP_TAC o PART_MATCH lhand FRONTIER_INTER_SUBSET o lhand o snd) THEN
      REWRITE_TAC[FRONTIER_COMPLEMENT];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `frontier ((c UNION q) UNION y:real^3->bool) SUBSET frontier (c UNION q) UNION y /\
      frontier (interior (x UNION n:real^3->bool)) SUBSET
      z0 UNION frontier (q:real^3->bool) UNION n`
    MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `frontier (c UNION q:real^3->bool) UNION frontier y` THEN
        REWRITE_TAC[FRONTIER_UNION_SUBSET] THEN
        MP_TAC(ISPEC `y:real^3->bool` FRONTIER_SUBSET_CLOSED) THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `frontier (x UNION n:real^3->bool)` THEN
        REWRITE_TAC[FRONTIER_INTERIOR_SUBSET] THEN
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `frontier (x:real^3->bool) UNION frontier n` THEN
        REWRITE_TAC[FRONTIER_UNION_SUBSET] THEN
        MP_TAC(ISPEC `n:real^3->bool` FRONTIER_SUBSET_CLOSED) THEN
        SUBGOAL_THEN `frontier (x:real^3->bool) SUBSET x DIFF interior x` MP_TAC THENL
         [REWRITE_TAC[frontier] THEN
          SUBGOAL_THEN `closure (x:real^3->bool) = x` SUBST1_TAC THENL
           [MATCH_MP_TAC CLOSURE_CLOSED THEN FIRST_ASSUM ACCEPT_TAC; SET_TAC[]];
          ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN
        MAP_EVERY UNDISCH_TAC
         [`q DIFF interior x SUBSET z0 UNION frontier (q:real^3->bool)`;
          `(x:real^3->bool) SUBSET q`] THEN
        SET_TAC[]];
      SET_TAC[]];
    MATCH_MP_TAC INTERIOR_MAXIMAL THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(q:real^3->bool) INTER interior c = {}` MP_TAC THENL
       [SUBGOAL_THEN `frontier (c:real^3->bool) INTER interior c = {}` MP_TAC THENL
         [REWRITE_TAC[frontier] THEN SET_TAC[]; ALL_TAC] THEN
        MP_TAC(ISPEC `c:real^3->bool` INTERIOR_SUBSET) THEN
        MAP_EVERY UNDISCH_TAC
         [`(q:real^3->bool) INTER c = e`; `frontier (c:real^3->bool) = e UNION e'`] THEN
        SET_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPEC `c:real^3->bool` INTERIOR_SUBSET) THEN
      MP_TAC(ISPEC `x UNION n:real^3->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(x:real^3->bool) SUBSET q` THEN SET_TAC[];
      MATCH_MP_TAC OPEN_DIFF THEN ASM_REWRITE_TAC[OPEN_INTERIOR]]]);;

(* ------------------------------------------------------------------------- *)
(* The generic tube lemma (DG                                                *)
(* exists_isPLBall_sdiff_interior_tube) as the term MOI_S4VU_TUBE_TERM.      *)
(* It is proved in pc_moi_tube3 (theorem MOI_TB3_TUBE, same text);           *)
(* PIECES, BALL and UNCLEAN_FROM_TUBE take it as an antecedent, and UNCLEAN  *)
(* discharges it with MOI_TB3_TUBE.                                          *)
(* ------------------------------------------------------------------------- *)

let MOI_S4VU_TUBE_TERM =
 `!x w k (p:real^3) p1 (g:real^1->real^3).
     PL_SCHOENFLIES_3_STATEMENT /\ PL_SCHOENFLIES_3_AMBIENT_STATEMENT /\
     pl_ball 3 x /\ pl_ball 3 w /\ x SUBSET interior w /\ closed k /\
     p IN interior x /\ ~(p1 IN w) /\
     path g /\ pathstart g = p /\ pathfinish g = p1 /\ DISJOINT (path_image g) k
     ==> ?n. compact n /\ DISJOINT n k /\ pl_ball 3 (w DIFF interior (x UNION n))`;;

(* ------------------------------------------------------------------------- *)
(* The pieces of the new face ball: the open set oo around d                 *)
(* (MOI_S4V_O_CHOICE), the outer push layer y of W = cb s UNION q beyond d   *)
(* and a collar of j in e' (as in the clean case of pc_moi_s34_op1b,         *)
(* avoiding the exit point p1), the pocket core x with slab z0               *)
(* (MOI_S4VU_SHRINK, avoiding the entry point p0), and the tube n along the  *)
(* route (MOI_TB3_TUBE).                                                     *)
(* ------------------------------------------------------------------------- *)

let MOI_S4VU_CLOSED_DECOMP = prove
 (`!c:real^N->bool.
     closed c ==> interior c UNION frontier c = c /\ frontier c INTER interior c = {}`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[frontier] THEN
  ASM_SIMP_TAC[CLOSURE_CLOSED] THEN MP_TAC(ISPEC `c:real^N->bool` INTERIOR_SUBSET) THEN
  SET_TAC[]);;

let MOI_S4VU_PIECES = prove
 (mk_imp(MOI_S4VU_TUBE_TERM,
 `!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v d j q e e'.
     PL_SCHOENFLIES_3_STATEMENT /\ PL_SCHOENFLIES_3_AMBIENT_STATEMENT /\
     moi_s34_tube tt kk /\ moi_s34_emb h (UNIONS tt) /\
     moi_s34_frame tt kk h ep f1 car /\ moi_s34_fbinv tt kk h f1 car cb /\
     s IN moi_s34_simp kk (&2) /\
     moi_s34_op1w tt kk f1 cb s v d j /\ DISJOINT (d DIFF j) (cb s) /\
     moi_s4v_pocket (cb s) d j q e e' /\ ~moi_s4v_clean tt kk f1 s q
     ==> ?oo y xc z0 n.
           open oo /\ d SUBSET oo /\ oo SUBSET car s /\
           (!w. {w} IN kk /\ ~(w IN s) ==> DISJOINT oo (IMAGE f1 (moi_s34_vb tt kk w))) /\
           (!s'. s' IN moi_s34_simp kk (&2) /\ ~(s' = s) ==> DISJOINT oo (cb s')) /\
           oo INTER IMAGE f1 (moi_s34_bd tt kk) SUBSET d UNION interior (cb s) /\
           compact y /\ y SUBSET oo /\ d SUBSET interior (cb s UNION q UNION y) /\
           pl_ball 3 xc /\ xc SUBSET q /\ DISJOINT xc d /\
           compact z0 /\ z0 SUBSET oo /\ q DIFF z0 SUBSET xc /\
           compact n /\ n SUBSET car s DIFF IMAGE f1 (moi_s34_nb tt kk) /\
           pl_ball 3 ((cb s UNION q UNION y) DIFF interior (xc UNION n))`),
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`;
                 `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`; `v:real^N`;
                 `d:real^3->bool`; `j:real^3->bool`] MOI_S4V_SETUP) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`;
                 `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`; `v:real^N`;
                 `d:real^3->bool`; `j:real^3->bool`] MOI_S4V_O_CHOICE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN(X_CHOOSE_THEN `oo:real^3->bool` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`;
                 `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`; `v:real^N`;
                 `d:real^3->bool`; `j:real^3->bool`; `q:real^3->bool`; `e:real^3->bool`;
                 `e':real^3->bool`] MOI_S4VU_ROUTE) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p0:real^3` (X_CHOOSE_THEN `p1:real^3`
    (X_CHOOSE_THEN `g:real^1->real^3` STRIP_ASSUME_TAC))) THEN
  UNDISCH_TAC `moi_s4v_pocket ((cb:(real^N->bool)->real^3->bool) s) d j q e e'` THEN
  REWRITE_TAC[moi_s4v_pocket] THEN STRIP_TAC THEN
  SUBGOAL_THEN `d INTER e' = (j:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP MOI_S4L_PL_CELL2_TOPO
      (ASSUME `pl_cell_with_boundary 2 (e':real^3->bool) j`)) THEN
    MAP_EVERY UNDISCH_TAC
     [`d INTER frontier ((cb:(real^N->bool)->real^3->bool) s) = j`;
      `e UNION e' = frontier ((cb:(real^N->bool)->real^3->bool) s)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (q:real^3->bool) /\ frontier q SUBSET q /\
                interior q UNION frontier q = q /\
                frontier q INTER interior q = {}` STRIP_ASSUME_TAC THENL
   [MP_TAC(MATCH_MP MOI_S4V_BALL_SIDES (ASSUME `pl_ball 3 (q:real^3->bool)`)) THEN
    STRIP_TAC THEN ASM_SIMP_TAC[MOI_S4VU_CLOSED_DECOMP];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_sphere 2 (frontier ((cb:(real^N->bool)->real^3->bool) s UNION q)) /\
    compact ((cb:(real^N->bool)->real^3->bool) s UNION q) /\
    interior ((cb:(real^N->bool)->real^3->bool) s UNION q) UNION frontier (cb s UNION q) =
    cb s UNION q`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(MATCH_MP MOI_S4V_BALL_SIDES
      (ASSUME `pl_ball 3 ((cb:(real^N->bool)->real^3->bool) s UNION q)`)) THEN
    STRIP_TAC THEN ASM_SIMP_TAC[MOI_S4VU_CLOSED_DECOMP];
    ALL_TAC] THEN
  (* the outer push, avoiding the exit point p1 *)
  SUBGOAL_THEN `open (oo DELETE (p1:real^3)) /\ d SUBSET oo DELETE p1`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC OPEN_DELETE THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`(d:real^3->bool) SUBSET oo`; `frontier q = (d:real^3->bool) UNION e`;
      `frontier q SUBSET (q:real^3->bool)`;
      `~((p1:real^3) IN (cb:(real^N->bool)->real^3->bool) s UNION q)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`e':real^3->bool`; `j:real^3->bool`; `oo DELETE (p1:real^3)`]
    MOI_S4V_COLLAR) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MAP_EVERY UNDISCH_TAC [`(j:real^3->bool) SUBSET d`; `d SUBSET oo DELETE (p1:real^3)`] THEN
    SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `e2:real^3->bool` (X_CHOOSE_THEN `j2:real^3->bool`
      STRIP_ASSUME_TAC))] THEN
  SUBGOAL_THEN `(j2:real^3->bool) SUBSET e2` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP MOI_S4L_PL_CELL2_TOPO
      (ASSUME `pl_cell_with_boundary 2 (e2:real^3->bool) j2`)) THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`frontier ((cb:(real^N->bool)->real^3->bool) s UNION q)`;
                 `e2:real^3->bool`; `j2:real^3->bool`] DISK_COMPLEMENT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MAP_EVERY UNDISCH_TAC
     [`e2 SUBSET e' DIFF (j:real^3->bool)`;
      `frontier ((cb:(real^N->bool)->real^3->bool) s UNION q) = d UNION e'`] THEN
    SET_TAC[];
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `(frontier ((cb:(real^N->bool)->real^3->bool) s UNION q) DIFF e2) UNION j2 SUBSET
    frontier (cb s UNION q) /\
    (frontier ((cb:(real^N->bool)->real^3->bool) s UNION q) DIFF e2) UNION j2 SUBSET
    oo DELETE (p1:real^3)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`e2 SUBSET e' DIFF (j:real^3->bool)`; `(j2:real^3->bool) SUBSET e2`;
      `e' DIFF (e2 DIFF j2) SUBSET (oo DELETE (p1:real^3))`;
      `d SUBSET oo DELETE (p1:real^3)`;
      `frontier ((cb:(real^N->bool)->real^3->bool) s UNION q) = d UNION e'`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(cb:(real^N->bool)->real^3->bool) s UNION q`;
                 `(frontier ((cb:(real^N->bool)->real^3->bool) s UNION q) DIFF e2) UNION j2`;
                 `j2:real^3->bool`; `oo DELETE (p1:real^3)`] MOI_S4V_OUTWARD_PUSH) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w2:real^3->bool` (X_CHOOSE_THEN `y:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_var(lhs(concl th)) &&
    fst(dest_var(lhs(concl th))) = "w2")) THEN
  SUBGOAL_THEN `(d:real^3->bool) SUBSET
                interior (((cb:(real^N->bool)->real^3->bool) s UNION q) UNION y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `((frontier ((cb:(real^N->bool)->real^3->bool) s UNION q) DIFF e2) UNION j2)
                DIFF j2` THEN
    CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`frontier ((cb:(real^N->bool)->real^3->bool) s UNION q) = d UNION e'`;
        `e2 SUBSET e' DIFF (j:real^3->bool)`; `(j2:real^3->bool) SUBSET e2`;
        `d INTER e' = (j:real^3->bool)`] THEN
      SET_TAC[];
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  (* the pocket core, avoiding the entry point p0 *)
  SUBGOAL_THEN `open (oo DELETE (p0:real^3)) /\ d SUBSET oo DELETE p0`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC OPEN_DELETE THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`(d:real^3->bool) SUBSET oo`; `frontier q = (d:real^3->bool) UNION e`;
      `frontier q INTER interior (q:real^3->bool) = {}`; `(p0:real^3) IN interior q`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`q:real^3->bool`; `d:real^3->bool`; `j:real^3->bool`;
                 `oo DELETE (p0:real^3)`] MOI_S4VU_SHRINK) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    UNDISCH_TAC `frontier q = (d:real^3->bool) UNION e` THEN SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `xc:real^3->bool` (X_CHOOSE_THEN `z0:real^3->bool`
      STRIP_ASSUME_TAC))] THEN
  SUBGOAL_THEN `(p0:real^3) IN interior xc` ASSUME_TAC THENL
   [SUBGOAL_THEN `interior q DIFF z0 SUBSET interior (xc:real^3->bool)` MP_TAC THENL
     [MATCH_MP_TAC INTERIOR_MAXIMAL THEN CONJ_TAC THENL
       [MP_TAC(ISPEC `q:real^3->bool` INTERIOR_SUBSET) THEN
        UNDISCH_TAC `q DIFF z0 SUBSET (xc:real^3->bool)` THEN SET_TAC[];
        MATCH_MP_TAC OPEN_DIFF THEN REWRITE_TAC[OPEN_INTERIOR] THEN
        MATCH_MP_TAC COMPACT_IMP_CLOSED THEN FIRST_ASSUM ACCEPT_TAC];
      MAP_EVERY UNDISCH_TAC
       [`(p0:real^3) IN interior q`; `(z0:real^3->bool) SUBSET oo DELETE p0`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(xc:real^3->bool) SUBSET
                interior (((cb:(real^N->bool)->real^3->bool) s UNION q) UNION y)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `interior q SUBSET interior (((cb:(real^N->bool)->real^3->bool) s UNION q) UNION y) /\
      interior ((cb:(real^N->bool)->real^3->bool) s UNION q) SUBSET
      interior ((cb s UNION q) UNION y)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC SUBSET_INTERIOR THEN SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `e SUBSET (cb:(real^N->bool)->real^3->bool) s UNION q` ASSUME_TAC THENL
     [UNDISCH_TAC `q INTER (cb:(real^N->bool)->real^3->bool) s = e` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `e INTER d SUBSET (j:real^3->bool)` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`d INTER frontier ((cb:(real^N->bool)->real^3->bool) s) = j`;
        `e UNION e' = frontier ((cb:(real^N->bool)->real^3->bool) s)`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`(xc:real^3->bool) SUBSET q`; `DISJOINT (xc:real^3->bool) d`;
      `interior q UNION frontier q = (q:real^3->bool)`;
      `frontier q = (d:real^3->bool) UNION e`;
      `interior ((cb:(real^N->bool)->real^3->bool) s UNION q) UNION
       frontier (cb s UNION q) = cb s UNION q`;
      `frontier ((cb:(real^N->bool)->real^3->bool) s UNION q) = d UNION e'`;
      `(e:real^3->bool) INTER e' = j`; `(j:real^3->bool) SUBSET d`;
      `e SUBSET (cb:(real^N->bool)->real^3->bool) s UNION q`;
      `e INTER d SUBSET (j:real^3->bool)`;
      `interior q SUBSET interior (((cb:(real^N->bool)->real^3->bool) s UNION q) UNION y)`;
      `interior ((cb:(real^N->bool)->real^3->bool) s UNION q) SUBSET
       interior ((cb s UNION q) UNION y)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the tube along the route *)
  SUBGOAL_THEN `(s:real^N->bool) IN kk /\ ~(s = {})` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(s:real^N->bool) IN moi_s34_simp kk (&2)` THEN
    REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN UNDISCH_TAC `aff_dim(s:real^N->bool) = &2` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `s:real^N->bool`] MOI_S4VU_O_OPEN) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`xc:real^3->bool`;
                 `((cb:(real^N->bool)->real^3->bool) s UNION q) UNION y`;
                 `(:real^3) DIFF ((car:(real^N->bool)->real^3->bool) s DIFF
                                  IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk))`;
                 `p0:real^3`; `p1:real^3`; `g:real^1->real^3`]
    (ASSUME MOI_S4VU_TUBE_TERM)) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [REWRITE_TAC[GSYM OPEN_CLOSED] THEN FIRST_ASSUM ACCEPT_TAC;
      MAP_EVERY UNDISCH_TAC
       [`~((p1:real^3) IN (cb:(real^N->bool)->real^3->bool) s UNION q)`;
        `y SUBSET oo DELETE (p1:real^3)`] THEN
      SET_TAC[];
      UNDISCH_TAC `path_image (g:real^1->real^3) SUBSET
                   (car:(real^N->bool)->real^3->bool) s DIFF
                   IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)` THEN
      SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `n:real^3->bool` STRIP_ASSUME_TAC)] THEN
  MAP_EVERY EXISTS_TAC [`oo:real^3->bool`; `y:real^3->bool`; `xc:real^3->bool`;
                        `z0:real^3->bool`; `n:real^3->bool`] THEN
  REWRITE_TAC[GSYM UNION_ASSOC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [UNDISCH_TAC `y SUBSET oo DELETE (p1:real^3)` THEN SET_TAC[];
    UNDISCH_TAC `z0 SUBSET oo DELETE (p0:real^3)` THEN SET_TAC[];
    UNDISCH_TAC `DISJOINT n ((:real^3) DIFF ((car:(real^N->bool)->real^3->bool) s DIFF
                                  IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)))` THEN
    SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The new face ball G = (cb s UNION q UNION y) DIFF interior               *)
(* (xc UNION n) and its invariants, and UNCLEAN_FROM_TUBE                    *)
(* |- tube term ==> MOI_S4V_UNCLEAN (assembled as OP1_OUT_FROM_UNCLEAN       *)
(* assembles the clean case:                                                 *)
(* ------------------------------------------------------------------------- *)

let MOI_S4VU_BALL = prove
 (mk_imp(MOI_S4VU_TUBE_TERM,
 `!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v d j q e e'.
     PL_SCHOENFLIES_3_STATEMENT /\ PL_SCHOENFLIES_3_AMBIENT_STATEMENT /\
     moi_s34_tube tt kk /\ moi_s34_emb h (UNIONS tt) /\
     moi_s34_frame tt kk h ep f1 car /\ moi_s34_fbinv tt kk h f1 car cb /\
     s IN moi_s34_simp kk (&2) /\
     moi_s34_op1w tt kk f1 cb s v d j /\ DISJOINT (d DIFF j) (cb s) /\
     moi_s4v_pocket (cb s) d j q e e' /\ ~moi_s4v_clean tt kk f1 s q
     ==> j IN components (moi_s34_trace tt kk f1 (cb s)) /\
         ?c2. pl_ball 3 c2 /\ IMAGE h (relative_frontier s) SUBSET interior c2 /\
              (!w. {w} IN kk /\ ~(w IN s) ==> DISJOINT c2 (IMAGE f1 (moi_s34_vb tt kk w))) /\
              (!s'. s' IN moi_s34_simp kk (&2) /\ ~(s' = s)
                    ==> c2 INTER cb s' SUBSET interior (IMAGE f1 (moi_s34_nb tt kk))) /\
              frontier c2 SUBSET car s /\
              moi_s34_trace tt kk f1 c2 = moi_s34_trace tt kk f1 (cb s) DIFF j /\
              (!x. x IN moi_s34_trace tt kk f1 c2
                   ==> ?u. open u /\ x IN u /\ frontier c2 INTER u = frontier (cb s) INTER u)`),
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`;
                 `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`; `v:real^N`;
                 `d:real^3->bool`; `j:real^3->bool`] MOI_S4V_SETUP) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`] MOI_S4L_TRACE_COMP_FACTS) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o REWRITE_RULE[moi_s34_fb1]) STRIP_ASSUME_TAC) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`;
                 `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`; `v:real^N`;
                 `d:real^3->bool`; `j:real^3->bool`; `q:real^3->bool`; `e:real^3->bool`;
                 `e':real^3->bool`]
    (MP MOI_S4VU_PIECES (ASSUME MOI_S4VU_TUBE_TERM))) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `oo:real^3->bool` (X_CHOOSE_THEN `y:real^3->bool`
    (X_CHOOSE_THEN `xc:real^3->bool` (X_CHOOSE_THEN `z0:real^3->bool`
    (X_CHOOSE_THEN `n:real^3->bool` STRIP_ASSUME_TAC))))) THEN
  UNDISCH_TAC `moi_s4v_pocket ((cb:(real^N->bool)->real^3->bool) s) d j q e e'` THEN
  REWRITE_TAC[moi_s4v_pocket] THEN STRIP_TAC THEN
  (* j is a component of the old trace: the trace meets oo exactly in j *)
  SUBGOAL_THEN `moi_s34_trace tt kk (f1:real^N->real^3) ((cb:(real^N->bool)->real^3->bool) s)
                INTER oo = j`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_s34_trace] THEN
    MAP_EVERY UNDISCH_TAC
     [`oo INTER IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) SUBSET
       d UNION interior ((cb:(real^N->bool)->real^3->bool) s)`;
      `d INTER frontier ((cb:(real^N->bool)->real^3->bool) s) = j`;
      `(j:real^3->bool) SUBSET d`; `(d:real^3->bool) SUBSET oo`;
      `d SUBSET IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`] THEN
    REWRITE_TAC[frontier] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(j:real^3->bool) IN components (moi_s34_trace tt kk (f1:real^N->real^3)
                                                 ((cb:(real^N->bool)->real^3->bool) s))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4N_RIM_COMPONENT THEN EXISTS_TAC `oo:real^3->bool` THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  (* closedness and the remaining facts for the generic lemmas *)
  SUBGOAL_THEN `closed ((cb:(real^N->bool)->real^3->bool) s) /\ closed (q:real^3->bool) /\
                closed (y:real^3->bool) /\ closed (n:real^3->bool) /\
                closed (z0:real^3->bool) /\ closed (xc:real^3->bool) /\
                closed (d:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    TRY(FIRST_ASSUM ACCEPT_TAC) THEN MATCH_MP_TAC MOI_S4D_PL_BALL_COMPACT THEN
    EXISTS_TAC `3` THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier ((cb:(real^N->bool)->real^3->bool) s) = e UNION e'` ASSUME_TAC THENL
   [FIRST_ASSUM(ACCEPT_TAC o SYM); ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) SUBSET
                IMAGE f1 (moi_s34_nb tt kk)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s34_frame tt kk (h:real^N->real^3) ep f1 car` THEN
    REWRITE_TAC[moi_s34_frame] THEN
    DISCH_THEN(MP_TAC o el 3 o CONJUNCTS) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT n (IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk))` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`n SUBSET (car:(real^N->bool)->real^3->bool) s DIFF
                IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)`;
      `IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) SUBSET IMAGE f1 (moi_s34_nb tt kk)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(cb:(real^N->bool)->real^3->bool) s`; `q:real^3->bool`; `y:real^3->bool`;
                 `xc:real^3->bool`; `n:real^3->bool`; `z0:real^3->bool`; `d:real^3->bool`;
                 `e:real^3->bool`; `e':real^3->bool`; `j:real^3->bool`;
                 `IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`; `oo:real^3->bool`]
    MOI_S4VU_G_TRACE) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`(cb:(real^N->bool)->real^3->bool) s`; `q:real^3->bool`; `y:real^3->bool`;
                 `xc:real^3->bool`; `n:real^3->bool`; `z0:real^3->bool`;
                 `e:real^3->bool`; `e':real^3->bool`] MOI_S4VU_G_GLOBAL) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `e SUBSET (cb:(real^N->bool)->real^3->bool) s /\
                e' SUBSET (cb:(real^N->bool)->real^3->bool) s` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`frontier ((cb:(real^N->bool)->real^3->bool) s) = e UNION e'`;
      `frontier ((cb:(real^N->bool)->real^3->bool) s) SUBSET cb s`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `((cb:(real^N->bool)->real^3->bool) s UNION q UNION y) DIFF
              interior (xc UNION n)` THEN
  REWRITE_TAC[moi_s34_trace] THEN
  REPEAT CONJ_TAC THENL
   [(* a PL ball *)
    FIRST_ASSUM ACCEPT_TAC;
    (* the relative frontier of s stays inside *)
    SUBGOAL_THEN `IMAGE (h:real^N->real^3) (relative_frontier s) SUBSET
                  IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)` ASSUME_TAC THENL
     [UNDISCH_TAC `moi_s34_frame tt kk (h:real^N->real^3) ep f1 car` THEN
      REWRITE_TAC[moi_s34_frame] THEN
      DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1 o funpow 9 CONJUNCT2) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `interior (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s))` THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; REWRITE_TAC[INTERIOR_SUBSET]];
        MATCH_MP_TAC IMAGE_SUBSET THEN
        MP_TAC(MATCH_MP MOI_S4L_GRAPH_TUBE
          (ASSUME `moi_s34_tube tt (kk:(real^N->bool)->bool)`)) THEN
        DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
        REWRITE_TAC[moi_s34_ft] THEN MATCH_MP_TAC SUBSET_UNIONS THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `interior ((cb:(real^N->bool)->real^3->bool) s) DIFF n` THEN
    CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`IMAGE (h:real^N->real^3) (relative_frontier s) SUBSET
         interior ((cb:(real^N->bool)->real^3->bool) s)`;
        `IMAGE (h:real^N->real^3) (relative_frontier s) SUBSET
         IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)`;
        `n SUBSET (car:(real^N->bool)->real^3->bool) s DIFF
                  IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)`] THEN
      SET_TAC[];
      FIRST_ASSUM ACCEPT_TAC];
    (* the foreign vertex balls *)
    X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o C MATCH_MP
      (CONJ (ASSUME `{w:real^N} IN kk`) (ASSUME `~((w:real^N) IN s)`)))) THEN
    MAP_EVERY UNDISCH_TAC
     [`((cb:(real^N->bool)->real^3->bool) s UNION q UNION y) DIFF interior (xc UNION n)
       SUBSET cb s UNION y UNION z0 UNION frontier q`;
      `frontier q = (d:real^3->bool) UNION e`;
      `e SUBSET (cb:(real^N->bool)->real^3->bool) s`;
      `(y:real^3->bool) SUBSET oo`; `(z0:real^3->bool) SUBSET oo`;
      `(d:real^3->bool) SUBSET oo`] THEN
    SET_TAC[];
    (* the other face balls *)
    X_GEN_TAC `s':real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(cb:(real^N->bool)->real^3->bool) s INTER cb s' SUBSET
                  interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk))`
    MP_TAC THENL
     [UNDISCH_TAC `moi_s34_fbinv tt kk (h:real^N->real^3) f1 car cb` THEN
      REWRITE_TAC[moi_s34_fbinv; moi_s34_fb2] THEN
      DISCH_THEN(MP_TAC o SPECL [`s:real^N->bool`; `s':real^N->bool`] o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ASSUME `~((s':real^N->bool) = s)`) THEN MESON_TAC[];
      ALL_TAC] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o C MATCH_MP
      (CONJ (ASSUME `(s':real^N->bool) IN moi_s34_simp kk (&2)`)
            (ASSUME `~((s':real^N->bool) = s)`)))) THEN
    MAP_EVERY UNDISCH_TAC
     [`((cb:(real^N->bool)->real^3->bool) s UNION q UNION y) DIFF interior (xc UNION n)
       SUBSET cb s UNION y UNION z0 UNION frontier q`;
      `frontier q = (d:real^3->bool) UNION e`;
      `e SUBSET (cb:(real^N->bool)->real^3->bool) s`;
      `(y:real^3->bool) SUBSET oo`; `(z0:real^3->bool) SUBSET oo`;
      `(d:real^3->bool) SUBSET oo`] THEN
    SET_TAC[];
    (* the new frontier lies in car s *)
    MAP_EVERY UNDISCH_TAC
     [`frontier (((cb:(real^N->bool)->real^3->bool) s UNION q UNION y) DIFF
                 interior (xc UNION n)) SUBSET
       frontier (cb s UNION q) UNION y UNION z0 UNION frontier q UNION n`;
      `frontier ((cb:(real^N->bool)->real^3->bool) s UNION q) = d UNION e'`;
      `frontier q = (d:real^3->bool) UNION e`;
      `frontier ((cb:(real^N->bool)->real^3->bool) s) = e UNION e'`;
      `frontier ((cb:(real^N->bool)->real^3->bool) s) SUBSET car s`;
      `d SUBSET (car:(real^N->bool)->real^3->bool) s`;
      `(y:real^3->bool) SUBSET oo`; `(z0:real^3->bool) SUBSET oo`;
      `oo SUBSET (car:(real^N->bool)->real^3->bool) s`;
      `n SUBSET (car:(real^N->bool)->real^3->bool) s DIFF
                IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)`] THEN
    SET_TAC[];
    (* the new trace *)
    FIRST_ASSUM ACCEPT_TAC;
    (* local agreement *)
    FIRST_ASSUM ACCEPT_TAC]);;

let UNCLEAN_FROM_TUBE = prove
 (mk_imp(MOI_S4VU_TUBE_TERM,MOI_S4V_UNCLEAN),
  DISCH_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`; `v:real^N`;
                 `d:real^3->bool`; `j:real^3->bool`] MOI_S4V_SETUP) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`; `v:real^N`;
                 `d:real^3->bool`; `j:real^3->bool`; `q:real^3->bool`; `e:real^3->bool`;
                 `e':real^3->bool`]
    (MP MOI_S4VU_BALL (ASSUME MOI_S4VU_TUBE_TERM))) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `PL_SCHOENFLIES_3_STATEMENT /\ PL_SCHOENFLIES_3_AMBIENT_STATEMENT` THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `c2:real^3->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`]
    MOI_S4L_TRACE_COMP_FACTS) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `moi_s34_fb1 tt kk h (f1:real^N->real^3) car s c2` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4V_FB1_OUT THEN
    MAP_EVERY EXISTS_TAC [`(cb:(real^N->bool)->real^3->bool) s`; `j:real^3->bool`;
                          `d:real^3->bool`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `\s':real^N->bool. if s' = s then c2 else (cb:(real^N->bool)->real^3->bool) s'` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S4V_FBINV_OUT THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    SIMP_TAC[];
    REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S4N_RANK_DROP THEN
    EXISTS_TAC `j:real^3->bool` THEN
    UNDISCH_TAC `moi_s34_fb1 tt kk h (f1:real^N->real^3) car s (cb s)` THEN
    REWRITE_TAC[moi_s34_fb1] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [MP_TAC(ISPECL [`moi_s34_trace tt kk (f1:real^N->real^3)
                       ((cb:(real^N->bool)->real^3->bool) s)`; `(:real^3)`;
                     `{}:real^3->bool`; `j:real^3->bool`] MOI_S4N_COMPONENTS_SIDE) THEN
      REWRITE_TAC[CLOSED_UNIV; CLOSED_EMPTY; INTER_EMPTY; EMPTY_SUBSET; UNION_EMPTY;
                  SUBSET_UNIV; INTER_UNIV] THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN SET_TAC[]]]);;

(* The main theorem UNCLEAN: the tube statement is MOI_TB3_TUBE.             *)

let UNCLEAN = prove
 (MOI_S4V_UNCLEAN,
  ACCEPT_TAC(MP UNCLEAN_FROM_TUBE MOI_TB3_TUBE));;


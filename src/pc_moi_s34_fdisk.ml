(* ========================================================================= *)
(* pc_moi_s34_fdisk: the face disks D_s'' of Sec 34 (p.244), main theorem   *)
(* FDISK : |- MOI_S34_FDISK of pc_moi_s34_stmt.ml.  For each 2-simplex s    *)
(* the face disk is an innermost disk of the boundary sphere of the face    *)
(* ball cb s cut along the trace components; it lies outside the tube,      *)
(* since a disk inside would contract a trace circle in the face torus,     *)
(* against its winding number (pc_moi_s34_trace).                           *)
(* ========================================================================= *)

needs "src/pc_moi_s34_stmt.ml";;
needs "src/pc_moi_sch3_lev.ml";;
needs "src/pc_moi_sch3_s2.ml";;
needs "src/pc_moi_pl2.ml";;
needs "src/pc_moi_fnd_tubea.ml";;
needs "src/pc_moi_fnd_gpb.ml";;
needs "src/pc_moi_s34_tinf.ml";;
needs "src/pc_moi_s34_scella.ml";;
needs "src/pc_moi_s34_outer.ml";;
needs "src/pc_moi_s34_l910.ml";;
needs "src/pc_moi_s34_trace.ml";;
needs "src/pc_moi_s34_tvarc.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Generic part (no Sec 34 vocabulary): innermost disks on a PL 2-sphere.   *)
(* A connected set missing the common boundary j of the two halves of a     *)
(* split lies in the half it meets.                                          *)
(* ------------------------------------------------------------------------- *)

let MOI_S4FD_SIDE = prove
 (`!d1 d2 j x:real^N->bool.
     pl_cell_with_boundary 2 d1 j /\ pl_cell_with_boundary 2 d2 j /\
     d1 INTER d2 = j /\ connected x /\ x SUBSET d1 UNION d2 /\
     DISJOINT x j /\ ~DISJOINT x d1
     ==> x SUBSET d1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`x:real^N->bool`; `d1:real^N->bool`; `d2:real^N->bool`]
    MOI_S4L_CONNECTED_TWO_CLOSED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
        ASM_MESON_TAC[MOI_S4L_PL_CELL_FACTS]) THEN
    ASM SET_TAC[];
    DISCH_THEN DISJ_CASES_TAC THEN ASM SET_TAC[]]);;

(* Innermost disks: for a finite nonempty family cc of pairwise disjoint PL *)
(* circles on a PL 2-sphere sg there are a member j and a disk d in sg     *)
(* bounded by j and missing the other members (minimal number of members    *)
(* met, then the split at a member inside, oriented away from j).           *)

let MOI_S4FD_INNERMOST = prove
 (`!sg (cc:(real^3->bool)->bool).
     pl_sphere 2 sg /\ FINITE cc /\ ~(cc = {}) /\
     (!j. j IN cc ==> pl_sphere 1 j /\ j SUBSET sg) /\
     (!j j'. j IN cc /\ j' IN cc /\ ~(j = j') ==> DISJOINT j j')
     ==> ?j d. j IN cc /\ pl_cell_with_boundary 2 d j /\ d SUBSET sg /\
               (!j'. j' IN cc /\ ~(j' = j) ==> DISJOINT d j')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!j0 d0:real^3->bool.
                  FINITE {k | k IN cc /\ ~(k = j0) /\ ~DISJOINT k d0}`
  (LABEL_TAC "fin") THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `cc:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?n j d d'. j IN cc /\ pl_cell_with_boundary 2 d j /\
               pl_cell_with_boundary 2 d' j /\
               d UNION d' = sg /\ d INTER d' = j /\
               CARD {k | k IN cc /\ ~(k = j) /\ ~DISJOINT k (d:real^3->bool)} = n`
  MP_TAC THENL
   [SUBGOAL_THEN `?j0:real^3->bool. j0 IN cc` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`sg:real^3->bool`; `j0:real^3->bool`] SPHERE_SPLIT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:real^3->bool` (X_CHOOSE_THEN `d2:real^3->bool`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC
     [`CARD {k | k IN cc /\ ~(k = j0) /\ ~DISJOINT k (d1:real^3->bool)}`;
      `j0:real^3->bool`; `d1:real^3->bool`; `d2:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `j:real^3->bool` (X_CHOOSE_THEN `d:real^3->bool`
      (X_CHOOSE_THEN `d':real^3->bool` STRIP_ASSUME_TAC)))
    (LABEL_TAC "min"))) THEN
  ASM_CASES_TAC `?k:real^3->bool. k IN cc /\ ~(k = j) /\ ~DISJOINT k d` THENL
   [ALL_TAC;
    MAP_EVERY EXISTS_TAC [`j:real^3->bool`; `d:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[DISJOINT_SYM]] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `k:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `pl_sphere 1 (k:real^3->bool) /\ k SUBSET sg /\
                pl_sphere 1 (j:real^3->bool) /\ j SUBSET sg /\ DISJOINT k j`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `connected (k:real^3->bool) /\ connected (j:real^3->bool)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[MOI_SLV_CIRCLE_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `(k:real^3->bool) SUBSET d` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4FD_SIDE THEN
    MAP_EVERY EXISTS_TAC [`d':real^3->bool`; `j:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sg:real^3->bool`; `k:real^3->bool`] SPHERE_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real^3->bool` (X_CHOOSE_THEN `e2:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`sg:real^3->bool`; `k:real^3->bool`; `e1:real^3->bool`;
                 `e2:real^3->bool`; `j:real^3->bool`] MOI_S4L_SPLIT_ORIENT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` (X_CHOOSE_THEN `u':real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `DISJOINT (u:real^3->bool) j` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(k:real^3->bool) SUBSET u` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4L_PL_CELL_FACTS]; ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^3->bool) SUBSET d` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4FD_SIDE THEN
    MAP_EVERY EXISTS_TAC [`d':real^3->bool`; `j:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_S4L_PL_CELL_FACTS];
      ASM SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  USE_THEN "min" (MP_TAC o SPEC
    `CARD {k' | k' IN cc /\ ~(k' = k) /\ ~DISJOINT k' (u:real^3->bool)}`) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "n" THEN MATCH_MP_TAC CARD_PSUBSET THEN
    USE_THEN "fin" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[PSUBSET_ALT] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `k':real^3->bool` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [DISCH_TAC THEN UNDISCH_TAC `~DISJOINT k' (u:real^3->bool)` THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        ASM SET_TAC[]];
      EXISTS_TAC `k:real^3->bool` THEN ASM_REWRITE_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`k:real^3->bool`; `u:real^3->bool`; `u':real^3->bool`]) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A component of a closed set with finitely many components has an open    *)
(* neighbourhood meeting no other component.                                 *)
(* ------------------------------------------------------------------------- *)

let MOI_S4FD_COMP_NBHD = prove
 (`!(t:real^N->bool) j.
     closed t /\ FINITE (components t) /\ j IN components t
     ==> ?u. open u /\ j SUBSET u /\ t INTER u = j INTER u`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `(:real^N) DIFF UNIONS (components t DELETE (j:real^N->bool))` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM closed] THEN MATCH_MP_TAC CLOSED_UNIONS THEN
    ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE] THEN ASM_MESON_TAC[CLOSED_COMPONENTS];
    REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIV; IN_UNIONS; IN_DELETE] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`t:real^N->bool`; `j:real^N->bool`; `c:real^N->bool`]
      COMPONENTS_NONOVERLAP) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    MATCH_MP_TAC(SET_RULE
     `!t j k:real^N->bool. t SUBSET j UNION k /\ j SUBSET t
                           ==> t INTER ((:real^N) DIFF k) = j INTER ((:real^N) DIFF k)`) THEN
    CONJ_TAC THENL
     [MP_TAC(ISPEC `t:real^N->bool` UNIONS_COMPONENTS) THEN SET_TAC[];
      ASM_MESON_TAC[IN_COMPONENTS_SUBSET]]]);;

(* ------------------------------------------------------------------------- *)
(* Sec 34 facts for one face.  A splitting disk met by a face ball belongs  *)
(* to an edge of the face (fb1: the ball misses the other vertex balls).    *)
(* ------------------------------------------------------------------------- *)

let MOI_S4FD_EDGE_IN_S = prove
 (`!(tt:(real^N->bool)->bool) kk h (f1:real^N->real^3) car s c g x.
     moi_s34_tube tt kk /\ s IN moi_s34_simp kk (&2) /\
     moi_s34_fb1 tt kk h f1 car s c /\ g IN moi_s34_simp kk (&1) /\
     x IN c /\ x IN IMAGE f1 (moi_s34_sd tt kk g)
     ==> g SUBSET s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `g:real^N->bool`] MOI_S4L_EDGE_VERTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(x:real^3) IN IMAGE f1 (moi_s34_vb tt kk u) /\
                x IN IMAGE f1 (moi_s34_vb (tt:(real^N->bool)->bool) kk w)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN IMAGE f1 (moi_s34_sd (tt:(real^N->bool)->bool) kk g)` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^N) IN s /\ (w:real^N) IN s` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s34_fb1 tt kk h (f1:real^N->real^3) car s c` THEN
    REWRITE_TAC[moi_s34_fb1] THEN
    DISCH_THEN(MP_TAC o el 3 o CONJUNCTS) THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `u:real^N` th) THEN MP_TAC(SPEC `w:real^N` th)) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^N->bool) IN kk` ASSUME_TAC THENL
   [UNDISCH_TAC `(s:real^N->bool) IN moi_s34_simp kk (&2)` THEN
    SIMP_TAC[moi_s34_simp; IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `s:real^N->bool`] MOI_S4A_KK_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN
  ASM_REWRITE_TAC[CONVEX_CONVEX_HULL] THEN ASM_MESON_TAC[]);;

(* Two set facts used below, in abstract form (so that SET_TAC does not   *)
(* expand images).                                                          *)

let MOI_S4FD_SING_MISS = prove
 (`!j x a b c (p:A).
     j INTER x = {p} /\ x SUBSET a INTER b /\ j SUBSET c /\ a INTER b INTER c = {}
     ==> F`,
  SET_TAC[]);;

let MOI_S4FD_SING_TWO = prove
 (`!j x a (p:A) y z.
     j INTER x = {p} /\ a SUBSET j /\ y IN a /\ z IN a /\ y IN x /\ z IN x
     ==> y = z`,
  SET_TAC[]);;

(* Lemma 9 in the form of moi_s34_l910 follows from traced and fb1: a trace *)
(* component meets the splitting disk of the edge opposite to any vertex of *)
(* s outside that vertex ball (no three vertex balls meet).                  *)

let MOI_S4FD_L9_ONE = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v j.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fbinv tt kk h f1 car cb /\ moi_s34_traced tt kk f1 cb /\
     s IN moi_s34_simp kk (&2) /\ {v} IN kk /\
     j IN components (moi_s34_trace tt kk f1 (cb s)) /\
     j SUBSET IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`;
                 `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`]
    MOI_S4L_TRACE_COMP_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(j:real^3->bool = {})` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `j SUBSET moi_s34_trace tt kk (f1:real^N->real^3)
                         ((cb:(real^N->bool)->real^3->bool) s)` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `j SUBSET IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N) IN s` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4L_TRACE_AT_V THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                          `h:real^N->real^3`; `f1:real^N->real^3`;
                          `car:(real^N->bool)->real^3->bool`;
                          `(cb:(real^N->bool)->real^3->bool) s`; `j:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`;
                 `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`]
    MOI_S4T_TRI_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:real^N` (X_CHOOSE_THEN `v2:real^N`
    (X_CHOOSE_TAC `v3:real^N`))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_s4t_tri]) THEN
  SUBGOAL_THEN `(v:real^N) IN {v1,v2,v3}` ASSUME_TAC THENL
   [UNDISCH_TAC `{x | x IN s /\ {x} IN kk} = {v1:real^N,v2,v3}` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^N`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?x y:real^N. x IN {v1,v2,v3} /\ y IN {v1,v2,v3} /\
                             ~(x = y) /\ ~(x = v) /\ ~(y = v)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(v:real^N) IN {v1,v2,v3}` THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`;
                 `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`;
                 `v1:real^N`; `v2:real^N`; `v3:real^N`; `x:real^N`; `y:real^N`]
    MOI_S4T_TRI_PAIR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `x:real^N`; `y:real^N`] MOI_S4L_EDGE_SD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^N) IN s /\ (y:real^N) IN s` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `{x | x IN s /\ {x} IN kk} = {v1:real^N,v2,v3}` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `x:real^N` th) THEN MP_TAC(SPEC `y:real^N` th)) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[x:real^N,y] SUBSET s` ASSUME_TAC THENL
   [SUBGOAL_THEN `(s:real^N->bool) IN kk` ASSUME_TAC THENL
     [UNDISCH_TAC `(s:real^N->bool) IN moi_s34_simp kk (&2)` THEN
      SIMP_TAC[moi_s34_simp; IN_ELIM_THM];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `s:real^N->bool`] MOI_S4A_KK_SIMPLEX) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
    UNDISCH_TAC `(x:real^N) IN s` THEN UNDISCH_TAC `(y:real^N) IN s` THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_s34_traced tt kk (f1:real^N->real^3) cb` THEN
  REWRITE_TAC[moi_s34_traced] THEN DISCH_THEN(MP_TAC o SPEC `s:real^N->bool`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `j:real^3->bool` o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `segment[x:real^N,y]` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `p:real^3`) THEN
  MP_TAC(ISPECL [`j:real^3->bool`;
                 `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk x INTER moi_s34_vb tt kk y)`;
                 `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk x)`;
                 `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk y)`;
                 `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)`; `p:real^3`]
    MOI_S4FD_SING_MISS) THEN
  ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_ACCEPT_TAC(SET_RULE
      `!f:A->B a b. IMAGE f (a INTER b) SUBSET IMAGE f a INTER IMAGE f b`);
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`] MOI_S4L_IMG_FACTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`x:real^N`; `y:real^N`; `v:real^N`] o
      CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[]]);;

(* Lemma 10 in the form of moi_s34_l910: the two ends of an arc of a trace  *)
(* component on one splitting disk would be two points of that component on *)
(* it (traced), the edge lying in s by fb1.                                 *)

let MOI_S4FD_L10_ONE = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s g a aa.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fbinv tt kk h f1 car cb /\ moi_s34_traced tt kk f1 cb /\
     s IN moi_s34_simp kk (&2) /\ g IN moi_s34_simp kk (&1) /\
     pl_cell_with_boundary 1 a aa /\
     a SUBSET moi_s34_trace tt kk f1 (cb s) /\
     aa SUBSET IMAGE f1 (moi_s34_sd tt kk g)
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`;
                 `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`]
    MOI_S4L_TRACE_COMP_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S4L_CELL1_PL_ARC) THEN
  DISCH_THEN(X_CHOOSE_THEN `ha:real^1->real^3` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ARC_DISTINCT_ENDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_PL_CELL_FACTS o
    check (fun th -> concl th = `pl_cell_with_boundary 1 (a:real^3->bool) aa`)) THEN
  SUBGOAL_THEN `pathstart ha IN (a:real^3->bool) /\ pathfinish ha IN a /\
                pathstart (ha:real^1->real^3) IN IMAGE f1 (moi_s34_sd tt kk g) /\
                pathfinish ha IN IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!aa a x (y:A) z. aa = {y,z} /\ aa SUBSET a /\ aa SUBSET x
                           ==> y IN a /\ z IN a /\ y IN x /\ z IN x`) THEN
    EXISTS_TAC `aa:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pathstart (ha:real^1->real^3) IN
                moi_s34_trace tt kk (f1:real^N->real^3) ((cb:(real^N->bool)->real^3->bool) s)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!a t (x:A). a SUBSET t /\ x IN a ==> x IN t`) THEN
    EXISTS_TAC `a:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?j. j IN components (moi_s34_trace tt kk (f1:real^N->real^3)
                                       ((cb:(real^N->bool)->real^3->bool) s)) /\
                    (a:real^3->bool) SUBSET j`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `pathstart (ha:real^1->real^3) IN
                  UNIONS (components (moi_s34_trace tt kk (f1:real^N->real^3)
                                        ((cb:(real^N->bool)->real^3->bool) s)))`
    MP_TAC THENL [ASM_REWRITE_TAC[GSYM UNIONS_COMPONENTS]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `j:real^3->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
    EXISTS_TAC `moi_s34_trace tt kk (f1:real^N->real^3)
                  ((cb:(real^N->bool)->real^3->bool) s)` THEN
    ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `pathstart (ha:real^1->real^3)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^N->bool) SUBSET s` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4FD_EDGE_IN_S THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                          `h:real^N->real^3`; `f1:real^N->real^3`;
                          `car:(real^N->bool)->real^3->bool`;
                          `(cb:(real^N->bool)->real^3->bool) s`;
                          `pathstart (ha:real^1->real^3)`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `!a t (x:A). a SUBSET t /\ x IN a ==> x IN t`) THEN
    EXISTS_TAC `moi_s34_trace tt kk (f1:real^N->real^3)
                  ((cb:(real^N->bool)->real^3->bool) s)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_s34_traced tt kk (f1:real^N->real^3) cb` THEN
  REWRITE_TAC[moi_s34_traced] THEN DISCH_THEN(MP_TAC o SPEC `s:real^N->bool`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `j:real^3->bool` o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `g:real^N->bool` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `p:real^3`) THEN
  UNDISCH_TAC `~(pathfinish ha:real^3 = pathstart ha)` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_S4FD_SING_TWO THEN
  MAP_EVERY EXISTS_TAC [`j:real^3->bool`;
                        `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)`;
                        `a:real^3->bool`; `p:real^3`] THEN
  ASM_REWRITE_TAC[]);;

(* Hence the unfolded Lemmas 9-10 (moi_s34_l910) hold under traced.         *)

let MOI_S4FD_TRACED_L910 = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fbinv tt kk h f1 car cb /\ moi_s34_traced tt kk f1 cb
     ==> moi_s34_l910 tt kk f1 cb`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_s34_l910] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `v:real^N`; `j:real^3->bool`] THEN
    STRIP_TAC THEN DISCH_TAC THEN MATCH_MP_TAC MOI_S4FD_L9_ONE THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                          `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                          `car:(real^N->bool)->real^3->bool`;
                          `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`;
                          `v:real^N`; `j:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `v:real^N`; `g:real^N->bool`;
                         `a:real^3->bool`; `aa:real^3->bool`] THEN
    STRIP_TAC THEN MATCH_MP_TAC MOI_S4FD_L10_ONE THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                          `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                          `car:(real^N->bool)->real^3->bool`;
                          `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`;
                          `g:real^N->bool`; `a:real^3->bool`; `aa:real^3->bool`] THEN
    ASM_REWRITE_TAC[]]);;

(* Points of a face ball in the tube lie in the face torus.                  *)

let MOI_S4FD_CB_NB = prove
 (`!(tt:(real^N->bool)->bool) kk h (f1:real^N->real^3) car s c.
     moi_s34_tube tt kk /\ moi_s34_fb1 tt kk h f1 car s c
     ==> c INTER IMAGE f1 (moi_s34_nb tt kk) SUBSET IMAGE f1 (moi_s34_ft tt kk s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`]
    MOI_S4L_GRAPH_TUBE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  FIRST_X_ASSUM(MP_TAC o el 3 o CONJUNCTS o REWRITE_RULE[moi_s34_fb1]) THEN
  REWRITE_TAC[moi_s34_ft; SUBSET; IN_INTER; IN_IMAGE; IN_UNIONS; IN_ELIM_THM;
              DISJOINT; EXTENSION; NOT_IN_EMPTY] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* No disk in the face torus bounds a trace component (MOI_S4T_COMP_NO_DISK *)
(* of pc_moi_s34_trace, with Lemmas 9-10 from traced).                      *)
(* ------------------------------------------------------------------------- *)

let MOI_S4FD_NO_DISK = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s j d.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fbinv tt kk h f1 car cb /\ moi_s34_traced tt kk f1 cb /\
     s IN moi_s34_simp kk (&2) /\
     j IN components (moi_s34_trace tt kk f1 (cb s)) /\
     contractible d /\ j SUBSET d /\ d SUBSET IMAGE f1 (moi_s34_ft tt kk s)
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`;
                 `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`]
    MOI_S4T_TRI_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:real^N` (X_CHOOSE_THEN `v2:real^N`
    (X_CHOOSE_TAC `v3:real^N`))) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`;
                 `cb:(real^N->bool)->real^3->bool`] MOI_S4FD_TRACED_L910) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s34_l910]) THEN
  MATCH_MP_TAC MOI_S4T_COMP_NO_DISK THEN
  MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                        `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                        `car:(real^N->bool)->real^3->bool`;
                        `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`;
                        `v1:real^N`; `v2:real^N`; `v3:real^N`; `j:real^3->bool`;
                        `d:real^3->bool`] THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* ------------------------------------------------------------------------- *)
(* A disk on the boundary sphere of a face ball, bounded by a trace          *)
(* component and meeting Bd N only there, lies outside the tube: its        *)
(* interior is connected and misses Bd N = f1(N) DIFF int f1(N), so it lies  *)
(* in the face torus (fb1) or misses int f1(N); the first is excluded by     *)
(* MOI_S4FD_NO_DISK.                                                         *)
(* ------------------------------------------------------------------------- *)

let MOI_S4FD_OUTSIDE = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s j d.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fbinv tt kk h f1 car cb /\ moi_s34_traced tt kk f1 cb /\
     s IN moi_s34_simp kk (&2) /\
     j IN components (moi_s34_trace tt kk f1 (cb s)) /\
     pl_cell_with_boundary 2 d j /\ d SUBSET frontier (cb s) /\
     d INTER IMAGE f1 (moi_s34_bd tt kk) = j
     ==> d INTER IMAGE f1 (moi_s34_nb tt kk) = j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`;
                 `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`]
    MOI_S4L_TRACE_COMP_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`;
                   `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`]
      MOI_S4T_TRI_EXISTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `v1:real^N` (X_CHOOSE_THEN `v2:real^N`
      (X_CHOOSE_THEN `v3:real^N` (STRIP_ASSUME_TAC o MATCH_MP MOI_S4T_TRI_BALLS)))) THEN
    ASM_SIMP_TAC[COMPACT_UNION];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s) SUBSET
                IMAGE f1 (moi_s34_nb tt kk) /\
                IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) SUBSET
                IMAGE f1 (moi_s34_nb tt kk)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`]
      MOI_S4L_GRAPH_TUBE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
    CONJ_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[moi_s34_ft] THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o el 3 o CONJUNCTS o REWRITE_RULE[moi_s34_frame] o
    check (fun th -> concl th = `moi_s34_frame tt kk h ep (f1:real^N->real^3) car`)) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `s:real^N->bool`;
                 `(cb:(real^N->bool)->real^3->bool) s`] MOI_S4FD_CB_NB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `moi_s34_trace tt kk (f1:real^N->real^3) ((cb:(real^N->bool)->real^3->bool) s)
                SUBSET IMAGE f1 (moi_s34_ft tt kk s)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s34_traced tt kk (f1:real^N->real^3) cb` THEN
    REWRITE_TAC[moi_s34_traced] THEN DISCH_THEN(MP_TAC o SPEC `s:real^N->bool`) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_PL_CELL2_TOPO) THEN
  SUBGOAL_THEN `(j:real^3->bool) SUBSET
                moi_s34_trace tt kk (f1:real^N->real^3) ((cb:(real^N->bool)->real^3->bool) s)`
  ASSUME_TAC THENL [ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(d:real^3->bool) DIFF j`;
                 `IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)`;
                 `(:real^3) DIFF interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk))`]
    MOI_S4L_CONNECTED_TWO_CLOSED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPEC `IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)` INTERIOR_SUBSET) THEN
      MP_TAC(SET_RULE
       `!d j fr c nn iw t:real^3->bool.
          d SUBSET fr /\ fr SUBSET c /\ c INTER nn SUBSET t /\ iw SUBSET nn
          ==> d DIFF j SUBSET t UNION ((:real^3) DIFF iw)`) THEN
      DISCH_THEN(MP_TAC o SPECL
       [`d:real^3->bool`; `j:real^3->bool`; `frontier ((cb:(real^N->bool)->real^3->bool) s)`;
        `(cb:(real^N->bool)->real^3->bool) s`;
        `IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)`;
        `interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk))`;
        `IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)`]) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
      MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN
      REWRITE_TAC[GSYM OPEN_CLOSED; OPEN_INTERIOR];
      MP_TAC(SET_RULE
       `!d j t nn iw ff:real^3->bool.
          t SUBSET nn /\ nn DIFF iw = ff /\ d INTER ff = j
          ==> (d DIFF j) INTER t INTER ((:real^3) DIFF iw) = {}`) THEN
      DISCH_THEN(MP_TAC o SPECL
       [`d:real^3->bool`; `j:real^3->bool`;
        `IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)`;
        `IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)`;
        `interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk))`;
        `IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`]) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN DISJ_CASES_TAC THENL
   [MATCH_MP_TAC(TAUT `F ==> p`) THEN MATCH_MP_TAC MOI_S4FD_NO_DISK THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                          `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                          `car:(real^N->bool)->real^3->bool`;
                          `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`;
                          `j:real^3->bool`; `d:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_S4T_CELL_CONTRACTIBLE]; ALL_TAC] THEN
    MP_TAC(SET_RULE
     `!d j tr t:real^3->bool. d DIFF j SUBSET t /\ j SUBSET tr /\ tr SUBSET t
                             ==> d SUBSET t`) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`j:real^3->bool`;
                          `moi_s34_trace tt kk (f1:real^N->real^3)
                             ((cb:(real^N->bool)->real^3->bool) s)`] THEN
    ASM_REWRITE_TAC[];
    MP_TAC(SET_RULE
     `!d j nn iw ff:real^3->bool.
        d DIFF j SUBSET (:real^3) DIFF iw /\ nn DIFF iw = ff /\ d INTER ff = j /\
        ff SUBSET nn
        ==> d INTER nn = j`) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk))`;
      `IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Under traced a trace component meets the rims in exactly three points,   *)
(* one on the rim of each edge of the face (the form of the vertex-arc      *)
(* lemma of pc_moi_s34_tvarc).                                              *)
(* ------------------------------------------------------------------------- *)

let MOI_S4FD_THREE_PTS = prove
 (`!(j:A->bool) tr rr ff a1 a2 a3 b12 b13 b23 p12 p13 p23.
     j SUBSET tr /\ tr SUBSET ff /\
     tr INTER rr SUBSET (b12 INTER ff) UNION (b13 INTER ff) UNION (b23 INTER ff) /\
     b12 INTER ff SUBSET rr /\ b13 INTER ff SUBSET rr /\ b23 INTER ff SUBSET rr /\
     b12 = a1 INTER a2 /\ b13 = a1 INTER a3 /\ b23 = a2 INTER a3 /\
     a1 INTER a2 INTER a3 = {} /\
     j INTER b12 = {p12} /\ j INTER b13 = {p13} /\ j INTER b23 = {p23}
     ==> j INTER rr = {p12,p13,p23} /\
         ~(p12 = p13) /\ ~(p12 = p23) /\ ~(p13 = p23)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_var(lhs(concl th))))) THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  ASM SET_TAC[]);;

let MOI_S4FD_PAIR_PT = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v1 v2 v3 j u w.
     moi_s4t_tri tt kk h ep f1 car cb s v1 v2 v3 /\ moi_s34_traced tt kk f1 cb /\
     j IN components (moi_s34_trace tt kk f1 (cb s)) /\
     u IN {v1,v2,v3} /\ w IN {v1,v2,v3} /\ ~(u = w)
     ==> ?p. j INTER IMAGE f1 (moi_s34_vb tt kk u INTER moi_s34_vb tt kk w) = {p}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[moi_s4t_tri] (ASSUME `moi_s4t_tri tt kk h ep (f1:real^N->real^3) car cb s v1 v2 v3`)) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`;
                 `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`;
                 `v1:real^N`; `v2:real^N`; `v3:real^N`; `u:real^N`; `w:real^N`]
    MOI_S4T_TRI_PAIR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `u:real^N`; `w:real^N`] MOI_S4L_EDGE_SD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(u:real^N) IN s /\ (w:real^N) IN s` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `{x | x IN s /\ {x} IN kk} = {v1:real^N,v2,v3}` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `u:real^N` th) THEN MP_TAC(SPEC `w:real^N` th)) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[u:real^N,w] SUBSET s` ASSUME_TAC THENL
   [SUBGOAL_THEN `(s:real^N->bool) IN kk` ASSUME_TAC THENL
     [UNDISCH_TAC `(s:real^N->bool) IN moi_s34_simp kk (&2)` THEN
      SIMP_TAC[moi_s34_simp; IN_ELIM_THM];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `s:real^N->bool`] MOI_S4A_KK_SIMPLEX) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
    UNDISCH_TAC `(u:real^N) IN s` THEN UNDISCH_TAC `(w:real^N) IN s` THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_s34_traced tt kk (f1:real^N->real^3) cb` THEN
  REWRITE_TAC[moi_s34_traced] THEN DISCH_THEN(MP_TAC o SPEC `s:real^N->bool`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `j:real^3->bool` o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `segment[u:real^N,w]` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[]);;

let MOI_S4FD_RIMS_THREE = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v1 v2 v3 j.
     moi_s4t_tri tt kk h ep f1 car cb s v1 v2 v3 /\ moi_s34_traced tt kk f1 cb /\
     j IN components (moi_s34_trace tt kk f1 (cb s))
     ==> CARD (j INTER moi_s34_rims tt kk f1) = 3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(v1:real^N = v2) /\ ~(v1 = v3) /\ ~(v2 = v3)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_s4t_tri]; ALL_TAC] THEN
  MAP_EVERY (fun (u,w) ->
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`;
                   `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`;
                   `v1:real^N`; `v2:real^N`; `v3:real^N`; `j:real^3->bool`; u; w]
      MOI_S4FD_PAIR_PT) THEN
    ASM_REWRITE_TAC[IN_INSERT] THEN STRIP_TAC)
   [`v1:real^N`,`v2:real^N`; `v1:real^N`,`v3:real^N`; `v2:real^N`,`v3:real^N`] THEN
  MP_TAC(ISPECL [`j:real^3->bool`;
                 `moi_s34_trace tt kk (f1:real^N->real^3) ((cb:(real^N->bool)->real^3->bool) s)`;
                 `moi_s34_rims tt kk (f1:real^N->real^3)`;
                 `IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`;
                 `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v1)`;
                 `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v2)`;
                 `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v3)`;
                 `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v1 INTER moi_s34_vb tt kk v2)`;
                 `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v1 INTER moi_s34_vb tt kk v3)`;
                 `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v2 INTER moi_s34_vb tt kk v3)`;
                 `p:real^3`; `p':real^3`; `p'':real^3`] MOI_S4FD_THREE_PTS) THEN
  ANTS_TAC THENL
   [ALL_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV] THEN
  STRIP_ASSUME_TAC(MATCH_MP MOI_S4T_TRI_BALLS (ASSUME `moi_s4t_tri tt kk h ep (f1:real^N->real^3) car cb s v1 v2 v3`)) THEN
  MP_TAC(MATCH_MP MOI_S4T_TRI_TRACE (ASSUME `moi_s4t_tri tt kk h ep (f1:real^N->real^3) car cb s v1 v2 v3`)) THEN
  DISCH_THEN(fun th -> MP_TAC(el 6 (CONJUNCTS th))) THEN DISCH_TAC THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[moi_s4t_tri] (ASSUME `moi_s4t_tri tt kk h ep (f1:real^N->real^3) car cb s v1 v2 v3`)) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`] MOI_S4L_IMAGES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o el 2 o CONJUNCTS) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`]
    MOI_S4L_GRAPH_TUBE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "vbn") (K ALL_TAC)))) THEN
  SUBGOAL_THEN
   `!a b:real^N. {a} IN kk /\ {b} IN kk
                 ==> IMAGE (f1:real^N->real^3)
                       (moi_s34_vb tt kk a INTER moi_s34_vb tt kk b INTER moi_s34_bd tt kk) =
                     IMAGE f1 (moi_s34_vb tt kk a INTER moi_s34_vb tt kk b) INTER
                     IMAGE f1 (moi_s34_bd tt kk)`
  (LABEL_TAC "rimeq") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM INTER_ASSOC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
      is_imp(snd(strip_forall(concl th))))) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `!a b n:real^N->bool. a SUBSET n ==> a INTER b SUBSET n`) THEN
    USE_THEN "vbn" (MP_TAC o SPEC `a:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY (fun (u,w) ->
    USE_THEN "rimeq" (MP_TAC o SPECL [u; w]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)])
   [`v1:real^N`,`v2:real^N`; `v1:real^N`,`v3:real^N`; `v2:real^N`,`v3:real^N`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC IN_COMPONENTS_SUBSET THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[moi_s34_trace; INTER_SUBSET]]);;

(* The arc of a trace component in a vertex ball: MOI_S4T_COMP_VERTEX_ARC   *)
(* (pc_moi_s34_tvarc), with Lemmas 9-10 and the three rim points from       *)
(* traced.                                                                  *)

let MOI_S4FD_VERTEX_ARC = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s j v.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fbinv tt kk h f1 car cb /\ moi_s34_traced tt kk f1 cb /\
     s IN moi_s34_simp kk (&2) /\
     j IN components (moi_s34_trace tt kk f1 (cb s)) /\
     {v} IN kk /\ v IN s
     ==> pl_cell_with_boundary 1 (j INTER IMAGE f1 (moi_s34_vb tt kk v))
           (UNIONS {j INTER IMAGE f1 (moi_s34_sd tt kk g) | g |
                    g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET s})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`;
                 `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`]
    MOI_S4T_TRI_EXISTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:real^N` (X_CHOOSE_THEN `v2:real^N`
    (X_CHOOSE_TAC `v3:real^N`))) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`;
                 `cb:(real^N->bool)->real^3->bool`] MOI_S4FD_TRACED_L910) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s34_l910]) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`;
                 `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`;
                 `v1:real^N`; `v2:real^N`; `v3:real^N`; `j:real^3->bool`]
    MOI_S4FD_RIMS_THREE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `(v:real^N) IN {v1,v2,v3}` ASSUME_TAC THENL
   [MP_TAC(REWRITE_RULE[moi_s4t_tri]
      (ASSUME `moi_s4t_tri tt kk h ep (f1:real^N->real^3) car cb s v1 v2 v3`)) THEN
    DISCH_THEN(MP_TAC o el 7 o CONJUNCTS) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^N`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S4T_COMP_VERTEX_ARC THEN
  MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`;
                        `car:(real^N->bool)->real^3->bool`;
                        `cb:(real^N->bool)->real^3->bool`;
                        `v1:real^N`; `v2:real^N`; `v3:real^N`] THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* ------------------------------------------------------------------------- *)
(* The face disk of one 2-simplex s: an innermost disk of the boundary      *)
(* sphere of cb s cut along the trace components.                           *)
(* ------------------------------------------------------------------------- *)

let MOI_S4FD_FACE = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fbinv tt kk h f1 car cb /\ moi_s34_traced tt kk f1 cb /\
     s IN moi_s34_simp kk (&2)
     ==> ?d. d SUBSET cb s /\
             DISJOINT d (interior (IMAGE f1 (moi_s34_nb tt kk))) /\
             pl_cell_with_boundary 2 d (d INTER IMAGE f1 (moi_s34_bd tt kk)) /\
             d INTER IMAGE f1 (moi_s34_nb tt kk) = d INTER IMAGE f1 (moi_s34_bd tt kk) /\
             d SUBSET car s /\
             (!w. {w} IN kk /\ ~(w IN s)
                  ==> DISJOINT d (IMAGE f1 (moi_s34_vb tt kk w))) /\
             (!v. {v} IN kk /\ v IN s
                  ==> pl_cell_with_boundary 1 (d INTER IMAGE f1 (moi_s34_vb tt kk v))
                        (UNIONS {d INTER IMAGE f1 (moi_s34_sd tt kk g) | g |
                                 g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET s})) /\
             (!g. g IN moi_s34_simp kk (&1) /\ g SUBSET s
                  ==> ?p. d INTER IMAGE f1 (moi_s34_sd tt kk g) = {p} /\
                          pl_curve_crossing_at (IMAGE f1 (moi_s34_bd tt kk))
                            (d INTER IMAGE f1 (moi_s34_bd tt kk))
                            (IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)) p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`;
                 `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`]
    MOI_S4L_TRACE_COMP_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `s:real^N->bool` o GEN_REWRITE_RULE I [moi_s34_traced] o
    check (fun th -> concl th = `moi_s34_traced tt kk (f1:real^N->real^3) cb`)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "trc"))) THEN
  SUBGOAL_THEN `pl_sphere 2 (frontier ((cb:(real^N->bool)->real^3->bool) s))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4L_BALL_FRONTIER_SPHERE THEN
    UNDISCH_TAC `moi_s34_fb1 tt kk h (f1:real^N->real^3) car s
                   ((cb:(real^N->bool)->real^3->bool) s)` THEN
    REWRITE_TAC[moi_s34_fb1] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`frontier ((cb:(real^N->bool)->real^3->bool) s)`;
                 `components (moi_s34_trace tt kk (f1:real^N->real^3)
                                ((cb:(real^N->bool)->real^3->bool) s))`]
    MOI_S4FD_INNERMOST) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [ASM_REWRITE_TAC[COMPONENTS_EQ_EMPTY];
      X_GEN_TAC `k:real^3->bool` THEN DISCH_TAC THEN CONJ_TAC THENL
       [FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN ASM_REWRITE_TAC[] THEN NO_TAC);
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `moi_s34_trace tt kk (f1:real^N->real^3)
                      ((cb:(real^N->bool)->real^3->bool) s)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC IN_COMPONENTS_SUBSET THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[moi_s34_trace; INTER_SUBSET]]];
      MAP_EVERY X_GEN_TAC [`k:real^3->bool`; `k':real^3->bool`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`moi_s34_trace tt kk (f1:real^N->real^3)
                        ((cb:(real^N->bool)->real^3->bool) s)`;
                     `k:real^3->bool`; `k':real^3->bool`] COMPONENTS_NONOVERLAP) THEN
      ASM_REWRITE_TAC[DISJOINT]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:real^3->bool` (X_CHOOSE_THEN `d:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_PL_CELL2_TOPO o
    check (fun th -> concl th = `pl_cell_with_boundary 2 (d:real^3->bool) j`)) THEN
  SUBGOAL_THEN `d INTER IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) = j` ASSUME_TAC THENL
   [MP_TAC(SET_RULE
     `!d ff fr tr (j:real^3->bool) cc.
        d SUBSET fr /\ tr = fr INTER ff /\ UNIONS cc = tr /\ j IN cc /\ j SUBSET d /\
        (!j'. j' IN cc /\ ~(j' = j) ==> DISJOINT d j')
        ==> d INTER ff = j`) THEN
    DISCH_THEN(MP_TAC o SPECL
     [`d:real^3->bool`; `IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`;
      `frontier ((cb:(real^N->bool)->real^3->bool) s)`;
      `moi_s34_trace tt kk (f1:real^N->real^3) ((cb:(real^N->bool)->real^3->bool) s)`;
      `j:real^3->bool`;
      `components (moi_s34_trace tt kk (f1:real^N->real^3)
                     ((cb:(real^N->bool)->real^3->bool) s))`]) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [REWRITE_TAC[moi_s34_trace];
      MATCH_ACCEPT_TAC(GSYM UNIONS_COMPONENTS)];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`;
                 `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`;
                 `j:real^3->bool`; `d:real^3->bool`] MOI_S4FD_OUTSIDE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`] MOI_S4L_FRAME_F1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_s34_fb1] o
    check (fun th -> concl th = `moi_s34_fb1 tt kk h (f1:real^N->real^3) car s
                                   ((cb:(real^N->bool)->real^3->bool) s)`)) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`] MOI_S4L_IMAGES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> LABEL_TAC "imi" (el 2 (CONJUNCTS th)) THEN
                       LABEL_TAC "sdn" (el 6 (CONJUNCTS th))) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`]
    MOI_S4L_GRAPH_TUBE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> LABEL_TAC "bdn" (CONJUNCT1(CONJUNCT2 th)) THEN
                       LABEL_TAC "vbn" (CONJUNCT1(CONJUNCT2(CONJUNCT2 th)))) THEN
  SUBGOAL_THEN `!x:real^3->bool. x SUBSET IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)
                                 ==> d INTER x = j INTER x`
  (LABEL_TAC "dj") THENL
   [X_GEN_TAC `x:real^3->bool` THEN DISCH_TAC THEN
    MP_TAC(SET_RULE `!d nn j x:real^3->bool.
                       d INTER nn = j /\ x SUBSET nn ==> d INTER x = j INTER x`) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `d:real^3->bool` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `frontier ((cb:(real^N->bool)->real^3->bool) s)` THEN ASM_REWRITE_TAC[];
    MP_TAC(SET_RULE `!d nn iw ff j:real^3->bool.
                       d INTER nn = j /\ d INTER ff = j /\ ff INTER iw = {} /\ iw SUBSET nn
                       ==> DISJOINT d iw`) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)`;
                          `IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`;
                          `j:real^3->bool`] THEN
    ASM_REWRITE_TAC[INTERIOR_SUBSET];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `frontier ((cb:(real^N->bool)->real^3->bool) s)` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
    MATCH_MP_TAC(SET_RULE `!d c x:real^3->bool. d SUBSET c /\ DISJOINT c x
                                                ==> DISJOINT d x`) THEN
    EXISTS_TAC `(cb:(real^N->bool)->real^3->bool) s` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `frontier ((cb:(real^N->bool)->real^3->bool) s)` THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN ASM_REWRITE_TAC[] THEN NO_TAC)];
    X_GEN_TAC `v:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `d INTER IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) =
                  j INTER IMAGE f1 (moi_s34_vb tt kk v)` SUBST1_TAC THENL
     [USE_THEN "dj" MATCH_MP_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      USE_THEN "vbn" (MP_TAC o SPEC `v:real^N`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `{d INTER IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) | g |
       g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET s} =
      {j INTER IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) | g |
       g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET s}` SUBST1_TAC THENL
     [MATCH_MP_TAC MOI_S4A_GSPEC_EQ THEN X_GEN_TAC `g:real^N->bool` THEN STRIP_TAC THEN
      USE_THEN "dj" MATCH_MP_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      USE_THEN "sdn" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_S4FD_VERTEX_ARC THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`;
                          `car:(real^N->bool)->real^3->bool`;
                          `cb:(real^N->bool)->real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `g:real^N->bool` THEN STRIP_TAC THEN
    USE_THEN "trc" (MP_TAC o SPEC `j:real^3->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `g:real^N->bool` o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `p:real^3`) THEN
    EXISTS_TAC `p:real^3` THEN
    SUBGOAL_THEN `p IN (j:real^3->bool) /\
                  p IN IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!j x (p:A). j INTER x = {p} ==> p IN j /\ p IN x`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `j INTER IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)` THEN
      CONJ_TAC THENL
       [USE_THEN "dj" MATCH_MP_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN
        USE_THEN "sdn" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`moi_s34_trace tt kk (f1:real^N->real^3)
                      ((cb:(real^N->bool)->real^3->bool) s)`;
                   `j:real^3->bool`] MOI_S4FD_COMP_NBHD) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(j:real^3->bool) SUBSET
                  moi_s34_trace tt kk (f1:real^N->real^3)
                    ((cb:(real^N->bool)->real^3->bool) s)` ASSUME_TAC THENL
     [MATCH_MP_TAC IN_COMPONENTS_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(p:real^3) IN moi_s34_trace tt kk (f1:real^N->real^3)
                                  ((cb:(real^N->bool)->real^3->bool) s)` ASSUME_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!a t (x:A). a SUBSET t /\ x IN a ==> x IN t`) THEN
      EXISTS_TAC `j:real^3->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(p:real^3) IN frontier ((cb:(real^N->bool)->real^3->bool) s) /\
                  p IN IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(p:real^3) IN moi_s34_trace tt kk (f1:real^N->real^3)
                                   ((cb:(real^N->bool)->real^3->bool) s)` THEN
      REWRITE_TAC[moi_s34_trace; IN_INTER] THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBST1_TAC(ASSUME `d INTER IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) = j`) THEN
    MATCH_MP_TAC MOI_FGB_CURVE_CROSSING_LOCAL THEN
    MAP_EVERY EXISTS_TAC
     [`moi_s34_trace tt kk (f1:real^N->real^3) ((cb:(real^N->bool)->real^3->bool) s)`;
      `IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) INTER u`] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
        try fst(dest_const(fst(strip_comb(snd(dest_imp(snd(strip_forall(concl th)))))))) =
            "pl_curve_crossing_at" with Failure _ -> false)) THEN
      ASM_REWRITE_TAC[IN_INTER] THEN
      USE_THEN "imi" (MP_TAC o SPECL [`moi_s34_sd tt kk (g:real^N->bool)`;
                                      `moi_s34_bd (tt:(real^N->bool)->bool) kk`]) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL [USE_THEN "sdn" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
                        USE_THEN "bdn" ACCEPT_TAC];
        DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[IN_INTER]];
      MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[IN_INTER] THEN
      MATCH_MP_TAC(SET_RULE `!a t (x:A). a SUBSET t /\ x IN a ==> x IN t`) THEN
      EXISTS_TAC `j:real^3->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(SET_RULE `!tr j u ff:real^3->bool.
                               tr INTER u = j INTER u
                               ==> tr INTER (ff INTER u) = j INTER (ff INTER u)`) THEN
      ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The theorem FDISK: the face disks D_s'' of Sec 34 (p.244).  Face disks of *)
(* different faces are disjoint: each lies in its face ball and misses      *)
(* int f1(N), and different face balls meet only in int f1(N) (fb2).        *)
(* ------------------------------------------------------------------------- *)

let FDISK = prove
 (MOI_S34_FDISK,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`;
                 `cb:(real^N->bool)->real^3->bool`] MOI_S4FD_FACE) THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  GEN_REWRITE_TAC LAND_CONV [SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `dd:(real^N->bool)->real^3->bool`) THEN
  EXISTS_TAC `dd:(real^N->bool)->real^3->bool` THEN
  REWRITE_TAC[moi_s34_fdisk] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o CONJUNCT2 o CONJUNCT2) THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `s':real^N->bool`] THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> MP_TAC(SPEC `s:real^N->bool` th) THEN
                        MP_TAC(SPEC `s':real^N->bool` th)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  UNDISCH_TAC `moi_s34_fbinv tt kk h (f1:real^N->real^3) car cb` THEN
  REWRITE_TAC[moi_s34_fbinv] THEN
  DISCH_THEN(MP_TAC o SPECL [`s:real^N->bool`; `s':real^N->bool`] o CONJUNCT2) THEN
  ASM_REWRITE_TAC[moi_s34_fb2] THEN
  MP_TAC(SET_RULE
   `!d d' c c' iw:real^3->bool.
      d SUBSET c /\ d' SUBSET c' /\ DISJOINT d iw /\
      (c INTER c' SUBSET iw) ==> DISJOINT d d'`) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`(dd:(real^N->bool)->real^3->bool) s`; `(dd:(real^N->bool)->real^3->bool) s'`;
    `(cb:(real^N->bool)->real^3->bool) s`; `(cb:(real^N->bool)->real^3->bool) s'`;
    `interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk))`]) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;


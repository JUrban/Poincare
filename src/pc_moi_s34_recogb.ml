needs "src/pc_moi_s34_recoga.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* pc_moi_s34_recogb: the target cells of the Sec 34 cell diagram meet like *)
(* their source cells, are locally finite and small (Moise, Geometric        *)
(* Topology in Dimensions 2 and 3, GTM 47, Sec 34, pp.244-246, stages (1)-  *)
(* (7), target side).  Main theorem (pc_moi_s34_stmt.ml):                    *)
(*   RECOG_B = MOI_S34_RECOG_B                                              *)
(* Route.                                                                    *)
(* (1) Open cells oc l = b l minus the targets of the proper faces of l;    *)
(* b l is the union of the open cells of the faces of l (induction on the   *)
(* kind dimension, from RECOG_A of pc_moi_s34_recoga).                      *)
(* (2) Profiles: a point of an open cell decides which face disks, tetra    *)
(* balls, splitting disks and vertex balls contain it; the profile          *)
(* determines the label, so distinct open cells are disjoint, and           *)
(* b l INTER b m is the union of the targets of the common faces.  The      *)
(* outer kinds use that cell interiors are open in a PL 2-sphere            *)
(* (DISK_COMPLEMENT) and in a PL circle (connectedness of complements).     *)
(* (3) Local finiteness from the frame carriers (a ball around a point off  *)
(* the open tetra balls meets the carriers of finitely many simplices).     *)
(* (4) The size bound from the frame: every target and the h-image of its   *)
(* source cell lie in convex hull (car q) for a simplex q at the point.    *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The hypothesis bundle and the elementary meeting relations of             *)
(* the targets (from the frame, the face disks and the tetra balls).         *)
(* ------------------------------------------------------------------------- *)

let moi_s4h_hyp = new_definition
 `moi_s4h_hyp (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool)
              (h:real^N->real^3) (ep:real^N->real) (f1:real^N->real^3)
              (car:(real^N->bool)->real^3->bool) (dd:(real^N->bool)->real^3->bool)
              (rr:(real^N->bool)->real^3->bool) <=>
   moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
   moi_s34_fdisk tt kk f1 car dd /\ moi_s34_resid tt kk f1 car dd rr /\
   moi_s34_outer tt kk f1 dd rr`;;

(* Tactic: add the five stage hypotheses from a moi_s4h_hyp assumption. *)

let MOI_S4H_UNFOLD_TAC : tactic =
  FIRST_ASSUM(fun th ->
    let f,_ = strip_comb (concl th) in
    if is_const f && fst(dest_const f) = "moi_s4h_hyp"
    then STRIP_ASSUME_TAC (REWRITE_RULE[moi_s4h_hyp] th) else NO_TAC);;

let MOI_S4H_HYP = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr.
     moi_s4h_hyp tt kk h ep f1 car dd rr
     ==> moi_s34_tube tt kk /\
         (!x y. x IN moi_s34_nb tt kk /\ y IN moi_s34_nb tt kk /\ f1 x = f1 y ==> x = y) /\
         f1 continuous_on moi_s34_nb tt kk`,
  REWRITE_TAC[moi_s4h_hyp] THEN MESON_TAC[MOI_S4G_FRAME_FACTS]);;

(* Images under f1 of subsets of N meet in the image of the intersection. *)

let MOI_S4H_IMG_INTER = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr A B y.
     moi_s4h_hyp tt kk h ep f1 car dd rr /\
     A SUBSET moi_s34_nb tt kk /\ B SUBSET moi_s34_nb tt kk /\
     y IN IMAGE f1 A /\ y IN IMAGE f1 B
     ==> y IN IMAGE f1 (A INTER B)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o MATCH_MP MOI_S4H_HYP) THEN
  UNDISCH_TAC `(y:real^3) IN IMAGE f1 (A:real^N->bool)` THEN
  UNDISCH_TAC `(y:real^3) IN IMAGE f1 (B:real^N->bool)` THEN
  UNDISCH_TAC `(A:real^N->bool) SUBSET moi_s34_nb tt kk` THEN
  UNDISCH_TAC `(B:real^N->bool) SUBSET moi_s34_nb tt kk` THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; IN_INTER] THEN MESON_TAC[]);;

(* R1: two vertex balls meet in the splitting disk of their edge. *)

let MOI_S4H_VB_VB = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr v w y.
     moi_s4h_hyp tt kk h ep f1 car dd rr /\ {v} IN kk /\ {w} IN kk /\ ~(v = w) /\
     y IN IMAGE f1 (moi_s34_vb tt kk v) /\ y IN IMAGE f1 (moi_s34_vb tt kk w)
     ==> ?g. g IN moi_s34_simp kk (&1) /\ v IN g /\ w IN g /\
             y IN IMAGE f1 (moi_s34_sd tt kk g)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4H_HYP) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                 `moi_s34_vb tt kk (v:real^N)`; `moi_s34_vb tt kk (w:real^N)`; `y:real^3`]
                MOI_S4H_IMG_INTER) THEN
  ASM_SIMP_TAC[MOI_S4G_VB_NB] THEN DISCH_TAC THEN
  SUBGOAL_THEN `graph_in_complex (tt:(real^N->bool)->bool) (skeleton 1 kk)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_s34_tube]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GRAPH_TUBE_DUAL_CELLS) THEN
  REWRITE_TAC[GSYM moi_s34_vb] THEN
  DISCH_THEN(MP_TAC o SPECL [`v:real^N`; `w:real^N`] o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[skeleton; IN_ELIM_THM; AFF_DIM_SING; INT_POS] THEN
  ASM_CASES_TAC `segment[v:real^N,w] IN kk` THEN ASM_REWRITE_TAC[] THENL
   [DISCH_THEN(K ALL_TAC) THEN EXISTS_TAC `segment[v:real^N,w]` THEN
    REWRITE_TAC[ENDS_IN_SEGMENT] THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[moi_s34_simp; IN_ELIM_THM; SEGMENT_CONVEX_HULL; AFF_DIM_CONVEX_HULL;
                      AFF_DIM_2] THEN
      UNDISCH_TAC `segment[v:real^N,w] IN kk` THEN REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
      SIMP_TAC[];
      SUBGOAL_THEN `moi_s34_sd tt kk (segment[v,w]) =
                    moi_s34_vb tt kk v INTER moi_s34_vb tt kk (w:real^N)` SUBST1_TAC THENL
       [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC MOI_S4A_SD_EDGE THEN
        ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL];
        ASM_REWRITE_TAC[]]];
    DISCH_TAC THEN UNDISCH_TAC `(y:real^3) IN IMAGE f1
       (moi_s34_vb tt kk v INTER moi_s34_vb tt kk (w:real^N))` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; NOT_IN_EMPTY]]);;

(* R2: a vertex ball misses the splitting disks of the edges not at v. *)

let MOI_S4H_VB_SD_EMPTY = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr v g.
     moi_s4h_hyp tt kk h ep f1 car dd rr /\ {v} IN kk /\ g IN moi_s34_simp kk (&1) /\
     ~(v IN g)
     ==> IMAGE f1 (moi_s34_vb tt kk v) INTER IMAGE f1 (moi_s34_sd tt kk g) = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4H_HYP) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `g:real^N->bool`] MOI_S4O_EDGE_FORM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `moi_s34_sd tt kk g = moi_s34_vb tt kk a INTER moi_s34_vb tt kk (b:real^N)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC MOI_S4A_SD_EDGE THEN
    ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(v:real^N = a) /\ ~(v = b)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ENDS_IN_SEGMENT]; ALL_TAC] THEN
  SUBGOAL_THEN `graph_in_complex (tt:(real^N->bool)->bool) (skeleton 1 kk)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_s34_tube]; ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `skeleton 1 (kk:(real^N->bool)->bool)`;
                 `v:real^N`; `a:real^N`; `b:real^N`] TUBE_TRIPLE) THEN
  ASM_REWRITE_TAC[GSYM moi_s34_vb; skeleton; IN_ELIM_THM; AFF_DIM_SING; INT_POS] THEN
  DISCH_TAC THEN REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_INTER] THEN
  X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                 `moi_s34_vb tt kk (v:real^N)`; `moi_s34_sd tt kk (g:real^N->bool)`; `y:real^3`]
                MOI_S4H_IMG_INTER) THEN
  ASM_SIMP_TAC[MOI_S4G_VB_NB; MOI_S4G_SD_NB] THEN
  ASM_REWRITE_TAC[INTER_ASSOC; IMAGE_CLAUSES; NOT_IN_EMPTY]);;

(* R3: splitting disks of different edges are disjoint. *)

let MOI_S4H_SD_SD_EMPTY = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr g g'.
     moi_s4h_hyp tt kk h ep f1 car dd rr /\ g IN moi_s34_simp kk (&1) /\
     g' IN moi_s34_simp kk (&1) /\ ~(g = g')
     ==> IMAGE f1 (moi_s34_sd tt kk g) INTER IMAGE f1 (moi_s34_sd tt kk g') = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4H_HYP) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `g':real^N->bool`] MOI_S4O_EDGE_FORM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^N` (X_CHOOSE_THEN `d:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `?w. {w} IN kk /\ w IN g' /\ ~((w:real^N) IN g)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `g:real^N->bool`] MOI_S4O_EDGE_FORM) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `~((c:real^N) IN g) \/ ~((d:real^N) IN g)` MP_TAC THENL
     [REWRITE_TAC[TAUT `~p \/ ~q <=> ~(p /\ q)`] THEN STRIP_TAC THEN
      UNDISCH_TAC `~(g:real^N->bool = g')` THEN REWRITE_TAC[] THEN
      CONV_TAC SYM_CONV THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                     `g':real^N->bool`; `g:real^N->bool`; `1`; `1`] MOI_S4G_NEST) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[CONVEX_CONTAINS_SEGMENT; CONVEX_SEGMENT];
      ASM_MESON_TAC[ENDS_IN_SEGMENT]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                 `w:real^N`; `g:real^N->bool`] MOI_S4H_VB_SD_EMPTY) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `g':real^N->bool`;
                 `w:real^N`] MOI_S4G_SD_SUB_VB) THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let MOI_S4H_SIMP_KK = prove
 (`!(kk:(real^N->bool)->bool) n s. s IN moi_s34_simp kk n ==> s IN kk`,
  REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_S4H_KK_CONVEX = prove
 (`!(tt:(real^N->bool)->bool) kk q. moi_s34_tube tt kk /\ q IN kk ==> convex q`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `q:real^N->bool`] MOI_S4A_KK_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[CONVEX_CONVEX_HULL]);;

(* An edge not contained in a simplex q of kk has a vertex outside q. *)

let MOI_S4H_EDGE_OUT = prove
 (`!(tt:(real^N->bool)->bool) kk g q.
     moi_s34_tube tt kk /\ g IN moi_s34_simp kk (&1) /\ q IN kk /\ ~(g SUBSET q)
     ==> ?w. {w} IN kk /\ w IN g /\ ~(w IN q)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `g:real^N->bool`] MOI_S4O_EDGE_FORM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `convex(q:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4H_KK_CONVEX]; ALL_TAC] THEN
  ASM_CASES_TAC `(a:real^N) IN q` THENL
   [EXISTS_TAC `b:real^N` THEN ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN
    DISCH_TAC THEN UNDISCH_TAC `~(g:real^N->bool SUBSET q)` THEN
    ASM_MESON_TAC[CONVEX_CONTAINS_SEGMENT];
    EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[ENDS_IN_SEGMENT]]);;

(* Facts on a face disk dd s. *)

let MOI_S4H_DD_FACTS = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr s.
     moi_s4h_hyp tt kk h ep f1 car dd rr /\ s IN moi_s34_simp kk (&2)
     ==> dd s INTER IMAGE f1 (moi_s34_nb tt kk) = dd s INTER IMAGE f1 (moi_s34_bd tt kk) /\
         dd s SUBSET car s /\ compact (dd s) /\
         (!w. {w} IN kk /\ ~(w IN s) ==> dd s INTER IMAGE f1 (moi_s34_vb tt kk w) = {}) /\
         (!s'. s' IN moi_s34_simp kk (&2) /\ ~(s' = s) ==> dd s INTER dd s' = {}) /\
         (!g. g IN moi_s34_simp kk (&1) /\ ~(g SUBSET s)
              ==> dd s INTER IMAGE f1 (moi_s34_sd tt kk g) = {})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4h_hyp] THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_s34_fdisk tt kk (f1:real^N->real^3) car dd` THEN
  REWRITE_TAC[moi_s34_fdisk] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `s:real^N->bool`) (LABEL_TAC "dd2")) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    ASSUME_TAC (el 0 cs) THEN ASSUME_TAC (el 1 cs) THEN ASSUME_TAC (el 2 cs) THEN
    LABEL_TAC "dj" (el 3 cs)) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!w. {w} IN kk /\ ~(w IN s)
                    ==> (dd:(real^N->bool)->real^3->bool) s INTER
                        IMAGE f1 (moi_s34_vb tt kk w) = {}`
  (LABEL_TAC "dvb") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM DISJOINT] THEN USE_THEN "dj" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_S4G_CELL_FACTS];
    REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM DISJOINT] THEN USE_THEN "dd2" MATCH_MP_TAC THEN
    ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `g:real^N->bool`;
                   `s:real^N->bool`] MOI_S4H_EDGE_OUT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[MOI_S4H_SIMP_KK]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `g:real^N->bool`;
                   `w:real^N`] MOI_S4G_SD_SUB_VB) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "dvb" (MP_TAC o SPEC `w:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SET_TAC[]]]);;

(* Facts on a tetra ball rr r. *)

let MOI_S4H_RR_FACTS = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr r.
     moi_s4h_hyp tt kk h ep f1 car dd rr /\ r IN moi_s34_simp kk (&3)
     ==> rr r INTER IMAGE f1 (moi_s34_nb tt kk) = rr r INTER IMAGE f1 (moi_s34_bd tt kk) /\
         rr r SUBSET convex hull (car r) /\ compact (rr r) /\ pl_ball 3 (rr r) /\
         frontier (rr r) =
         UNIONS {dd s | s | s IN moi_s34_simp kk (&2) /\ s SUBSET r} UNION
         (rr r INTER IMAGE f1 (moi_s34_bd tt kk)) /\
         (!w. {w} IN kk /\ ~(w IN r) ==> rr r INTER IMAGE f1 (moi_s34_vb tt kk w) = {}) /\
         (!s. s IN moi_s34_simp kk (&2) /\ ~(s SUBSET r) ==> rr r INTER dd s = {}) /\
         (!s. s IN moi_s34_simp kk (&2) /\ s SUBSET r ==> dd s SUBSET rr r) /\
         (!r'. r' IN moi_s34_simp kk (&3) /\ ~(r' = r)
               ==> rr r INTER rr r' =
                   UNIONS {dd s | s | s IN moi_s34_simp kk (&2) /\ s SUBSET r /\
                                      s SUBSET r'}) /\
         (!g. g IN moi_s34_simp kk (&1) /\ ~(g SUBSET r)
              ==> rr r INTER IMAGE f1 (moi_s34_sd tt kk g) = {})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4h_hyp] THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_s34_resid tt kk (f1:real^N->real^3) car dd rr` THEN
  REWRITE_TAC[moi_s34_resid] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `r:real^N->bool`)
    (CONJUNCTS_THEN2 (LABEL_TAC "rr2") (K ALL_TAC))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    ASSUME_TAC (el 0 cs) THEN ASSUME_TAC (el 1 cs) THEN LABEL_TAC "fr" (el 2 cs) THEN
    ASSUME_TAC (el 3 cs) THEN LABEL_TAC "dj" (el 6 cs) THEN LABEL_TAC "djd" (el 7 cs)) THEN
  SUBGOAL_THEN `compact((rr:(real^N->bool)->real^3->bool) r)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `(rr:(real^N->bool)->real^3->bool) r` MOI_S4G_BALL_CELL) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; MESON_TAC[MOI_S4G_CELL_FACTS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. {w} IN kk /\ ~(w IN r)
                    ==> (rr:(real^N->bool)->real^3->bool) r INTER
                        IMAGE f1 (moi_s34_vb tt kk w) = {}`
  (LABEL_TAC "rvb") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM DISJOINT] THEN USE_THEN "dj" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM DISJOINT] THEN USE_THEN "djd" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `frontier((rr:(real^N->bool)->real^3->bool) r)` THEN
    ASM_SIMP_TAC[FRONTIER_SUBSET_CLOSED; COMPACT_IMP_CLOSED] THEN
    USE_THEN "fr" SUBST1_TAC THEN
    MATCH_MP_TAC(SET_RULE `!a b c:real^3->bool. a SUBSET b ==> a SUBSET b UNION c`) THEN
    GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
    ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN USE_THEN "rr2" MATCH_MP_TAC THEN ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `g:real^N->bool`;
                   `r:real^N->bool`] MOI_S4H_EDGE_OUT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[MOI_S4H_SIMP_KK]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `g:real^N->bool`;
                   `w:real^N`] MOI_S4G_SD_SUB_VB) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "rvb" (MP_TAC o SPEC `w:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SET_TAC[]]]);;

(* Every face disk lies in a tetra ball (kk is pure). *)

let MOI_S4H_DD_IN_RR = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr s.
     moi_s4h_hyp tt kk h ep f1 car dd rr /\ s IN moi_s34_simp kk (&2)
     ==> ?r. r IN moi_s34_simp kk (&3) /\ s SUBSET r /\ dd s SUBSET rr r`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4H_HYP) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `s:real^N->bool`;
                 `2`] MOI_S4G_SIMP_VERTS) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?v:real^N. v IN V` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN DISCH_TAC THEN
    UNDISCH_TAC `CARD(V:real^N->bool) = 3` THEN ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `{v:real^N} IN kk` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `V:real^N->bool`;
                   `v:real^N`] MOI_S4A_VTX_KK) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[MOI_S4H_SIMP_KK]; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                 `s:real^N->bool`] MOI_S4O_KK_PURE) THEN
  SUBGOAL_THEN `(s:real^N->bool) IN kk /\ aff_dim s = &2` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(s:real^N->bool) IN moi_s34_simp kk (&2)` THEN
    REWRITE_TAC[moi_s34_simp; IN_ELIM_THM];
    ALL_TAC] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[HULL_INC]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:real^N->bool` THEN
  SUBGOAL_THEN `(r:real^N->bool) IN moi_s34_simp kk (&3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[moi_s34_simp; IN_ELIM_THM]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                 `r:real^N->bool`] MOI_S4H_RR_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o el 7 o CONJUNCTS) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Cell interiors are open in PL 2-spheres and in PL circles; an            *)
(* outer cell meets a patch or an edge arc only in its own boundary.         *)
(* ------------------------------------------------------------------------- *)

let MOI_S4H_BALL_SPHERE = prove
 (`!c:real^3->bool. pl_ball 3 c ==> pl_sphere 2 (frontier c)`,
  GEN_TAC THEN REWRITE_TAC[pl_ball; pl_sphere; ARITH_RULE `2 + 1 = 3`] THEN
  MESON_TAC[MOI_SCD_BALL_BOUNDARY_PLH]);;

let MOI_S4H_DISK_OPEN = prove
 (`!s d j:real^3->bool.
     pl_sphere 2 s /\ pl_cell_with_boundary 2 d j /\ d SUBSET s
     ==> open_in (subtopology euclidean s) (d DIFF j)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `d:real^3->bool`; `j:real^3->bool`] DISK_COMPLEMENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP MOI_S4G_CELL_FACTS) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `d:real^3->bool`; `j:real^3->bool`] MOI_S4G_CELL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  EXISTS_TAC `(:real^3) DIFF ((s DIFF d) UNION j)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_DIFF THEN ASM_SIMP_TAC[OPEN_UNIV; COMPACT_IMP_CLOSED];
    ASM SET_TAC[]]);;

(* A PL 1-cell is the image of an arc whose ends form its boundary. *)

let MOI_S4H_CELL1_ARC = prove
 (`!A bA:real^N->bool.
     pl_cell_with_boundary 1 A bA
     ==> ?gam:real^1->real^N. arc gam /\ path_image gam = A /\
                              bA = {pathstart gam, pathfinish gam}`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism; homeomorphism; MOI_PL2_SIMPLEX_1] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `(f:real^N->real^N) o linepath(a,b)` THEN
  REWRITE_TAC[PATH_IMAGE_COMPOSE; PATH_IMAGE_LINEPATH; PATHSTART_COMPOSE; PATHFINISH_COMPOSE;
              PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
  UNDISCH_TAC `k = segment[a:real^N,b]` THEN DISCH_THEN SUBST_ALL_TAC THEN
  ASM_SIMP_TAC[MOI_S4O_RF_SEGMENT; IMAGE_CLAUSES] THEN
  MATCH_MP_TAC ARC_CONTINUOUS_IMAGE THEN
  ASM_REWRITE_TAC[PATH_IMAGE_LINEPATH; ARC_LINEPATH_EQ] THEN ASM_MESON_TAC[]);;

let MOI_S4H_ARC_OPEN = prove
 (`!K A bA:real^N->bool.
     pl_sphere 1 K /\ pl_cell_with_boundary 1 A bA /\ A SUBSET K
     ==> open_in (subtopology euclidean K) (A DIFF bA)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S4H_CELL1_ARC) THEN
  DISCH_THEN(X_CHOOSE_THEN `gam:real^1->real^N` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S4O_CIRCLE_LOOP) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^1->real^N` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `path_image (c:real^1->real^N) = K` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  UNDISCH_TAC `path_image (gam:real^1->real^N) = A` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  UNDISCH_TAC `bA = {pathstart (gam:real^1->real^N), pathfinish gam}` THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  SUBGOAL_THEN `!y:real^N. y IN path_image gam /\ ~(y IN {pathstart gam, pathfinish gam})
                           ==> ~(y IN closure (path_image c DIFF path_image gam))`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `connected (path_image c DIFF (path_image gam DELETE (y:real^N)))` MP_TAC THENL
     [MATCH_MP_TAC CONNECTED_INTERMEDIATE_CLOSURE THEN
      EXISTS_TAC `path_image c DIFF path_image (gam:real^1->real^N)` THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`c:real^1->real^N`; `path_image (gam:real^1->real^N)`]
                      CONNECTED_COMPLEMENT_SUBSET_SIMPLE_PATH_IMAGE) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        MATCH_MP_TAC CONNECTED_PATH_IMAGE THEN ASM_SIMP_TAC[ARC_IMP_PATH];
        MP_TAC(ISPEC `path_image c DIFF path_image (gam:real^1->real^N)` CLOSURE_SUBSET) THEN
        ASM SET_TAC[]];
      MP_TAC(ISPECL [`c:real^1->real^N`; `path_image gam DELETE (y:real^N)`]
                    CONNECTED_COMPLEMENT_SUBSET_SIMPLE_PATH_IMAGE) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      MP_TAC(ISPECL [`gam:real^1->real^N`; `y:real^N`] CONNECTED_ARC_IMAGE_DELETE) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  EXISTS_TAC `(:real^N) DIFF (closure (path_image c DIFF path_image gam) UNION
                              {pathstart (gam:real^1->real^N), pathfinish gam})` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_DIFF THEN REWRITE_TAC[OPEN_UNIV] THEN MATCH_MP_TAC CLOSED_UNION THEN
    REWRITE_TAC[CLOSED_CLOSURE] THEN MATCH_MP_TAC FINITE_IMP_CLOSED THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
    MP_TAC(ISPEC `path_image c DIFF path_image (gam:real^1->real^N)` CLOSURE_SUBSET) THEN
    UNDISCH_TAC `!y:real^N. y IN path_image gam /\ ~(y IN {pathstart gam, pathfinish gam})
                           ==> ~(y IN closure (path_image c DIFF path_image gam))` THEN
    UNDISCH_TAC `path_image (gam:real^1->real^N) SUBSET path_image c` THEN
    SET_TAC[]]);;

(* The abstract meeting argument for an outer cell c = closure X and a cell *)
(* d inside U (X misses U), both with open interiors in S.                   *)

let MOI_S4H_OUTER_MEET = prove
 (`!S (c:real^N->bool) bc X U d bd.
     open_in (subtopology euclidean S) (c DIFF bc) /\
     open_in (subtopology euclidean S) (d DIFF bd) /\
     c = closure X /\ X SUBSET S /\ DISJOINT X U /\ d SUBSET U /\ d SUBSET S /\
     bd SUBSET closure (d DIFF bd)
     ==> c INTER d SUBSET bc`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(c DIFF bc) INTER (d DIFF bd) = {}:real^N->bool` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`subtopology euclidean (S:real^N->bool)`; `c DIFF bc:real^N->bool`;
                   `d DIFF bd:real^N->bool`] OPEN_IN_INTER) THEN
    ASM_REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `w INTER (X:real^N->bool) = {}` ASSUME_TAC THENL
     [UNDISCH_TAC `DISJOINT (X:real^N->bool) U` THEN ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`w:real^N->bool`; `X:real^N->bool`] OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(c:real^N->bool) = closure X` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c DIFF bc) INTER bd = {}:real^N->bool` ASSUME_TAC THENL
   [UNDISCH_TAC `open_in (subtopology euclidean S) (c DIFF bc:real^N->bool)` THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `w INTER (d DIFF bd:real^N->bool) = {}` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`w:real^N->bool`; `d DIFF bd:real^N->bool`] OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM SET_TAC[]);;

(* The boundary of a PL cell lies in the closure of its interior. *)

let MOI_S4H_CELL_BD_CLOSURE = prove
 (`!n (c:real^N->bool) b. pl_cell_with_boundary n c b ==> b SUBSET closure (c DIFF b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism; homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `compact(k:real^N->bool) /\ convex k` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE; POLYTOPE_IMP_COMPACT; POLYTOPE_IMP_CONVEX];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^N->real^N) (relative_interior k) SUBSET c DIFF b` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `k:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
    REWRITE_TAC[relative_frontier] THEN
    UNDISCH_TAC `!x:real^N. x IN k ==> (g:real^N->real^N)((f:real^N->real^N) x) = x` THEN
    ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
    UNDISCH_TAC `IMAGE (f:real^N->real^N) k = c` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `IMAGE (f:real^N->real^N) (closure (relative_interior k))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR] THEN
    REWRITE_TAC[relative_frontier; SUBSET_DIFF];
    MATCH_MP_TAC IMAGE_CLOSURE_SUBSET THEN REWRITE_TAC[CLOSED_CLOSURE] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED; COMPACT_IMP_CLOSED];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `c DIFF b:real^N->bool` THEN
      ASM_REWRITE_TAC[CLOSURE_SUBSET]]]);;

(* T2D: an outer patch meets a patch at v only in its boundary. *)

let MOI_S4H_OP_PA = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr v r.
     moi_s4h_hyp tt kk h ep f1 car dd rr /\ {v} IN kk /\ v IN complex_boundary kk /\
     r IN moi_s34_simp kk (&3) /\ v IN r
     ==> moi_s34_opatch tt kk f1 rr v INTER (rr r INTER IMAGE f1 (moi_s34_vb tt kk v))
         SUBSET
         UNIONS {dd s INTER IMAGE f1 (moi_s34_vb tt kk v) | s |
                 s IN moi_s34_simp kk (&2) /\ v IN s /\ s SUBSET complex_boundary kk} UNION
         UNIONS {moi_s34_oarc tt kk f1 rr g | g |
                 g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET complex_boundary kk}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MOI_S4H_UNFOLD_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`]
                MOI_S4G_FRAME_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `v:real^N` o el 2 o CONJUNCTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fr")) THEN
  ABBREV_TAC `S = frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v))` THEN
  SUBGOAL_THEN `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)
                SUBSET (S:real^3->bool) /\ closed S /\ pl_sphere 2 S` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN ASM_SIMP_TAC[FRONTIER_CLOSED; MOI_S4H_BALL_SPHERE] THEN
    USE_THEN "fr" SUBST1_TAC THEN SET_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "fr" (K ALL_TAC) THEN
  SUBGOAL_THEN `(rr:(real^N->bool)->real^3->bool) r INTER
                IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) SUBSET (S:real^3->bool)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                   `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                   `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                   `r:real^N->bool`; `moi_s34_vb tt kk (v:real^N)`] MOI_S4G_RR_SUB) THEN
    ASM_SIMP_TAC[MOI_S4G_VB_NB] THEN
    UNDISCH_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)
                 SUBSET (S:real^3->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                 `r:real^N->bool`] MOI_S4H_RR_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
  UNDISCH_TAC `moi_s34_resid tt kk (f1:real^N->real^3) car dd rr` THEN
  REWRITE_TAC[moi_s34_resid] THEN
  DISCH_THEN(MP_TAC o SPEC `r:real^N->bool` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `v:real^N` o el 4 o CONJUNCTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  UNDISCH_TAC `moi_s34_outer tt kk (f1:real^N->real^3) dd rr` THEN
  REWRITE_TAC[moi_s34_outer] THEN
  DISCH_THEN(MP_TAC o SPEC `v:real^N` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC MOI_S4H_OUTER_MEET THEN
  MAP_EVERY EXISTS_TAC
   [`S:real^3->bool`;
    `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) DIFF
     UNIONS {(rr:(real^N->bool)->real^3->bool) r' | r' |
             r' IN moi_s34_simp kk (&3) /\ v IN r'}`;
    `(rr:(real^N->bool)->real^3->bool) r`;
    `UNIONS {(dd:(real^N->bool)->real^3->bool) s INTER
             IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) | s |
             s IN moi_s34_simp kk (&2) /\ v IN s /\ s SUBSET r} UNION
     UNIONS {(rr:(real^N->bool)->real^3->bool) r INTER IMAGE f1 (moi_s34_sd tt kk g) | g |
             g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET r}`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S4H_DISK_OPEN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S4G_OPATCH_IN THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S4H_DISK_OPEN THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[moi_s34_opatch];
    MATCH_MP_TAC(SET_RULE `!a b s:real^3->bool. a SUBSET s ==> a DIFF b SUBSET s`) THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `(r:real^N->bool) IN moi_s34_simp kk (&3)` THEN
    UNDISCH_TAC `(v:real^N) IN r` THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_DIFF; IN_UNIONS; IN_ELIM_THM;
                NOT_IN_EMPTY] THEN MESON_TAC[];
    SET_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S4H_CELL_BD_CLOSURE THEN EXISTS_TAC `2` THEN ASM_REWRITE_TAC[]]);;

(* T1D: an outer arc meets an edge arc of its edge only in its ends. *)

let MOI_S4H_OA_EA = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr g r.
     moi_s4h_hyp tt kk h ep f1 car dd rr /\ g IN moi_s34_simp kk (&1) /\
     g SUBSET complex_boundary kk /\ r IN moi_s34_simp kk (&3) /\ g SUBSET r
     ==> moi_s34_oarc tt kk f1 rr g INTER (rr r INTER IMAGE f1 (moi_s34_sd tt kk g))
         SUBSET
         UNIONS {dd s INTER IMAGE f1 (moi_s34_sd tt kk g) | s |
                 s IN moi_s34_simp kk (&2) /\ g SUBSET s /\ s SUBSET complex_boundary kk}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MOI_S4H_UNFOLD_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`]
                MOI_S4G_FRAME_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `g:real^N->bool` o el 3 o CONJUNCTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(rr:(real^N->bool)->real^3->bool) r INTER
                IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) SUBSET
                IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                   `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                   `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                   `r:real^N->bool`; `moi_s34_sd tt kk (g:real^N->bool)`] MOI_S4G_RR_SUB) THEN
    ASM_SIMP_TAC[MOI_S4G_SD_NB] THEN SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_s34_resid tt kk (f1:real^N->real^3) car dd rr` THEN
  REWRITE_TAC[moi_s34_resid] THEN
  DISCH_THEN(MP_TAC o SPEC `r:real^N->bool` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `g:real^N->bool` o el 5 o CONJUNCTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  UNDISCH_TAC `moi_s34_outer tt kk (f1:real^N->real^3) dd rr` THEN
  REWRITE_TAC[moi_s34_outer] THEN
  DISCH_THEN(MP_TAC o SPEC `g:real^N->bool` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  ABBREV_TAC `S = IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)` THEN
  SUBGOAL_THEN `pl_sphere 1 (S:real^3->bool) /\ closed S` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`1`; `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)`; `S:real^3->bool`]
                    MOI_S4O_CELL_SPHERE) THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC MOI_S4G_CELL_BD_COMPACT THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S4H_OUTER_MEET THEN
  MAP_EVERY EXISTS_TAC
   [`S:real^3->bool`;
    `(S:real^3->bool) DIFF
     UNIONS {(rr:(real^N->bool)->real^3->bool) r' | r' |
             r' IN moi_s34_simp kk (&3) /\ g SUBSET r'}`;
    `(rr:(real^N->bool)->real^3->bool) r`;
    `UNIONS {(dd:(real^N->bool)->real^3->bool) s INTER
             IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) | s |
             s IN moi_s34_simp kk (&2) /\ g SUBSET s /\ s SUBSET r}`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S4H_ARC_OPEN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S4G_OARC_IN THEN ASM_REWRITE_TAC[SUBSET_REFL];
    MATCH_MP_TAC MOI_S4H_ARC_OPEN THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[moi_s34_oarc];
    SET_TAC[];
    UNDISCH_TAC `(r:real^N->bool) IN moi_s34_simp kk (&3)` THEN
    UNDISCH_TAC `(g:real^N->bool) SUBSET r` THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_DIFF; IN_UNIONS; IN_ELIM_THM;
                NOT_IN_EMPTY] THEN MESON_TAC[];
    SET_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S4H_CELL_BD_CLOSURE THEN EXISTS_TAC `1` THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The boundary bs l and the open cell oc l of a target; every               *)
(* target is the union of the open cells of the faces of its source cell.    *)
(* ------------------------------------------------------------------------- *)

let moi_s4h_bs = new_definition
 `moi_s4h_bs (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool) (f1:real^N->real^3)
             (dd:(real^N->bool)->real^3->bool) (rr:(real^N->bool)->real^3->bool)
             (l:real^N->bool) =
    UNIONS {moi_s34_tgt tt kk f1 dd rr m | m |
            m IN moi_s34_scells tt kk /\ m SUBSET l /\ ~(m = l)}`;;

let moi_s4h_oc = new_definition
 `moi_s4h_oc (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool) (f1:real^N->real^3)
             (dd:(real^N->bool)->real^3->bool) (rr:(real^N->bool)->real^3->bool)
             (l:real^N->bool) =
    moi_s34_tgt tt kk f1 dd rr l DIFF moi_s4h_bs tt kk f1 dd rr l`;;

(* The target of a source cell, its kind dimension and its PL cell. *)

let MOI_S4H_TGT_CELL = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr l.
     moi_s4h_hyp tt kk h ep f1 car dd rr /\ l IN moi_s34_scells tt kk
     ==> pl_cell_with_boundary (moi_s34_dim l) (moi_s34_tgt tt kk f1 dd rr l)
           (moi_s4h_bs tt kk f1 dd rr l)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOI_S4G_SCELLS_LAB; moi_s4h_bs] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN
    `q:real^N->bool` (X_CHOOSE_TAC `x:real^N->bool`)))) THEN
  MOI_S4H_UNFOLD_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `l:real^N->bool`;
                 `k:num`; `q:real^N->bool`; `x:real^N->bool`] MOI_S4G_DIM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                 `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                 `l:real^N->bool`; `k:num`; `q:real^N->bool`; `x:real^N->bool`]
                MOI_S4G_TGT_EVAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM MOI_S4G_SCELLS_LAB] THEN
  MATCH_MP_TAC MOI_S4G_TC THEN
  MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`;
                        `car:(real^N->bool)->real^3->bool`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_S4H_BS_SUB = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr l.
     moi_s4h_hyp tt kk h ep f1 car dd rr /\ l IN moi_s34_scells tt kk
     ==> moi_s4h_bs tt kk f1 dd rr l SUBSET moi_s34_tgt tt kk f1 dd rr l`,
  MESON_TAC[MOI_S4H_TGT_CELL; MOI_S4G_CELL_FACTS]);;

let MOI_S4H_MONO = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr l n.
     moi_s4h_hyp tt kk h ep f1 car dd rr /\ l IN moi_s34_scells tt kk /\
     n IN moi_s34_scells tt kk /\ n SUBSET l
     ==> moi_s34_tgt tt kk f1 dd rr n SUBSET moi_s34_tgt tt kk f1 dd rr l`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `n:real^N->bool = l` THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `moi_s4h_bs tt kk (f1:real^N->real^3) dd rr l` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[moi_s4h_bs] THEN GEN_REWRITE_TAC I [SUBSET] THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[MOI_S4H_BS_SUB]]);;

(* Proper faces have smaller dimension. *)

let MOI_S4H_DIM_LT = prove
 (`!(tt:(real^N->bool)->bool) kk l m.
     moi_s34_tube tt kk /\ l IN moi_s34_scells tt kk /\ m IN moi_s34_scells tt kk /\
     m SUBSET l /\ ~(m = l)
     ==> moi_s34_dim m < moi_s34_dim l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOI_S4G_SCELLS_LAB] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `q:real^N->bool` (X_CHOOSE_TAC `x:real^N->bool`)))
    (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `k':num` (X_CHOOSE_THEN `q':real^N->bool` (X_CHOOSE_TAC `x':real^N->bool`)))
    STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `l:real^N->bool`;
                 `k:num`; `q:real^N->bool`; `x:real^N->bool`; `m:real^N->bool`;
                 `k':num`; `q':real^N->bool`; `x':real^N->bool`] MOI_S4G_PROPER_FACE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `k':num`; `q':real^N->bool`; `x':real^N->bool`;
                 `k:num`; `q:real^N->bool`; `x:real^N->bool`] MOI_S4G_FACE_KD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `l:real^N->bool`;
                 `k:num`; `q:real^N->bool`; `x:real^N->bool`] MOI_S4G_DIM) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `m:real^N->bool`;
                 `k':num`; `q':real^N->bool`; `x':real^N->bool`] MOI_S4G_DIM) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[]);;

(* Every target is the union of the open cells of the faces of its source. *)

let MOI_S4H_OC_COVER = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr l.
     moi_s4h_hyp tt kk h ep f1 car dd rr /\ l IN moi_s34_scells tt kk
     ==> moi_s34_tgt tt kk f1 dd rr l =
         UNIONS {moi_s4h_oc tt kk f1 dd rr n | n |
                 n IN moi_s34_scells tt kk /\ n SUBSET l}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `!d (l:real^N->bool). moi_s4h_hyp tt kk h ep (f1:real^N->real^3) car dd rr /\
          l IN moi_s34_scells tt kk /\ moi_s34_dim l = d
          ==> moi_s34_tgt tt kk f1 dd rr l =
              UNIONS {moi_s4h_oc tt kk f1 dd rr n | n |
                      n IN moi_s34_scells tt kk /\ n SUBSET l}`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `d:num` THEN DISCH_TAC THEN
  X_GEN_TAC `l:real^N->bool` THEN STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
    ASM_CASES_TAC `(y:real^3) IN moi_s4h_bs tt kk (f1:real^N->real^3) dd rr l` THENL
     [UNDISCH_TAC `(y:real^3) IN moi_s4h_bs tt kk (f1:real^N->real^3) dd rr l` THEN
      REWRITE_TAC[moi_s4h_bs; UNIONS_GSPEC; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `m:real^N->bool` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `moi_s34_dim (m:real^N->bool)`) THEN ANTS_TAC THENL
       [UNDISCH_TAC `moi_s34_dim (l:real^N->bool) = d` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        MATCH_MP_TAC MOI_S4H_DIM_LT THEN EXISTS_TAC `tt:(real^N->bool)->bool` THEN
        ASM_MESON_TAC[moi_s4h_hyp];
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `m:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o AP_TERM `\s:real^3->bool. (y:real^3) IN s`) THEN
      ASM_REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `n:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `n:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      EXISTS_TAC `l:real^N->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL; moi_s4h_oc; IN_DIFF]];
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN X_GEN_TAC `n:real^N->bool` THEN
    STRIP_TAC THEN REWRITE_TAC[moi_s4h_oc] THEN
    MATCH_MP_TAC(SET_RULE `!a b c:real^3->bool. a SUBSET c ==> a DIFF b SUBSET c`) THEN
    MATCH_MP_TAC MOI_S4H_MONO THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`;
                          `car:(real^N->bool)->real^3->bool`] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The kind of a point of the target space (decided by membership            *)
(* in F(N), F(Bd N), the face disks, the tetra balls and the splitting       *)
(* disks), and uniqueness of the index objects containing a point.           *)
(* ------------------------------------------------------------------------- *)

let moi_s4h_kind = new_definition
 `moi_s4h_kind (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool) (f1:real^N->real^3)
               (dd:(real^N->bool)->real^3->bool) (rr:(real^N->bool)->real^3->bool)
               (y:real^3) =
   if ~(y IN IMAGE f1 (moi_s34_nb tt kk))
   then (if ?s. s IN moi_s34_simp kk (&2) /\ y IN dd s then 3 else 4)
   else if ~(y IN IMAGE f1 (moi_s34_bd tt kk))
   then (if ?g. g IN moi_s34_simp kk (&1) /\ y IN IMAGE f1 (moi_s34_sd tt kk g) then 2 else 1)
   else if ?s. s IN moi_s34_simp kk (&2) /\ y IN dd s
   then (if ?g. g IN moi_s34_simp kk (&1) /\ y IN IMAGE f1 (moi_s34_sd tt kk g) then 8 else 6)
   else if ?r. r IN moi_s34_simp kk (&3) /\ y IN rr r
   then (if ?g. g IN moi_s34_simp kk (&1) /\ y IN IMAGE f1 (moi_s34_sd tt kk g) then 7 else 5)
   else (if ?g. g IN moi_s34_simp kk (&1) /\ y IN IMAGE f1 (moi_s34_sd tt kk g)
         then 10 else 9)`;;

(* Uniqueness of the index objects at a point. *)

let MOI_S4H_UNIQ_VB = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr v y.
     moi_s4h_hyp tt kk h ep f1 car dd rr /\ {v} IN kk /\ y IN IMAGE f1 (moi_s34_vb tt kk v) /\
     ~(?g. g IN moi_s34_simp kk (&1) /\ y IN IMAGE f1 (moi_s34_sd tt kk g))
     ==> !w. {w} IN kk /\ y IN IMAGE f1 (moi_s34_vb tt kk w) ==> w = v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                 `v:real^N`; `w:real^N`; `y:real^3`] MOI_S4H_VB_VB) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let MOI_S4H_UNIQ_RR = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr r y.
     moi_s4h_hyp tt kk h ep f1 car dd rr /\ r IN moi_s34_simp kk (&3) /\ y IN rr r /\
     ~(?s. s IN moi_s34_simp kk (&2) /\ y IN dd s)
     ==> !r'. r' IN moi_s34_simp kk (&3) /\ y IN rr r' ==> r' = r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `r':real^N->bool` THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                 `r:real^N->bool`] MOI_S4H_RR_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `r':real^N->bool` o el 8 o CONJUNCTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o AP_TERM `\t:real^3->bool. (y:real^3) IN t`) THEN
  ASM_REWRITE_TAC[IN_INTER; UNIONS_GSPEC; IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

let MOI_S4H_UNIQ_DD = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr s y.
     moi_s4h_hyp tt kk h ep f1 car dd rr /\ s IN moi_s34_simp kk (&2) /\ y IN dd s
     ==> !s'. s' IN moi_s34_simp kk (&2) /\ y IN dd s' ==> s' = s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `s':real^N->bool` THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`] MOI_S4H_DD_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `s':real^N->bool` o el 4 o CONJUNCTS) THEN ASM_REWRITE_TAC[] THEN
  ASM SET_TAC[]);;

let MOI_S4H_UNIQ_SD = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr g y.
     moi_s4h_hyp tt kk h ep f1 car dd rr /\ g IN moi_s34_simp kk (&1) /\
     y IN IMAGE f1 (moi_s34_sd tt kk g)
     ==> !g'. g' IN moi_s34_simp kk (&1) /\ y IN IMAGE f1 (moi_s34_sd tt kk g') ==> g' = g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `g':real^N->bool` THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                 `g:real^N->bool`; `g':real^N->bool`] MOI_S4H_SD_SD_EMPTY) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* Bd N, vertex balls and splitting disks lie in N. *)

let MOI_S4H_IN_NB = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr y.
     moi_s4h_hyp tt kk h ep f1 car dd rr
     ==> (!v. {v} IN kk /\ y IN IMAGE f1 (moi_s34_vb tt kk v)
              ==> y IN IMAGE f1 (moi_s34_nb tt kk)) /\
         (!g. g IN moi_s34_simp kk (&1) /\ y IN IMAGE f1 (moi_s34_sd tt kk g)
              ==> y IN IMAGE f1 (moi_s34_nb tt kk)) /\
         (!q. q IN kk /\ y IN IMAGE f1 (moi_s34_bd tt kk)
              ==> y IN IMAGE f1 (moi_s34_nb tt kk))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4H_HYP) THEN
  REPEAT CONJ_TAC THEN GEN_TAC THEN STRIP_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
                  MOI_S4G_VB_NB);
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `g:real^N->bool`]
                  MOI_S4G_SD_NB);
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `q:real^N->bool`]
                  MOI_S4G_BD_NB)] THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_S4H_VB_BD_IN = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr v y.
     moi_s4h_hyp tt kk h ep f1 car dd rr /\ {v} IN kk /\
     y IN IMAGE f1 (moi_s34_vb tt kk v) /\ y IN IMAGE f1 (moi_s34_bd tt kk)
     ==> y IN IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4H_HYP) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                 `moi_s34_vb tt kk (v:real^N)`; `moi_s34_bd tt (kk:(real^N->bool)->bool)`;
                 `y:real^3`] MOI_S4H_IMG_INTER) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[MOI_S4G_VB_NB] THEN MATCH_MP_TAC MOI_S4G_BD_NB THEN
  EXISTS_TAC `{v:real^N}` THEN ASM_REWRITE_TAC[]);;

let MOI_S4H_SD_BD_IN = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr g y.
     moi_s4h_hyp tt kk h ep f1 car dd rr /\ g IN moi_s34_simp kk (&1) /\
     y IN IMAGE f1 (moi_s34_sd tt kk g) /\ y IN IMAGE f1 (moi_s34_bd tt kk)
     ==> y IN IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4H_HYP) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                 `moi_s34_sd tt kk (g:real^N->bool)`; `moi_s34_bd tt (kk:(real^N->bool)->bool)`;
                 `y:real^3`] MOI_S4H_IMG_INTER) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[MOI_S4G_SD_NB] THEN MATCH_MP_TAC MOI_S4G_BD_NB THEN
  EXISTS_TAC `g:real^N->bool` THEN ASM_MESON_TAC[MOI_S4H_SIMP_KK]);;

(* PROF1: points of the open vertex balls. *)

let MOI_S4H_PROF1 = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr v y.
     moi_s4h_hyp tt kk h ep f1 car dd rr /\ {v} IN kk /\
     y IN IMAGE f1 (moi_s34_vb tt kk v) /\
     ~(y IN frontier (IMAGE f1 (moi_s34_vb tt kk v)))
     ==> moi_s4h_kind tt kk f1 dd rr y = 1 /\
         (!m q' x'. moi_s4g_lab tt kk m 1 q' x' /\ y IN moi_s4g_tgtl tt kk f1 dd rr 1 q' x'
                    ==> q' = {v} /\ x' = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MOI_S4H_UNFOLD_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`]
                MOI_S4G_FRAME_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `v:real^N` o el 2 o CONJUNCTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th ->
    UNDISCH_TAC `~((y:real^3) IN frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)))` THEN
    REWRITE_TAC[CONJUNCT2 th]) THEN
  REWRITE_TAC[IN_UNION; DE_MORGAN_THM; UNIONS_GSPEC; IN_ELIM_THM; NOT_EXISTS_THM] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `~(?g. g IN moi_s34_simp kk (&1) /\
                      (y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g))` ASSUME_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `(v:real^N) IN g` THENL
     [ASM_MESON_TAC[];
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                     `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                     `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                     `v:real^N`; `g:real^N->bool`] MOI_S4H_VB_SD_EMPTY) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                   `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                   `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                   `v:real^N`; `y:real^3`] MOI_S4H_VB_BD_IN) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                   `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                   `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                   `y:real^3`] MOI_S4H_IN_NB) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[moi_s4h_kind]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4g_lab; ARITH_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC)) MP_TAC) THEN
  ASM_REWRITE_TAC[moi_s4g_tgtl; ARITH_EQ; MOI_S4G_CHOICE_SING] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                 `v:real^N`; `y:real^3`] MOI_S4H_UNIQ_VB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o SPEC `w:real^N`)] THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* Outer patches and outer arcs lie in F(C_v n Bd N) and F(D_g n Bd N). *)

let MOI_S4H_OPATCH_SUB = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr v.
     moi_s4h_hyp tt kk h ep f1 car dd rr /\ {v} IN kk
     ==> moi_s34_opatch tt kk f1 rr v SUBSET
         IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4H_HYP) THEN
  MATCH_MP_TAC MOI_S4G_OPATCH_IN THEN REWRITE_TAC[SUBSET_REFL] THEN
  MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
                MOI_S4G_VB_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s34_nb tt (kk:(real^N->bool)->bool)` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
                  MOI_S4G_VB_NB) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    SUBGOAL_THEN `moi_s34_vb tt kk (v:real^N) INTER moi_s34_bd tt kk =
                  moi_s34_vb tt kk v INTER (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`
    SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC COMPACT_INTER_CLOSED THEN ASM_REWRITE_TAC[]]);;

let MOI_S4H_OARC_SUB = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr g.
     moi_s4h_hyp tt kk h ep f1 car dd rr /\ g IN moi_s34_simp kk (&1)
     ==> moi_s34_oarc tt kk f1 rr g SUBSET
         IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)`,
  REPEAT STRIP_TAC THEN MOI_S4H_UNFOLD_TAC THEN
  MATCH_MP_TAC MOI_S4G_OARC_IN THEN REWRITE_TAC[SUBSET_REFL] THEN
  MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC MOI_S4G_CELL_BD_COMPACT THEN
  MAP_EVERY EXISTS_TAC [`2`; `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)`] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`]
                MOI_S4G_FRAME_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `g:real^N->bool` o el 3 o CONJUNCTS) THEN ASM_REWRITE_TAC[]);;

let MOI_S4H_VARS =
  [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
   `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
   `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`];;

(* PROF2: points of the open splitting disks. *)

let MOI_S4H_PROF2 = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr g y.
     moi_s4h_hyp tt kk h ep f1 car dd rr /\ g IN moi_s34_simp kk (&1) /\
     y IN IMAGE f1 (moi_s34_sd tt kk g) /\
     ~(y IN IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk))
     ==> moi_s4h_kind tt kk f1 dd rr y = 2 /\
         (!m q' x'. moi_s4g_lab tt kk m 2 q' x' /\ y IN moi_s4g_tgtl tt kk f1 dd rr 2 q' x'
                    ==> q' = g /\ x' = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL (MOI_S4H_VARS @ [`g:real^N->bool`; `y:real^3`]) MOI_S4H_SD_BD_IN) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)` ASSUME_TAC THENL
   [MP_TAC(ISPECL (MOI_S4H_VARS @ [`y:real^3`]) MOI_S4H_IN_NB) THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?g'. g' IN moi_s34_simp kk (&1) /\
                     (y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g')`
  ASSUME_TAC THENL [EXISTS_TAC `g:real^N->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[moi_s4h_kind]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4g_lab; ARITH_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[moi_s4g_tgtl; ARITH_EQ] THEN DISCH_TAC THEN
  MP_TAC(ISPECL (MOI_S4H_VARS @ [`g:real^N->bool`; `y:real^3`]) MOI_S4H_UNIQ_SD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o SPEC `q':real^N->bool`)] THEN
  ASM_REWRITE_TAC[]);;

(* PROF3: points of the open face disks. *)

let MOI_S4H_PROF3 = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr s y.
     moi_s4h_hyp tt kk h ep f1 car dd rr /\ s IN moi_s34_simp kk (&2) /\
     y IN dd s /\ ~(y IN dd s INTER IMAGE f1 (moi_s34_bd tt kk))
     ==> moi_s4h_kind tt kk f1 dd rr y = 3 /\
         (!m q' x'. moi_s4g_lab tt kk m 3 q' x' /\ y IN moi_s4g_tgtl tt kk f1 dd rr 3 q' x'
                    ==> q' = s /\ x' = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL (MOI_S4H_VARS @ [`s:real^N->bool`]) MOI_S4H_DD_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `~((y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk))` ASSUME_TAC THENL
   [DISCH_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?s'. s' IN moi_s34_simp kk (&2) /\
                     (y:real^3) IN (dd:(real^N->bool)->real^3->bool) s'`
  ASSUME_TAC THENL [EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[moi_s4h_kind]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4g_lab; ARITH_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[moi_s4g_tgtl; ARITH_EQ] THEN DISCH_TAC THEN
  MP_TAC(ISPECL (MOI_S4H_VARS @ [`s:real^N->bool`; `y:real^3`]) MOI_S4H_UNIQ_DD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o SPEC `q':real^N->bool`)] THEN
  ASM_REWRITE_TAC[]);;

(* PROF4: points of the open tetra balls. *)

let MOI_S4H_PROF4 = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr r y.
     moi_s4h_hyp tt kk h ep f1 car dd rr /\ r IN moi_s34_simp kk (&3) /\
     y IN rr r /\ ~(y IN frontier (rr r))
     ==> moi_s4h_kind tt kk f1 dd rr y = 4 /\
         (!m q' x'. moi_s4g_lab tt kk m 4 q' x' /\ y IN moi_s4g_tgtl tt kk f1 dd rr 4 q' x'
                    ==> q' = r /\ x' = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL (MOI_S4H_VARS @ [`r:real^N->bool`]) MOI_S4H_RR_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    ASSUME_TAC (el 0 cs) THEN LABEL_TAC "fr" (el 4 cs) THEN
    LABEL_TAC "rdd" (el 6 cs)) THEN
  SUBGOAL_THEN `~((y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk))` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~((y:real^3) IN frontier ((rr:(real^N->bool)->real^3->bool) r))` THEN
    USE_THEN "fr" SUBST1_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(?s. s IN moi_s34_simp kk (&2) /\
                      (y:real^3) IN (dd:(real^N->bool)->real^3->bool) s)` ASSUME_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `(s:real^N->bool) SUBSET r` THENL
     [UNDISCH_TAC `~((y:real^3) IN frontier ((rr:(real^N->bool)->real^3->bool) r))` THEN
      USE_THEN "fr" SUBST1_TAC THEN REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
      ASM_MESON_TAC[];
      USE_THEN "rdd" (MP_TAC o SPEC `s:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[moi_s4h_kind]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4g_lab; ARITH_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[moi_s4g_tgtl; ARITH_EQ] THEN DISCH_TAC THEN
  MP_TAC(ISPECL (MOI_S4H_VARS @ [`r:real^N->bool`; `y:real^3`]) MOI_S4H_UNIQ_RR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o SPEC `q':real^N->bool`)] THEN
  ASM_REWRITE_TAC[]);;

(* PROF5: points of the open patches. *)

let MOI_S4H_PROF5 = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr r v y.
     moi_s4h_hyp tt kk h ep f1 car dd rr /\ r IN moi_s34_simp kk (&3) /\ v IN r /\
     {v} IN kk /\ y IN rr r /\ y IN IMAGE f1 (moi_s34_vb tt kk v) /\
     ~(y IN UNIONS {dd s INTER IMAGE f1 (moi_s34_vb tt kk v) | s |
                    s IN moi_s34_simp kk (&2) /\ v IN s /\ s SUBSET r} UNION
            UNIONS {rr r INTER IMAGE f1 (moi_s34_sd tt kk g) | g |
                    g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET r})
     ==> moi_s4h_kind tt kk f1 dd rr y = 5 /\
         (!m q' x'. moi_s4g_lab tt kk m 5 q' x' /\ y IN moi_s4g_tgtl tt kk f1 dd rr 5 q' x'
                    ==> q' = r /\ x' = {v})`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM; IN_INTER; DE_MORGAN_THM; NOT_EXISTS_THM] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL (MOI_S4H_VARS @ [`r:real^N->bool`]) MOI_S4H_RR_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    ASSUME_TAC (el 0 cs) THEN LABEL_TAC "rdd" (el 6 cs) THEN LABEL_TAC "rsd" (el 9 cs)) THEN
  SUBGOAL_THEN `(y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)` ASSUME_TAC THENL
   [MP_TAC(ISPECL (MOI_S4H_VARS @ [`y:real^3`]) MOI_S4H_IN_NB) THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(rr:(real^N->bool)->real^3->bool) r INTER IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk) =
       rr r INTER IMAGE f1 (moi_s34_bd tt kk)`;
      `(y:real^3) IN (rr:(real^N->bool)->real^3->bool) r`;
      `(y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(?s. s IN moi_s34_simp kk (&2) /\
                      (y:real^3) IN (dd:(real^N->bool)->real^3->bool) s)` ASSUME_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `(s:real^N->bool) SUBSET r` THENL
     [ASM_CASES_TAC `(v:real^N) IN s` THENL
       [ASM_MESON_TAC[];
        MP_TAC(ISPECL (MOI_S4H_VARS @ [`s:real^N->bool`]) MOI_S4H_DD_FACTS) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o SPEC `v:real^N` o el 3 o CONJUNCTS) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o SPEC `y:real^3` o REWRITE_RULE[EXTENSION; IN_INTER; NOT_IN_EMPTY]) THEN
        ASM_REWRITE_TAC[]];
      USE_THEN "rdd" (MP_TAC o SPEC `s:real^N->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^3` o REWRITE_RULE[EXTENSION; IN_INTER; NOT_IN_EMPTY]) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(?g. g IN moi_s34_simp kk (&1) /\
                      (y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g))`
  ASSUME_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `(v:real^N) IN g` THENL
     [ASM_CASES_TAC `(g:real^N->bool) SUBSET r` THENL
       [ASM_MESON_TAC[];
        USE_THEN "rsd" (MP_TAC o SPEC `g:real^N->bool`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o SPEC `y:real^3` o REWRITE_RULE[EXTENSION; IN_INTER; NOT_IN_EMPTY]) THEN
        ASM_REWRITE_TAC[]];
      MP_TAC(ISPECL (MOI_S4H_VARS @ [`v:real^N`; `g:real^N->bool`]) MOI_S4H_VB_SD_EMPTY) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^3` o REWRITE_RULE[EXTENSION; IN_INTER; NOT_IN_EMPTY]) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?r'. r' IN moi_s34_simp kk (&3) /\
                     (y:real^3) IN (rr:(real^N->bool)->real^3->bool) r'`
  ASSUME_TAC THENL [EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[moi_s4h_kind]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4g_lab; ARITH_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC)) MP_TAC) THEN
  ASM_REWRITE_TAC[moi_s4g_tgtl; ARITH_EQ; MOI_S4G_CHOICE_SING; IN_INTER] THEN STRIP_TAC THEN
  MP_TAC(ISPECL (MOI_S4H_VARS @ [`r:real^N->bool`; `y:real^3`]) MOI_S4H_UNIQ_RR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o SPEC `q':real^N->bool`)] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL (MOI_S4H_VARS @ [`v:real^N`; `y:real^3`]) MOI_S4H_UNIQ_VB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o SPEC `w:real^N`)] THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* PROF6: points of the open face arcs. *)

let MOI_S4H_PROF6 = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr s v y.
     moi_s4h_hyp tt kk h ep f1 car dd rr /\ s IN moi_s34_simp kk (&2) /\ v IN s /\
     {v} IN kk /\ y IN dd s /\ y IN IMAGE f1 (moi_s34_vb tt kk v) /\
     ~(y IN UNIONS {dd s INTER IMAGE f1 (moi_s34_sd tt kk g) | g |
                    g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET s})
     ==> moi_s4h_kind tt kk f1 dd rr y = 6 /\
         (!m q' x'. moi_s4g_lab tt kk m 6 q' x' /\ y IN moi_s4g_tgtl tt kk f1 dd rr 6 q' x'
                    ==> q' = s /\ x' = {v})`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_INTER; NOT_EXISTS_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL (MOI_S4H_VARS @ [`s:real^N->bool`]) MOI_S4H_DD_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    ASSUME_TAC (el 0 cs) THEN LABEL_TAC "dsd" (el 5 cs)) THEN
  SUBGOAL_THEN `(y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)` ASSUME_TAC THENL
   [MP_TAC(ISPECL (MOI_S4H_VARS @ [`y:real^3`]) MOI_S4H_IN_NB) THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(dd:(real^N->bool)->real^3->bool) s INTER IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk) =
       dd s INTER IMAGE f1 (moi_s34_bd tt kk)`;
      `(y:real^3) IN (dd:(real^N->bool)->real^3->bool) s`;
      `(y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(?g. g IN moi_s34_simp kk (&1) /\
                      (y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g))`
  ASSUME_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `(v:real^N) IN g` THENL
     [ASM_CASES_TAC `(g:real^N->bool) SUBSET s` THENL
       [ASM_MESON_TAC[];
        USE_THEN "dsd" (MP_TAC o SPEC `g:real^N->bool`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o SPEC `y:real^3` o REWRITE_RULE[EXTENSION; IN_INTER; NOT_IN_EMPTY]) THEN
        ASM_REWRITE_TAC[]];
      MP_TAC(ISPECL (MOI_S4H_VARS @ [`v:real^N`; `g:real^N->bool`]) MOI_S4H_VB_SD_EMPTY) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^3` o REWRITE_RULE[EXTENSION; IN_INTER; NOT_IN_EMPTY]) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?s'. s' IN moi_s34_simp kk (&2) /\
                     (y:real^3) IN (dd:(real^N->bool)->real^3->bool) s'`
  ASSUME_TAC THENL [EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[moi_s4h_kind]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4g_lab; ARITH_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC)) MP_TAC) THEN
  ASM_REWRITE_TAC[moi_s4g_tgtl; ARITH_EQ; MOI_S4G_CHOICE_SING; IN_INTER] THEN STRIP_TAC THEN
  MP_TAC(ISPECL (MOI_S4H_VARS @ [`s:real^N->bool`; `y:real^3`]) MOI_S4H_UNIQ_DD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o SPEC `q':real^N->bool`)] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL (MOI_S4H_VARS @ [`v:real^N`; `y:real^3`]) MOI_S4H_UNIQ_VB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o SPEC `w:real^N`)] THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* PROF7: points of the open edge arcs. *)

let MOI_S4H_PROF7 = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr r g y.
     moi_s4h_hyp tt kk h ep f1 car dd rr /\ r IN moi_s34_simp kk (&3) /\
     g IN moi_s34_simp kk (&1) /\ g SUBSET r /\
     y IN rr r /\ y IN IMAGE f1 (moi_s34_sd tt kk g) /\
     ~(y IN UNIONS {dd s INTER IMAGE f1 (moi_s34_sd tt kk g) | s |
                    s IN moi_s34_simp kk (&2) /\ g SUBSET s /\ s SUBSET r})
     ==> moi_s4h_kind tt kk f1 dd rr y = 7 /\
         (!m q' x'. moi_s4g_lab tt kk m 7 q' x' /\ y IN moi_s4g_tgtl tt kk f1 dd rr 7 q' x'
                    ==> q' = r /\ x' = g)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_INTER; NOT_EXISTS_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL (MOI_S4H_VARS @ [`r:real^N->bool`]) MOI_S4H_RR_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    ASSUME_TAC (el 0 cs) THEN LABEL_TAC "rdd" (el 6 cs)) THEN
  SUBGOAL_THEN `(y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)` ASSUME_TAC THENL
   [MP_TAC(ISPECL (MOI_S4H_VARS @ [`y:real^3`]) MOI_S4H_IN_NB) THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(rr:(real^N->bool)->real^3->bool) r INTER IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk) =
       rr r INTER IMAGE f1 (moi_s34_bd tt kk)`;
      `(y:real^3) IN (rr:(real^N->bool)->real^3->bool) r`;
      `(y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(?s. s IN moi_s34_simp kk (&2) /\
                      (y:real^3) IN (dd:(real^N->bool)->real^3->bool) s)` ASSUME_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `(s:real^N->bool) SUBSET r` THENL
     [ASM_CASES_TAC `(g:real^N->bool) SUBSET s` THENL
       [ASM_MESON_TAC[];
        MP_TAC(ISPECL (MOI_S4H_VARS @ [`s:real^N->bool`]) MOI_S4H_DD_FACTS) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o SPEC `g:real^N->bool` o el 5 o CONJUNCTS) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o SPEC `y:real^3` o REWRITE_RULE[EXTENSION; IN_INTER; NOT_IN_EMPTY]) THEN
        ASM_REWRITE_TAC[]];
      USE_THEN "rdd" (MP_TAC o SPEC `s:real^N->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^3` o REWRITE_RULE[EXTENSION; IN_INTER; NOT_IN_EMPTY]) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(?r'. r' IN moi_s34_simp kk (&3) /\
                      (y:real^3) IN (rr:(real^N->bool)->real^3->bool) r') /\
                (?g'. g' IN moi_s34_simp kk (&1) /\
                      (y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g'))`
  (CONJUNCTS_THEN ASSUME_TAC) THENL
   [CONJ_TAC THENL [EXISTS_TAC `r:real^N->bool`; EXISTS_TAC `g:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[moi_s4h_kind]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4g_lab; ARITH_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[moi_s4g_tgtl; ARITH_EQ; IN_INTER] THEN STRIP_TAC THEN
  MP_TAC(ISPECL (MOI_S4H_VARS @ [`r:real^N->bool`; `y:real^3`]) MOI_S4H_UNIQ_RR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o SPEC `q':real^N->bool`)] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL (MOI_S4H_VARS @ [`g:real^N->bool`; `y:real^3`]) MOI_S4H_UNIQ_SD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o SPEC `x':real^N->bool`)] THEN
  ASM_REWRITE_TAC[]);;

(* PROF8: marked points. *)

let MOI_S4H_PROF8 = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr s g y.
     moi_s4h_hyp tt kk h ep f1 car dd rr /\ s IN moi_s34_simp kk (&2) /\
     g IN moi_s34_simp kk (&1) /\ g SUBSET s /\
     y IN dd s /\ y IN IMAGE f1 (moi_s34_sd tt kk g)
     ==> moi_s4h_kind tt kk f1 dd rr y = 8 /\
         (!m q' x'. moi_s4g_lab tt kk m 8 q' x' /\ y IN moi_s4g_tgtl tt kk f1 dd rr 8 q' x'
                    ==> q' = s /\ x' = g)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL (MOI_S4H_VARS @ [`s:real^N->bool`]) MOI_S4H_DD_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `(y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)` ASSUME_TAC THENL
   [MP_TAC(ISPECL (MOI_S4H_VARS @ [`y:real^3`]) MOI_S4H_IN_NB) THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(dd:(real^N->bool)->real^3->bool) s INTER IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk) =
       dd s INTER IMAGE f1 (moi_s34_bd tt kk)`;
      `(y:real^3) IN (dd:(real^N->bool)->real^3->bool) s`;
      `(y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(?s'. s' IN moi_s34_simp kk (&2) /\
                      (y:real^3) IN (dd:(real^N->bool)->real^3->bool) s') /\
                (?g'. g' IN moi_s34_simp kk (&1) /\
                      (y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g'))`
  (CONJUNCTS_THEN ASSUME_TAC) THENL
   [CONJ_TAC THENL [EXISTS_TAC `s:real^N->bool`; EXISTS_TAC `g:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[moi_s4h_kind]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4g_lab; ARITH_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[moi_s4g_tgtl; ARITH_EQ; IN_INTER] THEN STRIP_TAC THEN
  MP_TAC(ISPECL (MOI_S4H_VARS @ [`s:real^N->bool`; `y:real^3`]) MOI_S4H_UNIQ_DD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o SPEC `q':real^N->bool`)] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL (MOI_S4H_VARS @ [`g:real^N->bool`; `y:real^3`]) MOI_S4H_UNIQ_SD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o SPEC `x':real^N->bool`)] THEN
  ASM_REWRITE_TAC[]);;

(* PROF9: points of the open outer patches. *)

let MOI_S4H_PROF9 = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr v y.
     moi_s4h_hyp tt kk h ep f1 car dd rr /\ {v} IN kk /\ v IN complex_boundary kk /\
     y IN moi_s34_opatch tt kk f1 rr v /\
     ~(y IN UNIONS {dd s INTER IMAGE f1 (moi_s34_vb tt kk v) | s |
                    s IN moi_s34_simp kk (&2) /\ v IN s /\ s SUBSET complex_boundary kk} UNION
            UNIONS {moi_s34_oarc tt kk f1 rr g | g |
                    g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET complex_boundary kk})
     ==> moi_s4h_kind tt kk f1 dd rr y = 9 /\
         (!m q' x'. moi_s4g_lab tt kk m 9 q' x' /\ y IN moi_s4g_tgtl tt kk f1 dd rr 9 q' x'
                    ==> q' = {v} /\ x' = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MOI_S4H_UNFOLD_TAC THEN
  MP_TAC(ISPECL (MOI_S4H_VARS @ [`v:real^N`]) MOI_S4H_OPATCH_SUB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `y:real^3` o GEN_REWRITE_RULE I [SUBSET]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MOI_S4G_IN_IMAGE_INTER) THEN
  SUBGOAL_THEN `(y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)` ASSUME_TAC THENL
   [MP_TAC(ISPECL (MOI_S4H_VARS @ [`y:real^3`]) MOI_S4H_IN_NB) THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(?r. r IN moi_s34_simp kk (&3) /\
                      (y:real^3) IN (rr:(real^N->bool)->real^3->bool) r)` ASSUME_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `(v:real^N) IN r` THENL
     [MP_TAC(ISPECL (MOI_S4H_VARS @ [`v:real^N`; `r:real^N->bool`]) MOI_S4H_OP_PA) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^3` o GEN_REWRITE_RULE I [SUBSET]) THEN
      ASM_REWRITE_TAC[IN_INTER];
      MP_TAC(ISPECL (MOI_S4H_VARS @ [`r:real^N->bool`]) MOI_S4H_RR_FACTS) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `v:real^N` o el 5 o CONJUNCTS) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^3` o REWRITE_RULE[EXTENSION; IN_INTER; NOT_IN_EMPTY]) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(?s. s IN moi_s34_simp kk (&2) /\
                      (y:real^3) IN (dd:(real^N->bool)->real^3->bool) s)` ASSUME_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL (MOI_S4H_VARS @ [`s:real^N->bool`]) MOI_S4H_DD_IN_RR) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(?g. g IN moi_s34_simp kk (&1) /\
                      (y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g))`
  ASSUME_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `(v:real^N) IN g` THENL
     [MP_TAC(ISPECL (MOI_S4H_VARS @ [`g:real^N->bool`; `y:real^3`]) MOI_S4H_SD_BD_IN) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                     `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                     `rr:(real^N->bool)->real^3->bool`; `g:real^N->bool`; `y:real^3`]
                    MOI_S4G_SD_BD_SPLIT) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
       [ASM_MESON_TAC[];
        UNDISCH_TAC `~((y:real^3) IN
          UNIONS {(dd:(real^N->bool)->real^3->bool) s INTER
                  IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) | s |
                  s IN moi_s34_simp kk (&2) /\ v IN s /\ s SUBSET complex_boundary kk} UNION
          UNIONS {moi_s34_oarc tt kk f1 rr g | g |
                  g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET complex_boundary kk})` THEN
        REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN ASM_MESON_TAC[]];
      MP_TAC(ISPECL (MOI_S4H_VARS @ [`v:real^N`; `g:real^N->bool`]) MOI_S4H_VB_SD_EMPTY) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^3` o REWRITE_RULE[EXTENSION; IN_INTER; NOT_IN_EMPTY]) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[moi_s4h_kind]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4g_lab; ARITH_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC)) MP_TAC) THEN
  ASM_REWRITE_TAC[moi_s4g_tgtl; ARITH_EQ; MOI_S4G_CHOICE_SING] THEN DISCH_TAC THEN
  MP_TAC(ISPECL (MOI_S4H_VARS @ [`w:real^N`]) MOI_S4H_OPATCH_SUB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `y:real^3` o GEN_REWRITE_RULE I [SUBSET]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MOI_S4G_IN_IMAGE_INTER) THEN
  MP_TAC(ISPECL (MOI_S4H_VARS @ [`v:real^N`; `y:real^3`]) MOI_S4H_UNIQ_VB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o SPEC `w:real^N`)] THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* PROF10: points of the open outer arcs. *)

let MOI_S4H_PROF10 = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr g y.
     moi_s4h_hyp tt kk h ep f1 car dd rr /\ g IN moi_s34_simp kk (&1) /\
     g SUBSET complex_boundary kk /\ y IN moi_s34_oarc tt kk f1 rr g /\
     ~(y IN UNIONS {dd s INTER IMAGE f1 (moi_s34_sd tt kk g) | s |
                    s IN moi_s34_simp kk (&2) /\ g SUBSET s /\ s SUBSET complex_boundary kk})
     ==> moi_s4h_kind tt kk f1 dd rr y = 10 /\
         (!m q' x'. moi_s4g_lab tt kk m 10 q' x' /\ y IN moi_s4g_tgtl tt kk f1 dd rr 10 q' x'
                    ==> q' = g /\ x' = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MOI_S4H_UNFOLD_TAC THEN
  MP_TAC(ISPECL (MOI_S4H_VARS @ [`g:real^N->bool`]) MOI_S4H_OARC_SUB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `y:real^3` o GEN_REWRITE_RULE I [SUBSET]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MOI_S4G_IN_IMAGE_INTER) THEN
  SUBGOAL_THEN `(y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)` ASSUME_TAC THENL
   [MP_TAC(ISPECL (MOI_S4H_VARS @ [`y:real^3`]) MOI_S4H_IN_NB) THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(?r. r IN moi_s34_simp kk (&3) /\
                      (y:real^3) IN (rr:(real^N->bool)->real^3->bool) r)` ASSUME_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `(g:real^N->bool) SUBSET r` THENL
     [MP_TAC(ISPECL (MOI_S4H_VARS @ [`g:real^N->bool`; `r:real^N->bool`]) MOI_S4H_OA_EA) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^3` o GEN_REWRITE_RULE I [SUBSET]) THEN
      ASM_REWRITE_TAC[IN_INTER];
      MP_TAC(ISPECL (MOI_S4H_VARS @ [`r:real^N->bool`]) MOI_S4H_RR_FACTS) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `g:real^N->bool` o el 9 o CONJUNCTS) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^3` o REWRITE_RULE[EXTENSION; IN_INTER; NOT_IN_EMPTY]) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(?s. s IN moi_s34_simp kk (&2) /\
                      (y:real^3) IN (dd:(real^N->bool)->real^3->bool) s)` ASSUME_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL (MOI_S4H_VARS @ [`s:real^N->bool`]) MOI_S4H_DD_IN_RR) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `?g'. g' IN moi_s34_simp kk (&1) /\
                     (y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g')`
  ASSUME_TAC THENL [EXISTS_TAC `g:real^N->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[moi_s4h_kind]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4g_lab; ARITH_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[moi_s4g_tgtl; ARITH_EQ] THEN DISCH_TAC THEN
  MP_TAC(ISPECL (MOI_S4H_VARS @ [`q':real^N->bool`]) MOI_S4H_OARC_SUB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `y:real^3` o GEN_REWRITE_RULE I [SUBSET]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MOI_S4G_IN_IMAGE_INTER) THEN
  MP_TAC(ISPECL (MOI_S4H_VARS @ [`g:real^N->bool`; `y:real^3`]) MOI_S4H_UNIQ_SD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o SPEC `q':real^N->bool`)] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* An open cell determines its label; open cells of distinct source          *)
(* cells are disjoint; targets meet in the targets of their common faces.    *)
(* ------------------------------------------------------------------------- *)

let MOI_S4H_CASE_TAC (bs:thm) (prof:thm) (args:term list) : tactic =
  MP_TAC(ISPECL (MOI_S4H_VARS @ args) bs) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER]) THEN
  MATCH_MP_TAC prof THEN
  MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`;
                        `car:(real^N->bool)->real^3->bool`] THEN
  ASM_REWRITE_TAC[IN_INTER];;

let MOI_S4H_PROF_LAB = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr l k q x y.
     moi_s4h_hyp tt kk h ep f1 car dd rr /\ moi_s4g_lab tt kk l k q x /\
     y IN moi_s4h_oc tt kk f1 dd rr l
     ==> moi_s4h_kind tt kk f1 dd rr y = k /\
         (!m q' x'. moi_s4g_lab tt kk m k q' x' /\ y IN moi_s4g_tgtl tt kk f1 dd rr k q' x'
                    ==> q' = q /\ x' = x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MOI_S4H_UNFOLD_TAC THEN
  UNDISCH_TAC `(y:real^3) IN moi_s4h_oc tt kk (f1:real^N->real^3) dd rr l` THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                 `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                 `l:real^N->bool`; `k:num`; `q:real^N->bool`; `x:real^N->bool`]
                MOI_S4G_TGT_EVAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[moi_s4h_oc; moi_s4h_bs; IN_DIFF] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    let f,_ = strip_comb(concl th) in
    is_const f && fst(dest_const f) = "moi_s4g_lab")) THEN
  GEN_REWRITE_TAC LAND_CONV [moi_s4g_lab] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[moi_s4g_tgtl; ARITH_EQ; MOI_S4G_CHOICE_SING])) THENL
   [MOI_S4H_CASE_TAC MOI_S4G_BS1 MOI_S4H_PROF1 [`v:real^N`];
    MOI_S4H_CASE_TAC MOI_S4G_BS2 MOI_S4H_PROF2 [`q:real^N->bool`];
    MOI_S4H_CASE_TAC MOI_S4G_BS3 MOI_S4H_PROF3 [`q:real^N->bool`];
    MOI_S4H_CASE_TAC MOI_S4G_BS4 MOI_S4H_PROF4 [`q:real^N->bool`];
    MOI_S4H_CASE_TAC MOI_S4G_BS5 MOI_S4H_PROF5 [`q:real^N->bool`; `v:real^N`];
    MOI_S4H_CASE_TAC MOI_S4G_BS6 MOI_S4H_PROF6 [`q:real^N->bool`; `v:real^N`];
    MOI_S4H_CASE_TAC MOI_S4G_BS7 MOI_S4H_PROF7 [`q:real^N->bool`; `x:real^N->bool`];
    MOI_S4H_CASE_TAC MOI_S4G_BS8 MOI_S4H_PROF8 [`q:real^N->bool`; `x:real^N->bool`];
    MOI_S4H_CASE_TAC MOI_S4G_BS9 MOI_S4H_PROF9 [`v:real^N`];
    MOI_S4H_CASE_TAC MOI_S4G_BS10 MOI_S4H_PROF10 [`q:real^N->bool`]]);;

(* Open cells of distinct source cells are disjoint. *)

let MOI_S4H_OC_DISJ = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr l m y.
     moi_s4h_hyp tt kk h ep f1 car dd rr /\ l IN moi_s34_scells tt kk /\
     m IN moi_s34_scells tt kk /\ y IN moi_s4h_oc tt kk f1 dd rr l /\
     y IN moi_s4h_oc tt kk f1 dd rr m
     ==> l = m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOI_S4G_SCELLS_LAB] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `q:real^N->bool` (X_CHOOSE_TAC `x:real^N->bool`)))
    (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `k':num` (X_CHOOSE_THEN `q':real^N->bool` (X_CHOOSE_TAC `x':real^N->bool`)))
    STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4H_HYP) THEN
  MP_TAC(ISPECL (MOI_S4H_VARS @ [`l:real^N->bool`; `k:num`; `q:real^N->bool`;
                                 `x:real^N->bool`; `y:real^3`]) MOI_S4H_PROF_LAB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "idx")) THEN
  MP_TAC(ISPECL (MOI_S4H_VARS @ [`m:real^N->bool`; `k':num`; `q':real^N->bool`;
                                 `x':real^N->bool`; `y:real^3`]) MOI_S4H_PROF_LAB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `k':num = k` SUBST_ALL_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN moi_s4g_tgtl tt kk (f1:real^N->real^3) dd rr k q' x'` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                   `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                   `m:real^N->bool`; `k:num`; `q':real^N->bool`; `x':real^N->bool`]
                  MOI_S4G_TGT_EVAL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    UNDISCH_TAC `(y:real^3) IN moi_s4h_oc tt kk (f1:real^N->real^3) dd rr m` THEN
    REWRITE_TAC[moi_s4h_oc; IN_DIFF] THEN SIMP_TAC[];
    ALL_TAC] THEN
  USE_THEN "idx" (MP_TAC o SPECL [`m:real^N->bool`; `q':real^N->bool`; `x':real^N->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
  MATCH_MP_TAC MOI_S4G_LAB_FUN THEN
  MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                        `k:num`; `q:real^N->bool`; `x:real^N->bool`] THEN
  ASM_REWRITE_TAC[]);;

(* M1: targets meet in the targets of their common faces. *)

let MOI_S4H_MEET = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr l m.
     moi_s4h_hyp tt kk h ep f1 car dd rr /\ l IN moi_s34_scells tt kk /\
     m IN moi_s34_scells tt kk
     ==> moi_s34_tgt tt kk f1 dd rr l INTER moi_s34_tgt tt kk f1 dd rr m =
         UNIONS {moi_s34_tgt tt kk f1 dd rr n | n |
                 n IN moi_s34_scells tt kk /\ n SUBSET l /\ n SUBSET m}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_INTER] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL (MOI_S4H_VARS @ [`l:real^N->bool`]) MOI_S4H_OC_COVER) THEN
    MP_TAC(ISPECL (MOI_S4H_VARS @ [`m:real^N->bool`]) MOI_S4H_OC_COVER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\t:real^3->bool. (y:real^3) IN t`) THEN
    ASM_REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `n2:real^N->bool` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(MP_TAC o AP_TERM `\t:real^3->bool. (y:real^3) IN t`) THEN
    ASM_REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `n1:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL (MOI_S4H_VARS @ [`n1:real^N->bool`; `n2:real^N->bool`; `y:real^3`])
                  MOI_S4H_OC_DISJ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    EXISTS_TAC `n2:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:real^3) IN moi_s4h_oc tt kk (f1:real^N->real^3) dd rr n2` THEN
    REWRITE_TAC[moi_s4h_oc; IN_DIFF] THEN SIMP_TAC[];
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC; SUBSET_INTER] THEN
    X_GEN_TAC `n:real^N->bool` THEN STRIP_TAC THEN CONJ_TAC THEN
    MATCH_MP_TAC MOI_S4H_MONO THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`;
                          `car:(real^N->bool)->real^3->bool`] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Carriers of the targets (frame), and the size bound of RECOG_B.           *)
(* ------------------------------------------------------------------------- *)

let MOI_S4H_FRAME_CAR = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car.
     moi_s34_frame tt kk h ep f1 car
     ==> (!q. q IN kk /\ ~(q = {}) ==> open (car q) /\ IMAGE h q SUBSET car q) /\
         (!q q'. q IN kk /\ q' IN kk /\ ~(q = {}) /\ q SUBSET q' ==> car q SUBSET car q') /\
         (!v. {v} IN kk
              ==> IMAGE h (moi_s34_vb tt kk v) SUBSET car {v} /\
                  IMAGE f1 (moi_s34_vb tt kk v) SUBSET car {v}) /\
         (!y. y IN UNIONS {car q | q | q IN kk /\ ~(q = {})}
              ==> ?u. open u /\ y IN u /\
                      FINITE {q | q IN kk /\ ~(q = {}) /\ ~(car q INTER u = {})}) /\
         (!q x y z. q IN kk /\ x IN q /\ y IN car q /\ z IN car q
                    ==> dist(y,z) < ep x / &2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s34_frame] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THEN ASM_MESON_TAC[]);;

let MOI_S4H_SIMP_NE = prove
 (`!(kk:(real^N->bool)->bool) n s. s IN moi_s34_simp kk (&n) ==> ~(s = {})`,
  REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  UNDISCH_TAC `aff_dim(s:real^N->bool) = &n` THEN ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN
  INT_ARITH_TAC);;

(* A splitting disk lies in the carrier of its edge. *)

let MOI_S4H_SD_CAR = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr g.
     moi_s4h_hyp tt kk h ep f1 car dd rr /\ g IN moi_s34_simp kk (&1)
     ==> ?a. {a} IN kk /\ a IN g /\
             moi_s34_sd tt kk g SUBSET moi_s34_vb tt kk a /\
             IMAGE f1 (moi_s34_sd tt kk g) SUBSET car {a} /\ car {a} SUBSET car g`,
  REPEAT STRIP_TAC THEN MOI_S4H_UNFOLD_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4H_FRAME_CAR) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `g:real^N->bool`] MOI_S4O_EDGE_FORM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `g:real^N->bool`)) THEN
  EXISTS_TAC `a:real^N` THEN
  SUBGOAL_THEN `(a:real^N) IN segment[a,b]` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ENDS_IN_SEGMENT]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_s34_sd tt kk (segment[a,b]) SUBSET moi_s34_vb tt kk (a:real^N)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4G_SD_SUB_VB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk a)` THEN
    ASM_SIMP_TAC[IMAGE_SUBSET];
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 2)) THEN
    ASM_REWRITE_TAC[NOT_INSERT_EMPTY; SING_SUBSET] THEN
    ASM_MESON_TAC[MOI_S4H_SIMP_KK]]);;

let MOI_S4H_VB_CAR = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr v q.
     moi_s4h_hyp tt kk h ep f1 car dd rr /\ {v} IN kk /\ q IN kk /\ v IN q
     ==> IMAGE f1 (moi_s34_vb tt kk v) SUBSET car q /\
         IMAGE h (moi_s34_vb tt kk v) SUBSET car q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MOI_S4H_UNFOLD_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4H_FRAME_CAR) THEN
  SUBGOAL_THEN `car {v:real^N} SUBSET (car:(real^N->bool)->real^3->bool) q` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 2)) THEN
    ASM_REWRITE_TAC[NOT_INSERT_EMPTY; SING_SUBSET];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N` o check (fun th ->
    is_forall(concl th) && type_of(fst(dest_forall(concl th))) = `:real^N`)) THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let MOI_S4H_SD_CAR2 = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr g q.
     moi_s4h_hyp tt kk h ep f1 car dd rr /\ g IN moi_s34_simp kk (&1) /\ q IN kk /\
     g SUBSET q
     ==> IMAGE f1 (moi_s34_sd tt kk g) SUBSET car q /\
         IMAGE h (moi_s34_sd tt kk g) SUBSET car q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL (MOI_S4H_VARS @ [`g:real^N->bool`]) MOI_S4H_SD_CAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL (MOI_S4H_VARS @ [`a:real^N`; `q:real^N->bool`]) MOI_S4H_VB_CAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `moi_s34_sd tt kk g SUBSET moi_s34_vb tt kk (a:real^N)` THEN SET_TAC[]);;

let MOI_S4H_RR_FRONTIER_CAR = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr r.
     moi_s4h_hyp tt kk h ep f1 car dd rr /\ r IN moi_s34_simp kk (&3)
     ==> frontier (rr r) SUBSET car r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MOI_S4H_UNFOLD_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4H_FRAME_CAR) THEN
  MP_TAC(ISPECL (MOI_S4H_VARS @ [`r:real^N->bool`]) MOI_S4H_RR_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[el 4 (CONJUNCTS th)] THEN
    LABEL_TAC "dj" (el 5 (CONJUNCTS th))) THEN
  REWRITE_TAC[UNION_SUBSET; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `(car:(real^N->bool)->real^3->bool) s` THEN CONJ_TAC THENL
     [MP_TAC(ISPECL (MOI_S4H_VARS @ [`s:real^N->bool`]) MOI_S4H_DD_FACTS) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 2)) THEN
      ASM_MESON_TAC[MOI_S4H_SIMP_KK; MOI_S4H_SIMP_NE]];
    GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_INTER] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                   `(rr:(real^N->bool)->real^3->bool) r`; `r:real^N->bool`; `y:real^3`]
                  MOI_S4G_BD_COVER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[MOI_S4H_SIMP_KK];
        REPEAT STRIP_TAC THEN REWRITE_TAC[DISJOINT] THEN USE_THEN "dj" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL (MOI_S4H_VARS @ [`w:real^N`; `r:real^N->bool`]) MOI_S4H_VB_CAR) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[MOI_S4H_SIMP_KK]; ALL_TAC] THEN
    ASM SET_TAC[]]);;

(* The carrier of the index simplex of a label contains its target (tetra  *)
(* balls: their frontier).                                                  *)

let MOI_S4H_LAB_CAR = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr l k q x.
     moi_s4h_hyp tt kk h ep f1 car dd rr /\ moi_s4g_lab tt kk l k q x
     ==> q IN kk /\ ~(q = {}) /\
         (~(k = 4) ==> moi_s34_tgt tt kk f1 dd rr l SUBSET car q) /\
         (k = 4 ==> q IN moi_s34_simp kk (&3) /\ moi_s34_tgt tt kk f1 dd rr l = rr q /\
                    frontier (rr q) SUBSET car q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MOI_S4H_UNFOLD_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                 `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                 `l:real^N->bool`; `k:num`; `q:real^N->bool`; `x:real^N->bool`]
                MOI_S4G_TGT_EVAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    let f,_ = strip_comb(concl th) in
    is_const f && fst(dest_const f) = "moi_s4g_lab")) THEN
  GEN_REWRITE_TAC LAND_CONV [moi_s4g_lab] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[moi_s4g_tgtl; ARITH_EQ; MOI_S4G_CHOICE_SING; NOT_INSERT_EMPTY] THEN
  TRY(CONJ_TAC THENL [ASM_MESON_TAC[MOI_S4H_SIMP_KK]; ALL_TAC]) THEN
  TRY(CONJ_TAC THENL [ASM_MESON_TAC[MOI_S4H_SIMP_NE]; ALL_TAC]) THENL
   [(* 1 *) MP_TAC(ISPECL (MOI_S4H_VARS @ [`v:real^N`; `{v:real^N}`]) MOI_S4H_VB_CAR) THEN
    ASM_REWRITE_TAC[IN_SING] THEN SIMP_TAC[];
    (* 2 *) MP_TAC(ISPECL (MOI_S4H_VARS @ [`q:real^N->bool`; `q:real^N->bool`])
                          MOI_S4H_SD_CAR2) THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[MOI_S4H_SIMP_KK]; SIMP_TAC[]];
    (* 3 *) MP_TAC(ISPECL (MOI_S4H_VARS @ [`q:real^N->bool`]) MOI_S4H_DD_FACTS) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    (* 4 *) MATCH_MP_TAC MOI_S4H_RR_FRONTIER_CAR THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                          `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                          `dd:(real^N->bool)->real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    (* 5 *) MP_TAC(ISPECL (MOI_S4H_VARS @ [`v:real^N`; `q:real^N->bool`]) MOI_S4H_VB_CAR) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[MOI_S4H_SIMP_KK]; SET_TAC[]];
    (* 6 *) MP_TAC(ISPECL (MOI_S4H_VARS @ [`q:real^N->bool`]) MOI_S4H_DD_FACTS) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    (* 7 *) MP_TAC(ISPECL (MOI_S4H_VARS @ [`x:real^N->bool`; `q:real^N->bool`])
                          MOI_S4H_SD_CAR2) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[MOI_S4H_SIMP_KK]; SET_TAC[]];
    (* 8 *) MP_TAC(ISPECL (MOI_S4H_VARS @ [`q:real^N->bool`]) MOI_S4H_DD_FACTS) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    (* 9 *) MP_TAC(ISPECL (MOI_S4H_VARS @ [`v:real^N`]) MOI_S4H_OPATCH_SUB) THEN
    MP_TAC(ISPECL (MOI_S4H_VARS @ [`v:real^N`; `{v:real^N}`]) MOI_S4H_VB_CAR) THEN
    ASM_REWRITE_TAC[IN_SING] THEN SET_TAC[];
    (* 10 *) MP_TAC(ISPECL (MOI_S4H_VARS @ [`q:real^N->bool`]) MOI_S4H_OARC_SUB) THEN
    MP_TAC(ISPECL (MOI_S4H_VARS @ [`q:real^N->bool`; `q:real^N->bool`]) MOI_S4H_SD_CAR2) THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[MOI_S4H_SIMP_KK]; SET_TAC[]]]);;

(* The source cells of kinds 1, 2, 9, 10 lie in a vertex ball, with targets *)
(* in the image of that vertex ball.                                        *)

let MOI_S4H_VERT_CELL = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr l k q x.
     moi_s4h_hyp tt kk h ep f1 car dd rr /\ moi_s4g_lab tt kk l k q x /\
     (k = 1 \/ k = 2 \/ k = 9 \/ k = 10)
     ==> ?a. {a} IN kk /\ l SUBSET moi_s34_vb tt kk a /\
             moi_s34_tgt tt kk f1 dd rr l SUBSET IMAGE f1 (moi_s34_vb tt kk a)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MOI_S4H_UNFOLD_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                 `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                 `l:real^N->bool`; `k:num`; `q:real^N->bool`; `x:real^N->bool`]
                MOI_S4G_TGT_EVAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`] MOI_S4G_OUT_SUB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "o1") (LABEL_TAC "o2")) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    let f,_ = strip_comb(concl th) in
    is_const f && fst(dest_const f) = "moi_s4g_lab")) THEN
  GEN_REWRITE_TAC LAND_CONV [moi_s4g_lab] THEN STRIP_TAC THEN
  TRY(FIRST_X_ASSUM(MP_TAC o check (is_disj o concl)) THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
      NO_TAC) THEN
  ASM_REWRITE_TAC[ARITH_EQ; moi_s4g_tgtl; MOI_S4G_CHOICE_SING] THENL
   [(* 1 *) EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[SUBSET_REFL];
    (* 2 *) MP_TAC(ISPECL (MOI_S4H_VARS @ [`q:real^N->bool`]) MOI_S4H_SD_CAR) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN
    STRIP_TAC THEN ASM_SIMP_TAC[IMAGE_SUBSET];
    (* 9 *) EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "o1" (MP_TAC o SPEC `v:real^N`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SET_TAC[]];
      MP_TAC(ISPECL (MOI_S4H_VARS @ [`v:real^N`]) MOI_S4H_OPATCH_SUB) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    (* 10 *) MP_TAC(ISPECL (MOI_S4H_VARS @ [`q:real^N->bool`]) MOI_S4H_SD_CAR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "o2" (MP_TAC o SPEC `q:real^N->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `moi_s34_sd tt kk q SUBSET moi_s34_vb tt kk (a:real^N)` THEN SET_TAC[];
      MP_TAC(ISPECL (MOI_S4H_VARS @ [`q:real^N->bool`]) MOI_S4H_OARC_SUB) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `moi_s34_sd tt kk q SUBSET moi_s34_vb tt kk (a:real^N)` THEN SET_TAC[]]]);;

(* M3: a target and the h-image of its source cell are small at x. *)

let MOI_S4H_SMALL = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr l x y z.
     moi_s4h_hyp tt kk h ep f1 car dd rr /\ l IN moi_s34_scells tt kk /\
     x IN l /\ x IN UNIONS kk /\
     y IN IMAGE h l UNION moi_s34_tgt tt kk f1 dd rr l /\
     z IN IMAGE h l UNION moi_s34_tgt tt kk f1 dd rr l
     ==> dist(y,z) < ep x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MOI_S4H_UNFOLD_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4H_FRAME_CAR) THEN
  SUBGOAL_THEN `?sg. sg IN kk /\ (x:real^N) IN sg /\
                     IMAGE (h:real^N->real^3) l UNION moi_s34_tgt tt kk f1 dd rr l SUBSET
                     convex hull ((car:(real^N->bool)->real^3->bool) sg)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(l:real^N->bool) IN moi_s34_scells tt kk` THEN
    REWRITE_TAC[MOI_S4G_SCELLS_LAB] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `q:real^N->bool`
      (X_CHOOSE_TAC `x0:real^N->bool`))) THEN
    MP_TAC(ISPECL (MOI_S4H_VARS @ [`l:real^N->bool`; `k:num`; `q:real^N->bool`;
                                   `x0:real^N->bool`]) MOI_S4H_LAB_CAR) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_CASES_TAC `3 <= k /\ k <= 8` THENL
     [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `l:real^N->bool`;
                     `k:num`; `q:real^N->bool`; `x0:real^N->bool`] MOI_S4G_LAB_IN_KK) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXISTS_TAC `q:real^N->bool` THEN
      ASM_REWRITE_TAC[UNION_SUBSET] THEN REPEAT CONJ_TAC THENL
       [ASM SET_TAC[];
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `IMAGE (h:real^N->real^3) q` THEN ASM_SIMP_TAC[IMAGE_SUBSET] THEN
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `(car:(real^N->bool)->real^3->bool) q` THEN
        ASM_SIMP_TAC[HULL_SUBSET];
        ASM_CASES_TAC `k = 4` THENL
         [UNDISCH_TAC `k = 4 ==> q IN moi_s34_simp kk (&3) /\
                       moi_s34_tgt tt kk (f1:real^N->real^3) dd rr l = rr q /\
                       frontier ((rr:(real^N->bool)->real^3->bool) q) SUBSET car q` THEN
          ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
          MP_TAC(ISPECL (MOI_S4H_VARS @ [`q:real^N->bool`]) MOI_S4H_RR_FACTS) THEN
          ASM_REWRITE_TAC[] THEN SIMP_TAC[];
          MATCH_MP_TAC SUBSET_TRANS THEN
          EXISTS_TAC `(car:(real^N->bool)->real^3->bool) q` THEN
          REWRITE_TAC[HULL_SUBSET] THEN ASM_MESON_TAC[]]];
      MP_TAC(ISPECL (MOI_S4H_VARS @ [`l:real^N->bool`; `k:num`; `q:real^N->bool`;
                                     `x0:real^N->bool`]) MOI_S4H_VERT_CELL) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/
                      k = 9 \/ k = 10` MP_TAC THENL
         [UNDISCH_TAC `moi_s4g_lab tt kk l k q (x0:real^N->bool)` THEN
          REWRITE_TAC[moi_s4g_lab] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
          UNDISCH_TAC `~(3 <= k /\ k <= 8)` THEN ARITH_TAC];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `(x:real^N) IN UNIONS kk` THEN REWRITE_TAC[IN_UNIONS] THEN
      DISCH_THEN(X_CHOOSE_THEN `sg:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `sg:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(a:real^N) IN sg` ASSUME_TAC THENL
       [ONCE_REWRITE_TAC[TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
        MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `a:real^N`;
                       `sg:real^N->bool`] MOI_S4G_VB_OUT) THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL (MOI_S4H_VARS @ [`a:real^N`; `sg:real^N->bool`]) MOI_S4H_VB_CAR) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(ISPEC `(car:(real^N->bool)->real^3->bool) sg` (ISPEC `convex:(real^3->bool)->bool` HULL_SUBSET)) THEN
      UNDISCH_TAC `(l:real^N->bool) SUBSET moi_s34_vb tt kk a` THEN
      UNDISCH_TAC `moi_s34_tgt tt kk (f1:real^N->real^3) dd rr l SUBSET
                   IMAGE f1 (moi_s34_vb tt kk a)` THEN
      UNDISCH_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk a) SUBSET (car:(real^N->bool)->real^3->bool) sg` THEN
      UNDISCH_TAC `IMAGE (h:real^N->real^3) (moi_s34_vb tt kk a) SUBSET (car:(real^N->bool)->real^3->bool) sg` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a b. a IN convex hull ((car:(real^N->bool)->real^3->bool) sg) /\
                      b IN convex hull ((car:(real^N->bool)->real^3->bool) sg) ==> dist(a,b) <= ep (x:real^N) / &2`
  ASSUME_TAC THENL
   [REWRITE_TAC[DIST_CONVEX_HULL_BOUND_2] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (ep:real^N->real) x` ASSUME_TAC THENL
   [SUBGOAL_THEN `(h:real^N->real^3) x IN (car:(real^N->bool)->real^3->bool) sg` ASSUME_TAC THENL
     [SUBGOAL_THEN `IMAGE (h:real^N->real^3) sg SUBSET (car:(real^N->bool)->real^3->bool) sg` MP_TAC THENL
       [ASM_MESON_TAC[MEMBER_NOT_EMPTY]; ASM SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `dist((h:real^N->real^3) x,h x) < ep x / &2` MP_TAC THENL
     [ASM_MESON_TAC[]; REWRITE_TAC[DIST_REFL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `!d e. d <= e / &2 /\ &0 < e ==> d < e`) THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Local finiteness of the targets (M2).                                      *)
(* ------------------------------------------------------------------------- *)

let MOI_S4H_KD_LE = prove
 (`!k. moi_s4g_kd k <= 3`,
  GEN_TAC THEN REWRITE_TAC[moi_s4g_kd] THEN
  REPEAT COND_CASES_TAC THEN CONV_TAC NUM_REDUCE_CONV);;

(* A point of an open tetra ball lies in no other target. *)

let MOI_S4H_TB_INT = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr r l z.
     moi_s4h_hyp tt kk h ep f1 car dd rr /\ r IN moi_s34_simp kk (&3) /\
     l IN moi_s34_scells tt kk /\ z IN moi_s34_tgt tt kk f1 dd rr l /\
     z IN interior (rr r)
     ==> l = closure (r DIFF moi_s34_nb tt kk)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MOI_S4H_UNFOLD_TAC THEN
  ABBREV_TAC `tb = closure (r DIFF moi_s34_nb tt (kk:(real^N->bool)->bool))` THEN
  SUBGOAL_THEN `moi_s4g_lab tt kk tb 4 r ({}:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "tb" THEN REWRITE_TAC[moi_s4g_lab; ARITH_EQ] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(tb:real^N->bool) IN moi_s34_scells tt kk` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S4G_SCELLS_LAB] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3) IN moi_s4h_oc tt kk (f1:real^N->real^3) dd rr tb` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s4h_oc; IN_DIFF] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                   `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                   `tb:real^N->bool`; `4`; `r:real^N->bool`; `{}:real^N->bool`]
                  MOI_S4G_TGT_EVAL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[moi_s4g_tgtl; ARITH_EQ] THEN
    MP_TAC(ISPECL (MOI_S4H_VARS @ [`r:real^N->bool`]) MOI_S4G_BS4) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[GSYM moi_s4h_bs] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[frontier; IN_DIFF] THEN
    MP_TAC(ISPEC `(rr:(real^N->bool)->real^3->bool) r` INTERIOR_SUBSET) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL (MOI_S4H_VARS @ [`l:real^N->bool`]) MOI_S4H_OC_COVER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o AP_TERM `\t:real^3->bool. (z:real^3) IN t`) THEN
  ASM_REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL (MOI_S4H_VARS @ [`n:real^N->bool`; `tb:real^N->bool`; `z:real^3`])
                MOI_S4H_OC_DISJ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
  ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
  ONCE_REWRITE_TAC[TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `l:real^N->bool`;
                 `tb:real^N->bool`] MOI_S4H_DIM_LT) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(l:real^N->bool) IN moi_s34_scells tt kk` THEN
  REWRITE_TAC[MOI_S4G_SCELLS_LAB] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `q:real^N->bool`
    (X_CHOOSE_TAC `x:real^N->bool`))) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `l:real^N->bool`;
                 `k:num`; `q:real^N->bool`; `x:real^N->bool`] MOI_S4G_DIM) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `tb:real^N->bool`;
                 `4`; `r:real^N->bool`; `{}:real^N->bool`] MOI_S4G_DIM) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `moi_s4g_kd 4 = 3` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s4g_kd; ARITH_EQ]; ALL_TAC] THEN
  MP_TAC(SPEC `k:num` MOI_S4H_KD_LE) THEN ASM_ARITH_TAC);;

(* A simplex of kk contains finitely many simplices of kk. *)

let MOI_S4H_SUBSIMP_FINITE = prove
 (`!(tt:(real^N->bool)->bool) kk q.
     moi_s34_tube tt kk /\ q IN kk ==> FINITE {x | x IN kk /\ x SUBSET q}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `q:real^N->bool`] MOI_S4A_KK_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE (\E:real^N->bool. convex hull E) {E | E SUBSET V}` THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FINITE_POWERSET] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN
  X_GEN_TAC `x:real^N->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `x:real^N->bool`] MOI_S4A_KK_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `E:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `E:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `e:real^N` THEN DISCH_TAC THEN
  MATCH_MP_TAC MOI_S4A_VTX THEN
  MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`] THEN
  SUBGOAL_THEN `{e:real^N} IN kk` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `E:real^N->bool`;
                   `e:real^N`] MOI_S4A_VTX_KK) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^N) IN convex hull V` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`convex:(real^N->bool)->bool`; `E:real^N->bool`] HULL_SUBSET) THEN
    UNDISCH_TAC `(x:real^N->bool) SUBSET convex hull V` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_MESON_TAC[]);;

(* M2: local finiteness of the targets. *)

let MOI_S4H_LF = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr y.
     moi_s4h_hyp tt kk h ep f1 car dd rr /\
     y IN UNIONS {moi_s34_tgt tt kk f1 dd rr l | l | l IN moi_s34_scells tt kk}
     ==> ?u. open u /\ y IN u /\
             FINITE {l | l IN moi_s34_scells tt kk /\
                         ~(moi_s34_tgt tt kk f1 dd rr l INTER u = {})}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MOI_S4H_UNFOLD_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4H_FRAME_CAR) THEN
  UNDISCH_TAC `(y:real^3) IN UNIONS {moi_s34_tgt tt kk (f1:real^N->real^3) dd rr l | l |
                                     l IN moi_s34_scells tt kk}` THEN
  REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `l0:real^N->bool` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `?r. r IN moi_s34_simp kk (&3) /\
                     (y:real^3) IN interior ((rr:(real^N->bool)->real^3->bool) r)` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `interior ((rr:(real^N->bool)->real^3->bool) r)` THEN
    ASM_REWRITE_TAC[OPEN_INTERIOR] THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{closure (r DIFF moi_s34_nb tt (kk:(real^N->bool)->bool))}` THEN
    REWRITE_TAC[FINITE_SING; SUBSET; IN_ELIM_THM; IN_SING] THEN
    X_GEN_TAC `l:real^N->bool` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC)) THEN
    MATCH_MP_TAC MOI_S4H_TB_INT THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                          `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                          `rr:(real^N->bool)->real^3->bool`; `z:real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* y lies in the carrier of the index simplex of l0 *)
  SUBGOAL_THEN `?q0. q0 IN kk /\ ~(q0 = {}) /\
                     (y:real^3) IN (car:(real^N->bool)->real^3->bool) q0`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(l0:real^N->bool) IN moi_s34_scells tt kk` THEN
    REWRITE_TAC[MOI_S4G_SCELLS_LAB] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `q:real^N->bool`
      (X_CHOOSE_TAC `x:real^N->bool`))) THEN
    MP_TAC(ISPECL (MOI_S4H_VARS @ [`l0:real^N->bool`; `k:num`; `q:real^N->bool`;
                                   `x:real^N->bool`]) MOI_S4H_LAB_CAR) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXISTS_TAC `q:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `k = 4` THENL
     [UNDISCH_TAC `k = 4 ==> q IN moi_s34_simp kk (&3) /\
                   moi_s34_tgt tt kk (f1:real^N->real^3) dd rr l0 = rr q /\
                   frontier ((rr:(real^N->bool)->real^3->bool) q) SUBSET car q` THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(ISPECL (MOI_S4H_VARS @ [`q:real^N->bool`]) MOI_S4H_RR_FACTS) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o el 2 o CONJUNCTS) THEN
      SUBGOAL_THEN `(y:real^3) IN frontier ((rr:(real^N->bool)->real^3->bool) q)` MP_TAC THENL
       [REWRITE_TAC[frontier; IN_DIFF] THEN
        ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
        CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[]];
        ASM SET_TAC[]];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
    is_forall(concl th) && type_of(fst(dest_forall(concl th))) = `:real^3`)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u0:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `u0:real^3->bool` OPEN_CONTAINS_BALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `ball(y:real^3,e)` THEN ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
  ABBREV_TAC `Q = {q | q IN kk /\ ~(q = {}) /\
                       ~((car:(real^N->bool)->real^3->bool) q INTER u0 = {})}` THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `UNIONS {{moi_s4g_cell (tt:(real^N->bool)->bool) kk k q x | k,x |
                       k IN 1..10 /\ x IN {} INSERT {z | z IN kk /\ z SUBSET q}} | q |
                      q IN (Q:(real^N->bool)->bool)}` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FINITE_UNIONS] THEN CONJ_TAC THENL
     [REWRITE_TAC[SIMPLE_IMAGE] THEN MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `q:real^N->bool` THEN DISCH_TAC THEN
      MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN REWRITE_TAC[FINITE_NUMSEG; FINITE_INSERT] THEN
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_S4H_SUBSIMP_FINITE THEN
      EXISTS_TAC `tt:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(q:real^N->bool) IN Q` THEN EXPAND_TAC "Q" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `l:real^N->bool` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[MOI_S4G_SCELLS_LAB] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `q:real^N->bool`
    (X_CHOOSE_TAC `x:real^N->bool`))) THEN
  MP_TAC(ISPECL (MOI_S4H_VARS @ [`l:real^N->bool`; `k:num`; `q:real^N->bool`;
                                 `x:real^N->bool`]) MOI_S4H_LAB_CAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN EXISTS_TAC `q:real^N->bool` THEN
  MATCH_MP_TAC(TAUT `!a b. b /\ a ==> a /\ b`) THEN CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`k:num`; `x:real^N->bool`] THEN
    REWRITE_TAC[IN_NUMSEG; IN_INSERT; IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `moi_s4g_lab tt kk l k q (x:real^N->bool)` THEN
      REWRITE_TAC[moi_s4g_lab] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      UNDISCH_TAC `moi_s4g_lab tt kk l k q (x:real^N->bool)` THEN
      REWRITE_TAC[moi_s4g_lab] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      UNDISCH_TAC `moi_s4g_lab tt kk l k q (x:real^N->bool)` THEN
      REWRITE_TAC[moi_s4g_lab] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[MOI_S4H_SIMP_KK; SING_SUBSET];
      MATCH_MP_TAC MOI_S4G_LAB_CELL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EXPAND_TAC "Q" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `k = 4` THENL
     [UNDISCH_TAC `k = 4 ==> q IN moi_s34_simp kk (&3) /\
                   moi_s34_tgt tt kk (f1:real^N->real^3) dd rr l = rr q /\
                   frontier ((rr:(real^N->bool)->real^3->bool) q) SUBSET car q` THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      UNDISCH_TAC `~(moi_s34_tgt tt kk (f1:real^N->real^3) dd rr l INTER ball(y,e) = {})` THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `~(ball(y:real^3,e) INTER frontier ((rr:(real^N->bool)->real^3->bool) q) = {})`
      MP_TAC THENL
       [MATCH_MP_TAC CONNECTED_INTER_FRONTIER THEN REWRITE_TAC[CONNECTED_BALL] THEN
        CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
        UNDISCH_TAC `~(?r. r IN moi_s34_simp kk (&3) /\
                         (y:real^3) IN interior ((rr:(real^N->bool)->real^3->bool) r))` THEN
        REWRITE_TAC[] THEN EXISTS_TAC `q:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`(rr:(real^N->bool)->real^3->bool) q`; `ball(y:real^3,e)`]
                      INTERIOR_MAXIMAL) THEN
        REWRITE_TAC[OPEN_BALL] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        MP_TAC(ISPECL [`y:real^3`; `e:real`] CENTRE_IN_BALL) THEN ASM_REWRITE_TAC[] THEN
        SET_TAC[];
        ASM SET_TAC[]];
      ASM SET_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* RECOG_B.                                                                   *)
(* ------------------------------------------------------------------------- *)

let RECOG_B = prove
 (MOI_S34_RECOG_B,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_s4h_hyp tt kk h ep (f1:real^N->real^3) car dd rr` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[moi_s4h_hyp]; ALL_TAC] THEN
  REWRITE_TAC[moi_s34_tgt_meets] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S4H_MEET THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`;
                          `car:(real^N->bool)->real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_S4H_LF THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`;
                          `car:(real^N->bool)->real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S4H_SMALL THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                          `h:real^N->real^3`;
                          `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                          `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                          `l:real^N->bool`] THEN
    ASM_REWRITE_TAC[]]);;


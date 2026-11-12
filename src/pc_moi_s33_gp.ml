(* ========================================================================= *)
(* pc_moi_s33_gp: general position of a loop theorem disk against the       *)
(* pseudo-cells (Moise GTM 47, 33.1 Lemma 9 p.234, the general position     *)
(* step; the idea follows DG's exists_isLoopTheoremDisk_levelSet).  Main    *)
(* theorem S39_GP : |- MOI_S39_GP_BODY (pc_moi_s33_l9stmt.ml).  Route:      *)
(* the sheet d1 of the second-derived neighbourhood of d in a box           *)
(* triangulation that also triangulates a polyhedral piece P of the         *)
(* pseudo-cells near d; d1 INTER PCS is cut out of the PL circles of the    *)
(* derived frontier of P at the crossing points with Bd X.                  *)
(* ========================================================================= *)

needs "src/pc_moi_s33_l9stmt.ml";;
needs "src/pc_moi_fnd_split.ml";;
needs "src/pc_moi_pl1m.ml";;
needs "src/pc_moi_s30_comp.ml";;
needs "src/pc_moi_s33_x2.ml";;
needs "src/pc_moi_s33_fr2.ml";;
needs "src/pc_moi_fnd_sptrace.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Part 1: sides of BX.  In a chart at a frontier point of a closed         *)
(* set X equal to the closure of its interior, in which the frontier is the *)
(* plane y$2 = 0, one open half-ball lies in the interior of X and the      *)
(* other misses X.                                                           *)
(* ------------------------------------------------------------------------- *)

let MOI_S3GP_CHART_SIDE = prove
 (`!(X:real^3->bool) (u:real^3->bool) (h:real^3->real^3) h' z.
     closed X /\ closure (interior X) = X /\
     open u /\ z IN u /\ homeomorphism (u,IMAGE h u) (h,h') /\ open (IMAGE h u) /\
     h z = vec 0 /\
     IMAGE h (frontier X INTER u) = IMAGE h u INTER {y:real^3 | y$2 = &0}
     ==> ?r. &0 < r /\ ball(vec 0,r) SUBSET IMAGE h u /\
             ((!y. y IN ball(vec 0,r) /\ &0 < y$2 ==> h' y IN interior X) /\
              (!y. y IN ball(vec 0,r) /\ y$2 < &0 ==> ~(h' y IN X)) \/
              (!y. y IN ball(vec 0,r) /\ y$2 < &0 ==> h' y IN interior X) /\
              (!y. y IN ball(vec 0,r) /\ &0 < y$2 ==> ~(h' y IN X)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `homeomorphism (u:real^3->bool,IMAGE (h:real^3->real^3) u) (h,h')` THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `vec 0 IN IMAGE (h:real^3->real^3) u` ASSUME_TAC THENL
   [UNDISCH_TAC `(h:real^3->real^3) z = vec 0` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `vec 0:real^3` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL] o
    check (fun th -> concl th = `open (IMAGE (h:real^3->real^3) u)`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `frontier X = (X:real^3->bool) DIFF interior X` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP CLOSURE_CLOSED (ASSUME `closed (X:real^3->bool)`)) THEN
    REWRITE_TAC[frontier] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* z is a frontier point *)
  SUBGOAL_THEN `(z:real^3) IN frontier X` ASSUME_TAC THENL
   [SUBGOAL_THEN `(h:real^3->real^3) z IN IMAGE h (frontier X INTER u)` MP_TAC THENL
     [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; VEC_COMPONENT]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `w:real^3 = z` (fun th -> ASM_MESON_TAC[th]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  (* the chart points off the plane miss the frontier, those on it hit it *)
  SUBGOAL_THEN `!y:real^3. y IN ball(vec 0,r)
                           ==> ((h':real^3->real^3) y IN frontier X <=> y$2 = &0) /\ h' y IN u /\
                               (h:real^3->real^3) (h' y) = y`
  (LABEL_TAC "pl") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN IMAGE (h:real^3->real^3) u` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(h':real^3->real^3) y IN u /\ h (h' y) = y` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM SET_TAC[]; FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EQ_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `(y:real^3) IN IMAGE (h:real^3->real^3) (frontier X INTER u)` MP_TAC THENL
       [REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EXISTS_TAC `(h':real^3->real^3) y` THEN
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN SIMP_TAC[]];
      DISCH_TAC THEN
      SUBGOAL_THEN `(y:real^3) IN IMAGE (h:real^3->real^3) (frontier X INTER u)` MP_TAC THENL
       [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM]; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
      DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(h':real^3->real^3) y = w` (fun th -> ASM_REWRITE_TAC[th]) THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  (* each convex open part of the ball off the plane maps into int X or misses X *)
  SUBGOAL_THEN
   `!H. convex H /\ H SUBSET ball(vec 0,r) /\ (!y:real^3. y IN H ==> ~(y$2 = &0))
        ==> (!y. y IN H ==> (h':real^3->real^3) y IN interior X) \/
            (!y. y IN H ==> ~(h' y IN X))`
  (LABEL_TAC "half") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `connected (IMAGE (h':real^3->real^3) H)` ASSUME_TAC THENL
     [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_SIMP_TAC[CONVEX_CONNECTED] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `IMAGE (h:real^3->real^3) u` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (h':real^3->real^3) H INTER frontier X = {}` ASSUME_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
      X_GEN_TAC `x:real^3` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) MP_TAC) THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "pl" (MP_TAC o C MATCH_MP
        (MATCH_MP (SET_RULE `(y:real^3) IN H /\ H SUBSET b ==> y IN b`)
          (CONJ (ASSUME `(y:real^3) IN H`) (ASSUME `H SUBSET ball(vec 0:real^3,r)`)))) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `IMAGE (h':real^3->real^3) H SUBSET X` THENL
     [DISJ1_TAC THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      UNDISCH_TAC `IMAGE (h':real^3->real^3) H INTER frontier X = {}` THEN
      UNDISCH_TAC `IMAGE (h':real^3->real^3) H SUBSET X` THEN
      UNDISCH_TAC `frontier X = (X:real^3->bool) DIFF interior X` THEN
      UNDISCH_TAC `(y:real^3) IN H` THEN SET_TAC[];
      DISJ2_TAC THEN
      MP_TAC(ISPECL [`IMAGE (h':real^3->real^3) H`; `X:real^3->bool`]
                    CONNECTED_INTER_FRONTIER) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(IMAGE (h':real^3->real^3) H SUBSET X)` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `convex {y:real^3 | y IN ball(vec 0,r) /\ &0 < y$2} /\
    convex {y:real^3 | y IN ball(vec 0,r) /\ y$2 < &0}` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SET_RULE `{y:real^3 | y IN s /\ P y} = s INTER {y | P y}`] THEN
    CONJ_TAC THEN MATCH_MP_TAC CONVEX_INTER THEN REWRITE_TAC[CONVEX_BALL] THEN
    REWRITE_TAC[GSYM real_gt; CONVEX_HALFSPACE_COMPONENT_GT; CONVEX_HALFSPACE_COMPONENT_LT];
    ALL_TAC] THEN
  REMOVE_THEN "half" (fun th ->
    MP_TAC(SPEC `{y:real^3 | y IN ball(vec 0,r) /\ y$2 < &0}` th) THEN
    MP_TAC(SPEC `{y:real^3 | y IN ball(vec 0,r) /\ &0 < y$2}` th)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN SIMP_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN SIMP_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  (* the open set W of points mapped into the ball *)
  ABBREV_TAC `W = {x:real^3 | x IN u /\ (h:real^3->real^3) x IN ball(vec 0,r)}` THEN
  SUBGOAL_THEN `open (W:real^3->bool) /\ (z:real^3) IN W /\
                (!x. x IN W ==> (h:real^3->real^3) x IN ball(vec 0,r) /\
                                (h':real^3->real^3) (h x) = x)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[OPEN_BALL];
      ASM_REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL];
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj (concl th) &&
    can (find_term (fun t -> t = `&0 < (y:real^3)$2`)) (concl th))) THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj (concl th) &&
    can (find_term (fun t -> t = `(y:real^3)$2 < &0`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THENL
   [(* both halves inside: z would be interior *)
    SUBGOAL_THEN `(W:real^3->bool) SUBSET X` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(h:real^3->real^3) x IN ball(vec 0,r) /\ h' (h x) = x`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBST1_TAC(SYM(ASSUME `(h':real^3->real^3) (h x) = x`)) THEN
      REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
        (REAL_ARITH `&0 < ((h:real^3->real^3) x)$2 \/ (h x)$2 < &0 \/ (h x)$2 = &0`) THENL
       [ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET];
        ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET];
        USE_THEN "pl" (MP_TAC o C MATCH_MP
          (ASSUME `(h:real^3->real^3) x IN ball(vec 0,r)`)) THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^3) IN interior X` MP_TAC THENL
     [REWRITE_TAC[IN_INTERIOR] THEN
      FIRST_ASSUM(MP_TAC o SPEC `z:real^3` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL] o
        check (fun th -> concl th = `open (W:real^3->bool)`)) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC[];
      MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
      UNDISCH_TAC `(z:real^3) IN frontier X` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]];
    (* both halves outside: interior points near z are missing *)
    SUBGOAL_THEN `~((W:real^3->bool) INTER interior X = {})` MP_TAC THENL
     [MP_TAC(ISPECL [`W:real^3->bool`; `interior X:real^3->bool`]
                    OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `z:real^3` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(z:real^3) IN frontier X` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(h:real^3->real^3) x IN ball(vec 0,r) /\ h' (h x) = x`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
      (REAL_ARITH `&0 < ((h:real^3->real^3) x)$2 \/ (h x)$2 < &0 \/ (h x)$2 = &0`) THENL
     [ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET];
      ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET];
      MATCH_MP_TAC(TAUT `F ==> p`) THEN
      USE_THEN "pl" (MP_TAC o C MATCH_MP
        (ASSUME `(h:real^3->real^3) x IN ball(vec 0,r)`)) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(x:real^3) IN interior X` THEN SET_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Part 2: the pseudo-cells near W.  Each point of PCS INTER W has a        *)
(* neighbourhood in which PCS is one pseudo-cell interior (locally          *)
(* polyhedral, locally a plane); a compact d in W has an open               *)
(* neighbourhood v in W in which PCS lies in a compact polyhedron q made of *)
(* finitely many polytopes inside PCS INTER W.                              *)
(* ------------------------------------------------------------------------- *)

(* Set reasoning on the goal with its set-valued atoms generalized (the     *)
(* tactic MOI_S3L8_ASET_TAC of pc_moi_s33_l8, which is not in this closure). *)

let MOI_S3GP_ASET_TAC : tactic =
  let setops = ["INTER"; "UNION"; "DIFF"; "INSERT"; "EMPTY"; "UNIV"; "DELETE"] in
  let is_set_ty ty =
    (try (match dest_type ty with ("fun",[_;b]) -> b = bool_ty | _ -> false) with Failure _ -> false) in
  let rec tsize t =
    if is_comb t then tsize (rator t) + tsize (rand t) else if is_abs t then 1 + tsize (body t) else 1 in
  let rec collect bvs t acc =
    if is_abs t then
      (let v,b = dest_abs t in collect (v::bvs) b acc)
    else if is_comb t then
       (let hop,args = strip_comb t in
        let isop = is_const hop && mem (fst(dest_const hop)) setops in
        if is_set_ty (type_of t) && not isop && intersect (frees t) bvs = []
        then insert t acc
        else itlist (collect bvs) (hop::args) acc)
    else acc in
  fun (asl,w as g) ->
    let ats = collect [] w [] in
    let ats = sort (fun a b -> tsize a > tsize b) ats in
    (MAP_EVERY (fun t -> SPEC_TAC(t,genvar(type_of t))) ats THEN SET_TAC[]) g;;

let MOI_S3GP_PCS_CLOSED = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c.
     moi_s33_hd t l h e c
     ==> FINITE {e s | s IN l /\ aff_dim s = &1} /\
         (!s. s IN l /\ aff_dim s = &1 ==> closed (e s)) /\
         closed (moi_s39_pcs l e) /\ open (moi_s33_ww t l h)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [moi_s33_hd]) THEN
  SUBGOAL_THEN `FINITE (l:(real^3->bool)->bool) /\
                compact (IMAGE (h:real^3->real^3) (UNIONS l))` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[TUBE_FACTS]; ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^3->bool. s IN l /\ aff_dim s = &1
                                 ==> closed ((e:(real^3->bool)->real^3->bool) s)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real^3->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                   `s:real^3->bool`] MOI_S3X2_TUBE_EDGE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^3` (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                   `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                   `u:real^3`; `v:real^3`] MOI_S3X2_HD_EDGE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {(e:(real^3->bool)->real^3->bool) s | s IN l /\ aff_dim s = &1}`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
    MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[moi_s39_pcs] THEN MATCH_MP_TAC CLOSED_UNIONS THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN ASM_MESON_TAC[];
    REWRITE_TAC[moi_s33_ww] THEN MATCH_MP_TAC OPEN_DIFF THEN
    ASM_SIMP_TAC[OPEN_INTERIOR; COMPACT_IMP_CLOSED]]);;

(* Near a point z of PCS INTER W, PCS is the pseudo-cell through z.         *)

let MOI_S3GP_PCS_LOCAL = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c z.
     moi_s33_hd t l h e c /\ z IN moi_s39_pcs l e /\ z IN moi_s33_ww t l h
     ==> ?u v w. ~(u = v) /\ segment[u,v] IN l /\ z IN e(segment[u,v]) /\
                 e(segment[u,v]) SUBSET moi_s39_pcs l e /\
                 e(segment[u,v]) INTER moi_s33_ww t l h =
                 (e(segment[u,v]) DIFF moi_s33_rim t l h u v) DELETE h(midpoint(u,v)) /\
                 locally_polyhedral
                   ((e(segment[u,v]) DIFF moi_s33_rim t l h u v) DELETE h(midpoint(u,v))) /\
                 (!y. y IN (e(segment[u,v]) DIFF moi_s33_rim t l h u v) DELETE
                           h(midpoint(u,v))
                      ==> moi_s28_locally_r2
                            ((e(segment[u,v]) DIFF moi_s33_rim t l h u v) DELETE
                             h(midpoint(u,v))) y) /\
                 open w /\ z IN w /\ w SUBSET moi_s33_ww t l h /\
                 moi_s39_pcs l e INTER w = e(segment[u,v]) INTER w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`]
                MOI_S3GP_PCS_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [moi_s33_hd]) THEN
  FIRST_ASSUM(LABEL_TAC "dis" o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
    GEN_REWRITE_RULE I [moi_s33_hd]) THEN
  SUBGOAL_THEN `?s:real^3->bool. s IN l /\ aff_dim s = &1 /\
                                 (z:real^3) IN (e:(real^3->bool)->real^3->bool) s`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^3) IN moi_s39_pcs l e` THEN
    REWRITE_TAC[moi_s39_pcs; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `s:real^3->bool`] MOI_S3X2_TUBE_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3` (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `u:real^3`; `v:real^3`] MOI_S3X2_HD_EDGE) THEN
  ASM_REWRITE_TAC[GSYM moi_s33_ww] THEN STRIP_TAC THEN
  ABBREV_TAC `G = UNIONS {(e:(real^3->bool)->real^3->bool) s' |
                          s' IN l /\ aff_dim s' = &1 /\ ~(s' = segment[u:real^3,v])}` THEN
  SUBGOAL_THEN `moi_s39_pcs l (e:(real^3->bool)->real^3->bool) =
                e(segment[u:real^3,v]) UNION G` ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN REWRITE_TAC[moi_s39_pcs; GSYM UNIONS_INSERT] THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `E:real^3->bool` THEN
    REWRITE_TAC[IN_INSERT; IN_ELIM_THM] THEN
    MP_TAC(CONJ (ASSUME `segment[u:real^3,v] IN l`)
                (ASSUME `aff_dim(segment[u:real^3,v]) = &1`)) THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (G:real^3->bool) /\
                DISJOINT ((e:(real^3->bool)->real^3->bool) (segment[u:real^3,v])) G`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `{(e:(real^3->bool)->real^3->bool) s | s IN l /\ aff_dim s = &1}` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        REWRITE_TAC[FORALL_IN_GSPEC] THEN ASM_MESON_TAC[]];
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_UNIONS; IN_ELIM_THM] THEN
      X_GEN_TAC `y:real^3` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `E:real^3->bool` MP_TAC)) THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s':real^3->bool` STRIP_ASSUME_TAC)
        ASSUME_TAC) THEN
      USE_THEN "dis" (MP_TAC o SPECL [`s':real^3->bool`; `segment[u:real^3,v]`]) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`u:real^3`; `v:real^3`; `moi_s33_ww t l h DIFF (G:real^3->bool)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SET_TAC[];
    MATCH_MP_TAC OPEN_DIFF THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_DIFF] THEN ASM SET_TAC[];
    SET_TAC[];
    SET_TAC[]]);;

(* PCS INTER W is locally polyhedral.                                        *)

let MOI_S3GP_PCS_W_LP = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c.
     moi_s33_hd t l h e c
     ==> locally_polyhedral (moi_s39_pcs l e INTER moi_s33_ww t l h)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[locally_polyhedral; IN_INTER] THEN
  X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`; `z:real^3`]
                MOI_S3GP_PCS_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3` (X_CHOOSE_THEN `v:real^3` (X_CHOOSE_THEN
    `w:real^3->bool` STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `E0 = ((e:(real^3->bool)->real^3->bool)(segment[u,v]) DIFF
                    moi_s33_rim t l h u v) DELETE (h:real^3->real^3)(midpoint(u,v))` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o GEN_REWRITE_RULE I [locally_polyhedral] o
    check (fun th -> concl th = `locally_polyhedral (E0:real^3->bool)`)) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cc:(real^3->bool)->bool` (X_CHOOSE_THEN `uu:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`cc:(real^3->bool)->bool`; `uu INTER w:real^3->bool`] THEN
  ASM_SIMP_TAC[OPEN_INTER; IN_INTER] THEN CONJ_TAC THENL
   [ASM SET_TAC[]; ASM SET_TAC[]]);;

(* A compact subset of a locally polyhedral set has an open neighbourhood   *)
(* in which the set is covered by finitely many polytopes inside it.        *)

let MOI_S3GP_LP_COVER = prove
 (`!(S:real^N->bool) K.
     locally_polyhedral S /\ compact K /\ K SUBSET S
     ==> ?c u. FINITE c /\ (!k. k IN c ==> polytope k /\ k SUBSET S) /\
               open u /\ K SUBSET u /\ S INTER u SUBSET UNIONS c`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] o
    GEN_REWRITE_RULE I [locally_polyhedral]) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real^N->(real^N->bool)->bool`
    (X_CHOOSE_THEN `U:real^N->real^N->bool` (LABEL_TAC "lp"))) THEN
  FIRST_ASSUM(MP_TAC o SPEC `IMAGE (U:real^N->real^N->bool) K` o
    GEN_REWRITE_RULE I [COMPACT_EQ_HEINE_BOREL]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`U:real^N->real^N->bool`; `K:real^N->bool`; `f:(real^N->bool)->bool`]
                FINITE_SUBSET_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `F0:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `UNIONS (IMAGE (C:real^N->(real^N->bool)->bool) F0)` THEN
  EXISTS_TAC `UNIONS (IMAGE (U:real^N->real^N->bool) F0)` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[FINITE_UNIONS] THEN ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC[SUBSET];
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN ASM_MESON_TAC[SUBSET];
    MATCH_MP_TAC OPEN_UNIONS THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_MESON_TAC[SUBSET];
    ASM_MESON_TAC[];
    REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    X_GEN_TAC `y:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC)) THEN
    REMOVE_THEN "lp" (MP_TAC o SPEC `x:real^N`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* The polyhedral piece q of PCS near d.                                     *)

let MOI_S3GP_PIECE = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c d.
     moi_s33_hd t l h e c /\ compact d /\ d SUBSET moi_s33_ww t l h
     ==> ?q v. pl_polyhedron q /\ compact q /\
               q SUBSET moi_s39_pcs l e INTER moi_s33_ww t l h /\
               open v /\ d SUBSET v /\ v SUBSET moi_s33_ww t l h /\
               moi_s39_pcs l e INTER v SUBSET q`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`]
                MOI_S3GP_PCS_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`moi_s39_pcs l (e:(real^3->bool)->real^3->bool) INTER moi_s33_ww t l h`;
                 `d INTER moi_s39_pcs l (e:(real^3->bool)->real^3->bool)`]
                MOI_S3GP_LP_COVER) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S3GP_PCS_W_LP THEN
      EXISTS_TAC `c:real^3->real^3->bool` THEN ASM_REWRITE_TAC[];
      CONJ_TAC THENL [ASM_SIMP_TAC[COMPACT_INTER_CLOSED]; ASM SET_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cc:(real^3->bool)->bool` (X_CHOOSE_THEN `u:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `UNIONS cc:real^3->bool` THEN
  EXISTS_TAC `moi_s33_ww t l h INTER
              (u UNION ((:real^3) DIFF moi_s39_pcs l (e:(real^3->bool)->real^3->bool)))` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[pl_polyhedron] THEN EXISTS_TAC `cc:(real^3->bool)->bool` THEN
    ASM_MESON_TAC[];
    MATCH_MP_TAC COMPACT_UNIONS THEN ASM_MESON_TAC[POLYTOPE_IMP_COMPACT];
    REWRITE_TAC[UNIONS_SUBSET] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_UNION THEN
    ASM_REWRITE_TAC[GSYM closed];
    ASM SET_TAC[];
    SET_TAC[];
    ASM SET_TAC[]]);;

(* The piece embeds locally in the plane at each of its points, and is      *)
(* locally a plane at its points in v.                                       *)

let MOI_S3GP_PIECE_EMB2 = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c q y.
     moi_s33_hd t l h e c /\ q SUBSET moi_s39_pcs l e INTER moi_s33_ww t l h /\ y IN q
     ==> moi_s8ta_emb2 q y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`; `y:real^3`]
                MOI_S3GP_PCS_LOCAL) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^3` (X_CHOOSE_THEN `b:real^3` (X_CHOOSE_THEN
    `w:real^3->bool` STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `E0 = ((e:(real^3->bool)->real^3->bool)(segment[a,b]) DIFF
                    moi_s33_rim t l h a b) DELETE (h:real^3->real^3)(midpoint(a,b))` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
    is_forall (concl th) &&
    can (find_term (fun u -> u = `moi_s28_locally_r2:(real^3->bool)->real^3->bool`))
        (concl th))) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[moi_s28_locally_r2; homeomorphic; OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:real^3->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `O:real^3->bool` STRIP_ASSUME_TAC) (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `f:real^3->real^2` (X_CHOOSE_THEN `g:real^2->real^3` ASSUME_TAC))))) THEN
  REWRITE_TAC[moi_s8ta_emb2] THEN
  MAP_EVERY EXISTS_TAC [`q INTER (O INTER w):real^3->bool`; `f:real^3->real^2`;
                        `g:real^2->real^3`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_SIMP_TAC[OPEN_INTER];
    ASM SET_TAC[];
    MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`U:real^3->bool`; `(:real^2)`] THEN
    ASM_REWRITE_TAC[SUBSET_UNIV] THEN ASM SET_TAC[]]);;

let MOI_S3GP_PIECE_R2 = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c q v y.
     moi_s33_hd t l h e c /\ q SUBSET moi_s39_pcs l e /\
     open v /\ v SUBSET moi_s33_ww t l h /\ moi_s39_pcs l e INTER v SUBSET q /\
     y IN q /\ y IN v
     ==> moi_s28_locally_r2 q y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`; `y:real^3`]
                MOI_S3GP_PCS_LOCAL) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^3` (X_CHOOSE_THEN `b:real^3` (X_CHOOSE_THEN
    `w:real^3->bool` STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `E0 = ((e:(real^3->bool)->real^3->bool)(segment[a,b]) DIFF
                    moi_s33_rim t l h a b) DELETE (h:real^3->real^3)(midpoint(a,b))` THEN
  SUBGOAL_THEN `E0 INTER (w INTER v) = q INTER (w INTER v:real^3->bool)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_S8CU_R2_SUPER THEN EXISTS_TAC `q INTER (w INTER v):real^3->bool` THEN
  CONJ_TAC THENL
   [ALL_TAC; MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_SIMP_TAC[OPEN_INTER]] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC MOI_S8CU_R2_RESTRICT THEN
  MAP_EVERY EXISTS_TAC [`E0:real^3->bool`; `E0 INTER (w INTER v):real^3->bool`] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_SIMP_TAC[OPEN_INTER];
    ASM SET_TAC[];
    SET_TAC[];
    SET_TAC[]]);;

(* A crossing point is not in the relative interior of a 2-dimensional     *)
(* convex set lying locally in the trace s INTER m.                         *)

let MOI_S3GP_CROSS_NO_TRI = prove
 (`!(s:real^3->bool) m r y w.
     pl_crossing_at s m y /\ convex r /\ aff_dim r = &2 /\ y IN relative_interior r /\
     open w /\ y IN w /\ r INTER w SUBSET s INTER m
     ==> F`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S4L_CROSSING_LINE_CHART) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` (X_CHOOSE_THEN `h:real^3->real^1`
    (X_CHOOSE_THEN `h':real^1->real^3` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPEC `r:real^3->bool` MOI_S8TA_RELINT_R2) THEN ASM_REWRITE_TAC[homeomorphic] THEN
  DISCH_THEN(X_CHOOSE_THEN `phi:real^3->real^2` (X_CHOOSE_THEN `psi:real^2->real^3`
    ASSUME_TAC)) THEN
  ABBREV_TAC `O = relative_interior r INTER w INTER (u:real^3->bool)` THEN
  SUBGOAL_THEN `(O:real^3->bool) SUBSET relative_interior r /\ (y:real^3) IN O /\
                O SUBSET (s INTER m) INTER u`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN ASM_REWRITE_TAC[IN_INTER] THEN
    MP_TAC(ISPEC `r:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (phi:real^3->real^2) O) /\ ~(IMAGE phi O = {})`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`phi:real^3->real^2`; `psi:real^2->real^3`;
                     `relative_interior r:real^3->bool`; `(:real^2)`; `O:real^3->bool`]
                    HOMEOMORPHISM_IMP_OPEN_MAP) THEN
      ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN] THEN DISCH_THEN MATCH_MP_TAC THEN
      EXPAND_TAC "O" THEN
      MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_SIMP_TAC[OPEN_INTER];
      REWRITE_TAC[IMAGE_EQ_EMPTY] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
    can (term_match [] `homeomorphism (relative_interior (r:real^3->bool),(:real^2)) (phi,psi)`) (concl th))) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
    can (term_match [] `homeomorphism (a,IMAGE (h:real^3->real^1) a) (h,h')`) (concl th))) THEN
  SUBGOAL_THEN `IMAGE (psi:real^2->real^3) (IMAGE phi O) = O` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `IMAGE (\x:real^3. x) O` THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_EQ THEN REWRITE_TAC[o_THM] THEN ASM SET_TAC[];
      REWRITE_TAC[IMAGE_ID]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(h:real^3->real^1) o (psi:real^2->real^3)`; `IMAGE (phi:real^3->real^2) O`]
                INVARIANCE_OF_DIMENSION) THEN
  ASM_REWRITE_TAC[DIMINDEX_1; DIMINDEX_2; ARITH] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(s INTER m) INTER u:real^3->bool` THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[o_THM] THEN MAP_EVERY X_GEN_TAC [`p:real^2`; `p':real^2`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(psi:real^2->real^3) p IN O /\ psi p' IN O` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(psi:real^2->real^3) p = psi p'` MP_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`!x. x IN (s INTER m) INTER u ==> (h':real^1->real^3) ((h:real^3->real^1) x) = x`;
        `(O:real^3->bool) SUBSET (s INTER m) INTER u`;
        `(psi:real^2->real^3) p IN O`; `(psi:real^2->real^3) p' IN O`;
        `(h:real^3->real^1) ((psi:real^2->real^3) p) = h (psi p')`] THEN
      REWRITE_TAC[SUBSET] THEN MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `phi:real^3->real^2`) THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Part 3: sides at a crossing point.  If s crosses Bd X at y and,          *)
(* near y, s minus Bd X is the union of two convex sets A1 and A2, then     *)
(* near y one of them lies in Int X and the other misses X.                 *)
(* ------------------------------------------------------------------------- *)

let MOI_S3GP_CONN_SPLIT = prove
 (`!(s:real^N->bool) e1 e2.
     connected s /\ open e1 /\ open e2 /\ s SUBSET e1 UNION e2 /\ e1 INTER e2 = {}
     ==> s SUBSET e1 \/ s SUBSET e2`,
  REWRITE_TAC[connected] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`e1:real^N->bool`; `e2:real^N->bool`] o
    REWRITE_RULE[NOT_EXISTS_THM]) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_S3GP_CROSS_SIDES = prove
 (`!(X:real^3->bool) s y A1 A2 w.
     closed X /\ closure (interior X) = X /\ pl_crossing_at s (frontier X) y /\
     convex A1 /\ convex A2 /\ open w /\ y IN w /\
     (s DIFF frontier X) INTER w = (A1 UNION A2) INTER w
     ==> ?e. &0 < e /\
             ((A1 INTER ball(y,e) SUBSET interior X /\ DISJOINT (A2 INTER ball(y,e)) X) \/
              (A2 INTER ball(y,e) SUBSET interior X /\ DISJOINT (A1 INTER ball(y,e)) X))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pl_crossing_at]) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `homeomorphism (u,IMAGE (f:real^3->real^3) u) (f,g)` ASSUME_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  MP_TAC(ISPECL [`X:real^3->bool`; `u:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`;
                 `y:real^3`] MOI_S3GP_CHART_SIDE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sides")))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
    concl th = `homeomorphism (u,IMAGE (f:real^3->real^3) u) (f,g)`)) THEN
  ABBREV_TAC `W0 = {x:real^3 | x IN u /\ (f:real^3->real^3) x IN ball(vec 0,r)}` THEN
  ABBREV_TAC `Wp = {x:real^3 | x IN u /\
                    (f:real^3->real^3) x IN ball(vec 0,r) INTER {z:real^3 | &0 < z$2}}` THEN
  ABBREV_TAC `Wm = {x:real^3 | x IN u /\
                    (f:real^3->real^3) x IN ball(vec 0,r) INTER {z:real^3 | z$2 < &0}}` THEN
  SUBGOAL_THEN `open (W0:real^3->bool) /\ open (Wp:real^3->bool) /\ open (Wm:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["W0"; "Wp"; "Wm"] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC) THEN REWRITE_TAC[OPEN_BALL] THEN
    REWRITE_TAC[GSYM real_gt; OPEN_HALFSPACE_COMPONENT_GT; OPEN_HALFSPACE_COMPONENT_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `Wp INTER Wm = {}:real^3->bool` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Wp"; "Wm"] THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the two sides of the chart *)
  SUBGOAL_THEN `(Wp SUBSET interior X /\ DISJOINT Wm (X:real^3->bool)) \/
                (Wm SUBSET interior X /\ DISJOINT Wp (X:real^3->bool))` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Wp"; "Wm"] THEN
    REWRITE_TAC[SUBSET; DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    REMOVE_THEN "sides" (DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
     [DISJ1_TAC; DISJ2_TAC] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  (* points of s off Bd X in W0 are on one of the two sides *)
  SUBGOAL_THEN `!x:real^3. x IN s /\ ~(x IN frontier X) /\ x IN W0 ==> x IN Wp UNION Wm`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN MAP_EVERY EXPAND_TAC ["W0"; "Wp"; "Wm"] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNION; IN_INTER] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `((f:real^3->real^3) x)$2 = &0` THENL
     [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    SUBGOAL_THEN `(f:real^3->real^3) x IN IMAGE f (frontier X INTER u)` MP_TAC THENL
     [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `x':real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `x':real^3 = x` (fun th -> ASM_MESON_TAC[th]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  (* the radius *)
  SUBGOAL_THEN `(y:real^3) IN W0 INTER w` ASSUME_TAC THENL
   [EXPAND_TAC "W0" THEN ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; CENTRE_IN_BALL]; ALL_TAC] THEN
  MP_TAC(ISPEC `W0 INTER w:real^3->bool` OPEN_CONTAINS_BALL) THEN
  ASM_SIMP_TAC[OPEN_INTER] THEN DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
  (* each piece near y lies on one side *)
  SUBGOAL_THEN `!A:real^3->bool. convex A /\ A SUBSET A1 UNION A2
                                 ==> A INTER ball(y,e) SUBSET Wp \/ A INTER ball(y,e) SUBSET Wm`
  ASSUME_TAC THENL
   [X_GEN_TAC `A:real^3->bool` THEN STRIP_TAC THEN MATCH_MP_TAC MOI_S3GP_CONN_SPLIT THEN
    ASM_SIMP_TAC[CONVEX_CONNECTED; CONVEX_INTER; CONVEX_BALL] THEN
    REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN (s DIFF frontier X) INTER w` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_INTER; IN_DIFF] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  (* points of s on both sides near y *)
  SUBGOAL_THEN `?d. &0 < d /\ d <= r /\
                    !z. z IN ball(vec 0,d) ==> (g:real^3->real^3) z IN ball(y,e)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(g:real^3->real^3) continuous at (vec 0)` MP_TAC THENL
     [MP_TAC(ISPECL [`g:real^3->real^3`; `IMAGE (f:real^3->real^3) u`]
                    CONTINUOUS_ON_EQ_CONTINUOUS_AT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min d0 r` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_BALL] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(g:real^3->real^3) (vec 0) = y` (SUBST1_TAC o SYM) THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. &0 < abs t /\ abs t < d
        ==> (g:real^3->real^3) (t % basis 2) IN s /\ ~(g (t % basis 2) IN frontier X) /\
            g (t % basis 2) IN ball(y,e) /\
            (&0 < t ==> g (t % basis 2) IN Wp) /\ (t < &0 ==> g (t % basis 2) IN Wm)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(t % basis 2:real^3)$1 = &0 /\ (t % basis 2:real^3)$2 = t /\
                  t % basis 2 IN ball(vec 0:real^3,d)` STRIP_ASSUME_TAC THENL
     [SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_3; ARITH; REAL_MUL_RZERO;
               REAL_MUL_RID; IN_BALL; DIST_0; NORM_MUL; NORM_BASIS] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `t % basis 2 IN ball(vec 0:real^3,r)` ASSUME_TAC THENL
     [UNDISCH_TAC `t % basis 2 IN ball(vec 0:real^3,d)` THEN REWRITE_TAC[IN_BALL] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `t % basis 2 IN IMAGE (f:real^3->real^3) u` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(g:real^3->real^3) (t % basis 2) IN s INTER u` ASSUME_TAC THENL
     [SUBGOAL_THEN `t % basis 2 IN IMAGE (f:real^3->real^3) (s INTER u)` MP_TAC THENL
       [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM]; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[IN_INTER];
      ALL_TAC] THEN
    SUBGOAL_THEN `(f:real^3->real^3) ((g:real^3->real^3) (t % basis 2)) = t % basis 2` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      DISCH_TAC THEN
      SUBGOAL_THEN `t % basis 2 IN IMAGE (f:real^3->real^3) (frontier X INTER u)` MP_TAC THENL
       [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(g:real^3->real^3) (t % basis 2)` THEN
        ASM_REWRITE_TAC[IN_INTER] THEN ASM SET_TAC[];
        ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC];
      ASM SET_TAC[];
      DISCH_TAC THEN EXPAND_TAC "Wp" THEN REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      DISCH_TAC THEN EXPAND_TAC "Wm" THEN REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC(SPEC `d / &2` th) THEN MP_TAC(SPEC `--(d / &2)` th)) THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < d ==> &0 < abs(--(d / &2)) /\ abs(--(d / &2)) < d /\
                                      --(d / &2) < &0 /\ ~(&0 < --(d / &2))`;
               REAL_ARITH `&0 < d ==> &0 < abs(d / &2) /\ abs(d / &2) < d /\
                                      &0 < d / &2 /\ ~(d / &2 < &0)`] THEN
  REPEAT STRIP_TAC THEN
  (* the two convex pieces *)
  SUBGOAL_THEN
   `(A1 INTER ball(y,e) SUBSET Wp \/ A1 INTER ball(y,e) SUBSET Wm) /\
    (A2 INTER ball(y,e) SUBSET Wp \/ A2 INTER ball(y:real^3,e) SUBSET Wm)`
  (CONJUNCTS_THEN ASSUME_TAC) THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(g:real^3->real^3) (d / &2 % basis 2) IN (A1 UNION A2) INTER ball(y,e) /\
    g (--(d / &2) % basis 2) IN (A1 UNION A2) INTER ball(y,e)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `ball(y:real^3,e) SUBSET w` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(s DIFF frontier X) INTER w = (A1 UNION A2) INTER (w:real^3->bool)` THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`(Wp SUBSET interior X /\ DISJOINT Wm (X:real^3->bool)) \/
     (Wm SUBSET interior X /\ DISJOINT Wp (X:real^3->bool))`;
    `Wp INTER Wm = {}:real^3->bool`;
    `(g:real^3->real^3) (d / &2 % basis 2) IN Wp`;
    `(g:real^3->real^3) (--(d / &2) % basis 2) IN Wm`;
    `(g:real^3->real^3) (d / &2 % basis 2) IN (A1 UNION A2) INTER ball(y,e)`;
    `(g:real^3->real^3) (--(d / &2) % basis 2) IN (A1 UNION A2) INTER ball(y,e)`;
    `A1 INTER ball(y,e) SUBSET Wp \/ A1 INTER ball(y:real^3,e) SUBSET Wm`;
    `A2 INTER ball(y,e) SUBSET Wp \/ A2 INTER ball(y:real^3,e) SUBSET Wm`] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  SPEC_TAC(`(g:real^3->real^3) (d / &2 % basis 2)`,`p:real^3`) THEN
  SPEC_TAC(`(g:real^3->real^3) (--(d / &2) % basis 2)`,`q:real^3`) THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Part 4: cutting a PL circle C by a closed set D.  If every               *)
(* connected piece of C off a finite set Z lies in D or misses D, and at    *)
(* each point of Z in D the circle is locally two segments of which exactly *)
(* one half lies in D, then every component of C INTER D is either the     *)
(* whole circle (when Z is empty) or a PL arc whose ends are its points in  *)
(* Z.                                                                        *)
(* ------------------------------------------------------------------------- *)

let MOI_S3GP_CONN_SPLIT2 = prove
 (`!(s:real^N->bool) e1 e2.
     connected s /\ open e1 /\ open e2 /\ s SUBSET e1 UNION e2 /\ e1 INTER e2 INTER s = {}
     ==> s SUBSET e1 \/ s SUBSET e2`,
  REWRITE_TAC[connected] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`e1:real^N->bool`; `e2:real^N->bool`] o
    REWRITE_RULE[NOT_EXISTS_THM]) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* A connected subset of S meeting a closed H that is open in S lies in H.   *)

let MOI_S3GP_CLOPEN_PIECE = prove
 (`!(S:real^N->bool) H K.
     connected K /\ K SUBSET S /\ ~(K INTER H = {}) /\ closed H /\
     (!w. w IN H ==> ?e. &0 < e /\ S INTER ball(w,e) SUBSET H)
     ==> K SUBSET H`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_TAC `ee:real^N->real`) THEN
  MP_TAC(ISPECL [`K:real^N->bool`; `UNIONS {ball(w:real^N,ee w) | w IN H}`;
                 `(:real^N) DIFF H`] MOI_S3GP_CONN_SPLIT2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM closed] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_UNIONS THEN REWRITE_TAC[FORALL_IN_GSPEC; OPEN_BALL];
      REWRITE_TAC[SUBSET; IN_UNION; IN_UNIONS; IN_ELIM_THM; IN_DIFF; IN_UNIV] THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      ASM_CASES_TAC `(x:real^N) IN H` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `ball(x:real^N,ee x)` THEN CONJ_TAC THENL
       [EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[CENTRE_IN_BALL] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o check (fun th ->
          is_forall (concl th) && can (find_term (fun u -> u = `ee:real^N->real`)) (concl th))) THEN
        ASM_SIMP_TAC[]];
      GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
      REWRITE_TAC[IN_INTER; IN_UNIONS; IN_ELIM_THM; IN_DIFF; IN_UNIV; NOT_IN_EMPTY] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `B:real^N->bool` MP_TAC) STRIP_ASSUME_TAC) THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `w:real^N` o check (fun th ->
        is_forall (concl th) && can (find_term (fun u -> u = `ee:real^N->real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?w:real^N. w IN H /\ x IN ball(w,ee w)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `K SUBSET UNIONS {ball(w:real^N,ee w) | w IN H}` THEN
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `B:real^N->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
      EXISTS_TAC `w:real^N` THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^N` o check (fun th ->
      is_forall (concl th) && can (find_term (fun u -> u = `ee:real^N->real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ASM SET_TAC[]]);;

(* A point of a connected set with another point is a limit of the rest.    *)

let MOI_S3GP_CONN_LIMIT = prove
 (`!(S:real^N->bool) y. connected S /\ y IN S /\ ~(S = {y}) ==> y IN closure (S DELETE y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `S INTER ball(y:real^N,e) = {y}` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_BALL; IN_SING] THEN X_GEN_TAC `x:real^N` THEN
    EQ_TAC THENL
     [STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o REWRITE_RULE[NOT_EXISTS_THM]) THEN
      ASM_REWRITE_TAC[IN_DELETE] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_MESON_TAC[];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[DIST_REFL]];
    ALL_TAC] THEN
  UNDISCH_TAC `connected (S:real^N->bool)` THEN REWRITE_TAC[CONNECTED_CLOPEN] THEN
  DISCH_THEN(MP_TAC o SPEC `{y:real^N}`) THEN
  ASM_REWRITE_TAC[NOT_INSERT_EMPTY; NOT_IMP] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN
    REWRITE_TAC[OPEN_BALL];
    MATCH_MP_TAC CLOSED_SUBSET THEN REWRITE_TAC[CLOSED_SING] THEN ASM SET_TAC[]]);;

(* At an end w of the arc H, near w the set C INTER D lies in H.            *)

let MOI_S3GP_ARC_END = prove
 (`!(C:real^N->bool) Z D H w p1 p2 d.
     FINITE Z /\ closed H /\ H SUBSET C /\ closed (C DIFF (H DIFF Z)) /\
     w IN Z /\ w IN H /\ w IN closure (H DIFF Z) /\ H DIFF Z SUBSET D /\
     &0 < d /\ ~(p1 = w) /\ ~(p2 = w) /\
     C INTER ball(w,d) = (segment[w,p1] UNION segment[w,p2]) INTER ball(w,d) /\
     (segment[w,p1] DELETE w) INTER ball(w,d) SUBSET D /\
     DISJOINT ((segment[w,p2] DELETE w) INTER ball(w,d)) D
     ==> ?e. &0 < e /\ (C INTER D) INTER ball(w,e) SUBSET H`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Z DELETE (w:real^N)`; `w:real^N`] SEPARATE_POINT_CLOSED) THEN
  ASM_SIMP_TAC[FINITE_IMP_CLOSED; FINITE_DELETE; IN_DELETE] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d d0` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  ABBREV_TAC `s1 = (segment[w,p1] DELETE w) INTER ball(w:real^N,min d d0)` THEN
  SUBGOAL_THEN `ball(w:real^N,min d d0) SUBSET ball(w,d)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(C INTER D) INTER ball(w:real^N,min d d0) SUBSET w INSERT s1` ASSUME_TAC THENL
   [EXPAND_TAC "s1" THEN
    UNDISCH_TAC `ball(w:real^N,min d d0) SUBSET ball(w,d)` THEN
    UNDISCH_TAC `C INTER ball(w:real^N,d) = (segment[w,p1] UNION segment[w,p2]) INTER ball(w,d)` THEN
    UNDISCH_TAC `DISJOINT ((segment[w:real^N,p2] DELETE w) INTER ball(w,d)) D` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `s1 SUBSET C DIFF (Z:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "s1" THEN REWRITE_TAC[SUBSET; IN_DIFF; IN_INTER; IN_DELETE] THEN
    X_GEN_TAC `q:real^N` THEN STRIP_TAC THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(q:real^N) IN C INTER ball(w,d)` MP_TAC THENL
       [ASM_REWRITE_TAC[IN_INTER; IN_UNION] THEN ASM SET_TAC[];
        SET_TAC[]];
      DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `q:real^N` o check (fun th ->
        can (find_term (fun u -> u = `d0:real`)) (concl th) && is_forall (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(q:real^N) IN ball(w,min d d0)` THEN REWRITE_TAC[IN_BALL] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected (s1:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "s1" THEN MATCH_MP_TAC CONVEX_CONNECTED THEN
    MATCH_MP_TAC CONVEX_INTER THEN REWRITE_TAC[CONVEX_SEMIOPEN_SEGMENT; CONVEX_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(s1 INTER (H:real^N->bool) = {})` ASSUME_TAC THENL
   [UNDISCH_TAC `(w:real^N) IN closure (H DIFF Z)` THEN REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
    DISCH_THEN(MP_TAC o SPEC `min d d0`) THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(q:real^N) IN C /\ q IN D /\ ~(q = w) /\ q IN H` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(q:real^N) IN H DIFF Z` THEN UNDISCH_TAC `H SUBSET (C:real^N->bool)` THEN
      UNDISCH_TAC `H DIFF Z SUBSET (D:real^N->bool)` THEN UNDISCH_TAC `(w:real^N) IN Z` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(q:real^N) IN ball(w,min d d0)` ASSUME_TAC THENL
     [REWRITE_TAC[IN_BALL; REAL_LT_MIN] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(C INTER D) INTER ball(w:real^N,min d d0) SUBSET w INSERT s1` THEN
    MAP_EVERY UNDISCH_TAC [`(q:real^N) IN C`; `(q:real^N) IN D`; `~(q:real^N = w)`;
                           `(q:real^N) IN H`; `(q:real^N) IN ball(w,min d d0)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s1:real^N->bool`; `(:real^N) DIFF (C DIFF (H DIFF Z))`; `(:real^N) DIFF H`]
                MOI_S3GP_CONN_SPLIT2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM closed] THEN UNDISCH_TAC `s1 SUBSET C DIFF (Z:real^N->bool)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [UNDISCH_TAC `(C INTER D) INTER ball(w:real^N,min d d0) SUBSET w INSERT s1` THEN
    UNDISCH_TAC `s1 SUBSET (:real^N) DIFF (C DIFF (H DIFF Z))` THEN
    UNDISCH_TAC `s1 SUBSET C DIFF (Z:real^N->bool)` THEN
    UNDISCH_TAC `(w:real^N) IN H` THEN SET_TAC[];
    UNDISCH_TAC `~(s1 INTER (H:real^N->bool) = {})` THEN
    UNDISCH_TAC `s1 SUBSET (:real^N) DIFF H` THEN SET_TAC[]]);;

(* The circle cut.                                                           *)

let MOI_S3GP_CIRCLE_CUT = prove
 (`!(C:real^N->bool) Z D K.
     pl_sphere 1 C /\ FINITE Z /\ Z SUBSET C /\ closed D /\
     (!s0. connected s0 /\ s0 SUBSET C DIFF Z ==> s0 SUBSET D \/ DISJOINT s0 D) /\
     (!y. y IN Z /\ y IN D
          ==> ?p1 p2 d. &0 < d /\ ~(p1 = y) /\ ~(p2 = y) /\
                        C INTER ball(y,d) =
                        (segment[y,p1] UNION segment[y,p2]) INTER ball(y,d) /\
                        (segment[y,p1] DELETE y) INTER ball(y,d) SUBSET D /\
                        DISJOINT ((segment[y,p2] DELETE y) INTER ball(y,d)) D) /\
     K IN components (C INTER D)
     ==> (Z = {} /\ K = C) \/ pl_cell_with_boundary 1 K (K INTER Z)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "side") (CONJUNCTS_THEN2 (LABEL_TAC "loc")
     ASSUME_TAC)))))) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `g:real^1->real^N` STRIP_ASSUME_TAC o
    MATCH_MP MOI_S4O_CIRCLE_LOOP) THEN
  SUBGOAL_THEN `connected (C:real^N->bool) /\ compact C` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `path_image (g:real^1->real^N) = C` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[CONNECTED_SIMPLE_PATH_IMAGE; COMPACT_PATH_IMAGE; SIMPLE_PATH_IMP_PATH];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(K:real^N->bool = {}) /\ K SUBSET C INTER D /\ connected K`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY; IN_COMPONENTS_SUBSET; IN_COMPONENTS_CONNECTED];
    ALL_TAC] THEN
  (* points near y on a half-segment *)
  SUBGOAL_THEN
   `!y:real^N p d. ~(p = y) /\ &0 < d
                   ==> ?q. q IN (segment[y,p] DELETE y) INTER ball(y,d)`
  (LABEL_TAC "near") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`y:real^N`; `p:real^N`; `d:real`] MOI_S4L_SEGMENT_NEAR) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[];
    ALL_TAC] THEN
  (* no cut point *)
  ASM_CASES_TAC `Z:real^N->bool = {}` THENL
   [DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "side" (MP_TAC o SPEC `C:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[DIFF_EMPTY; SUBSET_REFL]; ALL_TAC] THEN STRIP_TAC THENL
     [SUBGOAL_THEN `C INTER D = C:real^N->bool` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `K IN components (C INTER D:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `components C = {C:real^N->bool}` SUBST1_TAC THENL
       [REWRITE_TAC[COMPONENTS_EQ_SING] THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `path_image (g:real^1->real^N) = C` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        REWRITE_TAC[PATH_IMAGE_NONEMPTY];
        REWRITE_TAC[IN_SING]];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  DISJ2_TAC THEN
  (* one cut point: impossible *)
  ASM_CASES_TAC `CARD(Z:real^N->bool) = 1` THENL
   [MATCH_MP_TAC(TAUT `F ==> p`) THEN
    SUBGOAL_THEN `?y:real^N. Z = {y}` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(Z:real^N->bool) HAS_SIZE 1` MP_TAC THENL
       [ASM_REWRITE_TAC[HAS_SIZE]; CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN SIMP_TAC[]];
      ALL_TAC] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `connected (C DELETE (y:real^N))` ASSUME_TAC THENL
     [UNDISCH_TAC `path_image (g:real^1->real^N) = C` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC CONNECTED_SIMPLE_PATH_IMAGE_DELETE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "side" (MP_TAC o SPEC `C DELETE (y:real^N)`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `(y:real^N) IN D` THENL
     [USE_THEN "loc" (MP_TAC o SPEC `y:real^N`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[IN_SING]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `p1:real^N` (X_CHOOSE_THEN `p2:real^N` (X_CHOOSE_THEN `d:real`
        STRIP_ASSUME_TAC))) THEN
      USE_THEN "near" (MP_TAC o SPECL [`y:real^N`; `p1:real^N`; `d:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_TAC `q1:real^N`)] THEN
      USE_THEN "near" (MP_TAC o SPECL [`y:real^N`; `p2:real^N`; `d:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_TAC `q2:real^N`)] THEN
      UNDISCH_TAC `C INTER ball(y:real^N,d) =
                   (segment[y,p1] UNION segment[y,p2]) INTER ball(y,d)` THEN
      MAP_EVERY UNDISCH_TAC
       [`(q1:real^N) IN (segment[y,p1] DELETE y) INTER ball(y,d)`;
        `(q2:real^N) IN (segment[y,p2] DELETE y) INTER ball(y,d)`;
        `(segment[y:real^N,p1] DELETE y) INTER ball(y,d) SUBSET D`;
        `DISJOINT ((segment[y:real^N,p2] DELETE y) INTER ball(y,d)) D`] THEN
      SET_TAC[];
      STRIP_TAC THENL
       [SUBGOAL_THEN `(y:real^N) IN closure (C DELETE y)` MP_TAC THENL
         [MATCH_MP_TAC MOI_S3GP_CONN_LIMIT THEN ASM_REWRITE_TAC[] THEN
          CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
          DISCH_TAC THEN
          MP_TAC(ISPEC `g:real^1->real^N` NONEMPTY_SIMPLE_PATH_ENDLESS) THEN
          ASM_REWRITE_TAC[] THEN
          SUBGOAL_THEN `pathstart (g:real^1->real^N) IN C` MP_TAC THENL
           [UNDISCH_TAC `path_image (g:real^1->real^N) = C` THEN
            DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[PATHSTART_IN_PATH_IMAGE];
            ALL_TAC] THEN
          ASM SET_TAC[];
          ALL_TAC] THEN
        MATCH_MP_TAC(SET_RULE `s SUBSET (D:real^N->bool) /\ ~((y:real^N) IN D)
                               ==> y IN s ==> F`) THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `~(K:real^N->bool = {})` THEN
        UNDISCH_TAC `K SUBSET C INTER (D:real^N->bool)` THEN
        UNDISCH_TAC `DISJOINT (C DELETE (y:real^N)) D` THEN UNDISCH_TAC `~((y:real^N) IN D)` THEN
        SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 <= CARD(Z:real^N->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `Z:real^N->bool` CARD_EQ_0) THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  (* a point of K off Z *)
  SUBGOAL_THEN `?x:real^N. x IN K /\ ~(x IN Z)` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(X_CHOOSE_TAC `z:real^N` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY] o
      check (fun th -> concl th = `~(K:real^N->bool = {})`)) THEN
    ASM_CASES_TAC `(z:real^N) IN Z` THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    SUBGOAL_THEN `(z:real^N) IN D` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "loc" (MP_TAC o SPEC `z:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `p1:real^N` (X_CHOOSE_THEN `p2:real^N` (X_CHOOSE_THEN `d:real`
      STRIP_ASSUME_TAC))) THEN
    MP_TAC(ISPECL [`Z DELETE (z:real^N)`; `z:real^N`] SEPARATE_POINT_CLOSED) THEN
    ASM_SIMP_TAC[FINITE_IMP_CLOSED; FINITE_DELETE; IN_DELETE] THEN
    DISCH_THEN(X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC) THEN
    USE_THEN "near" (MP_TAC o SPECL [`z:real^N`; `p1:real^N`; `min d d0`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN]; DISCH_THEN(X_CHOOSE_TAC `q:real^N`)] THEN
    EXISTS_TAC `q:real^N` THEN
    SUBGOAL_THEN `segment[z:real^N,q] SUBSET segment[z,p1] INTER ball(z,min d d0)`
    ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET_SEGMENT; ENDS_IN_SEGMENT] THEN ASM SET_TAC[];
        REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MINIMAL THEN
        REWRITE_TAC[CONVEX_BALL; INSERT_SUBSET; EMPTY_SUBSET; CENTRE_IN_BALL] THEN
        ASM_REWRITE_TAC[REAL_LT_MIN] THEN ASM SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `ball(z:real^N,min d d0) SUBSET ball(z,d)` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_BALL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `segment[z:real^N,q] SUBSET K` ASSUME_TAC THENL
     [MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
      EXISTS_TAC `C INTER D:real^N->bool` THEN ASM_REWRITE_TAC[CONNECTED_SEGMENT] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `segment[z:real^N,q] SUBSET segment[z,p1] INTER ball(z,min d d0)` THEN
        UNDISCH_TAC `ball(z:real^N,min d d0) SUBSET ball(z,d)` THEN
        UNDISCH_TAC `C INTER ball(z:real^N,d) =
                     (segment[z,p1] UNION segment[z,p2]) INTER ball(z,d)` THEN
        UNDISCH_TAC `(segment[z:real^N,p1] DELETE z) INTER ball(z,d) SUBSET D` THEN
        UNDISCH_TAC `(z:real^N) IN D` THEN SET_TAC[];
        MP_TAC(ISPECL [`z:real^N`; `q:real^N`] ENDS_IN_SEGMENT) THEN ASM SET_TAC[]];
      ALL_TAC] THEN
    CONJ_TAC THENL [MP_TAC(ISPECL [`z:real^N`; `q:real^N`] ENDS_IN_SEGMENT) THEN
                    ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `q:real^N` o check (fun th ->
      can (find_term (fun u -> u = `d0:real`)) (concl th) && is_forall (concl th))) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(q:real^N) IN (segment[z,p1] DELETE z) INTER ball(z,min d d0)` THEN
    REWRITE_TAC[IN_INTER; IN_BALL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the arc through x *)
  MP_TAC(ISPECL [`g:real^1->real^N`; `Z:real^N->bool`; `x:real^N`] MOI_P1M_LOOP_PIECE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ASM_REWRITE_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^1->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `pl_cell_with_boundary 1 (path_image h)
                  {pathstart h,pathfinish (h:real^1->real^N)}` MP_TAC THENL
   [MATCH_MP_TAC MOI_FCL_ARC_CELL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `path_image (h:real^1->real^N) DIFF {pathstart h,pathfinish h} =
                IMAGE (h:real^1->real^N) (interval(vec 0,vec 1)) /\
                connected (path_image h DIFF {pathstart h,pathfinish h}) /\
                compact (path_image h) /\ connected (path_image h) /\
                h continuous_on interval[vec 0,vec 1]`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SIMPLE_PATH_ENDLESS; CONNECTED_SIMPLE_PATH_ENDLESS; ARC_IMP_SIMPLE_PATH;
                 COMPACT_PATH_IMAGE; ARC_IMP_PATH; CONNECTED_ARC_IMAGE] THEN
    ASM_MESON_TAC[ARC_IMP_PATH; path];
    ALL_TAC] THEN
  ABBREV_TAC `H = path_image (h:real^1->real^N)` THEN
  ABBREV_TAC `a = pathstart (h:real^1->real^N)` THEN
  ABBREV_TAC `b = pathfinish (h:real^1->real^N)` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `H DIFF {a,b} = H DIFF (Z:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `H INTER Z = {a:real^N,b}` THEN SET_TAC[]; ALL_TAC] THEN
  (* H lies in the closure of its interior, hence in D *)
  SUBGOAL_THEN `connected (H DIFF (Z:real^N->bool)) /\ closed (C DIFF (H DIFF Z)) /\
                H SUBSET closure (H DIFF Z)`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `H DIFF {a,b} = H DIFF (Z:real^N->bool)`)) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `H = IMAGE (h:real^1->real^N) (closure(interval(vec 0,vec 1)))`
    (fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THENL
     [EXPAND_TAC "H" THEN REWRITE_TAC[path_image] THEN AP_TERM_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC CLOSURE_OPEN_INTERVAL THEN
      REWRITE_TAC[INTERVAL_EQ_EMPTY_1; DROP_VEC] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC IMAGE_CLOSURE_SUBSET THEN REWRITE_TAC[CLOSED_CLOSURE; CLOSURE_SUBSET] THEN
    SUBGOAL_THEN `closure(interval(vec 0:real^1,vec 1)) = interval[vec 0,vec 1]`
    (fun th -> ASM_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC CLOSURE_OPEN_INTERVAL THEN
    REWRITE_TAC[INTERVAL_EQ_EMPTY_1; DROP_VEC] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    concl th = `H DIFF {a,b} = IMAGE (h:real^1->real^N) (interval(vec 0,vec 1))`)) THEN
  SUBGOAL_THEN `H DIFF Z SUBSET (D:real^N->bool)` ASSUME_TAC THENL
   [USE_THEN "side" (MP_TAC o SPEC `H DIFF (Z:real^N->bool)`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `H SUBSET (D:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `closure (H DIFF (Z:real^N->bool))` THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  (* K = H *)
  SUBGOAL_THEN `K = H:real^N->bool` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S3GP_CLOPEN_PIECE THEN EXISTS_TAC `C INTER D:real^N->bool` THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
      ASM_CASES_TAC `(w:real^N) IN Z` THENL
       [USE_THEN "loc" (MP_TAC o SPEC `w:real^N`) THEN
        ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `p1:real^N` (X_CHOOSE_THEN `p2:real^N` (X_CHOOSE_THEN `d:real`
          STRIP_ASSUME_TAC))) THEN
        MATCH_MP_TAC MOI_S3GP_ARC_END THEN
        MAP_EVERY EXISTS_TAC [`Z:real^N->bool`; `p1:real^N`; `p2:real^N`; `d:real`] THEN
        ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN ASM SET_TAC[];
        MP_TAC(ISPECL [`C DIFF (H DIFF (Z:real^N->bool))`; `w:real^N`] SEPARATE_POINT_CLOSED) THEN
        ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_INTER; IN_BALL] THEN
        X_GEN_TAC `q:real^N` THEN STRIP_TAC THEN
        GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `q:real^N` o check (fun th ->
          can (find_term (fun u -> u = `e:real`)) (concl th) && is_forall (concl th))) THEN
        ASM_REWRITE_TAC[IN_DIFF; REAL_NOT_LE]];
      MATCH_MP_TAC COMPONENTS_MAXIMAL THEN EXISTS_TAC `C INTER D:real^N->bool` THEN
      ASM_REWRITE_TAC[SUBSET_INTER] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Part 5: the box triangulation of MOI_FSP_SETUP (pc_moi_fnd_split)        *)
(* with a fourth subcomplex lq triangulating a given compact polyhedron q.  *)
(* The proof is that of MOI_FSP_SETUP with the extra polyhedron carried     *)
(* through the triangulation and the iterated subdivisions.                 *)
(* ------------------------------------------------------------------------- *)

let MOI_S3GP_TRIANGULATE4 = prove
 (`!(p:real^N->bool) q1 q2 q3.
     pl_polyhedron p /\ pl_polyhedron q1 /\ pl_polyhedron q2 /\ pl_polyhedron q3 /\
     q1 SUBSET p /\ q2 SUBSET p /\ q3 SUBSET p
     ==> ?t l1 l2 l3. simplicial_complex t /\ UNIONS t = p /\
                      simplicial_subcomplex l1 t /\ UNIONS l1 = q1 /\
                      simplicial_subcomplex l2 t /\ UNIONS l2 = q2 /\
                      simplicial_subcomplex l3 t /\ UNIONS l3 = q3`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_polyhedron] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `cp:(real^N->bool)->bool` STRIP_ASSUME_TAC)
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `c1:(real^N->bool)->bool` STRIP_ASSUME_TAC)
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `c2:(real^N->bool)->bool` STRIP_ASSUME_TAC)
        (CONJUNCTS_THEN2 (X_CHOOSE_THEN `c3:(real^N->bool)->bool` STRIP_ASSUME_TAC)
          STRIP_ASSUME_TAC)))) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq (concl th) && is_var (lhs (concl th))))) THEN
  MP_TAC(ISPEC `cp UNION c1 UNION c2 UNION c3:(real^N->bool)->bool`
               POLYTOPES_SIMPLICIAL_REFINEMENT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_UNION; IN_UNION] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(real^N->bool)->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ref")))) THEN
  MAP_EVERY EXISTS_TAC
   [`t:(real^N->bool)->bool`;
    `{s:real^N->bool | s IN t /\ s SUBSET UNIONS c1}`;
    `{s:real^N->bool | s IN t /\ s SUBSET UNIONS c2}`;
    `{s:real^N->bool | s IN t /\ s SUBSET UNIONS c3}`] THEN
  SUBGOAL_THEN
   `!c:(real^N->bool)->bool.
      (!k. k IN c ==> k IN cp UNION c1 UNION c2 UNION c3)
      ==> simplicial_subcomplex {s | s IN t /\ s SUBSET UNIONS c} t /\
          UNIONS {s | s IN t /\ s SUBSET UNIONS c} = UNIONS c`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC MOI_FSP_SUBPOLY THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN USE_THEN "ref" MATCH_MP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[IN_UNION] THEN REWRITE_TAC[UNIONS_UNION] THEN ASM SET_TAC[]);;

let MOI_S3GP_SETUP4 = prove
 (`!(m:(real^3->bool)->bool) d j v q.
     FINITE m /\ combinatorial_manifold 2 m /\
     pl_cell_with_boundary 2 d j /\ d INTER UNIONS m = j /\ open v /\ d SUBSET v /\
     pl_polyhedron q
     ==> ?a b t ld lm lq.
           moi_fsp_box m d v a b t ld lm /\ q SUBSET interval(a,b) /\
           simplicial_subcomplex lq t /\ UNIONS lq = q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_fsp_box] THEN
  SUBGOAL_THEN `pl_polyhedron (d:real^3->bool) /\ compact d` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSP_CELL_POLYHEDRON]; ALL_TAC] THEN
  SUBGOAL_THEN `pl_polyhedron (UNIONS m:real^3->bool) /\ compact (UNIONS m)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `!s:real^3->bool. s IN m ==> polytope s` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `?n. n simplex (s:real^3->bool)` STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[combinatorial_manifold; lf_simplicial_complex]; ALL_TAC] THEN
      ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[pl_polyhedron] THEN EXISTS_TAC `m:(real^3->bool)->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC COMPACT_UNIONS THEN ASM_MESON_TAC[POLYTOPE_IMP_COMPACT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (q:real^3->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `pl_polyhedron (q:real^3->bool)` THEN REWRITE_TAC[pl_polyhedron] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC COMPACT_UNIONS THEN
    ASM_MESON_TAC[POLYTOPE_IMP_COMPACT];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(d:real^3->bool = {})` ASSUME_TAC THENL
   [UNDISCH_TAC `pl_cell_with_boundary 2 (d:real^3->bool) j` THEN
    REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism; homeomorphism] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
      (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
    UNDISCH_TAC `IMAGE (f:real^3->real^3) k = d` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY] THEN ASM_MESON_TAC[SIMPLEX_EMPTY; INT_ARITH `~(&2:int = -- &1)`];
    ALL_TAC] THEN
  MP_TAC(ISPEC `d UNION UNIONS m UNION q:real^3->bool` MOI_FSP_BOX) THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[BOUNDED_UNION; COMPACT_IMP_BOUNDED] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^3` (X_CHOOSE_THEN `b:real^3` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `d UNION UNIONS m SUBSET interval(a:real^3,b) /\ q SUBSET interval(a,b)`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^3`; `b:real^3`] MOI_FSP_BOX_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`interval[a:real^3,b]`; `d:real^3->bool`; `UNIONS m:real^3->bool`;
                 `q:real^3->bool`] MOI_S3GP_TRIANGULATE4) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MP_TAC(ISPECL [`a:real^3`; `b:real^3`] INTERVAL_OPEN_SUBSET_CLOSED) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:(real^3->bool)->bool` (X_CHOOSE_THEN `ld0:(real^3->bool)->bool`
    (X_CHOOSE_THEN `lm0:(real^3->bool)->bool` (X_CHOOSE_THEN `lq0:(real^3->bool)->bool`
    STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `lf_simplicial_complex (t0:(real^3->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FMB_SC_LF THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t0:(real^3->bool)->bool`; `ld0:(real^3->bool)->bool`;
                 `interval[a:real^3,b] INTER (v INTER interval(a,b))`]
                DERIVED_NBHD_SMALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_SIMP_TAC[OPEN_INTER; OPEN_INTERVAL];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  MAP_EVERY EXISTS_TAC
   [`a:real^3`; `b:real^3`; `ITER n barycentric_subdivision (t0:(real^3->bool)->bool)`;
    `ITER n barycentric_subdivision (ld0:(real^3->bool)->bool)`;
    `ITER n barycentric_subdivision (lm0:(real^3->bool)->bool)`;
    `ITER n barycentric_subdivision (lq0:(real^3->bool)->bool)`] THEN
  ABBREV_TAC `t = ITER n barycentric_subdivision (t0:(real^3->bool)->bool)` THEN
  ABBREV_TAC `ld = ITER n barycentric_subdivision (ld0:(real^3->bool)->bool)` THEN
  ABBREV_TAC `lm = ITER n barycentric_subdivision (lm0:(real^3->bool)->bool)` THEN
  ABBREV_TAC `lq = ITER n barycentric_subdivision (lq0:(real^3->bool)->bool)` THEN
  MP_TAC(ISPECL [`t0:(real^3->bool)->bool`; `ld0:(real^3->bool)->bool`; `n:num`]
                MOI_FDN_ITER_SUBCOMPLEX) THEN
  MP_TAC(ISPECL [`t0:(real^3->bool)->bool`; `lm0:(real^3->bool)->bool`; `n:num`]
                MOI_FDN_ITER_SUBCOMPLEX) THEN
  MP_TAC(ISPECL [`t0:(real^3->bool)->bool`; `lq0:(real^3->bool)->bool`; `n:num`]
                MOI_FDN_ITER_SUBCOMPLEX) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `FINITE (t:(real^3->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN MATCH_MP_TAC MOI_FSP_ITER_FINITE THEN
    ASM_MESON_TAC[simplicial_complex];
    ALL_TAC] THEN
  SUBGOAL_THEN `simplicial_complex (t:(real^3->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SCF_LF_SC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `interval[a:real^3,b] DIFF interval(a,b)`]
                PL_BALL_TRIANGULATION_BOUNDARY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `FINITE (lm:(real^3->bool)->bool) /\ simplicial_complex lm`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `FINITE (lm:(real^3->bool)->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `t:(real^3->bool)->bool` THEN
      ASM_MESON_TAC[simplicial_subcomplex];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_SCF_LF_SC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FDN_LF_SUBCOMPLEX THEN EXISTS_TAC `t:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `combinatorial_manifold 2 (lm:(real^3->bool)->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                   `\x:real^3. x`; `\x:real^3. x`] MOI_FRB_SURF_INVARIANT) THEN
    ASM_REWRITE_TAC[HOMEOMORPHISM_ID] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[combinatorial_manifold; combinatorial_manifold_with_boundary];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^3. {w} IN ld ==> pl_sphere 2 (UNIONS (simplicial_link t w))`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPEC `t:(real^3->bool)->bool` BOUNDARY_COMPLEX_SURFACE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `w:real^3` o CONJUNCT1) THEN
    SUBGOAL_THEN `{w:real^3} IN t /\ (w:real^3) IN d` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [ASM_MESON_TAC[simplicial_subcomplex; SUBSET];
        UNDISCH_TAC `UNIONS ld = (d:real^3->bool)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{w:real^3}` THEN ASM_REWRITE_TAC[IN_SING]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    MATCH_MP_TAC(TAUT `p ==> (p <=> q) ==> q`) THEN
    REWRITE_TAC[IN_DIFF] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `derived_nbhd t ld SUBSET v INTER interval(a:real^3,b)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Part 6: the triangulated piece q of PCS.  Its simplices have             *)
(* dimension at most 2, its first derived satisfies the hypotheses of the  *)
(* frontier2 lemmas near d, no triangle lies in Bd X, and at a point of the *)
(* derived frontier on Bd X the frontier is two segments of which one half  *)
(* runs into Int X and the other misses X.                                   *)
(* ------------------------------------------------------------------------- *)

let MOI_S3GP_PIECE_DIM = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c q lq.
     moi_s33_hd t l h e c /\ q SUBSET moi_s39_pcs l e INTER moi_s33_ww t l h /\
     simplicial_complex lq /\ UNIONS lq = q
     ==> !s. s IN lq ==> aff_dim s <= &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `s:real^3->bool` THEN DISCH_TAC THEN
  ASM_CASES_TAC `s:real^3->bool = {}` THENL
   [ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `y:real^3` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  MATCH_MP_TAC MOI_S8TA_EMB2_DIM THEN
  MAP_EVERY EXISTS_TAC [`lq:(real^3->bool)->bool`; `y:real^3`] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_S3GP_PIECE_EMB2 THEN
  MAP_EVERY EXISTS_TAC [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                        `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_S3GP_PIECE_FR2 = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c q v lq ldq.
     moi_s33_hd t l h e c /\ q SUBSET moi_s39_pcs l e /\
     open v /\ v SUBSET moi_s33_ww t l h /\ moi_s39_pcs l e INTER v SUBSET q /\
     simplicial_complex lq /\ UNIONS lq = q /\ simplicial_subcomplex ldq lq /\
     UNIONS ldq SUBSET v
     ==> !f. f IN barycentric_subdivision lq /\ aff_dim f = &1 /\ moi_frn_vp lq ldq f
             ==> ?z. z IN relative_interior f /\ moi_s28_locally_r2 (UNIONS lq) z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `f:real^3->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (lq:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF]; ALL_TAC] THEN
  MP_TAC(ISPECL [`lq:(real^3->bool)->bool`; `ldq:(real^3->bool)->bool`] MOI_FRN_SETUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `convex (f:real^3->bool) /\ closed f` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_COMPLEX_SIMPLEX; SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `~(v INTER relative_interior (f:real^3->bool) = {})` MP_TAC THENL
   [MP_TAC(ISPECL [`v:real^3->bool`; `relative_interior f:real^3->bool`]
                  OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `moi_frn_vp lq ldq (f:real^3->bool)` THEN REWRITE_TAC[moi_frn_vp] THEN
    UNDISCH_TAC `UNIONS ldq SUBSET (v:real^3->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_S3GP_PIECE_R2 THEN
  MAP_EVERY EXISTS_TAC [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                        `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                        `v:real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `f:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
  UNDISCH_TAC `UNIONS (barycentric_subdivision lq) = UNIONS (lq:(real^3->bool)->bool)` THEN
  UNDISCH_TAC `(f:real^3->bool) IN barycentric_subdivision lq` THEN
  UNDISCH_TAC `(z:real^3) IN relative_interior f` THEN
  UNDISCH_TAC `UNIONS lq = (q:real^3->bool)` THEN SET_TAC[]);;

(* No 2-dimensional convex set lies in q INTER Bd X.                          *)

let MOI_S3GP_NO_TRI_Q = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c x q r.
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\
     q SUBSET moi_s39_pcs l e INTER moi_s33_ww t l h /\
     convex r /\ aff_dim r = &2 /\ r SUBSET q INTER frontier (UNIONS x)
     ==> F`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?y:real^3. y IN relative_interior r` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY] THEN
    DISCH_TAC THEN UNDISCH_TAC `aff_dim(r:real^3->bool) = &2` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN r` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`; `y:real^3`]
                MOI_S3GP_PCS_LOCAL) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3` (X_CHOOSE_THEN `v:real^3` (X_CHOOSE_THEN
    `w:real^3->bool` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`]
                MOI_S3GP_PCS_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_crossing_at ((e:(real^3->bool)->real^3->bool)(segment[u,v]) DIFF
                                moi_s33_rim t l h u v) (frontier (UNIONS x)) (y:real^3)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s33_inv t l h e (x:(real^3->bool)->bool)` THEN
    REWRITE_TAC[moi_s33_inv; moi_s33_x2] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S3GP_CROSS_NO_TRI THEN
  MAP_EVERY EXISTS_TAC
   [`(e:(real^3->bool)->real^3->bool)(segment[u,v]) DIFF moi_s33_rim t l h u v`;
    `frontier (UNIONS x):real^3->bool`; `r:real^3->bool`; `y:real^3`;
    `w INTER moi_s33_ww t l h:real^3->bool`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[OPEN_INTER];
    REWRITE_TAC[IN_INTER] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `r SUBSET q INTER frontier (UNIONS x:real^3->bool)` THEN
  UNDISCH_TAC `q SUBSET moi_s39_pcs l e INTER moi_s33_ww t l (h:real^3->real^3)` THEN
  UNDISCH_TAC `moi_s39_pcs l e INTER w =
               (e:(real^3->bool)->real^3->bool)(segment[u,v]) INTER w` THEN
  UNDISCH_TAC `(e:(real^3->bool)->real^3->bool)(segment[u,v]) INTER moi_s33_ww t l h =
               (e(segment[u,v]) DIFF moi_s33_rim t l h u v) DELETE h(midpoint(u,v))` THEN
  SET_TAC[]);;

(* Simplices whose relative interior meets the polyhedron of a subcomplex   *)
(* belong to it.                                                             *)

let MOI_S3GP_RELINT_IN_SUB = prove
 (`!(L:(real^N->bool)->bool) K f y.
     simplicial_complex L /\ simplicial_subcomplex K L /\ f IN L /\
     y IN relative_interior f /\ y IN UNIONS K
     ==> f IN K`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_UNIONS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_subcomplex] o check (fun th ->
    concl th = `simplicial_subcomplex K (L:(real^N->bool)->bool)`)) THEN
  SUBGOAL_THEN `(s:real^N->bool) IN L` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(f INTER s) face_of (f:real^N->bool) /\ (f INTER s) face_of s`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `f INTER s = (f:real^N->bool)` ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`f INTER s:real^N->bool`; `f:real^N->bool`]
                  FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `f:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
    can (find_term (fun u -> u = `(face_of):(real^N->bool)->(real^N->bool)->bool`)) (concl th))) THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_MESON_TAC[]);;

(* A point of the derived frontier off the relative interiors of the        *)
(* triangles is the barycentre of a vp edge.                                 *)

let MOI_S3GP_DFR_MEET = prove
 (`!(t:(real^N->bool)->bool) l M y.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     (!s. s IN t ==> aff_dim s <= &2) /\
     (!r. r IN barycentric_subdivision t /\ aff_dim r = &2
          ==> DISJOINT (relative_interior r) M) /\
     y IN derived_frontier t l /\ y IN M
     ==> ?f. f IN barycentric_subdivision t /\ aff_dim f = &1 /\ moi_frn_vp t l f /\
             y = simplex_barycentre f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FRN_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!r:real^N->bool. r IN barycentric_subdivision t /\ ~(r = {})
                                 ==> simplex_barycentre r IN relative_interior r`
  (LABEL_TAC "bri") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SIMPLEX_BARYCENTRE_IN_RELATIVE_INTERIOR THEN
    ASM_MESON_TAC[MOI_BAR_COMPLEX_SIMPLEX];
    ALL_TAC] THEN
  UNDISCH_TAC `(y:real^N) IN derived_frontier t l` THEN
  ASM_SIMP_TAC[MOI_S3F2_DFR_CHAIN] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `c:(real^N->bool)->bool`] MOI_S3F2_VP_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [EXISTS_TAC `f:real^N->bool` THEN
    SUBGOAL_THEN `moi_frn_vp t l (f:real^N->bool)` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_SING]; ALL_TAC] THEN
    SUBGOAL_THEN `(f:real^N->bool) IN barycentric_subdivision t /\ ~(f = {})`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `moi_frn_vp t l (f:real^N->bool)` THEN REWRITE_TAC[moi_frn_vp] THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `y = simplex_barycentre (f:real^N->bool)` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^N) IN convex hull (IMAGE simplex_barycentre c)` THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_SING; IN_SING];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `f:real^N->bool`]
                  MOI_S3F2_VP_DIM) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `F ==> p`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `f:real^N->bool` o check (fun th ->
      can (find_term (fun u -> u = `M:real^N->bool`)) (concl th) && is_forall (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "bri" (MP_TAC o C MATCH_MP
      (CONJ (ASSUME `(f:real^N->bool) IN barycentric_subdivision t`)
            (ASSUME `~(f:real^N->bool = {})`))) THEN
    UNDISCH_TAC `(y:real^N) IN M` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_frn_vp t l (e:real^N->bool) /\ moi_frn_vp t l (r:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^N->bool) IN barycentric_subdivision t /\ ~(e = {}) /\
                (r:real^N->bool) IN barycentric_subdivision t /\ ~(r = {})`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`moi_frn_vp t l (e:real^N->bool)`;
                           `moi_frn_vp t l (r:real^N->bool)`] THEN
    REWRITE_TAC[moi_frn_vp] THEN SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(y:real^N) IN convex hull (IMAGE simplex_barycentre c)` THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES; GSYM SEGMENT_CONVEX_HULL] THEN DISCH_TAC THEN
  ASM_CASES_TAC `y = simplex_barycentre (e:real^N->bool)` THENL
   [EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN
  SUBGOAL_THEN `simplex_barycentre (r:real^N->bool) IN relative_interior r /\
                simplex_barycentre (e:real^N->bool) IN relative_interior e`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "bri" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN relative_interior r` ASSUME_TAC THENL
   [ASM_CASES_TAC `y = simplex_barycentre (r:real^N->bool)` THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`r:real^N->bool`; `simplex_barycentre (r:real^N->bool)`;
                   `simplex_barycentre (e:real^N->bool)`]
                  IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[MOI_BAR_COMPLEX_SIMPLEX; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
      MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
      MP_TAC(ISPEC `e:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[open_segment; IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
    ONCE_REWRITE_TAC[SEGMENT_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:real^N->bool` o check (fun th ->
    can (find_term (fun u -> u = `M:real^N->bool`)) (concl th) && is_forall (concl th))) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* Sides of the two triangles at a crossing barycentre.                      *)

let MOI_S3GP_TRACE_POINT = prove
 (`!(L:(real^3->bool)->bool) X s f r1 r2 y.
     simplicial_complex L /\ (!t. t IN L ==> aff_dim t <= &2) /\
     f IN L /\ aff_dim f = &1 /\ y IN relative_interior f /\
     {r | r IN L /\ aff_dim r = &2 /\ f SUBSET r} = {r1,r2} /\
     closed X /\ closure (interior X) = X /\ f SUBSET frontier X /\
     (?rho. &0 < rho /\ frontier X INTER UNIONS L INTER ball(y,rho) SUBSET f) /\
     pl_crossing_at s (frontier X) y /\
     (?w0. open w0 /\ y IN w0 /\ s INTER w0 = UNIONS L INTER w0)
     ==> ?e. &0 < e /\
             (((r1 DIFF f) INTER ball(y,e) SUBSET interior X /\
               DISJOINT ((r2 DIFF f) INTER ball(y,e)) X) \/
              ((r2 DIFF f) INTER ball(y,e) SUBSET interior X /\
               DISJOINT ((r1 DIFF f) INTER ball(y,e)) X))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "tri") MP_TAC)))))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC) (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `w0:real^3->bool` STRIP_ASSUME_TAC)))))) THEN
  SUBGOAL_THEN `!r:real^3->bool. r = r1 \/ r = r2
                                 ==> r IN L /\ aff_dim r = &2 /\ f SUBSET r`
  (LABEL_TAC "rr") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(r:real^3->bool) IN {r | r IN L /\ aff_dim r = &2 /\ f SUBSET r}` MP_TAC THENL
     [USE_THEN "tri" SUBST1_TAC THEN ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY]; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r:real^3->bool. r IN L ==> convex r` ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_complex (L:(real^3->bool)->bool)` THEN
    REWRITE_TAC[simplicial_complex] THEN MESON_TAC[SIMPLEX_IMP_CONVEX];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r:real^3->bool. r = r1 \/ r = r2 ==> convex (r DIFF f)` (LABEL_TAC "cvx") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "rr" (MP_TAC o C MATCH_MP (ASSUME `r:real^3->bool = r1 \/ r = r2`)) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `convex (r:real^3->bool) /\ (f:real^3->bool) face_of r` MP_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o SPECL [`f:real^3->bool`; `r:real^3->bool`] o
        CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o GEN_REWRITE_RULE I [simplicial_complex] o
        check (fun th -> concl th = `simplicial_complex (L:(real^3->bool)->bool)`)) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `f INTER r = (f:real^3->bool)` (fun th -> SIMP_TAC[th]) THEN ASM SET_TAC[];
      MESON_TAC[FACE_OF_STILLCONVEX]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^3->bool)->bool`; `f:real^3->bool`; `y:real^3`] MOI_S8TA_LOCAL_EDGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "tri" (fun th -> REWRITE_TAC[th; UNIONS_2]) THEN
  DISCH_THEN(X_CHOOSE_THEN `rr:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`X:real^3->bool`; `s:real^3->bool`; `y:real^3`; `r1 DIFF f:real^3->bool`;
                 `r2 DIFF f:real^3->bool`; `w0 INTER ball(y:real^3,min rr rho)`]
                MOI_S3GP_CROSS_SIDES) THEN
  ANTS_TAC THENL [ALL_TAC; DISCH_THEN ACCEPT_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
    USE_THEN "cvx" MATCH_MP_TAC THEN REWRITE_TAC[];
    USE_THEN "cvx" MATCH_MP_TAC THEN REWRITE_TAC[];
    ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL];
    ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL; REAL_LT_MIN];
    ALL_TAC] THEN
  SUBGOAL_THEN `(r1:real^3->bool) SUBSET UNIONS L /\ r2 SUBSET UNIONS L` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC(SET_RULE `(x:real^3->bool) IN L ==> x SUBSET UNIONS L`) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(y:real^3,min rr rho) SUBSET ball(y,rr) /\
                ball(y:real^3,min rr rho) SUBSET ball(y,rho)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`s INTER w0 = UNIONS L INTER (w0:real^3->bool)`;
    `UNIONS L INTER ball(y:real^3,rr) SUBSET f UNION r1 UNION r2`;
    `frontier X INTER UNIONS L INTER ball(y:real^3,rho) SUBSET f`;
    `(f:real^3->bool) SUBSET frontier X`;
    `(r1:real^3->bool) SUBSET UNIONS L`; `(r2:real^3->bool) SUBSET UNIONS L`;
    `ball(y:real^3,min rr rho) SUBSET ball(y,rr)`;
    `ball(y:real^3,min rr rho) SUBSET ball(y,rho)`] THEN
  SPEC_TAC(`frontier X:real^3->bool`,`M:real^3->bool`) THEN
  SPEC_TAC(`UNIONS L:real^3->bool`,`P:real^3->bool`) THEN
  SPEC_TAC(`ball(y:real^3,min rr rho)`,`B:real^3->bool`) THEN
  SPEC_TAC(`ball(y:real^3,rr)`,`B1:real^3->bool`) THEN
  SPEC_TAC(`ball(y:real^3,rho)`,`B2:real^3->bool`) THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Part 7: the derived frontier of the triangulated piece q near a          *)
(* point y on Bd X.  y is the barycentre of a vp edge f lying in Bd X; near *)
(* y the frontier is two segments [y,p1], [y,p2] towards the barycentres of *)
(* the two triangles on f, the half [y,p1] runs into Int X and the half     *)
(* [y,p2] misses X.                                                          *)
(* ------------------------------------------------------------------------- *)

let MOI_S3GP_TRACE_LOC = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c x q v lq lmq ldq y.
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\
     q SUBSET moi_s39_pcs l e INTER moi_s33_ww t l h /\
     open v /\ v SUBSET moi_s33_ww t l h /\ moi_s39_pcs l e INTER v SUBSET q /\
     simplicial_complex lq /\ UNIONS lq = q /\
     simplicial_subcomplex lmq lq /\ UNIONS lmq = frontier (UNIONS x) INTER q /\
     simplicial_subcomplex ldq lq /\ UNIONS ldq SUBSET v /\
     derived_frontier lq ldq SUBSET v /\
     y IN derived_frontier lq ldq /\ y IN frontier (UNIONS x)
     ==> ?p1 p2 d.
           &0 < d /\ ~(p1 = y) /\ ~(p2 = y) /\
           derived_frontier lq ldq INTER ball(y,d) =
           (segment[y,p1] UNION segment[y,p2]) INTER ball(y,d) /\
           (segment[y,p1] DELETE y) INTER ball(y,d) SUBSET interior (UNIONS x) /\
           DISJOINT ((segment[y,p2] DELETE y) INTER ball(y,d)) (UNIONS x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* basic facts *)
  SUBGOAL_THEN `closure (interior (UNIONS x)) = UNIONS (x:(real^3->bool)->bool) /\
                closed (UNIONS x)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `closure (interior (UNIONS x)) = UNIONS (x:(real^3->bool)->bool)`
    (fun th -> REWRITE_TAC[th] THEN MESON_TAC[th; CLOSED_CLOSURE]) THEN
    MATCH_MP_TAC MOI_FSP_REG_CLOSED THEN
    UNDISCH_TAC `moi_s33_inv t l h e (x:(real^3->bool)->bool)` THEN
    SIMP_TAC[moi_s33_inv; moi_s33_x2];
    ALL_TAC] THEN
  SUBGOAL_THEN `lf_simplicial_complex (lq:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF]; ALL_TAC] THEN
  MP_TAC(ISPECL [`lq:(real^3->bool)->bool`; `ldq:(real^3->bool)->bool`] MOI_FRN_SETUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`lq:(real^3->bool)->bool`; `lmq:(real^3->bool)->bool`]
                BARYCENTRIC_SUBDIVISION_SUBCOMPLEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `simplicial_complex (barycentric_subdivision (lq:(real^3->bool)->bool)) /\
                simplicial_complex (barycentric_subdivision (lmq:(real^3->bool)->bool))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC BARYCENTRIC_SUBDIVISION_SIMPLICIAL_COMPLEX THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S3F2_SUBCOMPLEX_SC THEN
    EXISTS_TAC `lq:(real^3->bool)->bool` THEN
    ASM_MESON_TAC[simplicial_subcomplex];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s IN lq ==> aff_dim (s:real^3->bool) <= &2` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3GP_PIECE_DIM THEN
    MAP_EVERY EXISTS_TAC [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
      `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
      `q:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s IN barycentric_subdivision lq ==> aff_dim (s:real^3->bool) <= &2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3F2_BSD_DIM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!f:real^3->bool. f IN barycentric_subdivision lq /\ aff_dim f = &1 /\ moi_frn_vp lq ldq f
                     ==> ?z. z IN relative_interior f /\ moi_s28_locally_r2 (UNIONS lq) z`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3GP_PIECE_FR2 THEN
    MAP_EVERY EXISTS_TAC [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
      `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
      `q:real^3->bool`; `v:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  (* no triangle in Bd X *)
  SUBGOAL_THEN `!r:real^3->bool. convex r /\ aff_dim r = &2 /\
                                 r SUBSET q INTER frontier (UNIONS x) ==> F`
  (LABEL_TAC "notri") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S3GP_NO_TRI_Q THEN
    MAP_EVERY EXISTS_TAC [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
      `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
      `x:(real^3->bool)->bool`; `q:real^3->bool`; `r:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r:real^3->bool. r IN barycentric_subdivision lq ==> convex r`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_COMPLEX_SIMPLEX; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  SUBGOAL_THEN `!r:real^3->bool. r IN barycentric_subdivision lmq ==> r SUBSET q INTER frontier (UNIONS x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `UNIONS (barycentric_subdivision lmq) = UNIONS (lmq:(real^3->bool)->bool)` THEN
    UNDISCH_TAC `UNIONS lmq = frontier (UNIONS x) INTER (q:real^3->bool)` THEN
    UNDISCH_TAC `(r:real^3->bool) IN barycentric_subdivision lmq` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r:real^3->bool. r IN barycentric_subdivision lq /\ aff_dim r = &2
                                 ==> DISJOINT (relative_interior r) (frontier (UNIONS x))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(r:real^3->bool) IN barycentric_subdivision lmq` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_S3GP_RELINT_IN_SUB THEN
      MAP_EVERY EXISTS_TAC [`barycentric_subdivision (lq:(real^3->bool)->bool)`; `z:real^3`] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `r:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
      UNDISCH_TAC `UNIONS (barycentric_subdivision lmq) = UNIONS (lmq:(real^3->bool)->bool)` THEN
      UNDISCH_TAC `UNIONS lmq = frontier (UNIONS x) INTER (q:real^3->bool)` THEN
      UNDISCH_TAC `UNIONS (barycentric_subdivision lq) = UNIONS (lq:(real^3->bool)->bool)` THEN
      UNDISCH_TAC `UNIONS lq = (q:real^3->bool)` THEN
      UNDISCH_TAC `(r:real^3->bool) IN barycentric_subdivision lq` THEN
      UNDISCH_TAC `(z:real^3) IN frontier (UNIONS x)` THEN
      UNDISCH_TAC `(z:real^3) IN relative_interior r` THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "notri" (MP_TAC o SPEC `r:real^3->bool`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* y is the barycentre of a vp edge f in Bd X *)
  MP_TAC(ISPECL [`lq:(real^3->bool)->bool`; `ldq:(real^3->bool)->bool`;
                 `frontier (UNIONS x):real^3->bool`; `y:real^3`] MOI_S3GP_DFR_MEET) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:real^3) IN relative_interior f /\ ~(f:real^3->bool = {})`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `~(f:real^3->bool = {})` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `aff_dim({}:real^3->bool) = &1` THEN REWRITE_TAC[AFF_DIM_EMPTY] THEN
      INT_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SIMPLEX_BARYCENTRE_IN_RELATIVE_INTERIOR THEN
    ASM_MESON_TAC[MOI_BAR_COMPLEX_SIMPLEX];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN q` ASSUME_TAC THENL
   [MP_TAC(ISPEC `f:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `UNIONS (barycentric_subdivision lq) = UNIONS (lq:(real^3->bool)->bool)` THEN
    UNDISCH_TAC `UNIONS lq = (q:real^3->bool)` THEN
    UNDISCH_TAC `(f:real^3->bool) IN barycentric_subdivision lq` THEN
    UNDISCH_TAC `(y:real^3) IN relative_interior f` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^3->bool) IN barycentric_subdivision lmq` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3GP_RELINT_IN_SUB THEN
    MAP_EVERY EXISTS_TAC [`barycentric_subdivision (lq:(real^3->bool)->bool)`; `y:real^3`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^3->bool) SUBSET frontier (UNIONS x)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  (* the frontier near y *)
  MP_TAC(ISPECL [`lq:(real^3->bool)->bool`; `ldq:(real^3->bool)->bool`; `f:real^3->bool`]
                MOI_S3F2_DFR_EDGE_STAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[DIMINDEX_3; ARITH]; ALL_TAC] THEN
  UNDISCH_THEN `y = simplex_barycentre (f:real^3->bool)` (fun th ->
    SUBST_ALL_TAC(SYM th) THEN ASSUME_TAC(SYM th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real^3->bool` (X_CHOOSE_THEN `r2:real^3->bool`
    (X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC))) THEN
  (* the trace near y is f *)
  MP_TAC(ISPECL [`barycentric_subdivision (lmq:(real^3->bool)->bool)`; `f:real^3->bool`;
                 `y:real^3`] MOI_S8TA_LOCAL_EDGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real^3->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      concl th = `!s. s IN barycentric_subdivision lq ==> aff_dim (s:real^3->bool) <= &2`)) THEN
    ASM_MESON_TAC[simplicial_subcomplex; SUBSET];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `{t | t IN barycentric_subdivision lmq /\ aff_dim t = &2 /\
                     (f:real^3->bool) SUBSET t} = {}` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN X_GEN_TAC `r:real^3->bool` THEN
    STRIP_TAC THEN USE_THEN "notri" (MP_TAC o SPEC `r:real^3->bool`) THEN
    REWRITE_TAC[] THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[simplicial_subcomplex; SUBSET];
    ALL_TAC] THEN
  (* the crossing chart *)
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`; `y:real^3`]
                MOI_S3GP_PCS_LOCAL) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3` (X_CHOOSE_THEN `u':real^3` (X_CHOOSE_THEN
    `w:real^3->bool` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `pl_crossing_at ((e:(real^3->bool)->real^3->bool)(segment[u,u']) DIFF
                                moi_s33_rim t l h u u') (frontier (UNIONS x)) (y:real^3)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s33_inv t l h e (x:(real^3->bool)->bool)` THEN
    REWRITE_TAC[moi_s33_inv; moi_s33_x2] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision (lq:(real^3->bool)->bool)`; `UNIONS x:real^3->bool`;
                 `(e:(real^3->bool)->real^3->bool)(segment[u,u']) DIFF moi_s33_rim t l h u u'`;
                 `f:real^3->bool`; `r1:real^3->bool`; `r2:real^3->bool`; `y:real^3`]
                MOI_S3GP_TRACE_POINT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXISTS_TAC `rho:real` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `UNIONS (barycentric_subdivision lmq) INTER ball(y:real^3,rho) SUBSET
                   f UNION UNIONS {t | t IN barycentric_subdivision lmq /\ aff_dim t = &2 /\
                                       f SUBSET t}` THEN
      ASM_REWRITE_TAC[UNIONS_0; UNION_EMPTY] THEN SET_TAC[];
      EXISTS_TAC `w INTER v:real^3->bool` THEN ASM_SIMP_TAC[OPEN_INTER; IN_INTER] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC
       [`moi_s39_pcs l e INTER w = (e:(real^3->bool)->real^3->bool)(segment[u,u']) INTER w`;
        `(e:(real^3->bool)->real^3->bool)(segment[u,u']) INTER moi_s33_ww t l h =
         (e(segment[u,u']) DIFF moi_s33_rim t l h u u') DELETE h(midpoint(u,u'))`;
        `moi_s39_pcs l e INTER v SUBSET (q:real^3->bool)`;
        `q SUBSET moi_s39_pcs l e INTER moi_s33_ww t l (h:real^3->real^3)`;
        `v SUBSET moi_s33_ww t l (h:real^3->real^3)`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  (* the half-segments lie in the open triangles *)
  SUBGOAL_THEN
   `!r:real^3->bool. r = r1 \/ r = r2
                     ==> ~(simplex_barycentre r = y) /\
                         segment[y,simplex_barycentre r] DELETE y SUBSET r DIFF f`
  (LABEL_TAC "half") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(r:real^3->bool) IN barycentric_subdivision lq /\ aff_dim r = &2 /\ f SUBSET r`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(r:real^3->bool) IN {r | r IN barycentric_subdivision lq /\ aff_dim r = &2 /\
                                             f SUBSET r}` MP_TAC THENL
       [FIRST_ASSUM(SUBST1_TAC o check (fun th ->
          is_eq (concl th) && rhs (concl th) = `{r1:real^3->bool,r2}`)) THEN
        ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY];
        REWRITE_TAC[IN_ELIM_THM]];
      ALL_TAC] THEN
    SUBGOAL_THEN `simplex_barycentre (r:real^3->bool) IN relative_interior r` ASSUME_TAC THENL
     [SUBGOAL_THEN `?n. n simplex (r:real^3->bool)` STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[MOI_BAR_COMPLEX_SIMPLEX]; ALL_TAC] THEN
      MATCH_MP_TAC SIMPLEX_BARYCENTRE_IN_RELATIVE_INTERIOR THEN
      EXISTS_TAC `n:int` THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `aff_dim({}:real^3->bool) = &2` THEN REWRITE_TAC[AFF_DIM_EMPTY] THEN
      INT_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `DISJOINT (relative_interior (r:real^3->bool)) (frontier (UNIONS x))`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `segment(y,simplex_barycentre r) SUBSET relative_interior (r:real^3->bool)`
    ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[SEGMENT_SYM] THEN
      MATCH_MP_TAC IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
      MP_TAC(ISPEC `f:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SEGMENT_CLOSED_OPEN] THEN
    MP_TAC(ISPEC `r:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(f:real^3->bool) SUBSET frontier (UNIONS x)` THEN
    UNDISCH_TAC `DISJOINT (relative_interior (r:real^3->bool)) (frontier (UNIONS x))` THEN
    UNDISCH_TAC `segment(y,simplex_barycentre r) SUBSET relative_interior (r:real^3->bool)` THEN
    UNDISCH_TAC `simplex_barycentre (r:real^3->bool) IN relative_interior r` THEN
    SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "half" (MP_TAC o SPEC `r1:real^3->bool`) THEN
  USE_THEN "half" (MP_TAC o SPEC `r2:real^3->bool`) THEN
  REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ball(y:real^3,min d0 e1) SUBSET ball(y,d0) /\
                ball(y:real^3,min d0 e1) SUBSET ball(y,e1)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `derived_frontier lq ldq INTER ball(y:real^3,min d0 e1) =
    (segment[y,simplex_barycentre r1] UNION segment[y,simplex_barycentre r2]) INTER
    ball(y,min d0 e1)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `derived_frontier lq ldq INTER ball(y:real^3,d0) =
                 (segment[y,simplex_barycentre r1] UNION segment[y,simplex_barycentre r2]) INTER
                 ball(y,d0)` THEN
    UNDISCH_TAC `ball(y:real^3,min d0 e1) SUBSET ball(y,d0)` THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (fun th ->
    is_disj (concl th) &&
    can (find_term (fun u -> u = `interior (UNIONS x:real^3->bool)`)) (concl th))) THENL
   [MAP_EVERY EXISTS_TAC [`simplex_barycentre (r1:real^3->bool)`;
                          `simplex_barycentre (r2:real^3->bool)`; `min d0 e1`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[REAL_LT_MIN]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`segment[y,simplex_barycentre r1] DELETE y SUBSET r1 DIFF (f:real^3->bool)`;
        `ball(y:real^3,min d0 e1) SUBSET ball(y,e1)`;
        `(r1 DIFF f) INTER ball(y:real^3,e1) SUBSET interior (UNIONS x)`] THEN
      SET_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`segment[y,simplex_barycentre r2] DELETE y SUBSET r2 DIFF (f:real^3->bool)`;
        `ball(y:real^3,min d0 e1) SUBSET ball(y,e1)`;
        `DISJOINT ((r2 DIFF f) INTER ball(y:real^3,e1)) (UNIONS x)`] THEN
      SET_TAC[]];
    MAP_EVERY EXISTS_TAC [`simplex_barycentre (r2:real^3->bool)`;
                          `simplex_barycentre (r1:real^3->bool)`; `min d0 e1`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[REAL_LT_MIN]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`segment[y,simplex_barycentre r2] DELETE y SUBSET r2 DIFF (f:real^3->bool)`;
        `ball(y:real^3,min d0 e1) SUBSET ball(y,e1)`;
        `(r2 DIFF f) INTER ball(y:real^3,e1) SUBSET interior (UNIONS x)`] THEN
      SET_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`segment[y,simplex_barycentre r1] DELETE y SUBSET r1 DIFF (f:real^3->bool)`;
        `ball(y:real^3,min d0 e1) SUBSET ball(y,e1)`;
        `DISJOINT ((r1 DIFF f) INTER ball(y:real^3,e1)) (UNIONS x)`] THEN
      SET_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Part 8: the side of the sheets, PL 1-cells, and the family.  In the      *)
(* box context the open sheets d1 - j1, d2 - j2 of the frontier F of the   *)
(* second-derived neighbourhood of d are F - Bd X intersected with Int X    *)
(* (d inside X) or with the complement of X (d outside X).  A union DF of   *)
(* finitely many PL circles, cut by a closed set D under the local side     *)
(* conditions, meets D in a finite family of PL circles missing Bd X and   *)
(* PL arcs whose ends are their points on Bd X.                             *)
(* ------------------------------------------------------------------------- *)

let MOI_S3GP_SHEET_SIDE = prove
 (`!(m:(real^3->bool)->bool) d j v a b t ld lm j1 j2 d1 d2 x.
     FINITE m /\ combinatorial_manifold 2 m /\
     pl_cell_with_boundary 2 d j /\ d INTER UNIONS m = j /\
     moi_fsp_box m d v a b t ld lm /\ moi_fsp_ends m j t ld j1 j2 d1 d2 /\
     FINITE x /\ combinatorial_manifold_with_boundary 3 x /\
     frontier (UNIONS x) = UNIONS m
     ==> ?G. (G = interior (UNIONS x) \/ G = (:real^3) DIFF UNIONS x) /\
             (derived_frontier t ld DIFF UNIONS m) INTER G = (d1 UNION d2) DIFF (j1 UNION j2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `d:real^3->bool`; `j:real^3->bool`;
                 `v:real^3->bool`; `a:real^3`; `b:real^3`; `t:(real^3->bool)->bool`;
                 `ld:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                 `x:(real^3->bool)->bool`] MOI_FSP_X_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `d:real^3->bool`; `j:real^3->bool`;
                 `v:real^3->bool`; `a:real^3`; `b:real^3`; `t:(real^3->bool)->bool`;
                 `ld:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`] MOI_FSP_N_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_fsp_box] o check (fun th ->
    can (term_match [] `moi_fsp_box m d v a b t ld (lm:(real^3->bool)->bool)`) (concl th))) THEN
  ABBREV_TAC `X = UNIONS (x:(real^3->bool)->bool)` THEN
  ABBREV_TAC `N = derived_nbhd t (ld:(real^3->bool)->bool)` THEN
  SUBGOAL_THEN `X DIFF interior X = UNIONS (m:(real^3->bool)->bool)` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `frontier X = UNIONS (m:(real^3->bool)->bool)`)) THEN
    REWRITE_TAC[frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th ->
    concl th = `d SUBSET X \/ d INTER X = (j:real^3->bool)`)) THENL
   [EXISTS_TAC `interior X:real^3->bool` THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `d:real^3->bool`; `j:real^3->bool`;
                   `v:real^3->bool`; `a:real^3`; `b:real^3`; `t:(real^3->bool)->bool`;
                   `ld:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                   `j1:real^3->bool`; `j2:real^3->bool`; `d1:real^3->bool`; `d2:real^3->bool`;
                   `{s | s IN t /\ s SUBSET (X:real^3->bool)}`; `{}:real^3->bool`]
                  MOI_FSP_CUT_SIDE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[UNION_EMPTY; CLOSED_EMPTY; DISJOINT_EMPTY] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `s:real^3->bool` THEN DISCH_TAC THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC[simplicial_subcomplex; SUBSET];
        UNDISCH_TAC `d SUBSET (X:real^3->bool)` THEN
        UNDISCH_TAC `UNIONS ld = (d:real^3->bool)` THEN
        UNDISCH_TAC `(s:real^3->bool) IN ld` THEN SET_TAC[]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPEC `X:real^3->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `X DIFF interior X = UNIONS (m:(real^3->bool)->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `(:real^3) DIFF X` THEN REWRITE_TAC[] THEN
    ABBREV_TAC `xt = {s | s IN t /\ s SUBSET (X:real^3->bool)}` THEN
    ABBREV_TAC `yA = {s | s IN t /\ s SUBSET closure (UNIONS t DIFF UNIONS (xt:(real^3->bool)->bool))}` THEN
    SUBGOAL_THEN `interior (interval[a:real^3,b]) = interval(a,b)` ASSUME_TAC THENL
     [REWRITE_TAC[INTERIOR_CLOSED_INTERVAL]; ALL_TAC] THEN
    (* the closed complement Y of X in the box *)
    SUBGOAL_THEN
     `simplicial_subcomplex yA (t:(real^3->bool)->bool) /\
      UNIONS yA = closure (interval[a,b] DIFF X) /\ FINITE yA /\
      combinatorial_manifold_with_boundary 3 yA /\
      complex_boundary yA = UNIONS m UNION (interval[a,b] DIFF interval(a:real^3,b)) /\
      closure (interval[a,b] DIFF X) = interval[a,b] DIFF interior X`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `simplicial_subcomplex yA (t:(real^3->bool)->bool)` ASSUME_TAC THENL
       [EXPAND_TAC "yA" THEN MATCH_MP_TAC MOI_FSP_COMP_SUBCX THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `UNIONS yA = closure (interval[a,b] DIFF (X:real^3->bool))` ASSUME_TAC THENL
       [EXPAND_TAC "yA" THEN ASM_SIMP_TAC[MOI_FSP_COMP_UNIONS2]; ALL_TAC] THEN
      SUBGOAL_THEN `FINITE (yA:(real^3->bool)->bool)` ASSUME_TAC THENL
       [ASM_MESON_TAC[FINITE_SUBSET; simplicial_subcomplex]; ALL_TAC] THEN
      MP_TAC(ISPECL [`X:real^3->bool`; `interval[a:real^3,b]`] MOI_FSP_FRONTIER_COMPL_BOX) THEN
      ASM_SIMP_TAC[CLOSED_INTERVAL; COMPACT_IMP_CLOSED] THEN
      DISCH_THEN(fun th -> let th1 = CONJUNCT1 th and th2 = CONJUNCT2 th in
        ASSUME_TAC th1 THEN ASSUME_TAC (REWRITE_RULE[th1] th2)) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `combinatorial_manifold_with_boundary 3 (yA:(real^3->bool)->bool)`
      ASSUME_TAC THENL
       [EXPAND_TAC "yA" THEN MATCH_MP_TAC MOI_FSP_COMP_CMWB THEN ASM_REWRITE_TAC[] THEN
        X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN MATCH_MP_TAC(TAUT `F ==> p`) THEN
        UNDISCH_TAC `(w:real^3) IN UNIONS m` THEN
        UNDISCH_TAC `(w:real^3) IN interval[a,b] DIFF interval(a,b)` THEN
        UNDISCH_TAC `d UNION UNIONS m SUBSET interval(a:real^3,b)` THEN SET_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `yA:(real^3->bool)->bool` COMPLEX_BOUNDARY_FRONTIER_3) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    (* ld lies in Y *)
    SUBGOAL_THEN `ld SUBSET (yA:(real^3->bool)->bool)` ASSUME_TAC THENL
     [SUBGOAL_THEN `d SUBSET closure (interval[a,b] DIFF (X:real^3->bool))` ASSUME_TAC THENL
       [FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP MOI_FSP_CELL_CLOSURE) THEN
        MATCH_MP_TAC SUBSET_CLOSURE THEN
        MP_TAC(ISPECL [`a:real^3`; `b:real^3`] INTERVAL_OPEN_SUBSET_CLOSED) THEN
        UNDISCH_TAC `d UNION UNIONS m SUBSET interval(a:real^3,b)` THEN
        UNDISCH_TAC `d INTER X = (j:real^3->bool)` THEN SET_TAC[];
        ALL_TAC] THEN
      EXPAND_TAC "yA" THEN GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `s:real^3->bool` THEN DISCH_TAC THEN CONJ_TAC THENL
       [MP_TAC(ASSUME `simplicial_subcomplex ld (t:(real^3->bool)->bool)`) THEN
        REWRITE_TAC[simplicial_subcomplex; SUBSET] THEN
        DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[];
        SUBGOAL_THEN `closure (UNIONS t DIFF UNIONS xt) =
                      closure (interval[a,b] DIFF (X:real^3->bool))` SUBST1_TAC THENL
         [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `d:real^3->bool` THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `UNIONS ld = (d:real^3->bool)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        UNDISCH_TAC `(s:real^3->bool) IN ld` THEN SET_TAC[]];
      ALL_TAC] THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `d:real^3->bool`; `j:real^3->bool`;
                 `v:real^3->bool`; `a:real^3`; `b:real^3`; `t:(real^3->bool)->bool`;
                 `ld:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                 `j1:real^3->bool`; `j2:real^3->bool`; `d1:real^3->bool`; `d2:real^3->bool`;
                 `yA:(real^3->bool)->bool`; `interval[a,b] DIFF interval(a:real^3,b)`]
                MOI_FSP_CUT_SIDE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_DIFF THEN REWRITE_TAC[CLOSED_INTERVAL; OPEN_INTERVAL];
      UNDISCH_TAC `N SUBSET v INTER interval(a:real^3,b)` THEN SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPEC `X:real^3->bool` INTERIOR_SUBSET) THEN
  MP_TAC(ISPECL [`a:real^3`; `b:real^3`] INTERVAL_OPEN_SUBSET_CLOSED) THEN
  UNDISCH_TAC `derived_frontier t ld SUBSET (N:real^3->bool)` THEN
  UNDISCH_TAC `N SUBSET v INTER interval(a:real^3,b)` THEN
  UNDISCH_TAC `X DIFF interior X = UNIONS (m:(real^3->bool)->bool)` THEN SET_TAC[]);;

(* The two ends of a PL 1-cell form a nonempty set.                           *)

let MOI_S3GP_CELL1_BD_NONEMPTY = prove
 (`!(a:real^N->bool) b. pl_cell_with_boundary 1 a b ==> ~(b = {})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[IMAGE_EQ_EMPTY; RELATIVE_FRONTIER_EQ_EMPTY] THEN DISCH_TAC THEN
  SUBGOAL_THEN `aff_dim (k:real^N->bool) = &1` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFF_DIM_SIMPLEX]; ALL_TAC] THEN
  MP_TAC(ISPEC `k:real^N->bool` AFFINE_BOUNDED_EQ_TRIVIAL) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `bounded (k:real^N->bool)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_BOUNDED]; ALL_TAC] THEN
  STRIP_TAC THENL
   [UNDISCH_TAC `aff_dim (k:real^N->bool) = &1` THEN ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN
    INT_ARITH_TAC;
    UNDISCH_TAC `aff_dim (k:real^N->bool) = &1` THEN ASM_REWRITE_TAC[AFF_DIM_SING] THEN
    INT_ARITH_TAC]);;

(* Near a point of a component of a closed set with finitely many           *)
(* components, the set is that component.                                    *)

let MOI_S3GP_COMP_LOCAL = prove
 (`!(S:real^N->bool) C y.
     closed S /\ FINITE (components S) /\ C IN components S /\ y IN C
     ==> ?d. &0 < d /\ S INTER ball(y,d) = C INTER ball(y,d)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`UNIONS (components S DELETE (C:real^N->bool))`; `y:real^N`]
                SEPARATE_POINT_CLOSED) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_UNIONS THEN ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE] THEN
      ASM_MESON_TAC[CLOSED_COMPONENTS];
      REWRITE_TAC[IN_UNIONS; IN_DELETE] THEN
      DISCH_THEN(X_CHOOSE_THEN `C':real^N->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`S:real^N->bool`; `C:real^N->bool`; `C':real^N->bool`]
                    COMPONENTS_NONOVERLAP) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:real^N` THEN REWRITE_TAC[IN_INTER; IN_BALL] THEN
  EQ_TAC THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(z:real^N) IN UNIONS (components S)` MP_TAC THENL
     [REWRITE_TAC[GSYM UNIONS_COMPONENTS] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS] THEN DISCH_THEN(X_CHOOSE_THEN `C':real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `C':real^N->bool = C` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N` o check (fun th ->
      is_forall (concl th) && can (find_term (fun u -> u = `d:real`)) (concl th))) THEN
    REWRITE_TAC[IN_UNIONS; IN_DELETE] THEN
    ANTS_TAC THENL [EXISTS_TAC `C':real^N->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_REAL_ARITH_TAC;
    ASM_MESON_TAC[IN_COMPONENTS_SUBSET; SUBSET]]);;

(* The family of components of D INTER DF.                                   *)

let MOI_S3GP_FAMILY = prove
 (`!(DF:real^N->bool) D M.
     FINITE (components DF) /\ (!k. k IN components DF ==> pl_sphere 1 k) /\
     closed D /\ FINITE (DF INTER M) /\
     (!s0. connected s0 /\ s0 SUBSET DF DIFF M ==> s0 SUBSET D \/ DISJOINT s0 D) /\
     (!y. y IN DF /\ y IN M /\ y IN D
          ==> ?p1 p2 d. &0 < d /\ ~(p1 = y) /\ ~(p2 = y) /\
                        DF INTER ball(y,d) =
                        (segment[y,p1] UNION segment[y,p2]) INTER ball(y,d) /\
                        (segment[y,p1] DELETE y) INTER ball(y,d) SUBSET D /\
                        DISJOINT ((segment[y,p2] DELETE y) INTER ball(y,d)) D)
     ==> FINITE (components (D INTER DF)) /\
         !a. a IN components (D INTER DF)
             ==> (pl_sphere 1 a /\ DISJOINT a M) \/ pl_cell_with_boundary 1 a (a INTER M)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "side") (LABEL_TAC "loc")))))) THEN
  SUBGOAL_THEN `closed (DF:real^N->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `DF = UNIONS (components (DF:real^N->bool))` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM UNIONS_COMPONENTS]; ALL_TAC] THEN
    MATCH_MP_TAC CLOSED_UNIONS THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `pl_sphere 1 (k:real^N->bool)` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `gk:real^1->real^N` STRIP_ASSUME_TAC o
      MATCH_MP MOI_S4O_CIRCLE_LOOP) THEN
    UNDISCH_TAC `path_image (gk:real^1->real^N) = k` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED; COMPACT_PATH_IMAGE; SIMPLE_PATH_IMP_PATH];
    ALL_TAC] THEN
  (* each component of D INTER DF is a component of the cut of one circle *)
  SUBGOAL_THEN
   `!a. a IN components (D INTER DF)
        ==> ?C:real^N->bool. C IN components DF /\ a SUBSET C /\ a IN components (C INTER D)`
  (LABEL_TAC "inC") THENL
   [X_GEN_TAC `a:real^N->bool` THEN DISCH_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [IN_COMPONENTS_MAXIMAL]) THEN
    FIRST_ASSUM(X_CHOOSE_TAC `z:real^N` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY] o
      check (fun th -> concl th = `~(a:real^N->bool = {})`)) THEN
    EXISTS_TAC `connected_component DF (z:real^N)` THEN
    SUBGOAL_THEN `a SUBSET connected_component DF (z:real^N)` ASSUME_TAC THENL
     [MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM SET_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[IN_COMPONENTS] THEN EXISTS_TAC `z:real^N` THEN ASM SET_TAC[];
      FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[IN_COMPONENTS_MAXIMAL] THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `c':real^N->bool` THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`DF:real^N->bool`; `z:real^N`] CONNECTED_COMPONENT_SUBSET) THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a. a IN components (D INTER DF)
        ==> (a IN components DF /\ DISJOINT a M) \/
            pl_cell_with_boundary 1 a (a INTER (M:real^N->bool))`
  (LABEL_TAC "each") THENL
   [X_GEN_TAC `a:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "inC" (MP_TAC o C MATCH_MP
      (ASSUME `a IN components (D INTER DF:real^N->bool)`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `C:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `C SUBSET (DF:real^N->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPECL [`C:real^N->bool`; `C INTER (M:real^N->bool)`; `D:real^N->bool`;
                   `a:real^N->bool`] MOI_S3GP_CIRCLE_CUT) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[];
        MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `DF INTER (M:real^N->bool)` THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        SET_TAC[];
        ASM_REWRITE_TAC[];
        X_GEN_TAC `s0:real^N->bool` THEN STRIP_TAC THEN USE_THEN "side" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
        USE_THEN "loc" (MP_TAC o SPEC `y:real^N`) THEN
        ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `p1:real^N` (X_CHOOSE_THEN `p2:real^N` (X_CHOOSE_THEN `d:real`
          STRIP_ASSUME_TAC))) THEN
        MP_TAC(ISPECL [`DF:real^N->bool`; `C:real^N->bool`; `y:real^N`] MOI_S3GP_COMP_LOCAL) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
        MAP_EVERY EXISTS_TAC [`p1:real^N`; `p2:real^N`; `min d d1`] THEN
        SUBGOAL_THEN `ball(y:real^N,min d d1) SUBSET ball(y,d) /\
                      ball(y:real^N,min d d1) SUBSET ball(y,d1)` STRIP_ASSUME_TAC THENL
         [REWRITE_TAC[SUBSET; IN_BALL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
        REPEAT CONJ_TAC THENL
         [ASM_REWRITE_TAC[REAL_LT_MIN];
          ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[];
          MAP_EVERY UNDISCH_TAC
           [`DF INTER ball(y:real^N,d) = (segment[y,p1] UNION segment[y,p2]) INTER ball(y,d)`;
            `DF INTER ball(y:real^N,d1) = C INTER ball(y,d1)`;
            `ball(y:real^N,min d d1) SUBSET ball(y,d)`;
            `ball(y:real^N,min d d1) SUBSET ball(y,d1)`] THEN
          SET_TAC[];
          MAP_EVERY UNDISCH_TAC
           [`(segment[y:real^N,p1] DELETE y) INTER ball(y,d) SUBSET D`;
            `ball(y:real^N,min d d1) SUBSET ball(y,d)`] THEN
          SET_TAC[];
          MAP_EVERY UNDISCH_TAC
           [`DISJOINT ((segment[y:real^N,p2] DELETE y) INTER ball(y,d)) D`;
            `ball(y:real^N,min d d1) SUBSET ball(y,d)`] THEN
          SET_TAC[]];
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    STRIP_TAC THENL
     [DISJ1_TAC THEN ASM_REWRITE_TAC[DISJOINT];
      DISJ2_TAC THEN
      SUBGOAL_THEN `a INTER M = a INTER (C INTER (M:real^N->bool))` SUBST1_TAC THENL
       [ASM SET_TAC[]; ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `components DF UNION
                {a | a IN components (D INTER DF) /\
                     ~(a INTER (DF INTER (M:real^N->bool)) = {})}` THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[FINITE_UNION] THEN
      MP_TAC(ISPECL [`\a:real^N->bool. a INTER (DF INTER M)`;
                     `{a | a IN components (D INTER DF) /\
                           ~(a INTER (DF INTER (M:real^N->bool)) = {})}`]
                    FINITE_IMAGE_INJ_EQ) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[IN_ELIM_THM] THEN
        MAP_EVERY X_GEN_TAC [`a1:real^N->bool`; `a2:real^N->bool`] THEN STRIP_TAC THEN
        MP_TAC(ISPECL [`D INTER DF:real^N->bool`; `a1:real^N->bool`; `a2:real^N->bool`]
                      COMPONENTS_EQ) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM SET_TAC[];
        DISCH_THEN(SUBST1_TAC o SYM)] THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{s | s SUBSET DF INTER (M:real^N->bool)}` THEN
      ASM_SIMP_TAC[FINITE_POWERSET] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      SET_TAC[];
      REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN X_GEN_TAC `a:real^N->bool` THEN
      DISCH_TAC THEN
      USE_THEN "each" (MP_TAC o C MATCH_MP
        (ASSUME `a IN components (D INTER DF:real^N->bool)`)) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3GP_CELL1_BD_NONEMPTY) THEN
      MP_TAC(ISPECL [`D INTER DF:real^N->bool`; `a:real^N->bool`] IN_COMPONENTS_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    X_GEN_TAC `a:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "each" (MP_TAC o C MATCH_MP
      (ASSUME `a IN components (D INTER DF:real^N->bool)`)) THEN
    STRIP_TAC THEN ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Part 9: the open triangles of the first derived of q miss Bd X, so       *)
(* the derived frontier meets Bd X in finitely many points; intersections  *)
(* of subcomplexes; the sheet d1 is a loop theorem disk (its rim j1 is     *)
(* homotopic in the annulus to the rim j of d).                             *)
(* ------------------------------------------------------------------------- *)

let MOI_S3GP_SUBCX_INTER = prove
 (`!(t:(real^N->bool)->bool) l m.
     simplicial_subcomplex l t /\ simplicial_subcomplex m t
     ==> simplicial_subcomplex (l INTER m) m`,
  REWRITE_TAC[simplicial_subcomplex; IN_INTER; SUBSET] THEN MESON_TAC[]);;

let MOI_S3GP_PIECE_TRI_MISS = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c x q lq lmq.
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\
     q SUBSET moi_s39_pcs l e INTER moi_s33_ww t l h /\
     simplicial_complex lq /\ UNIONS lq = q /\
     simplicial_subcomplex lmq lq /\ UNIONS lmq = frontier (UNIONS x) INTER q
     ==> !r. r IN barycentric_subdivision lq /\ aff_dim r = &2
             ==> DISJOINT (relative_interior r) (frontier (UNIONS x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (lq:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF]; ALL_TAC] THEN
  MP_TAC(ISPECL [`lq:(real^3->bool)->bool`; `lmq:(real^3->bool)->bool`]
                BARYCENTRIC_SUBDIVISION_SUBCOMPLEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`lq:(real^3->bool)->bool`; `lq:(real^3->bool)->bool`] MOI_FRN_SETUP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[simplicial_subcomplex; SUBSET_REFL] THEN
    ASM_MESON_TAC[simplicial_complex];
    STRIP_TAC] THEN
  SUBGOAL_THEN `simplicial_complex (barycentric_subdivision (lq:(real^3->bool)->bool))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC BARYCENTRIC_SUBDIVISION_SIMPLICIAL_COMPLEX THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `r:real^3->bool` THEN STRIP_TAC THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(r:real^3->bool) IN barycentric_subdivision lmq` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3GP_RELINT_IN_SUB THEN
    MAP_EVERY EXISTS_TAC [`barycentric_subdivision (lq:(real^3->bool)->bool)`; `z:real^3`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `r:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `UNIONS (barycentric_subdivision lmq) = UNIONS (lmq:(real^3->bool)->bool)` THEN
    UNDISCH_TAC `UNIONS lmq = frontier (UNIONS x) INTER (q:real^3->bool)` THEN
    UNDISCH_TAC `UNIONS (barycentric_subdivision lq) = UNIONS (lq:(real^3->bool)->bool)` THEN
    UNDISCH_TAC `UNIONS lq = (q:real^3->bool)` THEN
    UNDISCH_TAC `(r:real^3->bool) IN barycentric_subdivision lq` THEN
    UNDISCH_TAC `(z:real^3) IN frontier (UNIONS x)` THEN
    UNDISCH_TAC `(z:real^3) IN relative_interior r` THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S3GP_NO_TRI_Q THEN
  MAP_EVERY EXISTS_TAC [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
    `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
    `x:(real^3->bool)->bool`; `q:real^3->bool`; `r:real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_COMPLEX_SIMPLEX; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  UNDISCH_TAC `UNIONS (barycentric_subdivision lmq) = UNIONS (lmq:(real^3->bool)->bool)` THEN
  UNDISCH_TAC `UNIONS lmq = frontier (UNIONS x) INTER (q:real^3->bool)` THEN
  UNDISCH_TAC `(r:real^3->bool) IN barycentric_subdivision lmq` THEN SET_TAC[]);;

let MOI_S3GP_MEET_FINITE = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c x q lq lmq ldq.
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\
     q SUBSET moi_s39_pcs l e INTER moi_s33_ww t l h /\
     simplicial_complex lq /\ UNIONS lq = q /\
     simplicial_subcomplex lmq lq /\ UNIONS lmq = frontier (UNIONS x) INTER q /\
     simplicial_subcomplex ldq lq
     ==> FINITE (derived_frontier lq ldq INTER frontier (UNIONS x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (lq:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF]; ALL_TAC] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE simplex_barycentre (barycentric_subdivision (lq:(real^3->bool)->bool))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC MOI_BAR_SUBDIVISION_FINITE THEN
    ASM_MESON_TAC[simplicial_complex];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`lq:(real^3->bool)->bool`; `ldq:(real^3->bool)->bool`;
                 `frontier (UNIONS x):real^3->bool`; `y:real^3`] MOI_S3GP_DFR_MEET) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S3GP_PIECE_DIM THEN
      MAP_EVERY EXISTS_TAC [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
        `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
        `q:real^3->bool`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S3GP_PIECE_TRI_MISS THEN
      MAP_EVERY EXISTS_TAC [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
        `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
        `q:real^3->bool`; `lmq:(real^3->bool)->bool`] THEN
      ASM_REWRITE_TAC[]];
    MESON_TAC[]]);;

(* The sheet d1 is a loop theorem disk.                                       *)

let MOI_S3GP_LTD_D1 = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) x d j a1 j1 j2 d1.
     moi_s33_ltd t l h x d /\ d INTER frontier (UNIONS x) = j /\
     pl_annulus_with_ends a1 j1 j2 /\ a1 SUBSET frontier (UNIONS x) /\ j SUBSET a1 /\
     pl_cell_with_boundary 2 d1 j1 /\ d1 SUBSET moi_s33_ww t l h /\
     d1 INTER frontier (UNIONS x) = j1
     ==> moi_s33_ltd t l h x d1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_s33_ltd] o check (fun th ->
    concl th = `moi_s33_ltd t l h x (d:real^3->bool)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `IMAGE (f:real^3->real^3) (relative_frontier k) = j` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `pl_cell_with_boundary 2 d1 (j1:real^3->bool)` THEN
  REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:real^3->bool` (X_CHOOSE_THEN `f1:real^3->real^3`
    (X_CHOOSE_THEN `g1:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  REWRITE_TAC[moi_s33_ltd] THEN
  MAP_EVERY EXISTS_TAC [`k1:real^3->bool`; `f1:real^3->real^3`; `g1:real^3->real^3`] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    concl th = `j1 = IMAGE (f1:real^3->real^3) (relative_frontier k1)`)) THEN
  ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `a0:real^3` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`a1:real^3->bool`; `j1:real^3->bool`; `j2:real^3->bool`; `j:real^3->bool`]
                MOI_S3CP_ANNULUS_DEFORM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^3->real^3` STRIP_ASSUME_TAC o CONJUNCT1) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th) &&
    can (find_term (fun u -> u = `j:real^3->bool`)) (concl th))) THEN
  REWRITE_TAC[] THEN EXISTS_TAC `a0:real^3` THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_TRANS THEN EXISTS_TAC `r:real^3->real^3` THEN CONJ_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_WITH_SUBSET_RIGHT THEN EXISTS_TAC `a1:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`\y:real^3. y`; `\y:real^3. (a0:real^3)`; `r:real^3->real^3`; `j:real^3->bool`;
                   `j1:real^3->bool`; `frontier(UNIONS x):real^3->bool`]
                  HOMOTOPIC_COMPOSE_CONTINUOUS_RIGHT) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[o_DEF; ETA_AX]]);;

(* ------------------------------------------------------------------------- *)
(* Part 10: the side conditions for the sheet d1 (pieces of the            *)
(* derived frontier off Bd X lie in d1 or miss it; at a crossing point one *)
(* half lies in d1 and the other misses it), and the assembly S39_GP.       *)
(* ------------------------------------------------------------------------- *)

let MOI_S3GP_SIDE_CONN = prove
 (`!(Fr:real^3->bool) X G d1 d2 j1 j2 s0.
     closed X /\ (G = interior X \/ G = (:real^3) DIFF X) /\
     (Fr DIFF frontier X) INTER G = (d1 UNION d2) DIFF (j1 UNION j2) /\
     closed d1 /\ closed d2 /\ d1 INTER d2 = {} /\ d1 INTER j2 = {} /\
     j1 SUBSET frontier X /\
     connected s0 /\ s0 SUBSET Fr DIFF frontier X
     ==> s0 SUBSET d1 \/ DISJOINT s0 d1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `frontier X = X DIFF interior (X:real^3->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[frontier; CLOSURE_CLOSED]; ALL_TAC] THEN
  MP_TAC(ISPEC `X:real^3->bool` INTERIOR_SUBSET) THEN DISCH_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o check (fun th ->
    is_disj (concl th) && can (find_term (fun u -> u = `G:real^3->bool`)) (concl th))) THENL
   [MP_TAC(ISPECL [`s0:real^3->bool`; `interior X:real^3->bool`; `(:real^3) DIFF X`]
                  MOI_S3GP_CONN_SPLIT);
    MP_TAC(ISPECL [`s0:real^3->bool`; `(:real^3) DIFF X`; `interior X:real^3->bool`]
                  MOI_S3GP_CONN_SPLIT)] THEN
  (ANTS_TAC THENL
    [ASM_REWRITE_TAC[OPEN_INTERIOR; GSYM closed] THEN ASM SET_TAC[]; ALL_TAC] THEN
   STRIP_TAC THENL
    [MP_TAC(ISPECL [`s0:real^3->bool`; `(:real^3) DIFF d2`; `(:real^3) DIFF d1`]
                   MOI_S3GP_CONN_SPLIT2) THEN
     ASM_REWRITE_TAC[GSYM closed] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
     STRIP_TAC THENL [DISJ1_TAC THEN ASM SET_TAC[]; DISJ2_TAC THEN ASM SET_TAC[]];
     DISJ2_TAC THEN ASM SET_TAC[]]));;

let MOI_S3GP_SIDE_LOC = prove
 (`!(DF:real^3->bool) Fr X G d1 d2 j1 j2 y p1 p2 dd.
     closed X /\ (G = interior X \/ G = (:real^3) DIFF X) /\
     (Fr DIFF frontier X) INTER G = (d1 UNION d2) DIFF (j1 UNION j2) /\ DF SUBSET Fr /\
     closed d2 /\ ~(y IN d2) /\ j1 SUBSET frontier X /\ j2 SUBSET frontier X /\
     &0 < dd /\ ~(p1 = y) /\ ~(p2 = y) /\
     DF INTER ball(y,dd) = (segment[y,p1] UNION segment[y,p2]) INTER ball(y,dd) /\
     (segment[y,p1] DELETE y) INTER ball(y,dd) SUBSET interior X /\
     DISJOINT ((segment[y,p2] DELETE y) INTER ball(y,dd)) X
     ==> ?q1 q2 d'. &0 < d' /\ ~(q1 = y) /\ ~(q2 = y) /\
                    DF INTER ball(y,d') =
                    (segment[y,q1] UNION segment[y,q2]) INTER ball(y,d') /\
                    (segment[y,q1] DELETE y) INTER ball(y,d') SUBSET d1 /\
                    DISJOINT ((segment[y,q2] DELETE y) INTER ball(y,d')) d1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `frontier X = X DIFF interior (X:real^3->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[frontier; CLOSURE_CLOSED]; ALL_TAC] THEN
  MP_TAC(ISPECL [`d2:real^3->bool`; `y:real^3`] SEPARATE_POINT_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d3:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `ball(y:real^3,min dd d3) SUBSET ball(y,dd) /\
                DISJOINT (ball(y:real^3,min dd d3)) d2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [REWRITE_TAC[SUBSET; IN_BALL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_BALL; NOT_IN_EMPTY] THEN
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o check (fun th ->
      is_forall (concl th) && can (find_term (fun u -> u = `d3:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `DF INTER ball(y:real^3,min dd d3) =
                (segment[y,p1] UNION segment[y,p2]) INTER ball(y,min dd d3)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `DF INTER ball(y:real^3,dd) =
                 (segment[y,p1] UNION segment[y,p2]) INTER ball(y,dd)` THEN
    UNDISCH_TAC `ball(y:real^3,min dd d3) SUBSET ball(y,dd)` THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN (LABEL_TAC "gcase") o check (fun th ->
    is_disj (concl th) && can (find_term (fun u -> u = `G:real^3->bool`)) (concl th))) THENL
   [MAP_EVERY EXISTS_TAC [`p1:real^3`; `p2:real^3`; `min dd d3`];
    MAP_EVERY EXISTS_TAC [`p2:real^3`; `p1:real^3`; `min dd d3`]] THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  REMOVE_THEN "gcase" MP_TAC THEN
  MP_TAC(ISPEC `X:real^3->bool` INTERIOR_SUBSET) THEN
  MAP_EVERY UNDISCH_TAC
   [`(Fr DIFF frontier X) INTER G = (d1 UNION d2) DIFF (j1 UNION j2:real^3->bool)`;
    `DF SUBSET (Fr:real^3->bool)`;
    `DISJOINT (ball(y:real^3,min dd d3)) d2`;
    `ball(y:real^3,min dd d3) SUBSET ball(y,dd)`;
    `(segment[y:real^3,p1] DELETE y) INTER ball(y,dd) SUBSET interior X`;
    `DISJOINT ((segment[y:real^3,p2] DELETE y) INTER ball(y,dd)) X`;
    `DF INTER ball(y:real^3,min dd d3) =
     (segment[y,p1] UNION segment[y,p2]) INTER ball(y,min dd d3)`;
    `frontier X = X DIFF interior (X:real^3->bool)`;
    `(j1:real^3->bool) SUBSET frontier X`; `(j2:real^3->bool) SUBSET frontier X`] THEN
  SET_TAC[]);;

(* The unconditional part B of the splitting operation (fnd_split with its *)
(* three antecedents: the polygon lemma, the trace annulus, surface glue).  *)

let MOI_S3GP_PART_B =
  MP MOI_FSP_PART_B
     (CONJ (INST_TYPE [`:3`,`:N`] DERIVED_NBHD_POLYGON_2)
           (CONJ (MP SPLIT_TRACE_ANNULUS (INST_TYPE [`:3`,`:N`] DERIVED_NBHD_POLYGON_2))
                 (INST_TYPE [`:3`,`:N`] MOI_S6G_SURF_GLUE_BODY)));;

(* The assembly.                                                             *)

let MOI_S3GP_MAIN = prove
 (MOI_S39_GP_BODY,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* the disk d and its rim j *)
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_s33_ltd] o check (fun th ->
    concl th = `moi_s33_ltd t l h x (d:real^3->bool)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:real^3->bool` (X_CHOOSE_THEN `f0:real^3->real^3`
    (X_CHOOSE_THEN `g0:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `j = IMAGE (f0:real^3->real^3) (relative_frontier k0)` THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 d (j:real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[pl_cell_with_boundary] THEN
    MAP_EVERY EXISTS_TAC [`k0:real^3->bool`; `f0:real^3->real^3`; `g0:real^3->real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (d:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSP_CELL_BASIC]; ALL_TAC] THEN
  (* X and the surface m triangulating Bd X *)
  SUBGOAL_THEN `FINITE (x:(real^3->bool)->bool) /\ combinatorial_manifold_with_boundary 3 x`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s33_inv t l h e (x:(real^3->bool)->bool)` THEN
    SIMP_TAC[moi_s33_inv; moi_s33_x2];
    ALL_TAC] THEN
  SUBGOAL_THEN `closure (interior (UNIONS x)) = UNIONS (x:(real^3->bool)->bool) /\
                closed (UNIONS x)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `closure (interior (UNIONS x)) = UNIONS (x:(real^3->bool)->bool)`
    (fun th -> REWRITE_TAC[th] THEN MESON_TAC[th; CLOSED_CLOSURE]) THEN
    MATCH_MP_TAC MOI_FSP_REG_CLOSED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `x:(real^3->bool)->bool` BOUNDARY_COMPLEX_SURFACE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPEC `x:(real^3->bool)->bool` COMPLEX_BOUNDARY_FRONTIER_3) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `m = boundary_complex (x:(real^3->bool)->bool)` THEN
  SUBGOAL_THEN `FINITE (m:(real^3->bool)->bool) /\ UNIONS m = frontier (UNIONS x)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `x:(real^3->bool)->bool` THEN
      ASM_MESON_TAC[simplicial_subcomplex];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    can (find_term (fun u -> u = `complex_boundary (x:(real^3->bool)->bool)`)) (concl th)))) THEN
  (* the polyhedral piece q of PCS near d *)
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`; `d:real^3->bool`]
                MOI_S3GP_PIECE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^3->bool` (X_CHOOSE_THEN `v:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  (* the box *)
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `d:real^3->bool`; `j:real^3->bool`;
                 `v:real^3->bool`; `q:real^3->bool`] MOI_S3GP_SETUP4) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^3` (X_CHOOSE_THEN `b:real^3` (X_CHOOSE_THEN
    `t1:(real^3->bool)->bool` (X_CHOOSE_THEN `ld:(real^3->bool)->bool` (X_CHOOSE_THEN
    `lm:(real^3->bool)->bool` (X_CHOOSE_THEN `lq:(real^3->bool)->bool`
    STRIP_ASSUME_TAC)))))) THEN
  (* the sheets *)
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `d:real^3->bool`; `j:real^3->bool`;
                 `v:real^3->bool`; `a:real^3`; `b:real^3`; `t1:(real^3->bool)->bool`;
                 `ld:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`] MOI_S3GP_PART_B) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `j1:real^3->bool` (X_CHOOSE_THEN `j2:real^3->bool`
    (X_CHOOSE_THEN `d1:real^3->bool` (X_CHOOSE_THEN `d2:real^3->bool`
    (X_CHOOSE_THEN `m':(real^3->bool)->bool` (STRIP_ASSUME_TAC o
      REWRITE_RULE[ASSUME `UNIONS m = frontier (UNIONS (x:(real^3->bool)->bool))`])))))) THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `d:real^3->bool`; `j:real^3->bool`;
                 `v:real^3->bool`; `a:real^3`; `b:real^3`; `t1:(real^3->bool)->bool`;
                 `ld:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`] MOI_FSP_N_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    REWRITE_RULE[moi_fsp_box; ASSUME `UNIONS m = frontier (UNIONS (x:(real^3->bool)->bool))`] o
    check (fun th ->
    can (term_match [] `moi_fsp_box m d v a b t1 ld (lm:(real^3->bool)->bool)`) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    REWRITE_RULE[moi_fsp_ends; ASSUME `UNIONS m = frontier (UNIONS (x:(real^3->bool)->bool))`] o
    check (fun th ->
    can (term_match [] `moi_fsp_ends m j t1 ld j1 j2 d1 (d2:real^3->bool)`) (concl th))) THEN
  (* d1 is a loop theorem disk *)
  SUBGOAL_THEN `moi_s33_ltd t l h x (d1:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3GP_LTD_D1 THEN
    MAP_EVERY EXISTS_TAC [`d:real^3->bool`; `j:real^3->bool`;
                          `derived_nbhd t1 ld INTER frontier (UNIONS (x:(real^3->bool)->bool))`;
                          `j1:real^3->bool`; `j2:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  (* the triangulated piece and its subcomplexes *)
  SUBGOAL_THEN `simplicial_complex (lq:(real^3->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3F2_SUBCOMPLEX_SC THEN EXISTS_TAC `t1:(real^3->bool)->bool` THEN
    ASM_MESON_TAC[simplicial_subcomplex];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t1:(real^3->bool)->bool`; `ld:(real^3->bool)->bool`;
                 `lq:(real^3->bool)->bool`] MOI_FN2_DERIVED_TRACE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`t1:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                 `lq:(real^3->bool)->bool`] MOI_FN2_DERIVED_TRACE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `simplicial_subcomplex (ld INTER lq) (lq:(real^3->bool)->bool) /\
                simplicial_subcomplex (lm INTER lq) (lq:(real^3->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_S3GP_SUBCX_INTER THEN
    EXISTS_TAC `t1:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS (lm INTER lq) = frontier (UNIONS x) INTER (q:real^3->bool) /\
                UNIONS (ld INTER lq) SUBSET (v:real^3->bool) /\
                derived_frontier lq (ld INTER lq) SUBSET v /\
                derived_frontier lq (ld INTER lq) SUBSET derived_frontier t1 ld`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`UNIONS (lm INTER lq) = UNIONS lm INTER UNIONS (lq:(real^3->bool)->bool)`;
      `UNIONS (ld INTER lq) = UNIONS ld INTER UNIONS (lq:(real^3->bool)->bool)`;
      `derived_frontier t1 ld INTER UNIONS lq = derived_frontier lq (ld INTER (lq:(real^3->bool)->bool))`;
      `UNIONS lm = frontier (UNIONS (x:(real^3->bool)->bool))`;
      `UNIONS lq = (q:real^3->bool)`; `UNIONS ld = (d:real^3->bool)`;
      `(d:real^3->bool) SUBSET v`;
      `derived_frontier t1 ld SUBSET derived_nbhd t1 (ld:(real^3->bool)->bool)`;
      `derived_nbhd t1 ld SUBSET v INTER interval(a:real^3,b)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s IN lq ==> aff_dim (s:real^3->bool) <= &2` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3GP_PIECE_DIM THEN
    MAP_EVERY EXISTS_TAC [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
      `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
      `q:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f:real^3->bool. f IN barycentric_subdivision lq /\ aff_dim f = &1 /\
                     moi_frn_vp lq (ld INTER lq) f
                     ==> ?z. z IN relative_interior f /\ moi_s28_locally_r2 (UNIONS lq) z`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3GP_PIECE_FR2 THEN
    MAP_EVERY EXISTS_TAC [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
      `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
      `q:real^3->bool`; `v:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`lq:(real^3->bool)->bool`; `ld INTER (lq:(real^3->bool)->bool)`]
                MOI_S3F2_DFR_CIRCLES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[DIMINDEX_3; ARITH]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `q:real^3->bool`; `lq:(real^3->bool)->bool`;
                 `lm INTER (lq:(real^3->bool)->bool)`; `ld INTER (lq:(real^3->bool)->bool)`]
                MOI_S3GP_MEET_FINITE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  (* the side of the sheets *)
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `d:real^3->bool`; `j:real^3->bool`;
                 `v:real^3->bool`; `a:real^3`; `b:real^3`; `t1:(real^3->bool)->bool`;
                 `ld:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                 `j1:real^3->bool`; `j2:real^3->bool`; `d1:real^3->bool`; `d2:real^3->bool`;
                 `x:(real^3->bool)->bool`] MOI_S3GP_SHEET_SIDE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `G:real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `closed (d1:real^3->bool) /\ closed (d2:real^3->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSP_CELL_BASIC; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  (* d1 INTER PCS is d1 INTER DF *)
  ABBREV_TAC `DF = derived_frontier lq (ld INTER (lq:(real^3->bool)->bool))` THEN
  SUBGOAL_THEN `d1 INTER moi_s39_pcs l e = d1 INTER (DF:real^3->bool)` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`derived_frontier t1 ld INTER UNIONS lq = (DF:real^3->bool)`;
      `(d1:real^3->bool) SUBSET derived_frontier t1 ld`;
      `(d1:real^3->bool) SUBSET v`; `moi_s39_pcs l e INTER v SUBSET (q:real^3->bool)`;
      `q SUBSET moi_s39_pcs l e INTER moi_s33_ww t l (h:real^3->real^3)`;
      `UNIONS lq = (q:real^3->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `d1:real^3->bool` THEN
  EXISTS_TAC `components (d1 INTER moi_s39_pcs l (e:(real^3->bool)->real^3->bool))` THEN
  ASM_REWRITE_TAC[moi_s39_family; PAIRWISE_DISJOINT_COMPONENTS; GSYM UNIONS_COMPONENTS] THEN
  MATCH_MP_TAC MOI_S3GP_FAMILY THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [(* pieces off Bd X *)
    X_GEN_TAC `s0:real^3->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_S3GP_SIDE_CONN THEN
    MAP_EVERY EXISTS_TAC [`derived_frontier t1 (ld:(real^3->bool)->bool)`; `UNIONS (x:(real^3->bool)->bool)`;
                          `G:real^3->bool`; `d2:real^3->bool`; `j1:real^3->bool`;
                          `j2:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    (* crossing points *)
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                   `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                   `x:(real^3->bool)->bool`; `q:real^3->bool`; `v:real^3->bool`;
                   `lq:(real^3->bool)->bool`; `lm INTER (lq:(real^3->bool)->bool)`;
                   `ld INTER (lq:(real^3->bool)->bool)`; `y:real^3`] MOI_S3GP_TRACE_LOC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]] THEN
    DISCH_THEN(X_CHOOSE_THEN `p1:real^3` (X_CHOOSE_THEN `p2:real^3` (X_CHOOSE_THEN `dd:real`
      STRIP_ASSUME_TAC))) THEN
    MATCH_MP_TAC MOI_S3GP_SIDE_LOC THEN
    MAP_EVERY EXISTS_TAC [`derived_frontier t1 (ld:(real^3->bool)->bool)`; `UNIONS (x:(real^3->bool)->bool)`;
                          `G:real^3->bool`; `d2:real^3->bool`; `j1:real^3->bool`;
                          `j2:real^3->bool`; `p1:real^3`; `p2:real^3`; `dd:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

let S39_GP = prove
 (MOI_S39_GP_BODY,
  ACCEPT_TAC MOI_S3GP_MAIN);;


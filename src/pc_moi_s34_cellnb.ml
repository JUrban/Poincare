(* ========================================================================= *)
(* pc_moi_s34_cellnb: Moise Sec 34, Lemma 3 (GTM 47, p.240), the assembly   *)
(* of the two halves of the initial face balls.  Main theorems              *)
(*   CELLNB_FROM_GP : |- MOI_S4Z_GP_BALL ==> MOI_FND_SIMPLEX_SMALL_CELL     *)
(*                       ==> MOI_S34_CELLNB                                 *)
(*   CELLNB_FND     : |- MOI_FND_SIMPLEX_SMALL_CELL ==> MOI_S34_CELLNB      *)
(* Route: the frame gives local finiteness of the vertex balls near the     *)
(* compact set h(s) (index family of the carriers plus h(s) itself), so an  *)
(* open u around h(s) meets only finitely many vertex balls;               *)
(* pc_moi_s34_cellnba (INIT_BALL, on MOI_FND_SIMPLEX_SMALL_CELL and         *)
(* Moise 30.5) gives a small PL ball c0 around h(s) inside w0 INTER u; the  *)
(* general position half pc_moi_s34_cellnbb (GP_BALL) moves its frontier    *)
(* into general position with the tube and the rims.                        *)
(* MOI_FND_SIMPLEX_SMALL_CELL (pc_moi_fnd_stmt2.ml) is proved in            *)
(* pc_moi_fnd_rnsc (SIMPLEX_SMALL_CELL), and pc_moi_s34_status discharges   *)
(* it.                                                                      *)
(* ========================================================================= *)

needs "src/pc_moi_s34_cellnba.ml";;
needs "src/pc_moi_s34_cellnbb.ml";;

prioritize_real();;
type_invention_error := true;;

let MOI_S34CB_CELLNB_FND = mk_imp(MOI_FND_SIMPLEX_SMALL_CELL,MOI_S34_CELLNB);;

(* ------------------------------------------------------------------------- *)
(* The assembly.                                                             *)
(* ------------------------------------------------------------------------- *)

let CELLNB_FROM_GP = prove
 (mk_imp(MOI_S4Z_GP_BALL,mk_imp(MOI_FND_SIMPLEX_SMALL_CELL,MOI_S34_CELLNB)),
  DISCH_THEN(LABEL_TAC "gp") THEN DISCH_THEN(LABEL_TAC "fnd") THEN
  DISCH_THEN(LABEL_TAC "m305") THEN
  MAP_EVERY X_GEN_TAC
   [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
    `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
    `s:real^N->bool`; `w0:real^3->bool`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[moi_s34_frame] o
    check (fun th -> concl th = `moi_s34_frame (tt:(real^N->bool)->bool) kk
                                  (h:real^N->real^3) ep f1 car`)) THEN
  DISCH_THEN(fun th ->
    let cs = CONJUNCTS th in
    LABEL_TAC "carq" (el 4 cs) THEN LABEL_TAC "vb" (el 6 cs) THEN
    LABEL_TAC "lf" (el 11 cs)) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `s:real^N->bool`] MOI_S4K_FT_FACTS) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `~(s:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `aff_dim(s:real^N->bool) = &2` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `compact(IMAGE (h:real^N->real^3) s)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [UNDISCH_TAC `moi_s34_emb (h:real^N->real^3) (UNIONS tt)` THEN
      REWRITE_TAC[moi_s34_emb] THEN STRIP_TAC THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `UNIONS tt:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(s:real^N->bool) IN tt` THEN SET_TAC[];
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`]
        MOI_S4K_TUBE_FACTS) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      REWRITE_TAC[lf_simplicial_complex] THEN
      DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1 o CONJUNCT1) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[SIMPLEX_IMP_COMPACT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (h:real^N->real^3) s SUBSET car s` ASSUME_TAC THENL
   [USE_THEN "carq" (MP_TAC o SPEC `s:real^N->bool`) THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`{q:real^N->bool | q IN kk /\ ~(q = {})}`;
                 `\q:real^N->bool. if q = {} then IMAGE (h:real^N->real^3) s else car q`;
                 `{}:real^N->bool`] MOI_S4Q_LF_COVER) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "lf" (MP_TAC o SPEC `y:real^3`) THEN ANTS_TAC THENL
     [REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EXISTS_TAC `(car:(real^N->bool)->real^3->bool) s` THEN
      CONJ_TAC THENL [EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]; ASM SET_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^3->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb (concl th) &&
      fst(dest_const(fst(strip_comb(concl th)))) = "FINITE")) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `q:real^N->bool` THEN
    ASM_CASES_TAC `q:real^N->bool = {}` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CONJ_ASSOC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `FINITE {q:real^N->bool | q IN kk /\ ~(q = {}) /\
                             ~((car:(real^N->bool)->real^3->bool) q INTER u = {})}`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb (concl th) &&
      fst(dest_const(fst(strip_comb(concl th)))) = "FINITE")) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `q:real^N->bool` THEN
    ASM_CASES_TAC `q:real^N->bool = {}` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CONJ_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE {v:real^N | {v} IN kk /\
                       ~(IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) INTER
                         ((w0:real^3->bool) INTER u) = {})}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{v:real^N | {v} IN {q:real^N->bool | q IN kk /\ ~(q = {}) /\
                       ~((car:(real^N->bool)->real^3->bool) q INTER u = {})}}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE_INJ THEN CONJ_TAC THENL
       [REWRITE_TAC[] THEN SET_TAC[]; FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; NOT_INSERT_EMPTY] THEN
    X_GEN_TAC `v:real^N` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "vb" (fun th -> MP_TAC(MATCH_MP th (ASSUME `{v:real^N} IN kk`))) THEN
    STRIP_TAC THEN
    UNDISCH_TAC `~(IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) INTER
                   ((w0:real^3->bool) INTER u) = {})` THEN
    UNDISCH_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) SUBSET car {v:real^N}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "fnd" (fun fnd -> USE_THEN "m305" (fun m -> MP_TAC(SPECL
    [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
     `s:real^N->bool`; `(w0:real^3->bool) INTER u`]
    (MP (MP INIT_BALL fnd) m)))) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[OPEN_INTER; SUBSET_INTER];
    DISCH_THEN(X_CHOOSE_THEN `c0:real^3->bool` STRIP_ASSUME_TAC)] THEN
  USE_THEN "gp" (MP_TAC o SPECL
    [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
     `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
     `c0:real^3->bool`; `IMAGE (h:real^N->real^3) s`; `(w0:real^3->bool) INTER u`]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[OPEN_INTER]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `c:real^3->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let CELLNB_FND = prove
 (MOI_S34CB_CELLNB_FND,
  MATCH_ACCEPT_TAC(MP CELLNB_FROM_GP GP_BALL));;


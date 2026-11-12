needs "src/pc_moi_s33_stmt.ml";;
needs "src/pc_moi_fnd_surfa.ml";;
needs "src/pc_moi_fnd_euler.ml";;
needs "src/pc_moi_fnd_gf2.ml";;
needs "src/pc_moi_fnd_rnb2.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* pc_moi_s33_z2a: the GF(2) H^1 counts of surfaces (Moise GTM 47, Sec 33    *)
(* via Z/2 loop characters).  Main theorems                                  *)
(*   Z2_COUNT    : |- MOI_S33_Z2_COUNT    (closed: 2^(2 - chi) classes)     *)
(*   Z2_COUNT_BD : |- MOI_S33_Z2_COUNT_BD (nonempty boundary: 2^(1 - chi))  *)
(* (pc_moi_s33_stmt.ml).  Route:                                           *)
(* delta^1 and delta^0 as parity maps (moi_fz2_pm of pc_moi_fnd_gf2); the   *)
(* cocycles are the kernel of delta^1 on edge sets, the coboundaries the    *)
(* image of delta^0 on vertex sets (contained in the cocycles); |Z| * |im   *)
(* delta^1| = 2^E and |B| * 2 = 2^V (kernel {{}, V} by the connected        *)
(* 1-skeleton, MOI_FRB_CONN_OF_CONNECTED of pc_moi_fnd_rnb2); the classes  *)
(* are the cosets of B, so |H| * |B| = |Z|; the image of delta^1 is the     *)
(* even triangle sets (closed: each edge in two triangles) or all triangle  *)
(* sets (a boundary edge), by dual connectivity MOI_FRB_CMB2_DCONN; then the *)
(* Euler count V - E + F.                                                    *)
(* ========================================================================= *)


(* ------------------------------------------------------------------------- *)
(* Part 1. Euler characteristic of a complex of dimension at most 2.         *)
(* ------------------------------------------------------------------------- *)

(* The Euler characteristic of a complex of dimension at most 2 (the proof   *)
(* of MOI_FSA_CM_EULER with the dimension bound as hypothesis).              *)

let MOI_S3ZA_EULER_2D = prove
 (`!c:(real^N->bool)->bool.
        simplicial_complex c /\ (!s. s IN c ==> aff_dim s <= &2)
        ==> complex_euler c =
            &(CARD {v | {v} IN c}) - &(CARD {e | e IN c /\ aff_dim e = &1}) +
            &(CARD {t | t IN c /\ aff_dim t = &2})`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [simplicial_complex]) THEN
  ASM_SIMP_TAC[MOI_FEU_COMPLEX_EULER_SUM] THEN
  SUBGOAL_THEN
   `{s:real^N->bool | s IN c /\ ~(s = {})} =
    ({s | s IN c /\ aff_dim s = &0} UNION {e | e IN c /\ aff_dim e = &1}) UNION
    {t | t IN c /\ aff_dim t = &2}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `s:real^N->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNION] THEN
    ASM_CASES_TAC `(s:real^N->bool) IN c` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(s:real^N->bool) IN c`) o
      check (fun th -> can (term_match []
        `!s:real^N->bool. s IN c ==> aff_dim s <= &2`) (concl th))) THEN
    ASM_CASES_TAC `s:real^N->bool = {}` THEN ASM_REWRITE_TAC[AFF_DIM_EMPTY] THENL
     [CONV_TAC INT_REDUCE_CONV;
      MP_TAC(ISPEC `s:real^N->bool` AFF_DIM_POS_LE) THEN ASM_REWRITE_TAC[] THEN
      INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `DISJOINT {s:real^N->bool | s IN c /\ aff_dim s = &0}
             {e | e IN c /\ aff_dim e = &1} /\
    DISJOINT ({s:real^N->bool | s IN c /\ aff_dim s = &0} UNION
              {e | e IN c /\ aff_dim e = &1})
             {t | t IN c /\ aff_dim t = &2}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_UNION; IN_ELIM_THM;
                NOT_IN_EMPTY] THEN
    CONJ_TAC THEN X_GEN_TAC `s:real^N->bool` THEN
    ASM_CASES_TAC `aff_dim(s:real^N->bool) = &0` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `aff_dim(s:real^N->bool) = &1` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_UNION; FINITE_RESTRICT; FINITE_UNION] THEN
  SUBGOAL_THEN
   `sum {s:real^N->bool | s IN c /\ aff_dim s = &0}
        (\s. (-- &1) pow num_of_int(aff_dim s)) =
    sum {s:real^N->bool | s IN c /\ aff_dim s = &0} (\s. &1) /\
    sum {e:real^N->bool | e IN c /\ aff_dim e = &1}
        (\s. (-- &1) pow num_of_int(aff_dim s)) =
    sum {e:real^N->bool | e IN c /\ aff_dim e = &1} (\s. -- &1) /\
    sum {t:real^N->bool | t IN c /\ aff_dim t = &2}
        (\s. (-- &1) pow num_of_int(aff_dim s)) =
    sum {t:real^N->bool | t IN c /\ aff_dim t = &2} (\s. &1)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC SUM_EQ THEN
    SIMP_TAC[IN_ELIM_THM; NUM_OF_INT_OF_NUM] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_CONST; FINITE_RESTRICT] THEN
  SUBGOAL_THEN
   `{s:real^N->bool | s IN c /\ aff_dim s = &0} =
    IMAGE (\u:real^N. {u}) {u | {u} IN c}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `s:real^N->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; AFF_DIM_EQ_0] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {u:real^N | {u} IN c}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\u:real^N. {u}`; `{u:real^N | {u} IN c}`] CARD_IMAGE_INJ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NUM_OF_INT_OF_NUM] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RNEG; GSYM real_sub]);;


(* ------------------------------------------------------------------------- *)
(* Part 2. The coboundary maps; cocycles and coboundaries.                   *)
(* ------------------------------------------------------------------------- *)

(* The GF(2) coboundary maps as parity maps (pc_moi_fnd_gf2): delta^1 sends  *)
(* an edge set to the triangles containing an odd number of its edges,      *)
(* delta^0 a vertex set to the edges with an odd number of its vertices.    *)

let moi_s3za_d1 = new_definition
 `moi_s3za_d1 (c:(real^N->bool)->bool) z =
    moi_fz2_pm (\e t. e IN c /\ aff_dim e = &1 /\ e SUBSET t)
               {t | t IN c /\ aff_dim t = &2} z`;;

let moi_s3za_d0 = new_definition
 `moi_s3za_d0 (c:(real^N->bool)->bool) w =
    moi_fz2_pm (\v e. {v} IN c /\ v IN e) {e | e IN c /\ aff_dim e = &1} w`;;

let MOI_S3ZA_VERTS_FINITE = prove
 (`!c:(real^N->bool)->bool. FINITE c ==> FINITE {v | {v} IN c}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
  SET_TAC[]);;

let MOI_S3ZA_D1_SD = prove
 (`!c:(real^N->bool)->bool.
     FINITE c
     ==> !z1 z2. moi_s3za_d1 c (moi_fz2_sd z1 z2) =
                 moi_fz2_sd (moi_s3za_d1 c z1) (moi_s3za_d1 c z2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s3za_d1] THEN
  MATCH_MP_TAC MOI_FZ2_PM_SD THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let MOI_S3ZA_D0_SD = prove
 (`!c:(real^N->bool)->bool.
     FINITE c
     ==> !w1 w2. moi_s3za_d0 c (moi_fz2_sd w1 w2) =
                 moi_fz2_sd (moi_s3za_d0 c w1) (moi_s3za_d0 c w2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s3za_d0] THEN
  MATCH_MP_TAC MOI_FZ2_PM_SD THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{v:real^N | {v} IN c}` THEN
  ASM_SIMP_TAC[MOI_S3ZA_VERTS_FINITE] THEN SET_TAC[]);;

(* Cocycles are the edge sets in the kernel of delta^1.                     *)

let MOI_S3ZA_COCYCLE = prove
 (`!c (z:(real^N->bool)->bool).
     z2_cocycle c z <=>
     z SUBSET {e | e IN c /\ aff_dim e = &1} /\ moi_s3za_d1 c z = {}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[z2_cocycle] THEN
  SUBGOAL_THEN `(!e:real^N->bool. e IN z ==> e IN c /\ aff_dim e = &1) <=>
                z SUBSET {e | e IN c /\ aff_dim e = &1}` SUBST1_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)`) THEN DISCH_TAC THEN
  REWRITE_TAC[moi_s3za_d1; moi_fz2_pm] THEN
  GEN_REWRITE_TAC RAND_CONV [EXTENSION] THEN
  REWRITE_TAC[NOT_IN_EMPTY; IN_ELIM_THM] THEN
  SUBGOAL_THEN
   `!t:real^N->bool.
      {a | a IN z /\ a IN c /\ aff_dim a = &1 /\ a SUBSET t} = {e | e IN z /\ e SUBSET t}`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM NOT_EVEN] THEN MESON_TAC[]);;

(* Coboundaries are the images under delta^0 of vertex sets.                *)

let MOI_S3ZA_COBOUNDARY = prove
 (`!c (z:(real^N->bool)->bool).
     z SUBSET {e | e IN c /\ aff_dim e = &1}
     ==> (z2_coboundary c z <=>
          ?w. w SUBSET {v | {v} IN c} /\ z = moi_s3za_d0 c w)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[z2_coboundary; moi_s3za_d0; moi_fz2_pm] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_TAC `w:real^N->bool`) THEN
    EXISTS_TAC `{v:real^N | v IN w /\ {v} IN c}` THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `e:real^N->bool` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    SUBGOAL_THEN `{a:real^N | (a IN w /\ {a} IN c) /\ {a} IN c /\ a IN e} =
                  {v | v IN w /\ v IN e /\ {v} IN c}` SUBST1_TAC THENL
     [SET_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `(e:real^N->bool) IN c /\ aff_dim e = &1` THEN ASM_REWRITE_TAC[] THENL
     [ASM_MESON_TAC[]; ASM SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `w:real^N->bool` THEN X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq (concl th) &&
      lhs (concl th) = `z:(real^N->bool)->bool`)) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* Part 3. Coboundaries are cocycles; the kernel of delta^0.                 *)
(* ------------------------------------------------------------------------- *)

(* A vertex of a triangle lies on exactly two edges of the complex inside it. *)

let MOI_S3ZA_TRI_VERTEX_EDGES = prove
 (`!c t (v:real^N).
     simplicial_complex c /\ t IN c /\ aff_dim t = &2 /\ {v} IN c /\ v IN t
     ==> CARD {e | e IN c /\ aff_dim e = &1 /\ e SUBSET t /\ v IN e} = 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`; `v:real^N`]
    MOI_SCF_TRIANGLE_AT_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!u:real^N. {u} IN c /\ u IN t ==> u = v \/ u = a \/ u = b`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `{u:real^N} face_of t` MP_TAC THENL
     [SUBGOAL_THEN `{u:real^N} = {u} INTER t` SUBST1_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_MESON_TAC[simplicial_complex];
      ALL_TAC] THEN
    ASM_SIMP_TAC[FACE_OF_SING; EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p:real^N. (p = a \/ p = b) ==> segment[v,p] IN c /\ aff_dim(segment[v,p]) = &1 /\
                                    segment[v,p] SUBSET t /\ v IN segment[v,p]`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `segment[v:real^N,p] face_of t` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
      ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
      EXISTS_TAC `{v:real^N,p}` THEN REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[simplicial_complex];
      REWRITE_TAC[AFF_DIM_SEGMENT] THEN COND_CASES_TAC THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET];
      REWRITE_TAC[ENDS_IN_SEGMENT]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{e | e IN c /\ aff_dim e = &1 /\ e SUBSET t /\ v IN e} =
    {segment[v:real^N,a], segment[v,b]}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `e:real^N->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN EQ_TAC THENL
     [STRIP_TAC THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FSA_EDGE_VERTS) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `q:real^N` STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `(v:real^N) IN {u | {u} IN c /\ u IN e}` MP_TAC THENL
       [ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
      SUBGOAL_THEN `(p:real^N) IN t /\ q IN t` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(e:real^N->bool) SUBSET t` THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`p:real^N`; `q:real^N`] ENDS_IN_SEGMENT) THEN SET_TAC[];
        ALL_TAC] THEN
      STRIP_TAC THENL
       [MP_TAC(SPEC `q:real^N` (ASSUME
          `!u:real^N. {u} IN c /\ u IN t ==> u = v \/ u = a \/ u = b`)) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN ASM_MESON_TAC[];
        MP_TAC(SPEC `p:real^N` (ASSUME
          `!u:real^N. {u} IN c /\ u IN t ==> u = v \/ u = a \/ u = b`)) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
        ASM_MESON_TAC[SEGMENT_SYM]];
      STRIP_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!p:real^N. p = a \/ p = b ==> P p`) (concl th))) THEN
      REWRITE_TAC[]];
    ALL_TAC] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[SEGMENT_EQ] THEN
  COND_CASES_TAC THENL [ALL_TAC; CONV_TAC NUM_REDUCE_CONV] THEN
  UNDISCH_TAC `{v:real^N,a} = {v,b}` THEN
  REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN
  DISCH_THEN(MP_TAC o SPEC `a:real^N`) THEN ASM_MESON_TAC[]);;

(* delta^1 o delta^0 = 0: coboundaries are cocycles.                         *)

let MOI_S3ZA_D1_D0 = prove
 (`!c (w:real^N->bool).
     simplicial_complex c /\ w SUBSET {v | {v} IN c}
     ==> moi_s3za_d1 c (moi_s3za_d0 c w) = {}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [simplicial_complex]) THEN
  REWRITE_TAC[moi_s3za_d1; moi_s3za_d0; moi_fz2_pm; EXTENSION; NOT_IN_EMPTY;
              IN_ELIM_THM] THEN
  X_GEN_TAC `t:real^N->bool` THEN
  ASM_CASES_TAC `(t:real^N->bool) IN c /\ aff_dim t = &2` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[NOT_ODD] THEN
  SUBGOAL_THEN
   `EVEN (CARD {y | y IN {e | e IN c /\ aff_dim e = &1 /\ e SUBSET (t:real^N->bool)} /\
                    ODD (CARD {x | x IN w /\ {x} IN c /\ x IN y})})`
  MP_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[]] THEN
  MATCH_MP_TAC(REWRITE_RULE[] (ISPECL
   [`\x:real^N y:real^N->bool. {x} IN c /\ x IN y`] MOI_FZ2_DOUBLE_EVEN)) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{v:real^N | {v} IN c}` THEN
    ASM_SIMP_TAC[MOI_S3ZA_VERTS_FINITE];
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `{v:real^N} IN c` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_CASES_TAC `(v:real^N) IN t` THENL
     [SUBGOAL_THEN
       `{y | (y IN c /\ aff_dim y = &1 /\ y SUBSET t) /\ (v:real^N) IN y} =
        {e | e IN c /\ aff_dim e = &1 /\ e SUBSET t /\ v IN e}`
      SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[MOI_S3ZA_TRI_VERTEX_EDGES] THEN CONV_TAC NUM_REDUCE_CONV;
      SUBGOAL_THEN
       `{y | (y IN c /\ aff_dim y = &1 /\ y SUBSET t) /\ (v:real^N) IN y} = {}`
      SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[CARD_CLAUSES; EVEN]]]);;

(* The kernel of delta^0 on vertex sets: the empty set and all vertices     *)
(* (connected 1-skeleton, moi_frb_conn).                                     *)

let MOI_S3ZA_D0_KERNEL = prove
 (`!c (w:real^N->bool).
     simplicial_complex c /\ moi_frb_conn c /\ w SUBSET {v | {v} IN c}
     ==> (moi_s3za_d0 c w = {} <=> w = {} \/ w = {v | {v} IN c})`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC(TAUT `(~p /\ ~q ==> F) ==> p \/ q`) THEN STRIP_TAC THEN
    UNDISCH_TAC `moi_frb_conn (c:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_frb_conn] THEN DISCH_THEN(MP_TAC o SPEC `w:real^N->bool`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `~(x:real^N = y)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `aff_dim(segment[x:real^N,y]) = &1` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[AFF_DIM_SEGMENT]; ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `segment[x:real^N,y]`] MOI_FSA_EDGE_VERTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `q:real^N` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `{u:real^N | {u} IN c /\ u IN segment[x,y]} = {x,y}` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `{p:real^N,q} = {x,y}` (fun th -> REWRITE_TAC[th]) THEN
      UNDISCH_TAC `segment[x:real^N,y] = segment[p,q]` THEN
      REWRITE_TAC[SEGMENT_EQ] THEN MESON_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `moi_s3za_d0 c (w:real^N->bool) = {}` THEN
    REWRITE_TAC[moi_s3za_d0; moi_fz2_pm; EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `segment[x:real^N,y]`) THEN
    SUBGOAL_THEN `{a:real^N | a IN w /\ {a} IN c /\ a IN segment[x,y]} = {x}`
    SUBST1_TAC THENL
     [UNDISCH_TAC `{u:real^N | {u} IN c /\ u IN segment[x,y]} = {x,y}` THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
      ASM_MESON_TAC[];
      ASM_REWRITE_TAC[CARD_SING] THEN CONV_TAC NUM_REDUCE_CONV];
    STRIP_TAC THEN ASM_REWRITE_TAC[MOI_FZ2_PM_EMPTY; moi_s3za_d0] THEN
    REWRITE_TAC[moi_fz2_pm; EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM] THEN
    X_GEN_TAC `e:real^N->bool` THEN
    ASM_CASES_TAC `(e:real^N->bool) IN c /\ aff_dim e = &1` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FSA_EDGE_VERTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `q:real^N` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `{a:real^N | {a} IN c /\ {a} IN c /\ a IN e} = {p,q}` SUBST1_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
        rand (concl th) = `{p:real^N,q}`)) THEN SET_TAC[];
      ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
      CONV_TAC NUM_REDUCE_CONV]]);;


(* ------------------------------------------------------------------------- *)
(* Part 4. Counting cosets.                                                  *)
(* ------------------------------------------------------------------------- *)


let MOI_S3ZA_SD_CANCEL = prove
 (`!x y:A->bool. moi_fz2_sd x (moi_fz2_sd x y) = y`,
  REWRITE_TAC[EXTENSION; MOI_FZ2_IN_SD] THEN REPEAT GEN_TAC THEN CONV_TAC TAUT);;

let MOI_S3ZA_SD_TRIANGLE = prove
 (`!x y z:A->bool. moi_fz2_sd x y = moi_fz2_sd (moi_fz2_sd x z) (moi_fz2_sd y z)`,
  REWRITE_TAC[EXTENSION; MOI_FZ2_IN_SD] THEN REPEAT GEN_TAC THEN CONV_TAC TAUT);;

let MOI_S3ZA_SD_INJ = prove
 (`!x y z:A->bool. moi_fz2_sd x y = moi_fz2_sd x z <=> y = z`,
  MESON_TAC[MOI_S3ZA_SD_CANCEL]);;

(* Counting cosets: if the classes of a SYMDIFF-closed family Z are the     *)
(* cosets of a SYMDIFF-closed subfamily B containing the empty set, then    *)
(* the number of classes times |B| is |Z|.                                   *)

let MOI_S3ZA_CLASS_COUNT = prove
 (`!(Z:(A->bool)->bool) B cls.
     FINITE Z /\ B SUBSET Z /\ {} IN B /\
     (!x y. x IN Z /\ y IN Z ==> moi_fz2_sd x y IN Z) /\
     (!x y. x IN B /\ y IN B ==> moi_fz2_sd x y IN B) /\
     (!z. z IN Z ==> cls z = {z' | z' IN Z /\ moi_fz2_sd z z' IN B})
     ==> CARD (IMAGE cls Z) * CARD B = CARD Z`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "zsd")
    (CONJUNCTS_THEN2 (LABEL_TAC "bsd") (LABEL_TAC "def")))))) THEN
  SUBGOAL_THEN `FINITE (B:(A->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z x:A->bool. z IN Z ==> (x IN (cls:(A->bool)->(A->bool)->bool) z <=>
                              x IN Z /\ moi_fz2_sd z x IN B)`
  (LABEL_TAC "mem") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "def" (fun th ->
      REWRITE_TAC[MATCH_MP th (ASSUME `(z:A->bool) IN Z`)]) THEN
    REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:A->bool. z IN Z ==> (cls:(A->bool)->(A->bool)->bool) z = IMAGE (moi_fz2_sd z) B`
  (LABEL_TAC "img") THENL
   [X_GEN_TAC `z:A->bool` THEN DISCH_TAC THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:A->bool` THEN
    USE_THEN "mem" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(z:A->bool) IN Z`)]) THEN
    REWRITE_TAC[IN_IMAGE] THEN EQ_TAC THENL
     [STRIP_TAC THEN EXISTS_TAC `moi_fz2_sd (z:A->bool) x` THEN
      ASM_REWRITE_TAC[MOI_S3ZA_SD_CANCEL];
      DISCH_THEN(X_CHOOSE_THEN `b:A->bool` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[MOI_S3ZA_SD_CANCEL] THEN
      USE_THEN "zsd" MATCH_MP_TAC THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  REMOVE_THEN "def" (K ALL_TAC) THEN
  SUBGOAL_THEN
   `!z:A->bool. z IN Z ==> FINITE ((cls:(A->bool)->(A->bool)->bool) z) /\
                           CARD (cls z) = CARD (B:(A->bool)->bool)`
  (LABEL_TAC "card") THENL
   [X_GEN_TAC `z:A->bool` THEN DISCH_TAC THEN
    USE_THEN "img" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(z:A->bool) IN Z`)]) THEN
    ASM_SIMP_TAC[FINITE_IMAGE] THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN
    ASM_REWRITE_TAC[MOI_S3ZA_SD_INJ] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS (IMAGE (cls:(A->bool)->(A->bool)->bool) Z) = (Z:(A->bool)->bool)`
  (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:A->bool` THEN
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `z0:A->bool` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `(x:A->bool) IN (cls:(A->bool)->(A->bool)->bool) z0` THEN
      USE_THEN "mem" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(z0:A->bool) IN Z`)]) THEN
      SIMP_TAC[];
      DISCH_TAC THEN EXISTS_TAC `x:A->bool` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "mem" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(x:A->bool) IN Z`)]) THEN
      ASM_REWRITE_TAC[MOI_FZ2_SD]];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) CARD_UNIONS o rand o snd) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `z1:A->bool` THEN DISCH_TAC THEN X_GEN_TAC `z2:A->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `(~q ==> p) ==> ~p ==> q`) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    REWRITE_TAC[IN_INTER] THEN
    USE_THEN "mem" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(z1:A->bool) IN Z`)]) THEN
    USE_THEN "mem" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(z2:A->bool) IN Z`)]) THEN
    DISCH_THEN(X_CHOOSE_THEN `x:A->bool` STRIP_ASSUME_TAC) THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:A->bool` THEN
    USE_THEN "mem" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(z1:A->bool) IN Z`)]) THEN
    USE_THEN "mem" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(z2:A->bool) IN Z`)]) THEN
    SUBGOAL_THEN `moi_fz2_sd (z1:A->bool) z2 IN B` ASSUME_TAC THENL
     [SUBGOAL_THEN `moi_fz2_sd (z1:A->bool) z2 =
                    moi_fz2_sd (moi_fz2_sd z1 x) (moi_fz2_sd z2 x)` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM MOI_S3ZA_SD_TRIANGLE];
        USE_THEN "bsd" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    ASM_CASES_TAC `(y:A->bool) IN Z` THEN ASM_REWRITE_TAC[] THEN EQ_TAC THEN DISCH_TAC THENL
     [SUBGOAL_THEN `moi_fz2_sd (z2:A->bool) y =
                    moi_fz2_sd (moi_fz2_sd z1 z2) (moi_fz2_sd z1 y)` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; MOI_FZ2_IN_SD] THEN GEN_TAC THEN CONV_TAC TAUT;
        USE_THEN "bsd" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      SUBGOAL_THEN `moi_fz2_sd (z1:A->bool) y =
                    moi_fz2_sd (moi_fz2_sd z1 z2) (moi_fz2_sd z2 y)` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; MOI_FZ2_IN_SD] THEN GEN_TAC THEN CONV_TAC TAUT;
        USE_THEN "bsd" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `nsum (IMAGE (cls:(A->bool)->(A->bool)->bool) Z)
                    (\s:(A->bool)->bool. CARD (B:(A->bool)->bool))` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[NSUM_CONST; FINITE_IMAGE];
    MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_MESON_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* Part 5. The image of delta^1.                                             *)
(* ------------------------------------------------------------------------- *)

(* delta^1 of a single edge: the triangles containing it.                    *)

let MOI_S3ZA_D1_EDGE = prove
 (`!c (e:real^N->bool).
     e IN c /\ aff_dim e = &1
     ==> moi_s3za_d1 c {e} = {t | t IN c /\ aff_dim t = &2 /\ e SUBSET t}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s3za_d1; moi_fz2_pm] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `t:real^N->bool` THEN
  REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN
  ASM_CASES_TAC `(e:real^N->bool) SUBSET t` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `{a:real^N->bool | a = e /\ a IN c /\ aff_dim a = &1 /\ a SUBSET t} = {e}`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN GEN_TAC THEN
      EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[CARD_SING] THEN CONV_TAC NUM_REDUCE_CONV;
    SUBGOAL_THEN `{a:real^N->bool | a = e /\ a IN c /\ aff_dim a = &1 /\ a SUBSET t} = {}`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; NOT_IN_EMPTY] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[CARD_CLAUSES; ODD]]);;

(* For a closed surface delta^1 takes values in the even triangle sets      *)
(* (each edge lies in exactly two triangles).                                *)

let MOI_S3ZA_D1_EVEN = prove
 (`!c (z:(real^N->bool)->bool).
     FINITE c /\ combinatorial_manifold 2 c /\ z SUBSET {e | e IN c /\ aff_dim e = &1}
     ==> EVEN (CARD (moi_s3za_d1 c z))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s3za_d1; moi_fz2_pm] THEN
  MATCH_MP_TAC(REWRITE_RULE[] (ISPECL
   [`\e t:real^N->bool. e IN c /\ aff_dim e = &1 /\ e SUBSET t`] MOI_FZ2_DOUBLE_EVEN)) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM SET_TAC[];
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(e:real^N->bool) IN c /\ aff_dim e = &1` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `{y | y IN {t | t IN c /\ aff_dim t = &2} /\
           (e:real^N->bool) IN c /\ aff_dim e = &1 /\ e SUBSET y} =
      {t | t IN c /\ aff_dim t = &2 /\ e SUBSET t}`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[MOI_FSA_CM_EDGE2] THEN CONV_TAC NUM_REDUCE_CONV]);;

(* Every even set of triangles is a value of delta^1 (dual connectivity:    *)
(* two triangles sharing an edge are delta^1 of that edge).                  *)

let MOI_S3ZA_D1_PAIRS = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\ connected (UNIONS c)
     ==> !x. x SUBSET {t | t IN c /\ aff_dim t = &2} /\ EVEN (CARD x)
             ==> x IN IMAGE (moi_s3za_d1 c) {z | z SUBSET {e | e IN c /\ aff_dim e = &1}}`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF; combinatorial_manifold_with_boundary];
    ALL_TAC] THEN
  ABBREV_TAC `G = IMAGE (moi_s3za_d1 (c:(real^N->bool)->bool))
                        {z | z SUBSET {e | e IN c /\ aff_dim e = &1}}` THEN
  SUBGOAL_THEN `!u v:(real^N->bool)->bool. u IN G /\ v IN G ==> moi_fz2_sd u v IN G`
  ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FZ2_IMAGE_SD THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FZ2_POW_SD THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[MOI_S3ZA_D1_SD]];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_FZ2_EVEN_GEN THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    EXPAND_TAC "G" THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    EXISTS_TAC `{}:(real^N->bool)->bool` THEN
    REWRITE_TAC[EMPTY_SUBSET; moi_s3za_d1; MOI_FZ2_PM_EMPTY];
    ALL_TAC] THEN
  (* pairs: dual connectivity from t1 *)
  X_GEN_TAC `t1:real^N->bool` THEN X_GEN_TAC `t2:real^N->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`;
                 `{t | t IN {t | t IN c /\ aff_dim t = &2} /\
                       (t = t1 \/ {t1,t} IN (G:((real^N->bool)->bool)->bool))}`]
    MOI_FRB_CMB2_DCONN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [SET_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `t1:real^N->bool` THEN
      UNDISCH_TAC `(t1:real^N->bool) IN {t | t IN c /\ aff_dim t = &2}` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[];
      MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `t':real^N->bool`] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC)
        STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN
      ABBREV_TAC `e = (t:real^N->bool) INTER t'` THEN
      SUBGOAL_THEN `(e:real^N->bool) IN c` ASSUME_TAC THENL
       [EXPAND_TAC "e" THEN ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
      SUBGOAL_THEN `~(t:real^N->bool = t')` ASSUME_TAC THENL
       [DISCH_TAC THEN UNDISCH_TAC `aff_dim(e:real^N->bool) = &1` THEN
        EXPAND_TAC "e" THEN UNDISCH_TAC `aff_dim(t':real^N->bool) = &2` THEN
        FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> concl th = `(t:real^N->bool) = t'`)) THEN
        REWRITE_TAC[INTER_IDEMPOT] THEN INT_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `moi_s3za_d1 c {e} = {t:real^N->bool,t'}` ASSUME_TAC THENL
       [ASM_SIMP_TAC[MOI_S3ZA_D1_EDGE] THEN
        MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FGB_CMB2_EDGE) THEN
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `{t:real^N->bool,t'} SUBSET
                      {r | r IN c /\ aff_dim r = &2 /\ e SUBSET r}` ASSUME_TAC THENL
         [EXPAND_TAC "e" THEN ASM SET_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `FINITE {r:real^N->bool | r IN c /\ aff_dim r = &2 /\ e SUBSET r}`
        ASSUME_TAC THENL
         [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
          ASM_REWRITE_TAC[] THEN SET_TAC[];
          ALL_TAC] THEN
        SUBGOAL_THEN `CARD {t:real^N->bool,t'} = 2` ASSUME_TAC THENL
         [ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
                       NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV;
          ALL_TAC] THEN
        MP_TAC(ISPECL [`{t:real^N->bool,t'}`;
                       `{r:real^N->bool | r IN c /\ aff_dim r = &2 /\ e SUBSET r}`]
          CARD_SUBSET) THEN
        ASM_REWRITE_TAC[] THEN
        STRIP_TAC THEN STRIP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_SUBSET_EQ THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `{t:real^N->bool,t'} IN G` ASSUME_TAC THENL
       [EXPAND_TAC "G" THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
        EXISTS_TAC `{e:real^N->bool}` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        ALL_TAC] THEN
      ASM_CASES_TAC `(t':real^N->bool) = t1` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `(t:real^N->bool) = t1` THENL
       [UNDISCH_TAC `{t:real^N->bool,t'} IN G` THEN ASM_REWRITE_TAC[];
        SUBGOAL_THEN `{t1:real^N->bool,t} IN G` ASSUME_TAC THENL
         [ASM_MESON_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `{t1:real^N->bool,t'} = moi_fz2_sd {t1,t} {t,t'}` SUBST1_TAC THENL
         [GEN_REWRITE_TAC I [EXTENSION] THEN
          REWRITE_TAC[MOI_FZ2_IN_SD; IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
          FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
            `!u v:(real^N->bool)->bool. u IN G /\ v IN G ==> moi_fz2_sd u v IN G`)
            (concl th))) THEN
          ASM_REWRITE_TAC[]]]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `\s:(real^N->bool)->bool. (t2:real^N->bool) IN s`) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  UNDISCH_TAC `(t2:real^N->bool) IN {t | t IN c /\ aff_dim t = &2}` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[] THEN ASM_MESON_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* Part 6. The counts and the theorems Z2_COUNT and Z2_COUNT_BD.             *)
(* ------------------------------------------------------------------------- *)

(* The count: |H| * 2^(V - 1) * |im delta^1| = 2^E for a finite complex     *)
(* with a nonempty, edge-connected vertex set.                               *)

let MOI_S3ZA_H1_COUNT = prove
 (`!c:(real^N->bool)->bool.
     simplicial_complex c /\ moi_frb_conn c /\ ~({v | {v} IN c} = {})
     ==> CARD (moi_s33_h1z2 c) * 2 EXP (CARD {v | {v} IN c} - 1) *
         CARD (IMAGE (moi_s3za_d1 c) {z | z SUBSET {e | e IN c /\ aff_dim e = &1}}) =
         2 EXP (CARD {e | e IN c /\ aff_dim e = &1})`,
  GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [simplicial_complex]) THEN
  ABBREV_TAC `V = {v:real^N | {v} IN c}` THEN
  ABBREV_TAC `E = {e:real^N->bool | e IN c /\ aff_dim e = &1}` THEN
  SUBGOAL_THEN `FINITE (V:real^N->bool) /\ FINITE (E:(real^N->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "V" THEN MATCH_MP_TAC MOI_S3ZA_VERTS_FINITE THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "E" THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[]; SET_TAC[]]];
    ALL_TAC] THEN
  ABBREV_TAC `Z = {z:(real^N->bool)->bool | z2_cocycle c z}` THEN
  ABBREV_TAC `B = IMAGE (moi_s3za_d0 (c:(real^N->bool)->bool)) {w | w SUBSET V}` THEN
  SUBGOAL_THEN `!z:(real^N->bool)->bool. z IN Z <=> z SUBSET E /\ moi_s3za_d1 (c:(real^N->bool)->bool) z = {}`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Z"; "E"] THEN REWRITE_TAC[IN_ELIM_THM; MOI_S3ZA_COCYCLE];
    ALL_TAC] THEN
  (* |Z| * |im d1| = 2^E *)
  SUBGOAL_THEN
   `CARD (Z:((real^N->bool)->bool)->bool) *
    CARD (IMAGE (moi_s3za_d1 (c:(real^N->bool)->bool)) {z | z SUBSET (E:(real^N->bool)->bool)}) = 2 EXP CARD E`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `Z = {z:(real^N->bool)->bool | z SUBSET E /\ moi_s3za_d1 (c:(real^N->bool)->bool) z = {}}`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM]; ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC MOI_FZ2_KERNEL_IMAGE_POW THEN ASM_SIMP_TAC[MOI_S3ZA_D1_SD];
    ALL_TAC] THEN
  (* |B| * 2 = 2^V *)
  SUBGOAL_THEN `{w:real^N->bool | w SUBSET V /\ moi_s3za_d0 (c:(real^N->bool)->bool) w = {}} = {{}, V}`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `w:real^N->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_CASES_TAC `(w:real^N->bool) SUBSET V` THEN ASM_REWRITE_TAC[] THENL
     [EXPAND_TAC "V" THEN MATCH_MP_TAC MOI_S3ZA_D0_KERNEL THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 * CARD (B:((real^N->bool)->bool)->bool) = 2 EXP CARD (V:real^N->bool)`
  ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN
    MP_TAC(ISPECL [`V:real^N->bool`; `moi_s3za_d0 (c:(real^N->bool)->bool)`]
      MOI_FZ2_KERNEL_IMAGE_POW) THEN
    ASM_SIMP_TAC[MOI_S3ZA_D0_SD] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
    COND_CASES_TAC THENL [ASM_MESON_TAC[]; ARITH_TAC];
    ALL_TAC] THEN
  (* classes *)
  SUBGOAL_THEN `B SUBSET (Z:((real^N->bool)->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `w:real^N->bool` THEN DISCH_TAC THEN CONJ_TAC THENL
     [EXPAND_TAC "E" THEN REWRITE_TAC[moi_s3za_d0; MOI_FZ2_PM_SUBSET];
      MATCH_MP_TAC MOI_S3ZA_D1_D0 THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:(real^N->bool)->bool. z SUBSET E
      ==> (z2_coboundary (c:(real^N->bool)->bool) z <=> z IN (B:((real^N->bool)->bool)->bool))`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:(real^N->bool)->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`]
      MOI_S3ZA_COBOUNDARY) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "B" THEN EXPAND_TAC "V" THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD (moi_s33_h1z2 (c:(real^N->bool)->bool)) * CARD (B:((real^N->bool)->bool)->bool) =
    CARD (Z:((real^N->bool)->bool)->bool)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `moi_s33_h1z2 (c:(real^N->bool)->bool) = IMAGE (moi_s33_z2class c) Z`
    SUBST1_TAC THENL
     [REWRITE_TAC[moi_s33_h1z2] THEN EXPAND_TAC "Z" THEN
      GEN_REWRITE_TAC LAND_CONV [SIMPLE_IMAGE_GEN] THEN REWRITE_TAC[ETA_AX];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_S3ZA_CLASS_COUNT THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{z:(real^N->bool)->bool | z SUBSET E}` THEN
      ASM_SIMP_TAC[FINITE_POWERSET] THEN ASM SET_TAC[];
      FIRST_ASSUM ACCEPT_TAC;
      EXPAND_TAC "B" THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
      EXISTS_TAC `{}:real^N->bool` THEN
      REWRITE_TAC[EMPTY_SUBSET; moi_s3za_d0; MOI_FZ2_PM_EMPTY];
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL
       [MATCH_MP_TAC MOI_FZ2_POW_SD THEN ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[MOI_S3ZA_D1_SD; MOI_FZ2_SD]];
      EXPAND_TAC "B" THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FZ2_IMAGE_SD THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FZ2_POW_SD THEN ASM_REWRITE_TAC[];
        ASM_MESON_TAC[MOI_S3ZA_D0_SD]];
      X_GEN_TAC `z:(real^N->bool)->bool` THEN DISCH_TAC THEN
      REWRITE_TAC[moi_s33_z2class] THEN GEN_REWRITE_TAC I [EXTENSION] THEN
      X_GEN_TAC `y:(real^N->bool)->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN
      SUBGOAL_THEN `z2_cocycle (c:(real^N->bool)->bool) (y:(real^N->bool)->bool) <=> y IN Z` SUBST1_TAC THENL
       [EXPAND_TAC "Z" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
      ASM_CASES_TAC `(y:(real^N->bool)->bool) IN Z` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM moi_fz2_sd] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!z:(real^N->bool)->bool. z SUBSET E ==> (z2_coboundary (c:(real^N->bool)->bool) z <=> z IN B)`)
        (concl th))) THEN
      MATCH_MP_TAC MOI_FZ2_POW_SD THEN
      UNDISCH_TAC `(y:(real^N->bool)->bool) IN Z` THEN
      UNDISCH_TAC `(z:(real^N->bool)->bool) IN Z` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  (* combine *)
  SUBGOAL_THEN `CARD (B:((real^N->bool)->bool)->bool) = 2 EXP (CARD (V:real^N->bool) - 1)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `CARD (V:real^N->bool) = SUC (CARD V - 1)` MP_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `~(n = 0) ==> n = SUC(n - 1)`) THEN
      ASM_SIMP_TAC[CARD_EQ_0] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> UNDISCH_TAC `2 * CARD (B:((real^N->bool)->bool)->bool) =
                                      2 EXP CARD (V:real^N->bool)` THEN
                         GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [th]) THEN
    REWRITE_TAC[EXP] THEN ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `CARD (Z:((real^N->bool)->bool)->bool) *
               CARD (IMAGE (moi_s3za_d1 (c:(real^N->bool)->bool)) {z | z SUBSET (E:(real^N->bool)->bool)}) = 2 EXP CARD E` THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
    rand (concl th) = `CARD (Z:((real^N->bool)->bool)->bool)`)) THEN
  ASM_REWRITE_TAC[MULT_ASSOC]);;

(* Exponent arithmetic.                                                       *)

let MOI_S3ZA_EXP_SPLIT = prove
 (`!a k m. a * 2 EXP k = 2 EXP m ==> k <= m /\ a = 2 EXP (m - k)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(a = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `a * 2 EXP k = 2 EXP m` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES] THEN DISCH_THEN(MP_TAC o SYM) THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `(k:num) <= m` ASSUME_TAC THENL
   [SUBGOAL_THEN `2 EXP k <= 2 EXP m` MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
        lhand (concl th) = `a * 2 EXP k`)) THEN
      GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `x = 1 * x`] THEN
      MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC;
      REWRITE_TAC[LE_EXP; ARITH_EQ] THEN ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[EQ_MULT_RCANCEL]
   `!a b c. ~(c = 0) /\ a * c = b * c ==> a = b`) THEN
  EXISTS_TAC `2 EXP k` THEN REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN
  ASM_REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

(* Vertices and triangles exist in a nonempty finite surface.                 *)

let MOI_S3ZA_NONEMPTY = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\ ~(UNIONS c = {})
     ==> ~({v | {v} IN c} = {}) /\ ~({t | t IN c /\ aff_dim t = &2} = {})`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF; combinatorial_manifold_with_boundary];
    ALL_TAC] THEN
  SUBGOAL_THEN `?v:real^N. {v} IN c` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(UNIONS c:real^N->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `s:real^N->bool`
      STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_SCF_SC_VERTEX) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; MESON_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FRB_CMB2_VTRI) THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let MOI_S3ZA_H1_FINITE = prove
 (`!c:(real^N->bool)->bool. FINITE c ==> FINITE (moi_s33_h1z2 c)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s33_h1z2] THEN
  GEN_REWRITE_TAC RAND_CONV [SIMPLE_IMAGE_GEN] THEN
  MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{z:(real^N->bool)->bool | z SUBSET {e | e IN c /\ aff_dim e = &1}}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_POWERSET THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    REWRITE_TAC[SUBSET; IN_ELIM_THM; MOI_S3ZA_COCYCLE] THEN SIMP_TAC[]]);;

let Z2_COUNT = prove
 (MOI_S33_Z2_COUNT,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool) /\
                combinatorial_manifold_with_boundary 2 c`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FSA_CM_SC] THEN
    UNDISCH_TAC `combinatorial_manifold 2 (c:(real^N->bool)->bool)` THEN
    SIMP_TAC[combinatorial_manifold; combinatorial_manifold_with_boundary];
    ALL_TAC] THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_S3ZA_NONEMPTY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_S3ZA_H1_COUNT) THEN
  ASM_SIMP_TAC[MOI_FRB_CONN_OF_CONNECTED] THEN
  SUBGOAL_THEN
   `IMAGE (moi_s3za_d1 c) {z | z SUBSET {e | e IN c /\ aff_dim e = &1}} =
    {x | x SUBSET {t:real^N->bool | t IN c /\ aff_dim t = &2} /\ EVEN (CARD x)}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:(real^N->bool)->bool` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EQ_TAC THENL
     [REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `z:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[moi_s3za_d1; MOI_FZ2_PM_SUBSET];
        MATCH_MP_TAC MOI_S3ZA_D1_EVEN THEN ASM_REWRITE_TAC[]];
      STRIP_TAC THEN
      MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_S3ZA_D1_PAIRS) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {t:real^N->bool | t IN c /\ aff_dim t = &2}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_FZ2_EVEN_SUBSETS] THEN
  REWRITE_TAC[GSYM MULT_ASSOC; GSYM EXP_ADD] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_S3ZA_EXP_SPLIT) THEN STRIP_TAC THEN
  ABBREV_TAC `nv = CARD {v:real^N | {v} IN c}` THEN
  ABBREV_TAC `ne = CARD {e:real^N->bool | e IN c /\ aff_dim e = &1}` THEN
  ABBREV_TAC `nf = CARD {t:real^N->bool | t IN c /\ aff_dim t = &2}` THEN
  EXISTS_TAC `ne - ((nv - 1) + (nf - 1))` THEN
  ASM_SIMP_TAC[HAS_SIZE; MOI_S3ZA_H1_FINITE; MOI_FSA_CM_EULER] THEN
  SUBGOAL_THEN `~(nv = 0) /\ ~(nf = 0)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["nv"; "nf"] THEN
    ASM_SIMP_TAC[CARD_EQ_0; MOI_S3ZA_VERTS_FINITE];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; GSYM REAL_OF_NUM_ADD;
               ARITH_RULE `~(n = 0) ==> 1 <= n`] THEN
  REAL_ARITH_TAC);;

let Z2_COUNT_BD = prove
 (MOI_S33_Z2_COUNT_BD,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF; combinatorial_manifold_with_boundary];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(UNIONS c:real^N->bool = {})` ASSUME_TAC THENL
   [UNDISCH_TAC `~(surface_boundary c:real^N->bool = {})` THEN
    REWRITE_TAC[surface_boundary] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_S3ZA_NONEMPTY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_S3ZA_H1_COUNT) THEN
  ASM_SIMP_TAC[MOI_FRB_CONN_OF_CONNECTED] THEN
  SUBGOAL_THEN
   `IMAGE (moi_s3za_d1 c) {z | z SUBSET {e | e IN c /\ aff_dim e = &1}} =
    {x | x SUBSET {t:real^N->bool | t IN c /\ aff_dim t = &2}}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:(real^N->bool)->bool` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EQ_TAC THENL
     [REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `z:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[moi_s3za_d1; MOI_FZ2_PM_SUBSET];
      ALL_TAC] THEN
    DISCH_TAC THEN
    (* a boundary edge and its triangle *)
    UNDISCH_TAC `~(surface_boundary c:real^N->bool = {})` THEN
    REWRITE_TAC[surface_boundary; GSYM MEMBER_NOT_EMPTY; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` (X_CHOOSE_THEN `e:real^N->bool`
      (CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC))) THEN
    SUBGOAL_THEN `?t0:real^N->bool. {r | r IN c /\ aff_dim r = &2 /\ e SUBSET r} = {t0}`
    (X_CHOOSE_TAC `t0:real^N->bool`) THENL
     [REWRITE_TAC[GSYM MOI_FSA_CARD_EQ_1] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `moi_s3za_d1 c {e} = {t0:real^N->bool}` ASSUME_TAC THENL
     [ASM_SIMP_TAC[MOI_S3ZA_D1_EDGE]; ALL_TAC] THEN
    SUBGOAL_THEN `(t0:real^N->bool) IN {t | t IN c /\ aff_dim t = &2}` ASSUME_TAC THENL
     [UNDISCH_TAC `{r | r IN c /\ aff_dim r = &2 /\ e SUBSET r} = {t0:real^N->bool}` THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_S3ZA_D1_PAIRS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `FINITE (x:(real^N->bool)->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `EVEN (CARD (x:(real^N->bool)->bool))` THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `moi_fz2_sd x {t0:real^N->bool} IN
                  IMAGE (moi_s3za_d1 c) {z | z SUBSET {e | e IN c /\ aff_dim e = &1}}`
    MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_FZ2_POW_SD THEN ASM SET_TAC[];
        UNDISCH_TAC `~EVEN (CARD (x:(real^N->bool)->bool))` THEN
        REWRITE_TAC[GSYM NOT_ODD] THEN
        ASM_SIMP_TAC[MOI_FZ2_SD_PARITY; FINITE_SING; CARD_SING] THEN
        CONV_TAC NUM_REDUCE_CONV THEN MESON_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `moi_fz2_sd (z:(real^N->bool)->bool) {e}` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[MOI_S3ZA_D1_SD] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
        rand (concl th) = `moi_s3za_d1 c (z:(real^N->bool)->bool)`)) THEN
      ASM_REWRITE_TAC[MOI_FZ2_SD];
      MATCH_MP_TAC MOI_FZ2_POW_SD THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {t:real^N->bool | t IN c /\ aff_dim t = &2}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_POWERSET; GSYM EXP_ADD] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_S3ZA_EXP_SPLIT) THEN STRIP_TAC THEN
  ABBREV_TAC `nv = CARD {v:real^N | {v} IN c}` THEN
  ABBREV_TAC `ne = CARD {e:real^N->bool | e IN c /\ aff_dim e = &1}` THEN
  ABBREV_TAC `nf = CARD {t:real^N->bool | t IN c /\ aff_dim t = &2}` THEN
  EXISTS_TAC `ne - ((nv - 1) + nf)` THEN
  ASM_SIMP_TAC[HAS_SIZE; MOI_S3ZA_H1_FINITE] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN c ==> aff_dim s <= &2` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THENL
     [ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FRB_CMB2_PURE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`] AFF_DIM_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_S3ZA_EULER_2D] THEN
  SUBGOAL_THEN `~(nv = 0)` ASSUME_TAC THENL
   [EXPAND_TAC "nv" THEN
    ASM_SIMP_TAC[CARD_EQ_0; MOI_S3ZA_VERTS_FINITE; MOI_SCF_SC_FINITE];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; GSYM REAL_OF_NUM_ADD;
               ARITH_RULE `~(n = 0) ==> 1 <= n`] THEN
  REAL_ARITH_TAC);;


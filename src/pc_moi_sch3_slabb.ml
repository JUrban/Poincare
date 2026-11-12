(* ========================================================================= *)
(* pc_moi_sch3_slabb: MOI_SSL_SLAB_FROM_STAR : |- MOI_SSL_STAR_STMT ==>     *)
(* MOI_SSL_SLAB_STMT (Moise GTM 47, Sec 17, Lemma 6, p.124: the slab        *)
(* around one vertex is reduced to the star of the vertex by deleting free  *)
(* prisms).                                                                 *)
(* The first section sets up the deletion setting (prisms, regions, level   *)
(* sections).                                                               *)
(* ========================================================================= *)

needs "src/pc_moi_sch3_slab.ml";;

prioritize_real();;
type_invention_error := true;;

(* The prisms of the slab: 3-simplices without v meeting the open slab.     *)

let moi_ssb_prisms = new_definition
 `moi_ssb_prisms (k:(real^3->bool)->bool) (a:real^3) (v:real^3) t1 t2 =
    {t | t IN k /\ aff_dim t = &3 /\ ~(v IN t) /\
         ~(t INTER {x:real^3 | t1 < a dot x /\ a dot x < t2} = {})}`;;

(* The 3-simplices kept in the region for a set pp of prisms: the star of v *)
(* and pp.                                                                   *)

let moi_ssb_mem = new_definition
 `moi_ssb_mem (k:(real^3->bool)->bool) (v:real^3) pp =
    {t | t IN k /\ aff_dim t = &3 /\ (v IN t \/ t IN pp)}`;;

let moi_ssb_reg = new_definition
 `moi_ssb_reg (k:(real^3->bool)->bool) (a:real^3) (v:real^3) t1 t2 pp =
    UNIONS {t INTER {x:real^3 | t1 <= a dot x /\ a dot x <= t2} | t |
            t IN moi_ssb_mem k v pp}`;;

(* The wedges (3-simplices at v whose interior meets the level of v) and   *)
(* the level sections of the wedges and of pp.                               *)

let moi_ssb_wedges = new_definition
 `moi_ssb_wedges (k:(real^3->bool)->bool) (a:real^3) (v:real^3) =
    {t | t IN k /\ aff_dim t = &3 /\ v IN t /\
         ~(interior t INTER {x:real^3 | a dot x = a dot v} = {})}`;;

let moi_ssb_secs = new_definition
 `moi_ssb_secs (k:(real^3->bool)->bool) (a:real^3) (v:real^3) pp =
    {t INTER {x:real^3 | a dot x = a dot v} | t |
     t IN moi_ssb_wedges k a v \/ t IN pp}`;;

(* The star statement in the notation of this file.                        *)

let MOI_SSB_STAR_FORM = prove
 (`!k (a:real^3) v t1 t2.
     UNIONS (moi_ssb_secs k a v {}) =
     UNIONS {t INTER {x:real^3 | a dot x = a dot v} | t |
             t IN k /\ aff_dim t = &3 /\ v IN t /\
             ~(interior t INTER {x:real^3 | a dot x = a dot v} = {})} /\
     moi_ssb_reg k a v t1 t2 {} =
     UNIONS {t INTER {x:real^3 | t1 <= a dot x /\ a dot x <= t2} | t |
             t IN k /\ aff_dim t = &3 /\ v IN t}`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[moi_ssb_secs; moi_ssb_reg; moi_ssb_mem; moi_ssb_wedges; NOT_IN_EMPTY] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[]);;

(* Level sections of 3-simplices whose interior meets the level.           *)

let MOI_SSB_SEC_CELL = prove
 (`!s (a:real^3) lo hi k v t1 t2 t b.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ t IN k /\
     ~(interior t INTER {x | a dot x = b} = {})
     ==> polytope (t INTER {x | a dot x = b}) /\
         aff_dim (t INTER {x | a dot x = b}) = &2 /\
         relative_interior (t INTER {x | a dot x = b}) =
           interior t INTER {x | a dot x = b} /\
         t INTER {x | a dot x = b} SUBSET {x | a dot x = b}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSL_SLAB_FACTS) THEN
  SUBGOAL_THEN `simplicial_complex (k:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_ssl_slab_hyp]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `t:real^3->bool`] MOI_SSL_SC_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:real^3->bool`; `a:real^3`; `b:real`] MOI_SSL_LEVEL_SECTION) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[INTER_SUBSET]);;

(* Distinct 3-simplices of a complex: the interior of one misses the other. *)

let MOI_SSB_INTERIOR_DISJ = prove
 (`!k t t':real^3->bool.
     simplicial_complex k /\ t IN k /\ t' IN k /\
     aff_dim t = &3 /\ aff_dim t' = &3 /\ ~(t = t')
     ==> interior t INTER t' = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `t:real^3->bool`; `t':real^3->bool`]
    MOI_SSL_SC_INTER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `t:real^3->bool`] MOI_SSL_SC_SIMPLEX) THEN
  MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `t':real^3->bool`] MOI_SSL_SC_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `t INTER t':real^3->bool = t` THENL
   [SUBGOAL_THEN `t face_of (t':real^3->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`t:real^3->bool`; `t':real^3->bool`] FACE_OF_AFF_DIM_LT) THEN
    ASM_REWRITE_TAC[INT_LT_REFL];
    MP_TAC(ISPECL [`t:real^3->bool`; `t INTER t':real^3->bool`]
      FACE_OF_SUBSET_RELATIVE_FRONTIER) THEN
    ASM_REWRITE_TAC[relative_frontier] THEN
    MP_TAC(ISPEC `t:real^3->bool` INTERIOR_SUBSET_RELATIVE_INTERIOR) THEN
    MP_TAC(ISPEC `t:real^3->bool` INTERIOR_SUBSET) THEN
    SET_TAC[]]);;

(* Two 3-simplices with the same level section through an interior point   *)
(* are equal.                                                               *)

let MOI_SSB_SEC_INJ = prove
 (`!k t t' (a:real^3) b.
     simplicial_complex k /\ t IN k /\ t' IN k /\
     aff_dim t = &3 /\ aff_dim t' = &3 /\
     ~(interior t INTER {x | a dot x = b} = {}) /\
     t INTER {x | a dot x = b} = t' INTER {x | a dot x = b}
     ==> t = t'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `t:real^3->bool`; `t':real^3->bool`]
    MOI_SSB_INTERIOR_DISJ) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `t:real^3->bool` INTERIOR_SUBSET) THEN
  UNDISCH_TAC `~(interior t INTER {x:real^3 | a dot x = b} = {})` THEN
  UNDISCH_TAC `t INTER {x:real^3 | a dot x = b} = t' INTER {x | a dot x = b}` THEN
  SET_TAC[]);;

(* Facts about the slab setting used throughout.                           *)

let MOI_SSB_HYP = prove
 (`!s (a:real^3) lo hi k v t1 t2.
     moi_ssl_slab_hyp s a lo hi k v t1 t2
     ==> simplicial_complex k /\ FINITE k /\ ~(a = vec 0) /\
         t1 < t2 /\ t1 < a dot v /\ a dot v < t2 /\ {v} IN k /\
         UNIONS k = s UNION inside s /\ pl_sphere 2 s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_ssl_slab_hyp]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSL_SLAB_FACTS) THEN
  SUBGOAL_THEN `FINITE (k:(real^3->bool)->bool)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o REWRITE_RULE[simplicial_complex] o check (fun th ->
      concl th = `simplicial_complex (k:(real^3->bool)->bool)`)) THEN SIMP_TAC[];
    ASM_REWRITE_TAC[]]);;

(* A prism: four affinely independent vertices outside the slab on both    *)
(* sides, and interior points at every level of the slab.                   *)

let MOI_SSB_PRISM = prove
 (`!s (a:real^3) lo hi k v t1 t2 t.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ t IN moi_ssb_prisms k a v t1 t2
     ==> t IN k /\ aff_dim t = &3 /\ ~(v IN t) /\
         (?c. FINITE c /\ ~affine_dependent c /\ CARD c = 4 /\ t = convex hull c /\
              (!w. w IN c ==> {w} IN k /\ (a dot w < t1 \/ t2 < a dot w)) /\
              (?w. w IN c /\ a dot w < t1) /\ (?w. w IN c /\ t2 < a dot w)) /\
         (!b. t1 <= b /\ b <= t2 ==> ~(interior t INTER {x | a dot x = b} = {}))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_ssb_prisms; IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `t:real^3->bool`] MOI_SSL_PRISM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `c:real^3->bool`
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `c:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `aff_dim (t:real^3->bool) = &3` THEN
  ASM_SIMP_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_AFFINE_INDEPENDENT] THEN
  REWRITE_TAC[INT_ARITH `x - &1:int = &3 <=> x = &4`; INT_OF_NUM_EQ]);;

let MOI_SSB_PRISM_BASIC = prove
 (`!s (a:real^3) lo hi k v t1 t2 t.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ t IN moi_ssb_prisms k a v t1 t2
     ==> t IN k /\ aff_dim t = &3 /\ ~(v IN t) /\
         (!b. t1 <= b /\ b <= t2 ==> ~(interior t INTER {x | a dot x = b} = {}))`,
  MESON_TAC[MOI_SSB_PRISM]);;

(* The level sections for a set pp of prisms: finitely many polygons in the *)
(* level of v, meeting in faces; each comes from a unique wedge or prism.   *)

let MOI_SSB_SECS_REP = prove
 (`!s (a:real^3) lo hi k v t1 t2 pp c.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ pp SUBSET moi_ssb_prisms k a v t1 t2 /\
     c IN moi_ssb_secs k a v pp
     ==> ?t. t IN k /\ aff_dim t = &3 /\
             ~(interior t INTER {x | a dot x = a dot v} = {}) /\
             (t IN moi_ssb_wedges k a v \/ t IN pp) /\
             c = t INTER {x | a dot x = a dot v}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[moi_ssb_secs; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [UNDISCH_TAC `(t:real^3->bool) IN moi_ssb_wedges k a v` THEN
    SIMP_TAC[moi_ssb_wedges; IN_ELIM_THM];
    MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                   `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                   `t:real^3->bool`] MOI_SSB_PRISM_BASIC) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN ASM_REAL_ARITH_TAC]);;

let MOI_SSB_SECS_FACTS = prove
 (`!s (a:real^3) lo hi k v t1 t2 pp.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ pp SUBSET moi_ssb_prisms k a v t1 t2
     ==> FINITE (moi_ssb_secs k a v pp) /\
         (!c. c IN moi_ssb_secs k a v pp
              ==> polytope c /\ aff_dim c = &2 /\ c SUBSET {x | a dot x = a dot v}) /\
         (!c c'. c IN moi_ssb_secs k a v pp /\ c' IN moi_ssb_secs k a v pp
                 ==> (c INTER c') face_of c /\ (c INTER c') face_of c') /\
         moi_ssb_secs k a v {} SUBSET moi_ssb_secs k a v pp`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `pp:(real^3->bool)->bool`] MOI_SSB_SECS_REP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "rep") THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `IMAGE (\t:real^3->bool. t INTER {x:real^3 | a dot x = a dot v}) k` THEN
    ASM_SIMP_TAC[FINITE_IMAGE] THEN REWRITE_TAC[SUBSET; IN_IMAGE] THEN
    X_GEN_TAC `c:real^3->bool` THEN
    DISCH_THEN(fun th -> USE_THEN "rep" (MP_TAC o C MATCH_MP th)) THEN
    MESON_TAC[];
    X_GEN_TAC `c:real^3->bool` THEN
    DISCH_THEN(fun th -> USE_THEN "rep" (MP_TAC o C MATCH_MP th)) THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                   `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                   `t:real^3->bool`; `a dot (v:real^3)`] MOI_SSB_SEC_CELL) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`c:real^3->bool`; `c':real^3->bool`] THEN
    DISCH_THEN(CONJUNCTS_THEN (fun th -> USE_THEN "rep" (MP_TAC o C MATCH_MP th))) THEN
    DISCH_THEN(X_CHOOSE_THEN `t':real^3->bool` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `t:real^3->bool`; `t':real^3->bool`]
      MOI_SSL_SC_INTER) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `(t INTER {x:real^3 | a dot x = a dot v}) INTER (t' INTER {x | a dot x = a dot v}) =
      (t INTER t') INTER {x | a dot x = a dot v}` SUBST1_TAC THENL
     [SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THEN MATCH_MP_TAC FACE_OF_SLICE THEN
    ASM_REWRITE_TAC[CONVEX_HYPERPLANE];
    REWRITE_TAC[moi_ssb_secs; SUBSET; IN_ELIM_THM; NOT_IN_EMPTY] THEN MESON_TAC[]]);;

(* Deleting a prism deletes exactly its section.                           *)

let MOI_SSB_SECS_DELETE = prove
 (`!s (a:real^3) lo hi k v t1 t2 pp t0.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ pp SUBSET moi_ssb_prisms k a v t1 t2 /\
     t0 IN pp
     ==> moi_ssb_secs k a v (pp DELETE t0) =
           moi_ssb_secs k a v pp DELETE (t0 INTER {x | a dot x = a dot v}) /\
         t0 INTER {x | a dot x = a dot v} IN moi_ssb_secs k a v pp /\
         ~(t0 INTER {x | a dot x = a dot v} IN moi_ssb_secs k a v {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `t0:real^3->bool`] MOI_SSB_PRISM_BASIC) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `~(interior t0 INTER {x:real^3 | a dot x = a dot v} = {})` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. (t IN moi_ssb_wedges k a v \/ t IN pp)
        ==> (t INTER {x:real^3 | a dot x = a dot v} = t0 INTER {x | a dot x = a dot v} <=>
             t = t0)`
  (LABEL_TAC "key") THENL
   [X_GEN_TAC `t:real^3->bool` THEN DISCH_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_SSB_SEC_INJ THEN
      MAP_EVERY EXISTS_TAC [`k:(real^3->bool)->bool`; `a:real^3`; `a dot (v:real^3)`] THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
       [UNDISCH_TAC `(t:real^3->bool) IN moi_ssb_wedges k a v` THEN
        SIMP_TAC[moi_ssb_wedges; IN_ELIM_THM];
        MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                       `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                       `t:real^3->bool`] MOI_SSB_PRISM_BASIC) THEN
        ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]]];
      DISCH_THEN SUBST1_TAC THEN REFL_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((t0:real^3->bool) IN moi_ssb_wedges k a v)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[moi_ssb_wedges; IN_ELIM_THM]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[moi_ssb_secs; IN_ELIM_THM; IN_DELETE] THEN
    X_GEN_TAC `c:real^3->bool` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
      SUBGOAL_THEN `(t:real^3->bool) IN moi_ssb_wedges k a v \/ t IN pp` ASSUME_TAC THENL
       [MP_TAC(ASSUME `(t:real^3->bool) IN moi_ssb_wedges k a v \/ t IN pp /\ ~(t = t0)`) THEN
        CONV_TAC TAUT;
        ALL_TAC] THEN
      CONJ_TAC THENL [EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "key" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
        `(t:real^3->bool) IN moi_ssb_wedges k a v \/ t IN pp`)]) THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `(t0:real^3->bool) IN moi_ssb_wedges k a v \/ t0 IN pp /\ ~(t0 = t0)` THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:real^3->bool`
        (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) ASSUME_TAC) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
        is_eq(concl th) && lhs(concl th) = `c:real^3->bool`)) THEN
      EXISTS_TAC `t:real^3->bool` THEN REWRITE_TAC[] THEN
      ASM_CASES_TAC `t:real^3->bool = t0` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN
        UNDISCH_TAC `~(t0 INTER {x:real^3 | a dot x = a dot v} =
                       t0 INTER {x | a dot x = a dot v})` THEN REWRITE_TAC[];
        UNDISCH_TAC `(t:real^3->bool) IN moi_ssb_wedges k a v \/ t IN pp` THEN
        ASM_REWRITE_TAC[]]];
    REWRITE_TAC[moi_ssb_secs; IN_ELIM_THM] THEN EXISTS_TAC `t0:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[moi_ssb_secs; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `t:real^3->bool = t0` SUBST_ALL_TAC THENL
     [USE_THEN "key" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th (DISJ1 (ASSUME
        `(t:real^3->bool) IN moi_ssb_wedges k a v`) `(t:real^3->bool) IN pp`))]) THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `(t0:real^3->bool) IN moi_ssb_wedges k a v` THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The regions.  Each kept 3-simplex has a slab part that is a polytope     *)
(* with nonempty interior; deleting one prism from the region leaves the    *)
(* closure of the difference equal to the smaller region.                   *)
(* ------------------------------------------------------------------------- *)

let MOI_SSB_REG_PIECE = prove
 (`!s (a:real^3) lo hi k v t1 t2 pp t.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ pp SUBSET moi_ssb_prisms k a v t1 t2 /\
     t IN moi_ssb_mem k v pp
     ==> t IN k /\ aff_dim t = &3 /\
         polytope (t INTER {x | t1 <= a dot x /\ a dot x <= t2}) /\
         ~(interior (t INTER {x | t1 <= a dot x /\ a dot x <= t2}) = {}) /\
         closure (interior (t INTER {x | t1 <= a dot x /\ a dot x <= t2})) =
           t INTER {x | t1 <= a dot x /\ a dot x <= t2}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[moi_ssb_mem; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `t:real^3->bool`] MOI_SSL_SC_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(interior t INTER {x:real^3 | t1 < a dot x /\ a dot x < t2} = {})`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
     [SUBGOAL_THEN `~({x:real^3 | t1 < a dot x /\ a dot x < t2} INTER t = {})` MP_TAC THENL
       [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM] THEN
        EXISTS_TAC `v:real^3` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`{x:real^3 | t1 < a dot x /\ a dot x < t2}`; `interior t:real^3->bool`]
        OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
      ANTS_TAC THENL
       [MP_TAC(ISPECL [`a:real^3`; `t1:real`; `t2:real`] MOI_SSL_SLAB_BASIC) THEN
        ASM_SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `closure (interior t) = t:real^3->bool` SUBST1_TAC THENL
       [ASM_SIMP_TAC[CONVEX_CLOSURE_INTERIOR; CLOSURE_CLOSED]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN SET_TAC[];
      MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                     `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                     `t:real^3->bool`] MOI_SSB_PRISM_BASIC) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(t1 + t2) / &2`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM] THEN
      MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:real^3->bool`; `a:real^3`; `t1:real`; `t2:real`] MOI_SSL_SLAB_CELL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `t INTER {x:real^3 | t1 <= a dot x /\ a dot x <= t2}` MOI_SSL_CELL_FACTS) THEN
  ASM_SIMP_TAC[]);;

let MOI_SSB_REG_COMPACT = prove
 (`!s (a:real^3) lo hi k v t1 t2 pp.
     moi_ssl_slab_hyp s a lo hi k v t1 t2
     ==> compact (moi_ssb_reg k a v t1 t2 pp)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  REWRITE_TAC[moi_ssb_reg] THEN MATCH_MP_TAC COMPACT_UNIONS THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `k:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; moi_ssb_mem; IN_ELIM_THM] THEN MESON_TAC[];
    REWRITE_TAC[FORALL_IN_GSPEC; moi_ssb_mem; IN_ELIM_THM] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MOI_SSL_SC_SIMPLEX]; ALL_TAC] THEN
    MP_TAC(ISPECL [`a:real^3`; `t1:real`; `t2:real`] MOI_SSL_SLAB_BASIC) THEN
    ASM_SIMP_TAC[]]);;

let MOI_SSB_REG_DELETE = prove
 (`!s (a:real^3) lo hi k v t1 t2 pp t0.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ pp SUBSET moi_ssb_prisms k a v t1 t2 /\
     t0 IN pp
     ==> moi_ssb_reg k a v t1 t2 pp =
           moi_ssb_reg k a v t1 t2 (pp DELETE t0) UNION
           (t0 INTER {x | t1 <= a dot x /\ a dot x <= t2}) /\
         polytope (t0 INTER {x | t1 <= a dot x /\ a dot x <= t2}) /\
         ~(interior (t0 INTER {x | t1 <= a dot x /\ a dot x <= t2}) = {}) /\
         interior (t0 INTER {x | t1 <= a dot x /\ a dot x <= t2}) INTER
           moi_ssb_reg k a v t1 t2 (pp DELETE t0) = {} /\
         closure (moi_ssb_reg k a v t1 t2 pp DIFF
                  (t0 INTER {x | t1 <= a dot x /\ a dot x <= t2})) =
           moi_ssb_reg k a v t1 t2 (pp DELETE t0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `t0:real^3->bool`] MOI_SSB_PRISM_BASIC) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `pp DELETE (t0:real^3->bool) SUBSET moi_ssb_prisms k a v t1 t2`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(t0:real^3->bool) IN moi_ssb_mem k v pp` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[moi_ssb_mem; IN_ELIM_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `pp:(real^3->bool)->bool`; `t0:real^3->bool`] MOI_SSB_REG_PIECE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. t IN moi_ssb_mem k v (pp DELETE t0) ==> ~(t = t0) /\ t IN moi_ssb_mem k v pp`
  (LABEL_TAC "mem") THENL
   [REWRITE_TAC[moi_ssb_mem; IN_ELIM_THM; IN_DELETE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t IN moi_ssb_mem k v (pp DELETE t0)
        ==> interior (t0 INTER {x:real^3 | t1 <= a dot x /\ a dot x <= t2}) INTER t = {} /\
            interior (t INTER {x:real^3 | t1 <= a dot x /\ a dot x <= t2}) INTER t0 = {}`
  (LABEL_TAC "disj") THENL
   [X_GEN_TAC `t:real^3->bool` THEN DISCH_TAC THEN
    USE_THEN "mem" (fun th -> MP_TAC(MATCH_MP th (ASSUME
      `(t:real^3->bool) IN moi_ssb_mem k v (pp DELETE t0)`))) THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                   `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                   `pp:(real^3->bool)->bool`; `t:real^3->bool`] MOI_SSB_REG_PIECE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `t0:real^3->bool`; `t:real^3->bool`]
      MOI_SSB_INTERIOR_DISJ) THEN
    MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `t:real^3->bool`; `t0:real^3->bool`]
      MOI_SSB_INTERIOR_DISJ) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`t0 INTER {x:real^3 | t1 <= a dot x /\ a dot x <= t2}`;
                   `t0:real^3->bool`] SUBSET_INTERIOR) THEN
    MP_TAC(ISPECL [`t INTER {x:real^3 | t1 <= a dot x /\ a dot x <= t2}`;
                   `t:real^3->bool`] SUBSET_INTERIOR) THEN
    REWRITE_TAC[INTER_SUBSET] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_ssb_reg k a v t1 t2 pp =
    moi_ssb_reg k a v t1 t2 (pp DELETE t0) UNION
    (t0 INTER {x:real^3 | t1 <= a dot x /\ a dot x <= t2})`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_ssb_reg] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^3` THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
      ASM_CASES_TAC `t:real^3->bool = t0` THENL
       [DISJ2_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      DISJ1_TAC THEN EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(t:real^3->bool) IN moi_ssb_mem k v pp` THEN
      ASM_REWRITE_TAC[moi_ssb_mem; IN_ELIM_THM; IN_DELETE];
      REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM] THEN
        X_GEN_TAC `x:real^3` THEN MATCH_MP_TAC MONO_EXISTS THEN
        X_GEN_TAC `t:real^3->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "mem" (fun th -> MP_TAC(MATCH_MP th (ASSUME
          `(t:real^3->bool) IN moi_ssb_mem k v (pp DELETE t0)`))) THEN
        SIMP_TAC[];
        REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM] THEN
        X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN EXISTS_TAC `t0:real^3->bool` THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[moi_ssb_reg; INTER_UNIONS; EMPTY_UNIONS; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `t:real^3->bool` THEN DISCH_TAC THEN
    USE_THEN "disj" (fun th -> MP_TAC(MATCH_MP th (ASSUME
      `(t:real^3->bool) IN moi_ssb_mem k v (pp DELETE t0)`))) THEN
    SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THENL
     [SET_TAC[];
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC MOI_SSB_REG_COMPACT THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [moi_ssb_reg] THEN
  REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
  X_GEN_TAC `t:real^3->bool` THEN DISCH_TAC THEN
  USE_THEN "mem" (fun th -> MP_TAC(MATCH_MP th (ASSUME
    `(t:real^3->bool) IN moi_ssb_mem k v (pp DELETE t0)`))) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `pp:(real^3->bool)->bool`; `t:real^3->bool`] MOI_SSB_REG_PIECE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `t INTER {x:real^3 | t1 <= a dot x /\ a dot x <= t2} =
                closure (interior (t INTER {x | t1 <= a dot x /\ a dot x <= t2}))`
  (fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_CLOSURE THEN
  USE_THEN "disj" (fun th -> MP_TAC(MATCH_MP th (ASSUME
    `(t:real^3->bool) IN moi_ssb_mem k v (pp DELETE t0)`))) THEN
  SUBGOAL_THEN `t INTER {x:real^3 | t1 <= a dot x /\ a dot x <= t2} SUBSET
                moi_ssb_reg k a v t1 t2 (pp DELETE t0)` MP_TAC THENL
   [REWRITE_TAC[moi_ssb_reg; SUBSET; UNIONS_GSPEC; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN EXISTS_TAC `t:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `t INTER {x:real^3 | t1 <= a dot x /\ a dot x <= t2}` INTERIOR_SUBSET) THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The arc of a free prism section in terms of the faces of the prism.  The *)
(* crossing faces of conv c0 whose sections lie in the arc A are given by   *)
(* their omitted vertices; A is the union of their sections, and some       *)
(* crossing face is not among them.                                         *)
(* ------------------------------------------------------------------------- *)

let moi_ssb_omit = new_definition
 `moi_ssb_omit (a:real^3) t1 t2 h c0 A =
    {x | x IN c0 /\ (?p. p IN c0 DELETE x /\ a dot p < t1) /\
         (?q. q IN c0 DELETE x /\ t2 < a dot q) /\
         convex hull (c0 DELETE x) INTER {y:real^3 | a dot y = h} SUBSET A}`;;

(* The 3-subsets of a 4-set omit one point.                                *)

let MOI_SSB_THREE_SUBSET = prove
 (`!c0 (w:A->bool).
     FINITE c0 /\ CARD c0 = 4 /\ w SUBSET c0 /\ CARD w = 3
     ==> ?x. x IN c0 /\ w = c0 DELETE x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(c0 DIFF w:A->bool) HAS_SIZE 1` MP_TAC THENL
   [ASM_SIMP_TAC[HAS_SIZE; FINITE_DIFF; CARD_DIFF] THEN ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_TAC `x:A`) THEN EXISTS_TAC `x:A` THEN
  POP_ASSUM MP_TAC THEN UNDISCH_TAC `(w:A->bool) SUBSET c0` THEN SET_TAC[]);;

(* The relative frontier of a polygon is the union of its edges.           *)

let MOI_SSB_POLYGON_EDGES = prove
 (`!c:real^3->bool.
     polytope c /\ aff_dim c = &2
     ==> relative_frontier c = UNIONS {e | e face_of c /\ aff_dim e = &1}`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_POLYHEDRON; POLYTOPE_IMP_POLYHEDRON] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; facet_of] THEN
  X_GEN_TAC `e:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC INT_REDUCE_CONV THEN EQ_TAC THEN SIMP_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `aff_dim({}:real^3->bool) = &1` THEN
  REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC);;

(* Every edge of the section is the section of a crossing 2-face.           *)

let MOI_SSB_EDGE_FACE = prove
 (`!(a:real^3) t1 t2 h c0 e.
     ~affine_dependent c0 /\ CARD c0 = 4 /\ t1 < h /\ h < t2 /\
     (!z. z IN c0 ==> a dot z < t1 \/ t2 < a dot z) /\
     e face_of (convex hull c0 INTER {y | a dot y = h}) /\ aff_dim e = &1
     ==> ?x. x IN c0 /\ (?p. p IN c0 DELETE x /\ a dot p < t1) /\
             (?q. q IN c0 DELETE x /\ t2 < a dot q) /\
             e = convex hull (c0 DELETE x) INTER {y | a dot y = h}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE) THEN
  MP_TAC(ISPECL [`c0:real^3->bool`; `e:real^3->bool`; `a:real^3`; `h:real`]
    MOI_SSL_SECTION_EDGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `t1:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_TAC `p:real^3`)
    (CONJUNCTS_THEN2 (X_CHOOSE_TAC `q:real^3`) SUBST1_TAC))))) THEN
  MP_TAC(ISPECL [`c0:real^3->bool`; `w:real^3->bool`] MOI_SSB_THREE_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^3` (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_DELETE]) THEN
  SUBGOAL_THEN `(p:real^3) IN c0 /\ (q:real^3) IN c0` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(p:real^3) IN c0`) o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `t1:real`)) (concl th))) THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(q:real^3) IN c0`) o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `t1:real`)) (concl th))) THEN
  REPEAT DISCH_TAC THEN
  CONJ_TAC THENL [EXISTS_TAC `p:real^3`; EXISTS_TAC `q:real^3`] THEN
  ASM_REWRITE_TAC[IN_DELETE] THEN ASM_REAL_ARITH_TAC);;

let MOI_SSB_ATTACH_O = prove
 (`!(a:real^3) t1 t2 h c0 A.
     ~affine_dependent c0 /\ CARD c0 = 4 /\ t1 < h /\ h < t2 /\
     (!z. z IN c0 ==> a dot z < t1 \/ t2 < a dot z) /\
     A = UNIONS {e | e face_of (convex hull c0 INTER {y | a dot y = h}) /\
                     aff_dim e = &1 /\ e SUBSET A} /\
     ~(relative_frontier (convex hull c0 INTER {y | a dot y = h}) SUBSET A) /\
     ~(A = {})
     ==> A = UNIONS {convex hull (c0 DELETE x) INTER {y | a dot y = h} | x |
                     x IN moi_ssb_omit a t1 t2 h c0 A} /\
         ~(moi_ssb_omit a t1 t2 h c0 A = {}) /\
         (?z. z IN c0 /\ ~(z IN moi_ssb_omit a t1 t2 h c0 A) /\
              (?p. p IN c0 DELETE z /\ a dot p < t1) /\
              (?q. q IN c0 DELETE z /\ t2 < a dot q))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN
   `A = UNIONS {convex hull (c0 DELETE x) INTER {y:real^3 | a dot y = h} | x |
                x IN moi_ssb_omit a t1 t2 h c0 A}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC LAND_CONV [th]) o check (fun th ->
        is_eq(concl th) && lhs(concl th) = `A:real^3->bool`)) THEN
      REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN
      X_GEN_TAC `e:real^3->bool` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`a:real^3`; `t1:real`; `t2:real`; `h:real`; `c0:real^3->bool`;
                     `e:real^3->bool`] MOI_SSB_EDGE_FACE) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM] THEN
      X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN EXISTS_TAC `x:real^3` THEN
      REWRITE_TAC[moi_ssb_omit; IN_ELIM_THM] THEN
      UNDISCH_TAC `(e:real^3->bool) SUBSET A` THEN UNDISCH_TAC `(u:real^3) IN e` THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[];
      REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC; moi_ssb_omit; IN_ELIM_THM] THEN
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(moi_ssb_omit (a:real^3) t1 t2 h c0 A = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(A:real^3->bool = {})` THEN REWRITE_TAC[] THEN
    FIRST_ASSUM(SUBST1_TAC o check (fun th ->
      is_eq(concl th) && lhs(concl th) = `A:real^3->bool`)) THEN
    REWRITE_TAC[ASSUME `moi_ssb_omit (a:real^3) t1 t2 h c0 A = {}`; NOT_IN_EMPTY] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?p q:real^3. p IN c0 /\ q IN c0 /\ a dot p < h /\ h < a dot q`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(moi_ssb_omit (a:real^3) t1 t2 h c0 A = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; moi_ssb_omit; IN_ELIM_THM; IN_DELETE] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (X_CHOOSE_TAC `p:real^3`) (CONJUNCTS_THEN2
      (X_CHOOSE_TAC `q:real^3`) (K ALL_TAC))))) THEN
    MAP_EVERY EXISTS_TAC [`p:real^3`; `q:real^3`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `A:real^3->bool`))) THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  UNDISCH_TAC `~(relative_frontier (convex hull c0 INTER {y:real^3 | a dot y = h})
                 SUBSET A)` THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `polytope (convex hull c0 INTER {y:real^3 | a dot y = h}) /\
                aff_dim (convex hull c0 INTER {y:real^3 | a dot y = h}) = &2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC POLYTOPE_INTER_POLYHEDRON THEN
      ASM_SIMP_TAC[POLYTOPE_CONVEX_HULL; AFFINE_INDEPENDENT_IMP_FINITE;
                   POLYHEDRON_HYPERPLANE];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c0:real^3->bool`; `c0:real^3->bool`; `a:real^3`; `h:real`;
                   `p:real^3`; `q:real^3`] MOI_SSL_FACE_SECTION) THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
    CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_SSB_POLYGON_EDGES] THEN
  REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `e:real^3->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^3`; `t1:real`; `t2:real`; `h:real`; `c0:real^3->bool`;
                 `e:real^3->bool`] MOI_SSB_EDGE_FACE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^3` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o REWRITE_RULE[NOT_EXISTS_THM] o
    check (fun th -> is_neg(concl th) && is_exists(rand(concl th)))) THEN
  ASM_REWRITE_TAC[moi_ssb_omit; IN_ELIM_THM]);;

(* ------------------------------------------------------------------------- *)
(* The attaching set of a free prism.  Its intersection with the smaller    *)
(* region is the strip of slab faces over the omitted vertices of the faces *)
(* whose sections lie in the arc, and each such face is shared with a       *)
(* 3-simplex of the smaller region.                                         *)
(* ------------------------------------------------------------------------- *)

let MOI_SSB_AFF1_INFINITE = prove
 (`!s:real^N->bool. convex s /\ aff_dim s = &1 ==> INFINITE s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?p q:real^N. p IN s /\ q IN s /\ ~(p = q)` STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `s:real^N->bool = {}` THENL
     [UNDISCH_TAC `aff_dim(s:real^N->bool) = &1` THEN
      ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `?a:real^N. s = {a}` THENL
     [UNDISCH_TAC `aff_dim(s:real^N->bool) = &1` THEN
      FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC) THEN REWRITE_TAC[AFF_DIM_SING] THEN
      INT_ARITH_TAC;
      ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[INFINITE] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`p:real^N`; `q:real^N`] (CONJUNCT1 FINITE_SEGMENT)) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[CONVEX_CONTAINS_SEGMENT]);;

let MOI_SSB_HULL_VERTEX = prove
 (`!c0 w (y:real^3).
     ~affine_dependent c0 /\ w SUBSET c0 /\ y IN c0 /\ y IN convex hull w
     ==> y IN w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{y:real^3}`; `w:real^3->bool`] CONVEX_HULL_INTER) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN EXISTS_TAC `c0:real^3->bool` THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CONVEX_HULL_SING] THEN
  ASM_CASES_TAC `(y:real^3) IN w` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `{y:real^3} INTER w = {}` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[CONVEX_HULL_EMPTY] THEN ASM SET_TAC[]);;

(* Two distinct 3-simplices of k meet in the hull of a proper subset of the *)
(* vertices of the first.                                                   *)

let MOI_SSB_SIMPLEX_MEET = prove
 (`!k t0 t (c0:real^3->bool).
     simplicial_complex k /\ t0 IN k /\ t IN k /\
     aff_dim t0 = &3 /\ aff_dim t = &3 /\ ~(t = t0) /\
     ~affine_dependent c0 /\ t0 = convex hull c0
     ==> ?w. w SUBSET c0 /\ ~(w = c0) /\ t0 INTER t = convex hull w`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    concl th = `t0 = convex hull (c0:real^3->bool)`)) THEN
  MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `t0:real^3->bool`; `t:real^3->bool`]
    MOI_SSL_SC_INTER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c0:real^3->bool`; `t0 INTER t:real^3->bool`]
    FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `w:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  SUBGOAL_THEN `t0 SUBSET (t:real^3->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `t0 INTER t = convex hull (c0:real^3->bool)` THEN
    UNDISCH_TAC `convex hull c0 = t0:real^3->bool` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `t0:real^3->bool`; `t:real^3->bool`]
    MOI_SSB_INTERIOR_DISJ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `t0:real^3->bool`] MOI_SSL_SC_SIMPLEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `t0:real^3->bool` INTERIOR_SUBSET) THEN
  UNDISCH_TAC `t0 SUBSET (t:real^3->bool)` THEN SET_TAC[]);;

(* A point of the level of v common to t0 and a simplex of the smaller      *)
(* region lies in the arc of t0's section.                                  *)

let MOI_SSB_SEC_POINT = prove
 (`!s (a:real^3) lo hi k v t1 t2 pp t0 t z.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ pp SUBSET moi_ssb_prisms k a v t1 t2 /\
     t0 IN pp /\ t IN moi_ssb_mem k v (pp DELETE t0) /\
     z IN t0 /\ z IN t /\ a dot z = a dot v
     ==> z IN (t0 INTER {x | a dot x = a dot v}) INTER
              UNIONS (moi_ssb_secs k a v pp DELETE (t0 INTER {x | a dot x = a dot v}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `t0:real^3->bool`] MOI_SSB_PRISM_BASIC) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `~(interior t0 INTER {x:real^3 | a dot x = a dot v} = {})` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `(t:real^3->bool) IN moi_ssb_mem k v (pp DELETE t0)` THEN
  REWRITE_TAC[moi_ssb_mem; IN_ELIM_THM; IN_DELETE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(z:real^3 = v)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(t:real^3->bool = t0)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `t INTER {x:real^3 | a dot x = a dot v} IN moi_ssb_secs k a v pp`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_ssb_secs; IN_ELIM_THM] THEN EXISTS_TAC `t:real^3->bool` THEN
    REWRITE_TAC[] THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
     [DISJ1_TAC THEN ASM_REWRITE_TAC[moi_ssb_wedges; IN_ELIM_THM] THEN
      MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                     `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                     `t:real^3->bool`] MOI_SSL_STAR) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `~b ==> a \/ b ==> a`) THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `(z:real^3) IN t INTER {x | a dot x = a dot v}` MP_TAC THENL
       [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM]; ASM_REWRITE_TAC[IN_SING]];
      DISJ2_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_INTER; IN_UNIONS; IN_DELETE; IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `t INTER {x:real^3 | a dot x = a dot v}` THEN
  ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `t0:real^3->bool`; `t:real^3->bool`;
                 `a:real^3`; `a dot (v:real^3)`] MOI_SSB_SEC_INJ) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* Each face in O is shared with a 3-simplex of the smaller region.        *)

let MOI_SSB_IDENT_NB = prove
 (`!s (a:real^3) lo hi k v t1 t2 pp t0 c0 A x.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ pp SUBSET moi_ssb_prisms k a v t1 t2 /\
     t0 IN pp /\ ~affine_dependent c0 /\ CARD c0 = 4 /\ convex hull c0 = t0 /\
     (!w. w IN c0 ==> a dot w < t1 \/ t2 < a dot w) /\
     (!e. e face_of (t0 INTER {x | a dot x = a dot v}) /\ aff_dim e = &1 /\ e SUBSET A
          ==> ?d. d IN moi_ssb_secs k a v pp /\
                  ~(d = t0 INTER {x | a dot x = a dot v}) /\ e SUBSET d) /\
     x IN moi_ssb_omit a t1 t2 (a dot v) c0 A
     ==> ?t. t IN moi_ssb_mem k v (pp DELETE t0) /\
             t0 INTER t = convex hull (c0 DELETE x)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "edge") MP_TAC)))))))) THEN
  REWRITE_TAC[moi_ssb_omit; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_TAC `p:real^3`)
    (CONJUNCTS_THEN2 (X_CHOOSE_TAC `q:real^3`) ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `t0:real^3->bool`] MOI_SSB_PRISM_BASIC) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`c0:real^3->bool`; `c0 DELETE (x:real^3)`; `a:real^3`;
                 `a dot (v:real^3)`; `p:real^3`; `q:real^3`] MOI_SSL_FACE_SECTION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[DELETE_SUBSET] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_DELETE] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC INT_REDUCE_CONV THEN STRIP_TAC THEN
  USE_THEN "edge" (MP_TAC o SPEC
    `convex hull (c0 DELETE x) INTER {y:real^3 | a dot y = a dot v}`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `pp:(real^3->bool)->bool`; `d:real^3->bool`] MOI_SSB_SECS_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(t:real^3->bool = t0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `t:real^3->bool` THEN CONJ_TAC THENL
   [REWRITE_TAC[moi_ssb_mem; IN_ELIM_THM; IN_DELETE] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
     [DISJ1_TAC THEN UNDISCH_TAC `(t:real^3->bool) IN moi_ssb_wedges k a v` THEN
      SIMP_TAC[moi_ssb_wedges; IN_ELIM_THM];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `t0:real^3->bool`; `t:real^3->bool`;
                 `c0:real^3->bool`] MOI_SSB_SIMPLEX_MEET) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3->bool` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `convex hull (c0 DELETE x) SUBSET convex hull (w:real^3->bool)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `t0 INTER t = convex hull (w:real^3->bool)`)) THEN
    MATCH_MP_TAC SUBSET_OF_FACE_OF THEN EXISTS_TAC `t0:real^3->bool` THEN
    MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `t0:real^3->bool`; `t:real^3->bool`]
      MOI_SSL_SC_INTER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `convex hull c0 = t0:real^3->bool` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `~(relative_interior (convex hull (c0 DELETE x)) INTER
                   {x:real^3 | a dot x = a dot v} = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; DISJOINT; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(y:real^3) IN convex hull (c0 DELETE x)` ASSUME_TAC THENL
     [MP_TAC(ISPEC `convex hull (c0 DELETE x:real^3)` RELATIVE_INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(y:real^3) IN relative_interior (convex hull (c0 DELETE x))` THEN
      SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `convex hull c0 = t0:real^3->bool` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `(y:real^3) IN convex hull (c0 DELETE x)` THEN
      SPEC_TAC(`y:real^3`,`y:real^3`) THEN REWRITE_TAC[GSYM SUBSET] THEN
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`convex hull (c0 DELETE x) INTER {y:real^3 | a dot y = a dot v} SUBSET d`;
        `(y:real^3) IN {x | a dot x = a dot v}`;
        `(y:real^3) IN convex hull (c0 DELETE x)`;
        `d = t INTER {x:real^3 | a dot x = a dot v}`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_DELETE] THEN X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN
    CONJ_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST_ALL_TAC] THEN
    UNDISCH_TAC `~(w:real^3->bool = c0)` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    ASM_CASES_TAC `y:real^3 = x` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_SSB_HULL_VERTEX THEN EXISTS_TAC `c0:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      concl th = `convex hull (c0 DELETE x) SUBSET convex hull (w:real^3->bool)`)) THEN
    MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[IN_DELETE];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_DELETE] THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_SSB_HULL_VERTEX THEN EXISTS_TAC `c0:real^3->bool` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
    concl th = `convex hull (c0 DELETE x) SUBSET convex hull (w:real^3->bool)`)) THEN
  MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[IN_DELETE]);;

(* Every point of the attaching set lies in the slab part of a face in O.  *)

let MOI_SSB_IDENT_SUB = prove
 (`!s (a:real^3) lo hi k v t1 t2 pp t0 c0 A u.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ pp SUBSET moi_ssb_prisms k a v t1 t2 /\
     t0 IN pp /\ ~affine_dependent c0 /\ CARD c0 = 4 /\ convex hull c0 = t0 /\
     (!w. w IN c0 ==> a dot w < t1 \/ t2 < a dot w) /\
     (t0 INTER {x | a dot x = a dot v}) INTER
       UNIONS (moi_ssb_secs k a v pp DELETE (t0 INTER {x | a dot x = a dot v})) = A /\
     (!z. z IN A ==> ?x. x IN moi_ssb_omit a t1 t2 (a dot v) c0 A /\
                         z IN convex hull (c0 DELETE x) INTER {y | a dot y = a dot v}) /\
     u IN (t0 INTER {x | t1 <= a dot x /\ a dot x <= t2}) INTER
          moi_ssb_reg k a v t1 t2 (pp DELETE t0)
     ==> ?x. x IN moi_ssb_omit a t1 t2 (a dot v) c0 A /\
             u IN convex hull (c0 DELETE x) INTER {y | t1 <= a dot y /\ a dot y <= t2}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "out") (CONJUNCTS_THEN2 (LABEL_TAC "aeq")
    (CONJUNCTS_THEN2 (LABEL_TAC "acov") MP_TAC))))))))) THEN
  REWRITE_TAC[IN_INTER; moi_ssb_reg; UNIONS_GSPEC; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)
    (X_CHOOSE_THEN `t:real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `t0:real^3->bool`] MOI_SSB_PRISM_BASIC) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(t:real^3->bool) IN k /\ aff_dim t = &3 /\ ~(t = t0)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(t:real^3->bool) IN moi_ssb_mem k v (pp DELETE t0)` THEN
    REWRITE_TAC[moi_ssb_mem; IN_ELIM_THM; IN_DELETE] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `t0:real^3->bool`; `t:real^3->bool`;
                 `c0:real^3->bool`] MOI_SSB_SIMPLEX_MEET) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(u:real^3) IN convex hull w` ASSUME_TAC THENL
   [UNDISCH_TAC `t0 INTER t = convex hull (w:real^3->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. z IN convex hull w /\ a dot z = a dot v ==> z IN A`
  (LABEL_TAC "pt") THENL
   [X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    USE_THEN "aeq" (SUBST1_TAC o SYM) THEN MATCH_MP_TAC MOI_SSB_SEC_POINT THEN
    MAP_EVERY EXISTS_TAC [`s:real^3->bool`; `lo:real`; `hi:real`; `t1:real`; `t2:real`;
                          `t:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(z:real^3) IN convex hull w` THEN
    UNDISCH_TAC `t0 INTER t = convex hull (w:real^3->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN SIMP_TAC[IN_INTER];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`w:real^3->bool`; `a:real^3`; `t1:real`; `t2:real`; `u:real^3`]
    MOI_SSL_HULL_CROSS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `p:real^3` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(p:real^3 = q)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (w:real^3->bool) /\ CARD w < 4` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
    UNDISCH_TAC `CARD (c0:real^3->bool) = 4` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC CARD_PSUBSET THEN ASM_REWRITE_TAC[PSUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 <= CARD (w:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`{p:real^3,q}`; `w:real^3->bool`] CARD_SUBSET) THEN
    ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
    ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `CARD (w:real^3->bool) = 3` THENL
   [MP_TAC(ISPECL [`c0:real^3->bool`; `w:real^3->bool`] MOI_SSB_THREE_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `x:real^3` THEN
    REWRITE_TAC[moi_ssb_omit; IN_ELIM_THM; IN_INTER] THEN
    UNDISCH_TAC `w = c0 DELETE (x:real^3)` THEN DISCH_THEN(SUBST_ALL_TAC) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXISTS_TAC `p:real^3` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `q:real^3` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN USE_THEN "pt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `w = {p:real^3,q}` SUBST_ALL_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_SUBSET_EQ THEN
    ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    UNDISCH_TAC `CARD (w:real^3->bool) < 4` THEN UNDISCH_TAC `2 <= CARD (w:real^3->bool)` THEN
    UNDISCH_TAC `~(CARD (w:real^3->bool) = 3)` THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`convex hull {p:real^3,q}`; `a:real^3`; `a dot (v:real^3)`;
                 `p:real^3`; `q:real^3`] MOI_SSL_RELINT_LEVEL) THEN
  ANTS_TAC THENL
   [SIMP_TAC[CONVEX_CONVEX_HULL; HULL_INC; IN_INSERT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(z:real^3) IN A` MP_TAC THENL
   [USE_THEN "pt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> USE_THEN "acov" (MP_TAC o C MATCH_MP th)) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:real^3` THEN
  REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `convex hull {p:real^3,q} SUBSET convex hull (c0 DELETE x)` MP_TAC THENL
   [MATCH_MP_TAC SUBSET_OF_FACE_OF THEN EXISTS_TAC `convex hull c0:real^3->bool` THEN
    REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
      EXISTS_TAC `c0 DELETE (x:real^3)` THEN REWRITE_TAC[DELETE_SUBSET];
      MATCH_MP_TAC HULL_MONO THEN ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET];
      REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[]];
    UNDISCH_TAC `(u:real^3) IN convex hull {p,q}` THEN SET_TAC[]]);;

let MOI_SSB_ATTACH_IDENT = prove
 (`!s (a:real^3) lo hi k v t1 t2 pp t0 c0 A.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ pp SUBSET moi_ssb_prisms k a v t1 t2 /\
     t0 IN pp /\ ~affine_dependent c0 /\ CARD c0 = 4 /\ convex hull c0 = t0 /\
     (!w. w IN c0 ==> a dot w < t1 \/ t2 < a dot w) /\
     (t0 INTER {x | a dot x = a dot v}) INTER
       UNIONS (moi_ssb_secs k a v pp DELETE (t0 INTER {x | a dot x = a dot v})) = A /\
     (!z. z IN A ==> ?x. x IN moi_ssb_omit a t1 t2 (a dot v) c0 A /\
                         z IN convex hull (c0 DELETE x) INTER {y | a dot y = a dot v}) /\
     (!e. e face_of (t0 INTER {x | a dot x = a dot v}) /\ aff_dim e = &1 /\ e SUBSET A
          ==> ?d. d IN moi_ssb_secs k a v pp /\
                  ~(d = t0 INTER {x | a dot x = a dot v}) /\ e SUBSET d)
     ==> (t0 INTER {x | t1 <= a dot x /\ a dot x <= t2}) INTER
           moi_ssb_reg k a v t1 t2 (pp DELETE t0) =
         UNIONS {convex hull (c0 DELETE x) INTER {y | t1 <= a dot y /\ a dot y <= t2} | x |
                 x IN moi_ssb_omit a t1 t2 (a dot v) c0 A}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
    MATCH_MP_TAC MOI_SSB_IDENT_SUB THEN
    MAP_EVERY EXISTS_TAC [`s:real^3->bool`; `lo:real`; `hi:real`; `k:(real^3->bool)->bool`;
                          `pp:(real^3->bool)->bool`; `t0:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                   `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                   `pp:(real^3->bool)->bool`; `t0:real^3->bool`; `c0:real^3->bool`;
                   `A:real^3->bool`; `x:real^3`] MOI_SSB_IDENT_NB) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[SUBSET; IN_INTER; moi_ssb_reg; UNIONS_GSPEC; IN_ELIM_THM] THEN
    X_GEN_TAC `u:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(u:real^3) IN t0 INTER t` MP_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The planar picture at the level of v.  Points of the level in the filled *)
(* sphere other than v lie in crossing 3-simplices; for a set pp of prisms  *)
(* whose sections form a PL 2-cell with boundary j, a point of the cell off *)
(* j sees only kept simplices, and a point of j off s lies in a prism       *)
(* outside pp.                                                              *)
(* ------------------------------------------------------------------------- *)

let MOI_SSB_LEVEL_COVER = prove
 (`!s (a:real^3) lo hi k v t1 t2 y.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ y IN s UNION inside s /\
     a dot y = a dot v /\ ~(y = v)
     ==> ?t. t IN k /\ aff_dim t = &3 /\ y IN t /\
             ~(interior t INTER {x | a dot x = a dot v} = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSL_SLAB_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  MP_TAC(ISPEC `k:(real^3->bool)->bool` MOI_SSL_PURE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^3` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `t:real^3->bool`] MOI_SSL_SIMPLEX_HULL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    concl th = `t = convex hull (c:real^3->bool)`)) THEN
  MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `t:real^3->bool`] MOI_SSL_SC_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!w:real^3. w IN c ==> w = v \/ a dot w < t1 \/ t2 < a dot w`
  (LABEL_TAC "tri") THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `t1:real`)) (concl th) &&
      can (find_term ((=) `v:real^3`)) (concl th))) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN convex hull c` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `(?w1:real^3. w1 IN c /\ a dot w1 < t1) /\
                 (?w2:real^3. w2 IN c /\ t2 < a dot w2)` THENL
   [FIRST_X_ASSUM(CONJUNCTS_THEN2 (X_CHOOSE_TAC `w1:real^3`) (X_CHOOSE_TAC `w2:real^3`)) THEN
    MATCH_MP_TAC MOI_SSL_INTERIOR_LEVEL THEN
    MAP_EVERY EXISTS_TAC [`w1:real^3`; `w2:real^3`] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `convex hull c = t:real^3->bool` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `convex hull c = t:real^3->bool` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[DE_MORGAN_THM]) THENL
   [ASM_CASES_TAC `(v:real^3) IN c` THENL
     [MP_TAC(ISPECL [`c:real^3->bool`; `a:real^3`; `v:real^3`] MOI_SSL_HULL_ONE_SIDE) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
        USE_THEN "tri" (MP_TAC o SPEC `w:real^3`) THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[REAL_LT_TRANS];
        ALL_TAC] THEN
      REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_SING] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`c:real^3->bool`; `a:real^3`; `t2:real`; `y:real^3`]
        MOI_SSL_HULL_GT) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
        USE_THEN "tri" (MP_TAC o SPEC `w:real^3`) THEN ASM_REWRITE_TAC[] THEN
        ASM_CASES_TAC `w:real^3 = v` THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]] THEN
        ASM_MESON_TAC[REAL_NOT_LT; REAL_LT_TRANS; REAL_LE_LT];
        ASM_REAL_ARITH_TAC]];
    ASM_CASES_TAC `(v:real^3) IN c` THENL
     [MP_TAC(ISPECL [`c:real^3->bool`; `a:real^3`; `v:real^3`] MOI_SSL_HULL_ONE_SIDE_LT) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
        USE_THEN "tri" (MP_TAC o SPEC `w:real^3`) THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[REAL_LT_TRANS];
        ALL_TAC] THEN
      REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_SING] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`c:real^3->bool`; `a:real^3`; `t1:real`; `y:real^3`]
        MOI_SSL_HULL_LT) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
        USE_THEN "tri" (MP_TAC o SPEC `w:real^3`) THEN ASM_REWRITE_TAC[] THEN
        ASM_CASES_TAC `w:real^3 = v` THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]] THEN
        ASM_MESON_TAC[REAL_NOT_LT; REAL_LT_TRANS; REAL_LE_LT];
        ASM_REAL_ARITH_TAC]]]);;

(* The union of the sections is a plane set in the fibre at the level of v. *)

let MOI_SSB_FCELL = prove
 (`!s (a:real^3) lo hi k v t1 t2 pp j.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ pp SUBSET moi_ssb_prisms k a v t1 t2 /\
     pl_cell_with_boundary 2 (UNIONS (moi_ssb_secs k a v pp)) j
     ==> relative_frontier (UNIONS (moi_ssb_secs k a v pp)) = j /\
         relative_interior (UNIONS (moi_ssb_secs k a v pp)) =
           UNIONS (moi_ssb_secs k a v pp) DIFF j /\
         j SUBSET UNIONS (moi_ssb_secs k a v pp) /\
         compact (UNIONS (moi_ssb_secs k a v pp)) /\
         affine hull (UNIONS (moi_ssb_secs k a v pp)) = {x | a dot x = a dot v} /\
         UNIONS (moi_ssb_secs k a v pp) SUBSET
           (s UNION inside s) INTER {x | a dot x = a dot v}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `pp:(real^3->bool)->bool`] MOI_SSB_SECS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^3`; `a dot (v:real^3)`; `UNIONS (moi_ssb_secs k a v pp)`;
                 `j:real^3->bool`] MOI_SSL_PLANE_CELL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[UNIONS_SUBSET] THEN ASM_MESON_TAC[]; SIMP_TAC[]] THEN
  STRIP_TAC THEN REWRITE_TAC[UNIONS_SUBSET; SUBSET_INTER] THEN
  X_GEN_TAC `c:real^3->bool` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `pp:(real^3->bool)->bool`; `c:real^3->bool`] MOI_SSB_SECS_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `UNIONS k = (s:real^3->bool) UNION inside s` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC(SET_RULE `(t:real^3->bool) IN k ==> t INTER e SUBSET UNIONS k`) THEN
    ASM_REWRITE_TAC[];
    SET_TAC[]]);;

(* A point of the cell off its boundary sees only wedges and prisms of pp. *)

let MOI_SSB_PLANE_INT = prove
 (`!s (a:real^3) lo hi k v t1 t2 pp j z t.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ pp SUBSET moi_ssb_prisms k a v t1 t2 /\
     pl_cell_with_boundary 2 (UNIONS (moi_ssb_secs k a v pp)) j /\
     z IN UNIONS (moi_ssb_secs k a v pp) /\ ~(z IN j) /\
     t IN k /\ aff_dim t = &3 /\ z IN t /\
     ~(interior t INTER {x | a dot x = a dot v} = {})
     ==> t IN moi_ssb_wedges k a v \/ t IN pp`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `pp:(real^3->bool)->bool`; `j:real^3->bool`] MOI_SSB_FCELL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z:real^3) IN relative_interior (UNIONS (moi_ssb_secs k a v pp))`
  MP_TAC THENL [ASM_REWRITE_TAC[IN_DIFF]; ALL_TAC] THEN
  REWRITE_TAC[relative_interior; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `uu:real^3->bool` STRIP_ASSUME_TAC o
    REWRITE_RULE[OPEN_IN_OPEN] o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "open_in" with _ -> false)) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `t:real^3->bool`; `a dot (v:real^3)`] MOI_SSB_SEC_CELL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `closure (interior t INTER {x:real^3 | a dot x = a dot v}) =
                t INTER {x | a dot x = a dot v}` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && is_comb(lhs(concl th)) &&
      rator(lhs(concl th)) = `relative_interior:(real^3->bool)->real^3->bool`)) THEN
    MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `t:real^3->bool`] MOI_SSL_SC_SIMPLEX) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CONVEX_INTER; CONVEX_HYPERPLANE;
                 CLOSURE_CLOSED; CLOSED_INTER; CLOSED_HYPERPLANE];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((uu:real^3->bool) INTER (interior t INTER {x | a dot x = a dot v}) = {})`
  MP_TAC THENL
   [MP_TAC(ISPECL [`uu:real^3->bool`; `interior t INTER {x:real^3 | a dot x = a dot v}`]
      OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM] THEN
    EXISTS_TAC `z:real^3` THEN
    SUBGOAL_THEN `(z:real^3) IN {x | a dot x = a dot v} INTER uu` MP_TAC THENL
     [ASM_MESON_TAC[]; REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN STRIP_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:real^3) IN UNIONS (moi_ssb_secs k a v pp)` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      is_binary "SUBSET" (concl th) && lhand(concl th) = `u:real^3->bool`)) THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `pp:(real^3->bool)->bool`; `c:real^3->bool`] MOI_SSB_SECS_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t':real^3->bool` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  ASM_CASES_TAC `t':real^3->bool = t` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `t:real^3->bool`; `t':real^3->bool`]
    MOI_SSB_INTERIOR_DISJ) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `y:real^3` THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(y:real^3) IN c` THEN ASM_REWRITE_TAC[IN_INTER] THEN SIMP_TAC[]);;

(* A boundary point of the cell off s and off v lies in a prism not in pp. *)

let MOI_SSB_PLANE_FR = prove
 (`!s (a:real^3) lo hi k v t1 t2 pp j z.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ pp SUBSET moi_ssb_prisms k a v t1 t2 /\
     pl_cell_with_boundary 2 (UNIONS (moi_ssb_secs k a v pp)) j /\
     z IN j /\ ~(z IN s) /\ ~(z = v)
     ==> ?t. t IN moi_ssb_prisms k a v t1 t2 /\ ~(t IN pp) /\ z IN t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSL_SLAB_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `pp:(real^3->bool)->bool`; `j:real^3->bool`] MOI_SSB_FCELL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  ABBREV_TAC `kk = {t:real^3->bool | t IN k /\ aff_dim t = &3 /\
                     ~(interior t INTER {x | a dot x = a dot v} = {}) /\
                     ~(t IN moi_ssb_wedges k a v \/ t IN pp)}` THEN
  SUBGOAL_THEN `~((z:real^3) IN UNIONS kk)` ASSUME_TAC THENL
   [EXPAND_TAC "kk" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; DE_MORGAN_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real^3->bool` o REWRITE_RULE[NOT_EXISTS_THM] o
      check (fun th -> is_neg(concl th) && is_exists(rand(concl th)))) THEN
    ASM_REWRITE_TAC[moi_ssb_prisms; IN_ELIM_THM] THEN
    ASM_CASES_TAC `(v:real^3) IN t` THENL
     [UNDISCH_TAC `~((t:real^3->bool) IN moi_ssb_wedges k a v)` THEN
      ASM_REWRITE_TAC[moi_ssb_wedges; IN_ELIM_THM];
      ASM_REWRITE_TAC[]] THEN
    UNDISCH_TAC `~(interior t INTER {x:real^3 | a dot x = a dot v} = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `y:real^3` THEN CONJ_TAC THENL
     [MP_TAC(ISPEC `t:real^3->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(y:real^3) IN interior t` THEN SET_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (UNIONS kk:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `k:(real^3->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "kk" THEN SET_TAC[];
      EXPAND_TAC "kk" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `t:real^3->bool` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `t:real^3->bool`] MOI_SSL_SC_SIMPLEX) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?r1. &0 < r1 /\ ball(z:real^3,r1) INTER UNIONS kk = {}`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `(:real^3) DIFF UNIONS kk` OPEN_CONTAINS_BALL) THEN
    ASM_REWRITE_TAC[GSYM closed] THEN DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3) IN inside s` ASSUME_TAC THENL
   [UNDISCH_TAC `j SUBSET UNIONS (moi_ssb_secs k a v pp)` THEN
    UNDISCH_TAC `UNIONS (moi_ssb_secs k a v pp) SUBSET
                 (s UNION inside s) INTER {x:real^3 | a dot x = a dot v}` THEN
    UNDISCH_TAC `(z:real^3) IN j` THEN UNDISCH_TAC `~((z:real^3) IN s)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?r2. &0 < r2 /\ ball(z:real^3,r2) SUBSET inside s` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `inside s:real^3->bool` OPEN_CONTAINS_BALL) THEN
    ASM_SIMP_TAC[OPEN_INSIDE] THEN DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3) IN relative_interior (UNIONS (moi_ssb_secs k a v pp))`
  MP_TAC THENL
   [REWRITE_TAC[relative_interior; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `{x:real^3 | a dot x = a dot v} INTER ball(z,min r1 (min r2 (dist(z,v))))` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN REWRITE_TAC[OPEN_BALL];
      REWRITE_TAC[IN_INTER; IN_ELIM_THM; CENTRE_IN_BALL] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `j SUBSET UNIONS (moi_ssb_secs k a v pp)` THEN
        UNDISCH_TAC `UNIONS (moi_ssb_secs k a v pp) SUBSET
                     (s UNION inside s) INTER {x:real^3 | a dot x = a dot v}` THEN
        UNDISCH_TAC `(z:real^3) IN j` THEN SET_TAC[];
        ASM_SIMP_TAC[REAL_LT_MIN; DIST_POS_LT]];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; IN_BALL; REAL_LT_MIN] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                   `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                   `y:real^3`] MOI_SSB_LEVEL_COVER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC(SET_RULE `(y:real^3) IN i ==> y IN s UNION i`) THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
          is_binary "SUBSET" (concl th) && rand(concl th) = `inside s:real^3->bool`)) THEN
        ASM_REWRITE_TAC[IN_BALL];
        DISCH_THEN SUBST_ALL_TAC THEN
        UNDISCH_TAC `dist(z:real^3,v) < dist(z,v)` THEN REWRITE_TAC[REAL_LT_REFL]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `(t:real^3->bool) IN moi_ssb_wedges k a v \/ t IN pp` THENL
     [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `t INTER {x:real^3 | a dot x = a dot v}` THEN
      ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; moi_ssb_secs] THEN
      EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `ball(z:real^3,r1) INTER UNIONS kk = {}` THEN
      REWRITE_TAC[EXTENSION; IN_INTER; IN_BALL; IN_UNIONS; NOT_IN_EMPTY] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
      EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "kk" THEN ASM_REWRITE_TAC[IN_ELIM_THM]];
    ASM_REWRITE_TAC[IN_DIFF]]);;

(* A point of the cell on s lies on its boundary j.                         *)

let MOI_SSB_FCELL_S = prove
 (`!s (a:real^3) lo hi k v t1 t2 pp j z.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ pp SUBSET moi_ssb_prisms k a v t1 t2 /\
     pl_cell_with_boundary 2 (UNIONS (moi_ssb_secs k a v pp)) j /\
     z IN UNIONS (moi_ssb_secs k a v pp) /\ z IN s
     ==> z IN j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSL_SLAB_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `pp:(real^3->bool)->bool`; `j:real^3->bool`] MOI_SSB_FCELL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a dot (v:real^3)` o check (fun th ->
    is_forall(concl th) && can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "pl_cell_with_boundary")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`a:real^3`; `a dot (v:real^3)`;
                 `(s UNION inside s) INTER {x:real^3 | a dot x = a dot v}`;
                 `s INTER {x:real^3 | a dot x = a dot v}`] MOI_SSL_PLANE_CELL) THEN
  ASM_REWRITE_TAC[INTER_SUBSET] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`UNIONS (moi_ssb_secs k a v pp):real^3->bool`;
                 `(s UNION inside s) INTER {x:real^3 | a dot x = a dot v}`]
    SUBSET_RELATIVE_INTERIOR) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(z:real^3) IN UNIONS (moi_ssb_secs k a v pp)` THEN
  UNDISCH_TAC `UNIONS (moi_ssb_secs k a v pp) SUBSET
               (s UNION inside s) INTER {x:real^3 | a dot x = a dot v}` THEN
  UNDISCH_TAC `(z:real^3) IN s` THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The ends of the arc of a free cell lie on edges outside the arc (the     *)
(* complementary arc rf c INTER j is connected and has no isolated points), *)
(* so a vertex of the cell all of whose edges lie in the arc is not on the  *)
(* boundary j of the cell complex.                                          *)
(* ------------------------------------------------------------------------- *)

let MOI_SSB_ENDS = prove
 (`!c j (bb:real^1->real^3) z.
     polytope c /\ aff_dim c = &2 /\ closed j /\
     arc bb /\ path_image bb SUBSET relative_frontier c /\
     (relative_frontier c INTER j) INTER path_image bb = {pathstart bb, pathfinish bb} /\
     connected (relative_frontier c INTER j) /\
     z IN path_image bb /\
     (!e. e face_of c /\ aff_dim e = &1 /\ z IN e ==> e SUBSET path_image bb)
     ==> ~(z IN j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `jj = relative_frontier c INTER (j:real^3->bool)` THEN
  SUBGOAL_THEN `(z:real^3) IN jj` ASSUME_TAC THENL
   [EXPAND_TAC "jj" THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `z = pathstart (bb:real^1->real^3) \/ z = pathfinish bb` ASSUME_TAC THENL
   [UNDISCH_TAC `jj INTER path_image bb = {pathstart (bb:real^1->real^3), pathfinish bb}` THEN
    UNDISCH_TAC `(z:real^3) IN jj` THEN UNDISCH_TAC `(z:real^3) IN path_image bb` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?w:real^3. w IN jj /\ ~(w = z) /\ w IN path_image bb /\
                (pathstart bb = z \/ pathstart bb = w) /\
                (pathfinish bb = z \/ pathfinish bb = w)`
  (X_CHOOSE_THEN `w:real^3` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THENL
   [FIRST_ASSUM(ASSUME_TAC o MATCH_MP ARC_DISTINCT_ENDS) THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
     [EXISTS_TAC `pathfinish (bb:real^1->real^3)`;
      EXISTS_TAC `pathstart (bb:real^1->real^3)`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `jj INTER path_image bb = {pathstart (bb:real^1->real^3), pathfinish bb}` THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `nn = UNIONS {e:real^3->bool | e face_of c /\ aff_dim e = &1 /\
                                         ~(e SUBSET path_image bb)}` THEN
  SUBGOAL_THEN `closed (nn:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "nn" THEN MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{e:real^3->bool | e face_of c}` THEN
      ASM_SIMP_TAC[FINITE_POLYTOPE_FACES] THEN SET_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC FACE_OF_IMP_COMPACT THEN
      EXISTS_TAC `c:real^3->bool` THEN ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX; POLYTOPE_IMP_COMPACT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN jj /\ ~(y = z) /\ ~(y = w) ==> y IN nn` ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~((y:real^3) IN path_image bb)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `jj INTER path_image bb = {pathstart (bb:real^1->real^3), pathfinish bb}` THEN
      REWRITE_TAC[EXTENSION; IN_INTER; IN_INSERT; NOT_IN_EMPTY] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^3) IN relative_frontier c` MP_TAC THENL
     [EXPAND_TAC "jj" THEN UNDISCH_TAC `(y:real^3) IN jj` THEN EXPAND_TAC "jj" THEN
      SET_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[MOI_SSB_POLYGON_EDGES; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real^3->bool` STRIP_ASSUME_TAC) THEN
    EXPAND_TAC "nn" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `e:real^3->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3) IN nn` MP_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[CLOSED_LIMPT] o check (fun th ->
      concl th = `closed (nn:real^3->bool)`)) THEN
    REWRITE_TAC[LIMPT_APPROACHABLE] THEN X_GEN_TAC `d:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`jj:real^3->bool`; `z:real^3`] CONNECTED_IMP_PERFECT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `q:real^3`) THEN
      UNDISCH_TAC `(w:real^3) IN jj` THEN UNDISCH_TAC `(z:real^3) IN jj` THEN
      ASM_REWRITE_TAC[IN_SING] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[LIMPT_APPROACHABLE] THEN
    DISCH_THEN(MP_TAC o SPEC `min d (dist(z:real^3,w))`) THEN
    ASM_SIMP_TAC[REAL_LT_MIN; DIST_POS_LT] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `dist(w:real^3,z) < dist(z,w)` THEN REWRITE_TAC[DIST_SYM; REAL_LT_REFL];
    ALL_TAC] THEN
  EXPAND_TAC "nn" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^3->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real^3->bool` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `z:real^3`)) (concl th))) THEN
  ASM_REWRITE_TAC[]);;

(* The boundary of a PL 2-cell is closed.                                  *)

let MOI_SSB_CELL_BOUNDARY_CLOSED = prove
 (`!d j:real^3->bool. pl_cell_with_boundary 2 d j ==> closed j`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MOI_SS2_CELL_FACTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
  MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `k:real^3->bool` THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[pl_homeomorphism; homeomorphism];
      REWRITE_TAC[relative_frontier] THEN
      SUBGOAL_THEN `closed (k:real^3->bool)` (fun th -> SIMP_TAC[th; CLOSURE_CLOSED]) THENL
       [ASM_MESON_TAC[simplex; COMPACT_IMP_CLOSED; COMPACT_CONVEX_HULL;
                      FINITE_IMP_COMPACT; AFFINE_INDEPENDENT_IMP_FINITE];
        SET_TAC[]]];
    MATCH_MP_TAC COMPACT_RELATIVE_FRONTIER_BOUNDED THEN
    ASM_MESON_TAC[simplex; COMPACT_IMP_BOUNDED; COMPACT_CONVEX_HULL;
                  FINITE_IMP_COMPACT; AFFINE_INDEPENDENT_IMP_FINITE]]);;

(* A slab point of a crossing edge is in its relative interior.            *)

let MOI_SSB_PAIR_REL = prove
 (`!(a:real^3) t1 t2 p q u.
     a dot p < t1 /\ t2 < a dot q /\ u IN convex hull {p,q} /\
     t1 < a dot u /\ a dot u < t2
     ==> u IN relative_interior (convex hull {p,q})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(p:real^3 = q)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM SEGMENT_CONVEX_HULL]) THEN
  ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; RELATIVE_INTERIOR_SEGMENT; open_segment;
                  IN_DIFF; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
  CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC);;

(* The setting of one deletion step: a prism t0 of pp whose section is free *)
(* in the cell complex of the sections, with the data of MOI_SSL_FREE_PLANE *)
(* and of MOI_SSB_ATTACH_O.                                                 *)

let moi_ssb_free = new_definition
 `moi_ssb_free s (a:real^3) lo hi k v t1 t2 pp t0 c0 j (bb:real^1->real^3) <=>
    moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ pp SUBSET moi_ssb_prisms k a v t1 t2 /\
    t0 IN pp /\ ~affine_dependent c0 /\ CARD c0 = 4 /\ convex hull c0 = t0 /\
    (!w. w IN c0 ==> a dot w < t1 \/ t2 < a dot w) /\
    pl_cell_with_boundary 2 (UNIONS (moi_ssb_secs k a v pp)) j /\
    arc bb /\ path_image bb SUBSET relative_frontier (t0 INTER {x | a dot x = a dot v}) /\
    (t0 INTER {x | a dot x = a dot v}) INTER
      UNIONS (moi_ssb_secs k a v pp DELETE (t0 INTER {x | a dot x = a dot v})) =
      path_image bb /\
    (relative_frontier (t0 INTER {x | a dot x = a dot v}) INTER j) INTER path_image bb =
      {pathstart bb, pathfinish bb} /\
    (relative_frontier (t0 INTER {x | a dot x = a dot v}) INTER j) UNION path_image bb =
      relative_frontier (t0 INTER {x | a dot x = a dot v}) /\
    connected (relative_frontier (t0 INTER {x | a dot x = a dot v}) INTER j) /\
    (!e. e face_of (t0 INTER {x | a dot x = a dot v}) /\ aff_dim e = &1 /\
         e SUBSET path_image bb
         ==> ?d. d IN moi_ssb_secs k a v pp /\
                 ~(d = t0 INTER {x | a dot x = a dot v}) /\ e SUBSET d) /\
    (!z. z IN path_image bb
         ==> ?x. x IN moi_ssb_omit a t1 t2 (a dot v) c0 (path_image bb) /\
                 z IN convex hull (c0 DELETE x) INTER {y | a dot y = a dot v}) /\
    ~(moi_ssb_omit a t1 t2 (a dot v) c0 (path_image bb) = {}) /\
    (?z. z IN c0 /\ ~(z IN moi_ssb_omit a t1 t2 (a dot v) c0 (path_image bb)) /\
         (?p. p IN c0 DELETE z /\ a dot p < t1) /\
         (?q. q IN c0 DELETE z /\ t2 < a dot q))`;;

(* A point of the open slab in the relative interior of a face in O is     *)
(* interior to the region: the face is shared by t0 and a kept simplex.     *)

let MOI_SSB_CRIT_FACE = prove
 (`!s (a:real^3) lo hi k v t1 t2 pp t0 c0 j bb x u.
     moi_ssb_free s a lo hi k v t1 t2 pp t0 c0 j bb /\
     x IN moi_ssb_omit a t1 t2 (a dot v) c0 (path_image bb) /\
     u IN relative_interior (convex hull (c0 DELETE x)) /\
     t1 < a dot u /\ a dot u < t2
     ==> u IN interior (moi_ssb_reg k a v t1 t2 pp)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_ssb_free] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `pp:(real^3->bool)->bool`; `t0:real^3->bool`; `c0:real^3->bool`;
                 `path_image (bb:real^1->real^3)`; `x:real^3`] MOI_SSB_IDENT_NB) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `t0:real^3->bool`] MOI_SSB_PRISM_BASIC) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(t:real^3->bool) IN k /\ aff_dim t = &3 /\
                t IN moi_ssb_mem k v pp` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(t:real^3->bool) IN moi_ssb_mem k v (pp DELETE t0)` THEN
    REWRITE_TAC[moi_ssb_mem; IN_ELIM_THM; IN_DELETE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(t0:real^3->bool) IN moi_ssb_mem k v pp` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[moi_ssb_mem; IN_ELIM_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `t0:real^3->bool`; `t:real^3->bool`]
    MOI_SSL_SC_INTER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `t0:real^3->bool`] MOI_SSL_SC_SIMPLEX) THEN
  MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `t:real^3->bool`] MOI_SSL_SC_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t0:real^3->bool`; `t:real^3->bool`; `convex hull (c0 DELETE x:real^3)`;
                 `u:real^3`] MOI_SSL_TWO_CELL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^3) IN moi_ssb_omit a t1 t2 (a dot v) c0 (path_image bb)` THEN
    REWRITE_TAC[moi_ssb_omit; IN_ELIM_THM] THEN STRIP_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `aff_dim ((c0:real^3->bool) DELETE x)` THEN
    REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN
    SUBGOAL_THEN `~affine_dependent ((c0:real^3->bool) DELETE x)` ASSUME_TAC THENL
     [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN EXISTS_TAC `c0:real^3->bool` THEN
      ASM_REWRITE_TAC[DELETE_SUBSET];
      ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT; CARD_DELETE] THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `open (interior (t0 UNION t) INTER {x:real^3 | t1 < a dot x /\ a dot x < t2})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_INTER THEN REWRITE_TAC[OPEN_INTERIOR] THEN
    MP_TAC(ISPECL [`a:real^3`; `t1:real`; `t2:real`] MOI_SSL_SLAB_BASIC) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior (t0 UNION t) INTER {x:real^3 | t1 < a dot x /\ a dot x < t2}
                SUBSET moi_ssb_reg k a v t1 t2 pp` MP_TAC THENL
   [REWRITE_TAC[moi_ssb_reg; SUBSET; IN_INTER; IN_ELIM_THM; UNIONS_GSPEC] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN t0 UNION t` MP_TAC THENL
     [ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
     [EXISTS_TAC `t0:real^3->bool`; EXISTS_TAC `t:real^3->bool`] THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP INTERIOR_MAXIMAL (CONJ th (ASSUME
    `open (interior (t0 UNION t) INTER {x:real^3 | t1 < a dot x /\ a dot x < t2})`)))) THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM]);;

(* A point of the open slab on an edge shared by two faces in O is interior *)
(* to the region: the section point of the edge is an inner vertex of the  *)
(* arc, so all simplices around the edge are kept.                          *)

let MOI_SSB_CRIT_EDGE = prove
 (`!s (a:real^3) lo hi k v t1 t2 pp t0 c0 j bb x y u.
     moi_ssb_free s a lo hi k v t1 t2 pp t0 c0 j bb /\
     x IN moi_ssb_omit a t1 t2 (a dot v) c0 (path_image bb) /\
     y IN moi_ssb_omit a t1 t2 (a dot v) c0 (path_image bb) /\ ~(x = y) /\
     u IN convex hull ((c0 DELETE x) DELETE y) /\ t1 < a dot u /\ a dot u < t2
     ==> u IN interior (moi_ssb_reg k a v t1 t2 pp)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_ssb_free] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `t0:real^3->bool`] MOI_SSB_PRISM_BASIC) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN c0 /\ (y:real^3) IN c0` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(x:real^3) IN moi_ssb_omit a t1 t2 (a dot v) c0 (path_image bb)`;
      `(y:real^3) IN moi_ssb_omit a t1 t2 (a dot v) c0 (path_image bb)`] THEN
    REWRITE_TAC[moi_ssb_omit; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the crossing pair *)
  MP_TAC(ISPECL [`(c0 DELETE x) DELETE (y:real^3)`; `a:real^3`; `t1:real`; `t2:real`;
                 `u:real^3`] MOI_SSL_HULL_CROSS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_DELETE] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `p:real^3` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(p:real^3 = q)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(c0 DELETE x) DELETE (y:real^3) = {p,q}` ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_SUBSET_EQ THEN
    ASM_SIMP_TAC[FINITE_DELETE; CARD_DELETE; IN_DELETE; INSERT_SUBSET; EMPTY_SUBSET] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_DELETE]) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^3. w IN c0 ==> w = x \/ w = y \/ w = p \/ w = q` (LABEL_TAC "four")
  THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    UNDISCH_TAC `(c0 DELETE x) DELETE (y:real^3) = {p,q}` THEN
    REWRITE_TAC[EXTENSION; IN_DELETE; IN_INSERT; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `w:real^3`) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(u:real^3) IN convex hull ((c0 DELETE x) DELETE y)` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`a:real^3`; `t1:real`; `t2:real`; `p:real^3`; `q:real^3`; `u:real^3`]
    MOI_SSB_PAIR_REL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* the edge is a simplex of k *)
  SUBGOAL_THEN `convex hull {p:real^3,q} IN k` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o el 2 o CONJUNCTS o REWRITE_RULE[simplicial_complex] o
      check (fun th -> concl th = `simplicial_complex (k:(real^3->bool)->bool)`)) THEN
    EXISTS_TAC `t0:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `convex hull c0 = t0:real^3->bool` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    EXISTS_TAC `{p:real^3,q}` THEN REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_DELETE]) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  (* its section point *)
  MP_TAC(ISPECL [`convex hull {p:real^3,q}`; `a:real^3`; `a dot (v:real^3)`;
                 `p:real^3`; `q:real^3`] MOI_SSL_RELINT_LEVEL) THEN
  ANTS_TAC THENL
   [SIMP_TAC[CONVEX_CONVEX_HULL; HULL_INC; IN_INSERT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(z:real^3) IN convex hull {p,q}` ASSUME_TAC THENL
   [MP_TAC(ISPEC `convex hull {p:real^3,q}` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(z:real^3) IN relative_interior (convex hull {p,q})` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {p:real^3,q} SUBSET convex hull (c0 DELETE x) /\
                convex hull {p:real^3,q} SUBSET t0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC HULL_MONO;
      UNDISCH_TAC `convex hull c0 = t0:real^3->bool` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC HULL_MONO] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_DELETE]) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3) IN path_image bb` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN moi_ssb_omit a t1 t2 (a dot v) c0 (path_image bb)` THEN
    REWRITE_TAC[moi_ssb_omit; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  (* the section point is not on j *)
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `t0:real^3->bool`; `a dot (v:real^3)`] MOI_SSB_SEC_CELL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`t0 INTER {x:real^3 | a dot x = a dot v}`; `j:real^3->bool`;
                 `bb:real^1->real^3`; `z:real^3`] MOI_SSB_ENDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_SSB_CELL_BOUNDARY_CLOSED]; ALL_TAC] THEN
    X_GEN_TAC `e:real^3->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`a:real^3`; `t1:real`; `t2:real`; `a dot (v:real^3)`; `c0:real^3->bool`;
                   `e:real^3->bool`] MOI_SSB_EDGE_FACE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x':real^3` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
    SUBGOAL_THEN `convex hull {p:real^3,q} SUBSET convex hull (c0 DELETE x')` ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_OF_FACE_OF THEN EXISTS_TAC `convex hull c0:real^3->bool` THEN
      REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
        EXISTS_TAC `c0 DELETE (x':real^3)` THEN REWRITE_TAC[DELETE_SUBSET];
        ASM_REWRITE_TAC[];
        REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
        EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(z:real^3) IN e` THEN ASM_REWRITE_TAC[IN_INTER] THEN SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(x':real^3 = p) /\ ~(x' = q)` STRIP_ASSUME_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[IN_DELETE]) THEN
      CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THENL
       [SUBGOAL_THEN `(p:real^3) IN c0 DELETE p` MP_TAC THENL
         [ALL_TAC; REWRITE_TAC[IN_DELETE]] THEN
        MATCH_MP_TAC MOI_SSB_HULL_VERTEX THEN EXISTS_TAC `c0:real^3->bool` THEN
        ASM_REWRITE_TAC[DELETE_SUBSET];
        SUBGOAL_THEN `(q:real^3) IN c0 DELETE q` MP_TAC THENL
         [ALL_TAC; REWRITE_TAC[IN_DELETE]] THEN
        MATCH_MP_TAC MOI_SSB_HULL_VERTEX THEN EXISTS_TAC `c0:real^3->bool` THEN
        ASM_REWRITE_TAC[DELETE_SUBSET]] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        is_binary "SUBSET" (concl th) &&
        lhand(concl th) = `convex hull {p:real^3,q}` &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "DELETE"))
          (rand(concl th)))) THEN
      MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x':real^3) IN moi_ssb_omit a t1 t2 (a dot v) c0 (path_image bb)`
    MP_TAC THENL
     [USE_THEN "four" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x':real^3) IN c0`))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[moi_ssb_omit; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  (* all simplices containing u are kept *)
  SUBGOAL_THEN `(z:real^3) IN UNIONS (moi_ssb_secs k a v pp)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                   `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                   `pp:(real^3->bool)->bool`; `t0:real^3->bool`] MOI_SSB_SECS_DELETE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `t0 INTER {x:real^3 | a dot x = a dot v}` THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_ssb_reg] THEN MATCH_MP_TAC MOI_SSL_INT_CRIT THEN
  MAP_EVERY EXISTS_TAC [`s:real^3->bool`; `k:(real^3->bool)->bool`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[moi_ssb_mem; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    UNDISCH_TAC `UNIONS k = (s:real^3->bool) UNION inside s` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `t0:real^3->bool` THEN ASM SET_TAC[];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`s:real^3->bool`; `k:(real^3->bool)->bool`; `convex hull {p:real^3,q}`;
                   `u:real^3`] MOI_SSL_SPHERE_SIMPLICES) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                   `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                   `pp:(real^3->bool)->bool`; `j:real^3->bool`; `z:real^3`]
      MOI_SSB_FCELL_S) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    X_GEN_TAC `t:real^3->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `convex hull {p:real^3,q}`; `t:real^3->bool`;
                   `u:real^3`] MOI_SSL_RELINT_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `t:real^3->bool`] MOI_SSL_SC_SIMPLEX) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                   `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                   `pp:(real^3->bool)->bool`; `j:real^3->bool`; `z:real^3`;
                   `t:real^3->bool`] MOI_SSB_PLANE_INT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MOI_SSL_INTERIOR_LEVEL THEN
      MAP_EVERY EXISTS_TAC [`p:real^3`; `q:real^3`] THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[HULL_INC; IN_INSERT; SUBSET];
        ASM_MESON_TAC[HULL_INC; IN_INSERT; SUBSET];
        ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      REWRITE_TAC[moi_ssb_mem; IN_ELIM_THM; moi_ssb_wedges] THEN ASM_MESON_TAC[]]]);;

(* Points of the open slab in the slab part of a face in O but on no face *)
(* outside O are interior to the region.                                   *)

let MOI_SSB_CRIT_INT = prove
 (`!s (a:real^3) lo hi k v t1 t2 pp t0 c0 j bb x u.
     moi_ssb_free s a lo hi k v t1 t2 pp t0 c0 j bb /\
     x IN moi_ssb_omit a t1 t2 (a dot v) c0 (path_image bb) /\
     u IN convex hull (c0 DELETE x) /\ t1 < a dot u /\ a dot u < t2 /\
     (!z. z IN c0 /\ ~(z IN moi_ssb_omit a t1 t2 (a dot v) c0 (path_image bb))
          ==> ~(u IN convex hull (c0 DELETE z)))
     ==> u IN interior (moi_ssb_reg k a v t1 t2 pp)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_ssb_free] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_ssb_free")) (concl th))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE) THEN
  ASM_CASES_TAC `(u:real^3) IN relative_interior (convex hull (c0 DELETE x))` THENL
   [MATCH_MP_TAC MOI_SSB_CRIT_FACE THEN
    MAP_EVERY EXISTS_TAC [`s:real^3->bool`; `lo:real`; `hi:real`; `t0:real^3->bool`;
                          `c0:real^3->bool`; `j:real^3->bool`; `bb:real^1->real^3`;
                          `x:real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~affine_dependent ((c0:real^3->bool) DELETE x)` ASSUME_TAC THENL
   [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN EXISTS_TAC `c0:real^3->bool` THEN
    ASM_REWRITE_TAC[DELETE_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^3) IN relative_frontier (convex hull (c0 DELETE x))` MP_TAC THENL
   [REWRITE_TAC[relative_frontier; IN_DIFF] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `(s:real^3->bool) SUBSET closure s /\ u IN s ==> u IN closure s`) THEN
    ASM_REWRITE_TAC[CLOSURE_SUBSET];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_CONVEX_HULL; UNIONS_GSPEC; IN_ELIM_THM; IN_DELETE] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:real^3) IN moi_ssb_omit a t1 t2 (a dot v) c0 (path_image bb)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `u:real^3`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(u:real^3) IN convex hull ((c0 DELETE x) DELETE y)` THEN
    SPEC_TAC(`u:real^3`,`u:real^3`) THEN REWRITE_TAC[GSYM SUBSET] THEN
    MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_SSB_CRIT_EDGE THEN
  MAP_EVERY EXISTS_TAC [`s:real^3->bool`; `lo:real`; `hi:real`; `t0:real^3->bool`;
                        `c0:real^3->bool`; `j:real^3->bool`; `bb:real^1->real^3`;
                        `x:real^3`; `y:real^3`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* A level section of a segment with an endpoint off the level is finite.   *)

let MOI_SSB_SEG_LEVEL_FINITE = prove
 (`!(a:real^3) h p q.
     ~(a dot p = h) ==> FINITE (convex hull {p,q} INTER {x | a dot x = h})`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `a dot (p:real^3) = a dot q` THENL
   [SUBGOAL_THEN `convex hull {p:real^3,q} INTER {x | a dot x = h} = {}`
      (fun th -> REWRITE_TAC[th; FINITE_EMPTY]) THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY;
                GSYM SEGMENT_CONVEX_HULL; IN_SEGMENT] THEN
    X_GEN_TAC `y:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `w:real` STRIP_ASSUME_TAC) MP_TAC) THEN
    ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN
    UNDISCH_TAC `~(a dot (p:real^3) = h)` THEN UNDISCH_TAC `a dot (p:real^3) = a dot q` THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{(&1 - (h - a dot p) / (a dot q - a dot p)) % p +
               ((h - a dot p) / (a dot q - a dot p)) % (q:real^3)}` THEN
  REWRITE_TAC[FINITE_SING] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; IN_SING;
              GSYM SEGMENT_CONVEX_HULL; IN_SEGMENT] THEN
  X_GEN_TAC `y:real^3` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `w:real` STRIP_ASSUME_TAC) MP_TAC) THEN
  ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN DISCH_TAC THEN
  SUBGOAL_THEN `w = (h - a dot p) / (a dot q - a dot (p:real^3))` SUBST1_TAC THENL
   [SUBGOAL_THEN `~(a dot q - a dot (p:real^3) = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `(&1 - w) * a dot (p:real^3) + w * a dot q = h` THEN
    CONV_TAC REAL_FIELD;
    REFL_TAC]);;

(* Points of the open slab on an edge between a face in O and a face       *)
(* outside O are frontier points of the region: the section point of the   *)
(* edge lies on j.                                                          *)

let MOI_SSB_CRIT_FR = prove
 (`!s (a:real^3) lo hi k v t1 t2 pp t0 c0 j bb x z u.
     moi_ssb_free s a lo hi k v t1 t2 pp t0 c0 j bb /\
     x IN moi_ssb_omit a t1 t2 (a dot v) c0 (path_image bb) /\
     z IN c0 /\ ~(z IN moi_ssb_omit a t1 t2 (a dot v) c0 (path_image bb)) /\
     u IN convex hull (c0 DELETE x) /\ u IN convex hull (c0 DELETE z) /\
     t1 < a dot u /\ a dot u < t2
     ==> u IN frontier (moi_ssb_reg k a v t1 t2 pp)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_ssb_free] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `t0:real^3->bool`] MOI_SSB_PRISM_BASIC) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN c0` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN moi_ssb_omit a t1 t2 (a dot v) c0 (path_image bb)` THEN
    SIMP_TAC[moi_ssb_omit; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(x:real^3 = z)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~((z:real^3) IN moi_ssb_omit a t1 t2 (a dot v) c0 (path_image bb))` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^3) IN convex hull ((c0 DELETE x) DELETE z)` ASSUME_TAC THENL
   [SUBGOAL_THEN `convex hull (c0 DELETE x) INTER convex hull (c0 DELETE z) =
                  convex hull ((c0 DELETE x) DELETE (z:real^3))` MP_TAC THENL
     [SUBGOAL_THEN `(c0 DELETE x) DELETE (z:real^3) = (c0 DELETE x) INTER (c0 DELETE z)`
      SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC CONVEX_HULL_INTER THEN MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN
      EXISTS_TAC `c0:real^3->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[IN_INTER]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(c0 DELETE x) DELETE (z:real^3)`; `a:real^3`; `t1:real`; `t2:real`;
                 `u:real^3`] MOI_SSL_HULL_CROSS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_DELETE] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `p:real^3` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(p:real^3 = q)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(c0 DELETE x) DELETE (z:real^3) = {p,q}` ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_SUBSET_EQ THEN
    ASM_SIMP_TAC[FINITE_DELETE; CARD_DELETE; IN_DELETE; INSERT_SUBSET; EMPTY_SUBSET] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_DELETE]) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `(u:real^3) IN convex hull ((c0 DELETE x) DELETE z)` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_DELETE]) THEN
  MP_TAC(ISPECL [`a:real^3`; `t1:real`; `t2:real`; `p:real^3`; `q:real^3`; `u:real^3`]
    MOI_SSB_PAIR_REL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `convex hull {p:real^3,q} IN k` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o el 2 o CONJUNCTS o REWRITE_RULE[simplicial_complex] o
      check (fun th -> concl th = `simplicial_complex (k:(real^3->bool)->bool)`)) THEN
    EXISTS_TAC `t0:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `convex hull c0 = t0:real^3->bool` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    EXISTS_TAC `{p:real^3,q}` THEN REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`convex hull {p:real^3,q}`; `a:real^3`; `a dot (v:real^3)`;
                 `p:real^3`; `q:real^3`] MOI_SSL_RELINT_LEVEL) THEN
  ANTS_TAC THENL
   [SIMP_TAC[CONVEX_CONVEX_HULL; HULL_INC; IN_INSERT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(w:real^3) IN convex hull {p,q}` ASSUME_TAC THENL
   [MP_TAC(ISPEC `convex hull {p:real^3,q}` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(w:real^3) IN relative_interior (convex hull {p,q})` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {p:real^3,q} SUBSET convex hull (c0 DELETE z) /\
                convex hull {p:real^3,q} SUBSET t0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC HULL_MONO;
      UNDISCH_TAC `convex hull c0 = t0:real^3->bool` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC HULL_MONO] THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_DELETE] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the face omitting z is crossing but outside O *)
  SUBGOAL_THEN `~(convex hull (c0 DELETE z) INTER {y:real^3 | a dot y = a dot v} SUBSET
                  path_image bb)` ASSUME_TAC THENL
   [UNDISCH_TAC `~((z:real^3) IN moi_ssb_omit a t1 t2 (a dot v) c0 (path_image bb))` THEN
    REWRITE_TAC[moi_ssb_omit; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `a /\ b ==> ~(a /\ b /\ c) ==> ~c`) THEN CONJ_TAC THENL
     [EXISTS_TAC `p:real^3`; EXISTS_TAC `q:real^3`] THEN
    ASM_REWRITE_TAC[IN_DELETE];
    ALL_TAC] THEN
  (* its section is an edge of the section of t0 *)
  MP_TAC(ISPECL [`c0:real^3->bool`; `c0 DELETE (z:real^3)`; `a:real^3`; `a dot (v:real^3)`;
                 `p:real^3`; `q:real^3`] MOI_SSL_FACE_SECTION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[DELETE_SUBSET; IN_DELETE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_DELETE] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC INT_REDUCE_CONV THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `t0:real^3->bool`; `a dot (v:real^3)`] MOI_SSB_SEC_CELL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC] THEN
  SUBGOAL_THEN `convex hull (c0 DELETE z) INTER {y:real^3 | a dot y = a dot v} SUBSET
                relative_frontier (t0 INTER {x | a dot x = a dot v})` ASSUME_TAC THENL
   [MATCH_MP_TAC FACE_OF_SUBSET_RELATIVE_FRONTIER THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o AP_TERM `aff_dim:(real^3->bool)->int`) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  (* the section meets the arc in finitely many points *)
  SUBGOAL_THEN `FINITE (convex hull (c0 DELETE z) INTER {y:real^3 | a dot y = a dot v} INTER
                        path_image bb)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `UNIONS {convex hull ((c0 DELETE z) DELETE x') INTER
                        {y:real^3 | a dot y = a dot v} | x' | x' IN c0 DELETE z}` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FINITE_UNIONS] THEN CONJ_TAC THENL
       [REWRITE_TAC[SIMPLE_IMAGE] THEN MATCH_MP_TAC FINITE_IMAGE THEN
        ASM_SIMP_TAC[FINITE_DELETE];
        REWRITE_TAC[FORALL_IN_GSPEC; IN_DELETE] THEN X_GEN_TAC `x':real^3` THEN STRIP_TAC THEN
        SUBGOAL_THEN `((c0 DELETE z) DELETE (x':real^3)) HAS_SIZE 2` MP_TAC THENL
         [ASM_SIMP_TAC[HAS_SIZE; FINITE_DELETE; CARD_DELETE; IN_DELETE] THEN
          CONV_TAC NUM_REDUCE_CONV;
          ALL_TAC] THEN
        CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
        DISCH_THEN(X_CHOOSE_THEN `p':real^3` (X_CHOOSE_THEN `q':real^3`
          (CONJUNCTS_THEN2 ASSUME_TAC (fun th -> ASSUME_TAC th THEN SUBST1_TAC th)))) THEN
        MATCH_MP_TAC MOI_SSB_SEG_LEVEL_FINITE THEN
        SUBGOAL_THEN `(p':real^3) IN c0` ASSUME_TAC THENL
         [UNDISCH_TAC `(c0 DELETE z) DELETE (x':real^3) = {p',q'}` THEN SET_TAC[];
          ALL_TAC] THEN
        FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(p':real^3) IN c0`) o check (fun th ->
          aconv (concl th) `!w:real^3. w IN c0 ==> a dot w < t1 \/ t2 < a dot w`)) THEN
        MP_TAC(ASSUME `t1 < a dot (v:real^3)`) THEN MP_TAC(ASSUME `a dot (v:real^3) < t2`) THEN
        REAL_ARITH_TAC];
      REWRITE_TAC[SUBSET; IN_INTER; UNIONS_GSPEC; IN_ELIM_THM] THEN
      X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
        is_forall(concl th) && can (find_term (fun t -> is_const t &&
          fst(dest_const t) = "moi_ssb_omit")) (concl th) && not(is_neg(concl th)))) THEN
      ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `x':real^3` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `x':real^3` THEN
      SUBGOAL_THEN `(x':real^3) IN c0 /\ ~(x' = z)` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [UNDISCH_TAC `(x':real^3) IN moi_ssb_omit a t1 t2 (a dot v) c0 (path_image bb)` THEN
          SIMP_TAC[moi_ssb_omit; IN_ELIM_THM];
          DISCH_THEN SUBST_ALL_TAC THEN
          UNDISCH_TAC `~((z:real^3) IN moi_ssb_omit a t1 t2 (a dot v) c0 (path_image bb))` THEN
          ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_DELETE] THEN
      SUBGOAL_THEN `convex hull (c0 DELETE z) INTER convex hull (c0 DELETE x') =
                    convex hull ((c0 DELETE z) DELETE (x':real^3))` MP_TAC THENL
       [SUBGOAL_THEN `(c0 DELETE z) DELETE (x':real^3) = (c0 DELETE z) INTER (c0 DELETE x')`
        SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC CONVEX_HULL_INTER THEN MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN
        EXISTS_TAC `c0:real^3->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
        DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[IN_INTER]]];
    ALL_TAC] THEN
  (* hence w is a limit of section points off the arc, so w lies on j *)
  SUBGOAL_THEN `(w:real^3) IN convex hull (c0 DELETE z) INTER {y | a dot y = a dot v}`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    UNDISCH_TAC `convex hull {p:real^3,q} SUBSET convex hull (c0 DELETE z)` THEN
    UNDISCH_TAC `(w:real^3) IN convex hull {p,q}` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `convex hull (c0 DELETE z) INTER {y:real^3 | a dot y = a dot v}`
    COMPACT_CONVEX_COLLINEAR_SEGMENT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `w:real^3` THEN
      FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC COMPACT_INTER_CLOSED THEN REWRITE_TAC[CLOSED_HYPERPLANE] THEN
      MATCH_MP_TAC COMPACT_CONVEX_HULL THEN MATCH_MP_TAC FINITE_IMP_COMPACT THEN
      ASM_SIMP_TAC[FINITE_DELETE];
      MATCH_MP_TAC CONVEX_INTER THEN REWRITE_TAC[CONVEX_CONVEX_HULL; CONVEX_HYPERPLANE];
      REWRITE_TAC[COLLINEAR_AFF_DIM] THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `al:real^3` (X_CHOOSE_TAC `be:real^3`)) THEN
  SUBGOAL_THEN `~(al:real^3 = be)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC
     `aff_dim (convex hull (c0 DELETE z) INTER {x:real^3 | a dot x = a dot v}) = &1` THEN
    ASM_REWRITE_TAC[SEGMENT_REFL; AFF_DIM_SING] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`al:real^3`; `be:real^3`;
                 `convex hull (c0 DELETE z) INTER {y:real^3 | a dot y = a dot v} INTER
                  path_image bb`] MOI_SSL_SEG_CLOSURE_DIFF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o SYM)] THEN
  SUBGOAL_THEN
   `closure(segment[al:real^3,be] DIFF
            (convex hull (c0 DELETE z) INTER {y:real^3 | a dot y = a dot v} INTER
             path_image bb)) SUBSET
    relative_frontier (t0 INTER {x | a dot x = a dot v}) INTER j`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THENL
     [MP_TAC(ASSUME `convex hull (c0 DELETE z) INTER {y:real^3 | a dot y = a dot v} =
                     segment[al,be]`) THEN
      MP_TAC(ASSUME `convex hull (c0 DELETE z) INTER {y:real^3 | a dot y = a dot v} SUBSET
                     relative_frontier (t0 INTER {x | a dot x = a dot v})`) THEN
      MP_TAC(ASSUME `relative_frontier (t0 INTER {x:real^3 | a dot x = a dot v}) INTER j UNION
                     path_image bb = relative_frontier (t0 INTER {x | a dot x = a dot v})`) THEN
      SET_TAC[];
      MATCH_MP_TAC CLOSED_INTER THEN REWRITE_TAC[CLOSED_RELATIVE_FRONTIER] THEN
      MATCH_MP_TAC MOI_SSB_CELL_BOUNDARY_CLOSED THEN
      EXISTS_TAC `UNIONS (moi_ssb_secs k a (v:real^3) pp)` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^3) IN j` ASSUME_TAC THENL
   [MP_TAC(ASSUME `segment[al:real^3,be] =
                   closure(segment[al,be] DIFF
                     (convex hull (c0 DELETE z) INTER {y | a dot y = a dot v} INTER
                      path_image bb))`) THEN
    MP_TAC(ASSUME `convex hull (c0 DELETE z) INTER {y:real^3 | a dot y = a dot v} =
                   segment[al,be]`) THEN
    MP_TAC(ASSUME `(w:real^3) IN convex hull (c0 DELETE z) INTER {y | a dot y = a dot v}`) THEN
    MP_TAC(ASSUME
     `closure(segment[al:real^3,be] DIFF
              (convex hull (c0 DELETE z) INTER {y:real^3 | a dot y = a dot v} INTER
               path_image bb)) SUBSET
      relative_frontier (t0 INTER {x | a dot x = a dot v}) INTER j`) THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the frontier criterion *)
  SUBGOAL_THEN `(u:real^3) IN t0 /\ (w:real^3) IN t0` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `convex hull {p:real^3,q} SUBSET t0` THEN
    UNDISCH_TAC `(w:real^3) IN convex hull {p,q}` THEN
    UNDISCH_TAC `(u:real^3) IN convex hull {p,q}` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(t0:real^3->bool) IN moi_ssb_mem k v pp` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[moi_ssb_mem; IN_ELIM_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `k:(real^3->bool)->bool`; `a:real^3`; `t1:real`;
                 `t2:real`; `moi_ssb_mem k v pp`; `u:real^3`] MOI_SSL_FR_CRIT) THEN
  REWRITE_TAC[moi_ssb_reg] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    REWRITE_TAC[moi_ssb_mem; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_INTER] THEN EXISTS_TAC `t0:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ASSUME `t1 < a dot (u:real^3)`) THEN MP_TAC(ASSUME `a dot (u:real^3) < t2`) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `(w:real^3) IN s` THENL
   [DISJ1_TAC THEN
    MP_TAC(ISPECL [`s:real^3->bool`; `k:(real^3->bool)->bool`; `convex hull {p:real^3,q}`;
                   `w:real^3`] MOI_SSL_SPHERE_SIMPLICES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(u:real^3) IN convex hull {p,q}` THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT DISJ2_TAC THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(w:real^3 = v)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~((v:real^3) IN t0)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `pp:(real^3->bool)->bool`; `j:real^3->bool`; `w:real^3`] MOI_SSB_PLANE_FR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t:real^3->bool` THEN
  UNDISCH_TAC `(t:real^3->bool) IN moi_ssb_prisms k a v t1 t2` THEN
  REWRITE_TAC[moi_ssb_prisms; IN_ELIM_THM] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[moi_ssb_mem; IN_ELIM_THM] THEN
  MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `convex hull {p:real^3,q}`; `t:real^3->bool`;
                 `w:real^3`] MOI_SSL_RELINT_SUBSET) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `(u:real^3) IN convex hull {p,q}` THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* One deletion step.  The prism t0 meets the smaller region in the strip   *)
(* over the omitted vertices, a PL 2-cell whose inner points are interior   *)
(* to the region and whose boundary lies on the frontier of the region;     *)
(* MOI_SSL_PUSH_DELETE then reduces the region to the smaller one.  The     *)
(* bundled setting comes from the output of MOI_SSL_FREE_PLANE.             *)
(* ------------------------------------------------------------------------- *)

(* A PL 2-cell contains its boundary and is nonempty.                       *)

let MOI_SSB_CELL_SUB = prove
 (`!d j:real^3->bool. pl_cell_with_boundary 2 d j ==> j SUBSET d /\ ~(d = {})`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MOI_SS2_CELL_FACTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `kk:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)))) THEN
  CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    UNDISCH_TAC `~((d:real^3->bool) DIFF j = {})` THEN SET_TAC[]]);;

(* Points of the region on the bounding planes of the slab are frontier    *)
(* points of the region.                                                    *)

let MOI_SSB_FR_LEVEL = prove
 (`!s (a:real^3) lo hi k v t1 t2 pp u.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\
     u IN moi_ssb_reg k a v t1 t2 pp /\ (a dot u = t1 \/ a dot u = t2)
     ==> u IN frontier (moi_ssb_reg k a v t1 t2 pp)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  REWRITE_TAC[moi_ssb_reg] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `k:(real^3->bool)->bool`; `a:real^3`; `t1:real`;
                 `t2:real`; `moi_ssb_mem k v pp`; `u:real^3`] MOI_SSL_FR_CRIT) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[moi_ssb_mem; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    UNDISCH_TAC `a dot (u:real^3) = t1 \/ a dot u = t2` THEN CONV_TAC TAUT]);;

(* The attaching set of the prism t0: the strip over the omitted vertices.  *)

let MOI_SSB_ATTACH_FR = prove
 (`!s (a:real^3) lo hi k v t1 t2 pp t0 c0 j bb.
     moi_ssb_free s a lo hi k v t1 t2 pp t0 c0 j bb
     ==> frontier (t0 INTER {x | t1 <= a dot x /\ a dot x <= t2}) INTER
         closure (moi_ssb_reg k a v t1 t2 pp DIFF
                  (t0 INTER {x | t1 <= a dot x /\ a dot x <= t2})) =
         UNIONS {convex hull (c0 DELETE x) INTER {y | t1 <= a dot y /\ a dot y <= t2} | x |
                 x IN moi_ssb_omit a t1 t2 (a dot v) c0 (path_image bb)}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_ssb_free] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `pp:(real^3->bool)->bool`; `t0:real^3->bool`; `c0:real^3->bool`;
                 `path_image (bb:real^1->real^3)`] MOI_SSB_ATTACH_IDENT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `pp:(real^3->bool)->bool`; `t0:real^3->bool`] MOI_SSB_REG_DELETE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  MP_TAC(ISPEC `t0 INTER {x:real^3 | t1 <= a dot x /\ a dot x <= t2}` MOI_SSL_CELL_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ASSUME `interior (t0 INTER {x:real^3 | t1 <= a dot x /\ a dot x <= t2}) INTER
                 moi_ssb_reg k a v t1 t2 (pp DELETE t0) = {}`) THEN
  SET_TAC[]);;

(* One deletion step (Moise, Lemma 6 of Sec 17): the frontier of the region *)
(* for pp is simple if that of the region for pp DELETE t0 is.              *)

let MOI_SSB_STEP = prove
 (`!s (a:real^3) lo hi k v t1 t2 pp t0 c0 j bb.
     moi_ssb_free s a lo hi k v t1 t2 pp t0 c0 j bb /\
     moi_sch3_simple (frontier (moi_ssb_reg k a v t1 t2 (pp DELETE t0)))
     ==> moi_sch3_simple (frontier (moi_ssb_reg k a v t1 t2 pp))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_SSB_ATTACH_FR) THEN
  MP_TAC(ASSUME `moi_ssb_free s (a:real^3) lo hi k v t1 t2 pp t0 c0 j bb`) THEN
  REWRITE_TAC[moi_ssb_free] THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE) THEN
  FIRST_ASSUM(ASSUME_TAC o SPEC `pp:(real^3->bool)->bool` o MATCH_MP MOI_SSB_REG_COMPACT) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `pp:(real^3->bool)->bool`; `t0:real^3->bool`] MOI_SSB_REG_DELETE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (ASSUME_TAC o MATCH_MP (SET_RULE `(r:real^3->bool) = r' UNION c ==> c SUBSET r`))
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  SUBGOAL_THEN `(t0:real^3->bool) IN moi_ssb_prisms k a v t1 t2` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      concl th = `pp SUBSET moi_ssb_prisms k a (v:real^3) t1 t2`)) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `t0:real^3->bool`] MOI_SSB_PRISM_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(t0:real^3->bool) IN moi_ssb_mem k v pp` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[moi_ssb_mem; IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. convex hull (c0 DELETE x) SUBSET t0` (LABEL_TAC "hsub") THENL
   [GEN_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `convex hull c0 = t0:real^3->bool`)) THEN
    MATCH_MP_TAC HULL_MONO THEN REWRITE_TAC[DELETE_SUBSET];
    ALL_TAC] THEN
  (* the omitted vertices and the arc *)
  SUBGOAL_THEN `moi_ssb_omit a t1 t2 (a dot v) c0 (path_image bb) SUBSET (c0:real^3->bool) /\
                (!x. x IN moi_ssb_omit a t1 t2 (a dot v) c0 (path_image bb)
                     ==> (?p. p IN c0 DELETE x /\ a dot p < t1) /\
                         (?q. q IN c0 DELETE x /\ t2 < a dot q))` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[moi_ssb_omit; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS {convex hull (c0 DELETE x) INTER {y:real^3 | a dot y = a dot v} | x |
                        x IN moi_ssb_omit a t1 t2 (a dot v) c0 (path_image bb)} =
                path_image (bb:real^1->real^3)` ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real^3` (CONJUNCTS_THEN2 MP_TAC MP_TAC)) THEN
      REWRITE_TAC[moi_ssb_omit; IN_ELIM_THM; SUBSET] THEN MESON_TAC[];
      DISCH_TAC THEN FIRST_ASSUM(fun th ->
        ACCEPT_TAC(MATCH_MP th (ASSUME `(y:real^3) IN path_image bb`)))];
    ALL_TAC] THEN
  (* the strip is a PL 2-cell *)
  MP_TAC(ISPECL [`a:real^3`; `t1:real`; `t2:real`; `a dot (v:real^3)`; `c0:real^3->bool`;
                 `moi_ssb_omit a t1 t2 (a dot v) c0 (path_image (bb:real^1->real^3))`]
    MOI_SSL_STRIP_CELL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONNECTED_PATH_IMAGE THEN
    ASM_SIMP_TAC[ARC_IMP_PATH];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `je:real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "sb") (LABEL_TAC "sc")))) THEN
  SUBGOAL_THEN
   `(je:real^3->bool) SUBSET
    UNIONS {convex hull (c0 DELETE x) INTER {y | t1 <= a dot y /\ a dot y <= t2} | x |
            x IN moi_ssb_omit a t1 t2 (a dot v) c0 (path_image bb)}` (LABEL_TAC "jsub") THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SSB_CELL_SUB o check (fun th ->
      can (find_term ((=) `je:real^3->bool`)) (concl th))) THEN
    DISCH_THEN(ACCEPT_TAC o CONJUNCT1);
    ALL_TAC] THEN
  (* the deletion *)
  MP_TAC(ISPECL [`moi_ssb_reg k a v t1 t2 pp`;
                 `t0 INTER {x:real^3 | t1 <= a dot x /\ a dot x <= t2}`;
                 `je:real^3->bool`] MOI_SSL_PUSH_DELETE) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [(* inner points of the strip are interior to the region *)
    REWRITE_TAC[SUBSET; IN_DIFF] THEN X_GEN_TAC `u:real^3` THEN STRIP_TAC THEN
    REMOVE_THEN "sc" (MP_TAC o SPEC `u:real^3`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC
     `(u:real^3) IN
      UNIONS {convex hull (c0 DELETE x) INTER {y | t1 <= a dot y /\ a dot y <= t2} | x |
              x IN moi_ssb_omit a t1 t2 (a dot v) c0 (path_image bb)}` THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                   `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                   `pp:(real^3->bool)->bool`; `t0:real^3->bool`; `c0:real^3->bool`;
                   `j:real^3->bool`; `bb:real^1->real^3`; `x:real^3`; `u:real^3`]
      MOI_SSB_CRIT_INT) THEN
    ASM_REWRITE_TAC[];
    (* boundary points of the strip are frontier points of the region *)
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(u:real^3) IN
      UNIONS {convex hull (c0 DELETE x) INTER {y | t1 <= a dot y /\ a dot y <= t2} | x |
              x IN moi_ssb_omit a t1 t2 (a dot v) c0 (path_image bb)}` MP_TAC THENL
     [USE_THEN "jsub" (MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(u:real^3) IN moi_ssb_reg k a v t1 t2 pp` ASSUME_TAC THENL
     [REWRITE_TAC[moi_ssb_reg; UNIONS_GSPEC; IN_ELIM_THM; IN_INTER] THEN
      EXISTS_TAC `t0:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "hsub" (MP_TAC o SPEC `x:real^3`) THEN
      UNDISCH_TAC `(u:real^3) IN convex hull (c0 DELETE x)` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `a dot (u:real^3) = t1` THENL
     [MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                     `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                     `pp:(real^3->bool)->bool`; `u:real^3`] MOI_SSB_FR_LEVEL) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `a dot (u:real^3) = t2` THENL
     [MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                     `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                     `pp:(real^3->bool)->bool`; `u:real^3`] MOI_SSB_FR_LEVEL) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REMOVE_THEN "sb" (MP_TAC o SPEC `u:real^3`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                   `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                   `pp:(real^3->bool)->bool`; `t0:real^3->bool`; `c0:real^3->bool`;
                   `j:real^3->bool`; `bb:real^1->real^3`; `x:real^3`; `z:real^3`;
                   `u:real^3`] MOI_SSB_CRIT_FR) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY (fun t -> MP_TAC(ASSUME t))
     [`t1 <= a dot (u:real^3)`; `a dot (u:real^3) <= t2`;
      `~(a dot (u:real^3) = t1)`; `~(a dot (u:real^3) = t2)`] THEN
    REAL_ARITH_TAC]);;

(* The data of MOI_SSL_FREE_PLANE for the free section of t0 give the      *)
(* bundled setting of a deletion step.                                     *)

let MOI_SSB_FREE_INTRO = prove
 (`!s (a:real^3) lo hi k v t1 t2 pp t0 j (bb:real^1->real^3).
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ pp SUBSET moi_ssb_prisms k a v t1 t2 /\
     t0 IN pp /\ pl_cell_with_boundary 2 (UNIONS (moi_ssb_secs k a v pp)) j /\
     arc bb /\ path_image bb SUBSET relative_frontier (t0 INTER {x | a dot x = a dot v}) /\
     (t0 INTER {x | a dot x = a dot v}) INTER
       UNIONS (moi_ssb_secs k a v pp DELETE (t0 INTER {x | a dot x = a dot v})) =
       path_image bb /\
     (relative_frontier (t0 INTER {x | a dot x = a dot v}) INTER j) INTER path_image bb =
       {pathstart bb, pathfinish bb} /\
     (relative_frontier (t0 INTER {x | a dot x = a dot v}) INTER j) UNION path_image bb =
       relative_frontier (t0 INTER {x | a dot x = a dot v}) /\
     (!e. e face_of (t0 INTER {x | a dot x = a dot v}) /\ aff_dim e = &1
          ==> (e SUBSET path_image bb /\
               ?d. d IN moi_ssb_secs k a v pp /\
                   ~(d = t0 INTER {x | a dot x = a dot v}) /\ e SUBSET d) \/
              e SUBSET j) /\
     UNIONS {e | e face_of (t0 INTER {x | a dot x = a dot v}) /\ aff_dim e = &1 /\
                 e SUBSET path_image bb} = path_image bb /\
     ~(relative_frontier (t0 INTER {x | a dot x = a dot v}) SUBSET path_image bb) /\
     connected (relative_frontier (t0 INTER {x | a dot x = a dot v}) INTER j)
     ==> ?c0. moi_ssb_free s a lo hi k v t1 t2 pp t0 c0 j bb`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  SUBGOAL_THEN `(t0:real^3->bool) IN moi_ssb_prisms k a v t1 t2` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      concl th = `pp SUBSET moi_ssb_prisms k a (v:real^3) t1 t2`)) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `t0:real^3->bool`] MOI_SSB_PRISM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `c0:real^3->bool` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))
      ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    concl th = `t0 = convex hull (c0:real^3->bool)`)) THEN
  SUBGOAL_THEN `!w:real^3. w IN c0 ==> a dot w < t1 \/ t2 < a dot w` ASSUME_TAC THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(w:real^3) IN c0`) o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `k:(real^3->bool)->bool`)) (concl th))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  (* edges in the arc are shared with another section *)
  SUBGOAL_THEN
   `!e. e face_of (t0 INTER {x:real^3 | a dot x = a dot v}) /\ aff_dim e = &1 /\
        e SUBSET path_image bb
        ==> ?d. d IN moi_ssb_secs k a v pp /\
                ~(d = t0 INTER {x | a dot x = a dot v}) /\ e SUBSET d`
  ASSUME_TAC THENL
   [X_GEN_TAC `e:real^3->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real^3->bool` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `j:real^3->bool`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "face_of")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(DISJ_CASES_THEN2 ACCEPT_TAC ASSUME_TAC) THEN
    MATCH_MP_TAC(TAUT `F ==> p`) THEN
    MP_TAC(ISPEC `e:real^3->bool` MOI_SSB_AFF1_INFINITE) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC FACE_OF_IMP_CONVEX THEN
        EXISTS_TAC `t0 INTER {x:real^3 | a dot x = a dot v}` THEN FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[INFINITE] THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{pathstart bb, pathfinish (bb:real^1->real^3)}` THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `{pathstart bb, pathfinish (bb:real^1->real^3)}`)) THEN
    MP_TAC(ASSUME `path_image bb SUBSET
                   relative_frontier (t0 INTER {x:real^3 | a dot x = a dot v})`) THEN
    MP_TAC(ASSUME `e SUBSET path_image (bb:real^1->real^3)`) THEN
    MP_TAC(ASSUME `(e:real^3->bool) SUBSET j`) THEN SET_TAC[];
    ALL_TAC] THEN
  (* the omitted vertices *)
  MP_TAC(ISPECL [`a:real^3`; `t1:real`; `t2:real`; `a dot (v:real^3)`; `c0:real^3->bool`;
                 `path_image (bb:real^1->real^3)`] MOI_SSB_ATTACH_O) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[PATH_IMAGE_NONEMPTY]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN ASSUME_TAC)) THEN
  DISCH_THEN(fun th ->
    SUBGOAL_THEN
     `!z. z IN path_image bb
          ==> ?x. x IN moi_ssb_omit a t1 t2 (a dot v) c0 (path_image bb) /\
                  z IN convex hull (c0 DELETE x) INTER {y:real^3 | a dot y = a dot v}`
    ASSUME_TAC THENL
     [MP_TAC th THEN REWRITE_TAC[EXTENSION; UNIONS_GSPEC; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC]) THEN
  EXISTS_TAC `c0:real^3->bool` THEN REWRITE_TAC[moi_ssb_free] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Induction on the number of prisms (deleting free prisms one at a time),  *)
(* the region and the sections for all prisms, and the main theorem         *)
(* MOI_SSL_SLAB_FROM_STAR.                                                  *)
(* ------------------------------------------------------------------------- *)

(* The frontier of the region for any set pp of prisms whose sections form *)
(* a PL 2-cell together with the wedge sections is simple, given the star   *)
(* statement (the case pp = {}).                                            *)

let MOI_SSB_INDUCT = prove
 (`!s (a:real^3) lo hi k v t1 t2.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\
     (?j0. pl_cell_with_boundary 2 (UNIONS (moi_ssb_secs k a v {})) j0) /\
     moi_sch3_simple (frontier (moi_ssb_reg k a v t1 t2 {}))
     ==> !n pp j. CARD pp = n /\ pp SUBSET moi_ssb_prisms k a v t1 t2 /\
                  pl_cell_with_boundary 2 (UNIONS (moi_ssb_secs k a v pp)) j
                  ==> moi_sch3_simple (frontier (moi_ssb_reg k a v t1 t2 pp))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_TAC `j0:real^3->bool`) ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  SUBGOAL_THEN `FINITE (moi_ssb_prisms k a (v:real^3) t1 t2)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `k:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[moi_ssb_prisms; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(moi_ssb_secs k a (v:real^3) {} = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`UNIONS (moi_ssb_secs k a (v:real^3) {})`; `j0:real^3->bool`]
      MOI_SSB_CELL_SUB) THEN
    ASM_REWRITE_TAC[UNIONS_0];
    ALL_TAC] THEN
  INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `pp:(real^3->bool)->bool = {}` SUBST1_TAC THENL
     [SUBGOAL_THEN `FINITE (pp:(real^3->bool)->bool)` ASSUME_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `moi_ssb_prisms k a (v:real^3) t1 t2` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `CARD (pp:(real^3->bool)->bool) = 0` THEN ASM_SIMP_TAC[CARD_EQ_0];
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (pp:(real^3->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `moi_ssb_prisms k a (v:real^3) t1 t2` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?t0':real^3->bool. t0' IN pp` (X_CHOOSE_TAC `t0':real^3->bool`) THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN DISCH_TAC THEN
    UNDISCH_TAC `CARD (pp:(real^3->bool)->bool) = SUC n` THEN
    ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `pp:(real^3->bool)->bool`] MOI_SSB_SECS_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `pp:(real^3->bool)->bool`; `t0':real^3->bool`] MOI_SSB_SECS_DELETE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  (* a free section that is not a wedge section *)
  MP_TAC(ISPECL [`a:real^3`; `a dot (v:real^3)`; `moi_ssb_secs k a (v:real^3) pp`;
                 `moi_ssb_secs k a (v:real^3) {}`; `j:real^3->bool`] MOI_SSL_FREE_PLANE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      FIRST_ASSUM(X_CHOOSE_TAC `y:real^3->bool` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY] o
        check (fun th -> concl th = `~(moi_ssb_secs k a (v:real^3) {} = {})`)) THEN
      SUBGOAL_THEN `~(y = t0' INTER {x:real^3 | a dot x = a dot v})` ASSUME_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN
        UNDISCH_TAC `~(t0' INTER {x:real^3 | a dot x = a dot v} IN moi_ssb_secs k a v {})` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC `CARD {y:real^3->bool, t0' INTER {x:real^3 | a dot x = a dot v}}` THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
        ARITH_TAC;
        MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
        FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
          concl th = `moi_ssb_secs k a (v:real^3) {} SUBSET moi_ssb_secs k a v pp`)) THEN
        FIRST_ASSUM ACCEPT_TAC];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      DISJ2_TAC THEN EXISTS_TAC `j0:real^3->bool` THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN
      UNDISCH_TAC `~(t0' INTER {x:real^3 | a dot x = a dot v} IN moi_ssb_secs k a v {})` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool` (X_CHOOSE_THEN `bb:real^1->real^3`
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `path_image (bb:real^1->real^3)`)) THEN
  (* the free section is the section of a prism t0 of pp *)
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `pp:(real^3->bool)->bool`; `c:real^3->bool`] MOI_SSB_SECS_REP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real^3->bool` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  SUBGOAL_THEN `(t0:real^3->bool) IN pp` ASSUME_TAC THENL
   [UNDISCH_TAC `(t0:real^3->bool) IN moi_ssb_wedges k a v \/ t0 IN pp` THEN
    MATCH_MP_TAC(TAUT `~p ==> p \/ q ==> q`) THEN DISCH_TAC THEN
    UNDISCH_TAC `~((c:real^3->bool) IN moi_ssb_secs k a v {})` THEN
    REWRITE_TAC[moi_ssb_secs; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    EXISTS_TAC `t0:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `c:real^3->bool`)) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `pp:(real^3->bool)->bool`; `t0:real^3->bool`] MOI_SSB_SECS_DELETE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  (* the induction hypothesis for pp DELETE t0 *)
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`pp DELETE (t0:real^3->bool)`;
     `closure ((j UNION relative_frontier (t0 INTER {x:real^3 | a dot x = a dot v})) DIFF
               (relative_frontier (t0 INTER {x | a dot x = a dot v}) INTER j))`] o
    check (fun th -> is_forall(concl th) && can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "moi_sch3_simple")) (concl th))) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[CARD_DELETE] THEN ARITH_TAC;
      UNDISCH_TAC `pp SUBSET moi_ssb_prisms k a (v:real^3) t1 t2` THEN SET_TAC[];
      ASM_REWRITE_TAC[]];
    DISCH_TAC] THEN
  (* the deletion step *)
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `pp:(real^3->bool)->bool`; `t0:real^3->bool`; `j:real^3->bool`;
                 `bb:real^1->real^3`] MOI_SSB_FREE_INTRO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `c0:real^3->bool`) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                 `pp:(real^3->bool)->bool`; `t0:real^3->bool`; `c0:real^3->bool`;
                 `j:real^3->bool`; `bb:real^1->real^3`] MOI_SSB_STEP) THEN
  ASM_REWRITE_TAC[]);;

(* A 3-simplex without v meeting the closed slab meets the open slab.       *)

let MOI_SSB_MEETS_OPEN = prove
 (`!s (a:real^3) lo hi k v t1 t2 t x.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ t IN k /\ ~(v IN t) /\
     x IN t /\ t1 <= a dot x /\ a dot x <= t2
     ==> ~(t INTER {y | t1 < a dot y /\ a dot y < t2} = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSL_SLAB_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `t:real^3->bool`] MOI_SSL_SIMPLEX_HULL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    concl th = `t = convex hull (c:real^3->bool)`)) THEN
  SUBGOAL_THEN `!w:real^3. w IN c ==> a dot w < t1 \/ t2 < a dot w` ASSUME_TAC THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(w:real^3 = v)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `~((v:real^3) IN convex hull c)` THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `t1:real`)) (concl th) &&
      can (find_term ((=) `v:real^3`)) (concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:real^3->bool`; `a:real^3`; `t1:real`; `t2:real`; `x:real^3`]
    MOI_SSL_HULL_CROSS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `p:real^3` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`convex hull c:real^3->bool`; `a:real^3`; `a dot (v:real^3)`;
                 `p:real^3`; `q:real^3`] MOI_SSL_RELINT_LEVEL) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[CONVEX_CONVEX_HULL] THEN ASM_SIMP_TAC[HULL_INC] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `convex hull c:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM; SUBSET] THEN
  DISCH_TAC THEN DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `y:real^3` THEN ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* With all prisms the region is the part of the ball in the slab.         *)

let MOI_SSB_REG_ALL = prove
 (`!s (a:real^3) lo hi k v t1 t2.
     moi_ssl_slab_hyp s a lo hi k v t1 t2
     ==> moi_ssb_reg k a v t1 t2 (moi_ssb_prisms k a v t1 t2) =
         (s UNION inside s) INTER {x | t1 <= a dot x /\ a dot x <= t2}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSL_SLAB_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^3` THEN
  REWRITE_TAC[moi_ssb_reg; moi_ssb_mem; UNIONS_GSPEC; IN_ELIM_THM; IN_INTER] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `UNIONS k = (s:real^3->bool) UNION inside s` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_UNIONS] THEN
    EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[];
    STRIP_TAC THEN
    MP_TAC(ISPEC `k:(real^3->bool)->bool` MOI_SSL_PURE) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^3` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(v:real^3) IN t` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[moi_ssb_prisms; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                   `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                   `t:real^3->bool`; `y:real^3`] MOI_SSB_MEETS_OPEN) THEN
    ASM_REWRITE_TAC[]]);;

(* With all prisms the sections fill the fibre of the ball at the level of *)
(* v.                                                                       *)

let MOI_SSB_SECS_ALL = prove
 (`!s (a:real^3) lo hi k v t1 t2.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ ~(moi_ssb_secs k a v {} = {})
     ==> UNIONS (moi_ssb_secs k a v (moi_ssb_prisms k a v t1 t2)) =
         (s UNION inside s) INTER {x | a dot x = a dot v}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  SUBGOAL_THEN `?w:real^3->bool. w IN moi_ssb_wedges k a v` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(moi_ssb_secs k a (v:real^3) {} = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; moi_ssb_secs; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^3` THEN
  REWRITE_TAC[moi_ssb_secs; UNIONS_GSPEC; IN_ELIM_THM; IN_INTER] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(t:real^3->bool) IN k` ASSUME_TAC THENL
     [UNDISCH_TAC `(t:real^3->bool) IN moi_ssb_wedges k a v \/
                   t IN moi_ssb_prisms k a v t1 t2` THEN
      REWRITE_TAC[moi_ssb_wedges; moi_ssb_prisms; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `UNIONS k = (s:real^3->bool) UNION inside s` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_UNIONS] THEN
    EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[];
    STRIP_TAC THEN
    ASM_CASES_TAC `y:real^3 = v` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN EXISTS_TAC `w:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(w:real^3->bool) IN moi_ssb_wedges k a v` THEN
      SIMP_TAC[moi_ssb_wedges; IN_ELIM_THM];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                   `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                   `y:real^3`] MOI_SSB_LEVEL_COVER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(v:real^3) IN t` THENL
     [DISJ1_TAC THEN ASM_REWRITE_TAC[moi_ssb_wedges; IN_ELIM_THM];
      DISJ2_TAC THEN ASM_REWRITE_TAC[moi_ssb_prisms; IN_ELIM_THM] THEN
      MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                     `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`;
                     `t:real^3->bool`; `y:real^3`] MOI_SSB_MEETS_OPEN) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]]);;

(* The frontier of the part of the ball in a slab.                          *)

let MOI_SSB_FRONTIER_SLAB = prove
 (`!s (a:real^3) lo hi t1 t2.
     pl_sphere 2 s /\ moi_sch3_fibred s a lo hi /\ t1 < t2
     ==> frontier ((s UNION inside s) INTER {x | t1 <= a dot x /\ a dot x <= t2}) =
         ((s UNION inside s) INTER {x | a dot x = t1}) UNION
         ((s UNION inside s) INTER {x | a dot x = t2}) UNION
         (s INTER {x | t1 <= a dot x /\ a dot x <= t2})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`] MOI_SSL_FIB_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^3`; `t1:real`; `t2:real`] MOI_SSL_SLAB_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[frontier] THEN
  ASM_SIMP_TAC[CLOSURE_CLOSED; CLOSED_INTER; INTERIOR_INTER] THEN
  MP_TAC(ISPEC `s:real^3->bool` INSIDE_NO_OVERLAP) THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_DIFF; IN_UNION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  DISCH_TAC THEN X_GEN_TAC `x:real^3` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3`) THEN
  ASM_CASES_TAC `(x:real^3) IN s` THEN ASM_CASES_TAC `(x:real^3) IN inside s` THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* The main theorem (Moise, Lemma 6 of Sec 17, from the star of the        *)
(* vertex).                                                                *)

let MOI_SSL_SLAB_FROM_STAR = prove
 (mk_imp(MOI_SSL_STAR_STMT, MOI_SSL_SLAB_STMT),
  DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                       `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `moi_ssl_slab_hyp s (a:real^3) lo hi k v t1 t2` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[moi_ssl_slab_hyp]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSB_HYP) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SSL_SLAB_FACTS) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                                `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`;
                                `t2:real`] o
    check (fun th -> is_forall(concl th) && can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "moi_ssl_slab_hyp")) (concl th))) THEN
  REWRITE_TAC[GSYM MOI_SSB_STAR_FORM] THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `j0:real^3->bool`) ASSUME_TAC) THEN
  SUBGOAL_THEN `~(moi_ssb_secs k a (v:real^3) {} = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`UNIONS (moi_ssb_secs k a (v:real^3) {})`; `j0:real^3->bool`]
      MOI_SSB_CELL_SUB) THEN
    ASM_REWRITE_TAC[UNIONS_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`]
    MOI_SSB_INDUCT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `j0:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL
    [`CARD (moi_ssb_prisms k a (v:real^3) t1 t2)`; `moi_ssb_prisms k a (v:real^3) t1 t2`;
     `s INTER {x:real^3 | a dot x = a dot v}`]) THEN
  REWRITE_TAC[SUBSET_REFL] THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                   `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`]
      MOI_SSB_SECS_ALL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t &&
        fst(dest_const t) = "pl_cell_with_boundary")) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `v:real^3`; `t1:real`; `t2:real`]
    MOI_SSB_REG_ALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`; `t1:real`; `t2:real`]
    MOI_SSB_FRONTIER_SLAB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[]);;


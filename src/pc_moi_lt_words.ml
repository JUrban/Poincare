(* ========================================================================= *)
(* pc_moi_lt_words: the two cancellation identities of the cut-and-paste of  *)
(* the loop theorem (Moise p.186) in map form, the statements MOI_LT_WORD_3  *)
(* and MOI_LT_WORD_4 of pc_moi_loop_stmt.ml.                                 *)
(* ========================================================================= *)

needs "src/pc_moi_loop_stmt.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Groupoid facts for path homotopy: left cancellation and the swap xy = 1   *)
(* implies yx = 1.                                                           *)
(* ------------------------------------------------------------------------- *)

let MOI_LTW_CANCEL = prove
 (`!(s:real^M->bool) p q a.
     path p /\ path_image p SUBSET s /\ path q /\ path_image q SUBSET s /\
     pathfinish p = pathstart q /\
     homotopic_paths s (p ++ q) (linepath(a,a))
     ==> homotopic_paths s q (reversepath p)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `a:real^M = pathstart p` SUBST_ALL_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_PATHS_IMP_PATHSTART) THEN
    ASM_SIMP_TAC[PATHSTART_JOIN; PATHSTART_LINEPATH];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
  EXISTS_TAC `linepath(pathstart q,pathstart q) ++ (q:real^1->real^M)` THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_LID THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
  EXISTS_TAC `(reversepath p ++ p) ++ (q:real^1->real^M)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
    REWRITE_TAC[PATHFINISH_LINEPATH; PATHFINISH_JOIN; PATHSTART_JOIN;
                PATHSTART_REVERSEPATH] THEN
    ASM_REWRITE_TAC[HOMOTOPIC_PATHS_REFL] THEN
    ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && lhs(concl th) = `pathfinish(p:real^1->real^M)`)) THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_LINV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
  EXISTS_TAC `reversepath p ++ ((p:real^1->real^M) ++ q)` THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_ASSOC THEN
    ASM_REWRITE_TAC[PATH_REVERSEPATH; PATH_IMAGE_REVERSEPATH;
                    PATHFINISH_REVERSEPATH];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
  EXISTS_TAC `reversepath p ++
              linepath(pathstart p,pathstart (p:real^1->real^M))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
    ASM_REWRITE_TAC[HOMOTOPIC_PATHS_REFL; PATH_REVERSEPATH;
                    PATH_IMAGE_REVERSEPATH; PATHFINISH_REVERSEPATH;
                    PATHSTART_JOIN];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `reversepath p:real^1->real^M`]
    HOMOTOPIC_PATHS_RID) THEN
  ASM_REWRITE_TAC[PATH_REVERSEPATH; PATH_IMAGE_REVERSEPATH;
                  PATHFINISH_REVERSEPATH]);;

let MOI_LTW_SWAP = prove
 (`!(s:real^M->bool) x y a.
     path x /\ path_image x SUBSET s /\ path y /\ path_image y SUBSET s /\
     pathfinish x = pathstart y /\ pathfinish y = pathstart x /\
     homotopic_paths s (x ++ y) (linepath(a,a))
     ==> homotopic_paths s (y ++ x) (linepath(pathstart y,pathstart y))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `x:real^1->real^M`; `y:real^1->real^M`;
                 `a:real^M`] MOI_LTW_CANCEL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
  EXISTS_TAC `reversepath x ++ (x:real^1->real^M)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
    ASM_REWRITE_TAC[HOMOTOPIC_PATHS_REFL];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `pathfinish(x:real^1->real^M)`)) THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_LINV THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* WORD_3 (Moise p.186): with s3 homotopic to s1, s1 s4 s3 s2 = 1 gives      *)
(* s1 s2 s3 s4 = 1 (x y = 1 implies y x = 1 for x = s1 s4, y = s1 s2).       *)
(* ------------------------------------------------------------------------- *)

let MOI_LTW_W3 = prove
 (`!(s:real^M->bool) s1 s2 s3 s4 a b.
     path s1 /\ path s2 /\ path s3 /\ path s4 /\
     path_image s1 SUBSET s /\ path_image s2 SUBSET s /\
     path_image s3 SUBSET s /\ path_image s4 SUBSET s /\
     pathstart s1 = a /\ pathfinish s1 = b /\ pathstart s2 = b /\
     pathfinish s2 = a /\ pathstart s3 = a /\ pathfinish s3 = b /\
     pathstart s4 = b /\ pathfinish s4 = a /\
     homotopic_paths s s1 s3 /\
     homotopic_paths s (s1 ++ s4 ++ s3 ++ s2) (linepath(a,a))
     ==> homotopic_paths s (s1 ++ s2 ++ s3 ++ s4) (linepath(a,a))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `homotopic_paths s ((s1:real^1->real^M) ++ s4 ++ s1 ++ s2)
                      (s1 ++ s4 ++ s3 ++ s2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
    ASM_REWRITE_TAC[HOMOTOPIC_PATHS_REFL; PATHSTART_JOIN] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
    ASM_REWRITE_TAC[HOMOTOPIC_PATHS_REFL; PATHSTART_JOIN] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
    ASM_REWRITE_TAC[HOMOTOPIC_PATHS_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `homotopic_paths s (((s1:real^1->real^M) ++ s4) ++ (s1 ++ s2))
                      (linepath(a,a))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
    EXISTS_TAC `(s1:real^1->real^M) ++ s4 ++ s1 ++ s2` THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN
      MATCH_MP_TAC HOMOTOPIC_PATHS_ASSOC THEN
      ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; PATHSTART_JOIN; UNION_SUBSET];
      MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
      EXISTS_TAC `(s1:real^1->real^M) ++ s4 ++ s3 ++ s2` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `(s1:real^1->real^M) ++ s4`;
                 `(s1:real^1->real^M) ++ s2`; `a:real^M`] MOI_LTW_SWAP) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN;
                 UNION_SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[PATHSTART_JOIN] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
  EXISTS_TAC `((s1:real^1->real^M) ++ s2) ++ (s1 ++ s4)` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
  EXISTS_TAC `(s1:real^1->real^M) ++ s2 ++ s1 ++ s4` THEN CONJ_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
    ASM_REWRITE_TAC[HOMOTOPIC_PATHS_REFL; PATHSTART_JOIN] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
    ASM_REWRITE_TAC[HOMOTOPIC_PATHS_REFL; PATHSTART_JOIN] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
    ASM_REWRITE_TAC[HOMOTOPIC_PATHS_REFL] THEN
    ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC HOMOTOPIC_PATHS_ASSOC THEN
    ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; PATHSTART_JOIN; UNION_SUBSET]]);;

let MOI_LTW_ENDPOINT_TAC =
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE REFL_TAC ORELSE
   FIRST_ASSUM(ACCEPT_TAC o SYM) ORELSE ALL_TAC);;

let MOI_LTW_EQ2_TAC mid =
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC mid THEN
  CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE FIRST_ASSUM(ACCEPT_TAC o SYM));;

let MOI_LTW_WORD_3 = prove
 (MOI_LT_WORD_3,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_IMP_HOMOTOPIC_LOOPS THEN
  REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHFINISH_LINEPATH] THEN
  CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `s1:real^1->real^M`; `s2:real^1->real^M`;
                 `s3:real^1->real^M`; `s4:real^1->real^M`;
                 `pathstart(s1:real^1->real^M)`;
                 `pathfinish(s1:real^1->real^M)`] MOI_LTW_W3) THEN
  DISCH_THEN MATCH_MP_TAC THEN MOI_LTW_ENDPOINT_TAC THENL
   [MOI_LTW_EQ2_TAC `pathstart(s3:real^1->real^M)`;
    MOI_LTW_EQ2_TAC `pathfinish(s3:real^1->real^M)`;
    MATCH_MP_TAC HOMOTOPIC_PATHS_LOOP_PARTS THEN
    EXISTS_TAC `pathstart(s1:real^1->real^M)` THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_HOMOTOPIC_PATHS_NULL o
      check (fun th -> try rator(concl th) =
        `homotopic_loops (s:real^M->bool) (s1 ++ s4 ++ s3 ++ s2)` with Failure _ -> false)) THEN
    REWRITE_TAC[PATHSTART_JOIN]]);;

(* ------------------------------------------------------------------------- *)
(* WORD_4 (Moise p.186): with s1 s3 = 1, s1 s2^-1 s3 s4^-1 = 1 gives         *)
(* s1 s2 s3 s4 = 1 (s3 = s1^-1, s4 = (s1 s2 s1^-1)^-1).                       *)
(* ------------------------------------------------------------------------- *)

let MOI_LTW_SIDE_TAC =
  ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN;
               PATH_REVERSEPATH; PATH_IMAGE_REVERSEPATH; PATHSTART_REVERSEPATH;
               PATHFINISH_REVERSEPATH; UNION_SUBSET; HOMOTOPIC_PATHS_REFL];;

let MOI_LTW_W4 = prove
 (`!(s:real^M->bool) s1 s2 s3 s4 a b.
     path s1 /\ path s2 /\ path s3 /\ path s4 /\
     path_image s1 SUBSET s /\ path_image s2 SUBSET s /\
     path_image s3 SUBSET s /\ path_image s4 SUBSET s /\
     pathstart s1 = a /\ pathfinish s1 = b /\ pathstart s2 = b /\
     pathfinish s2 = b /\ pathstart s3 = b /\ pathfinish s3 = a /\
     pathstart s4 = a /\ pathfinish s4 = a /\
     homotopic_paths s s3 (reversepath s1) /\
     homotopic_paths s (s1 ++ reversepath s2 ++ s3 ++ reversepath s4)
                       (linepath(a,a))
     ==> homotopic_paths s (s1 ++ s2 ++ s3 ++ s4) (linepath(a,a))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `homotopic_paths s
      ((((s1:real^1->real^M) ++ reversepath s2) ++ reversepath s1) ++
       reversepath s4) (linepath(a,a))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
    EXISTS_TAC `(s1:real^1->real^M) ++ reversepath s2 ++ s3 ++ reversepath s4` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
    EXISTS_TAC `(s1:real^1->real^M) ++ reversepath s2 ++ reversepath s1 ++
                reversepath s4` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
      EXISTS_TAC `((s1:real^1->real^M) ++ reversepath s2) ++
                  (reversepath s1 ++ reversepath s4)` THEN
      CONJ_TAC THEN ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN
      MATCH_MP_TAC HOMOTOPIC_PATHS_ASSOC THEN MOI_LTW_SIDE_TAC;
      MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN MOI_LTW_SIDE_TAC THEN
      MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN MOI_LTW_SIDE_TAC THEN
      MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN MOI_LTW_SIDE_TAC THEN
      ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `homotopic_paths s (s4:real^1->real^M)
      ((s1 ++ reversepath s2) ++ reversepath s1)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^M->bool`;
                   `((s1:real^1->real^M) ++ reversepath s2) ++ reversepath s1`;
                   `reversepath(s4:real^1->real^M)`; `a:real^M`]
      MOI_LTW_CANCEL) THEN
    ANTS_TAC THENL [MOI_LTW_SIDE_TAC; ALL_TAC] THEN
    REWRITE_TAC[HOMOTOPIC_PATHS_REVERSEPATH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `reversepath ((s1:real^1->real^M) ++ (s2 ++ reversepath s1)) =
    (s1 ++ reversepath s2) ++ reversepath s1`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[REVERSEPATH_JOINPATHS; PATHSTART_JOIN; PATHFINISH_JOIN;
                 PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH;
                 REVERSEPATH_REVERSEPATH];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
  EXISTS_TAC `(s1:real^1->real^M) ++ s2 ++ reversepath s1 ++
              reversepath (s1 ++ (s2 ++ reversepath s1))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN MOI_LTW_SIDE_TAC THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN MOI_LTW_SIDE_TAC THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN MOI_LTW_SIDE_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
  EXISTS_TAC `((s1:real^1->real^M) ++ (s2 ++ reversepath s1)) ++
              reversepath (s1 ++ (s2 ++ reversepath s1))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
    EXISTS_TAC `(s1:real^1->real^M) ++ ((s2 ++ reversepath s1) ++
                reversepath (s1 ++ (s2 ++ reversepath s1)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN MOI_LTW_SIDE_TAC THEN
      MATCH_MP_TAC HOMOTOPIC_PATHS_ASSOC THEN MOI_LTW_SIDE_TAC;
      MATCH_MP_TAC HOMOTOPIC_PATHS_ASSOC THEN MOI_LTW_SIDE_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^M->bool`;
                 `(s1:real^1->real^M) ++ (s2 ++ reversepath s1)`]
    HOMOTOPIC_PATHS_RINV) THEN
  ANTS_TAC THENL [MOI_LTW_SIDE_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[PATHSTART_JOIN]);;

let MOI_LTW_EQ1_TAC = FIRST_ASSUM ACCEPT_TAC ORELSE FIRST_ASSUM(ACCEPT_TAC o SYM);;

let MOI_LTW_WORD_4 = prove
 (MOI_LT_WORD_4,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_IMP_HOMOTOPIC_LOOPS THEN
  REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHFINISH_LINEPATH] THEN
  CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `s1:real^1->real^M`; `s2:real^1->real^M`;
                 `s3:real^1->real^M`; `s4:real^1->real^M`;
                 `pathstart(s1:real^1->real^M)`;
                 `pathfinish(s1:real^1->real^M)`] MOI_LTW_W4) THEN
  DISCH_THEN MATCH_MP_TAC THEN MOI_LTW_ENDPOINT_TAC THENL
   [MOI_LTW_EQ2_TAC `pathstart(s2:real^1->real^M)`;
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `pathfinish(s2:real^1->real^M)` THEN
    CONJ_TAC THENL
     [MOI_LTW_EQ1_TAC; MOI_LTW_EQ2_TAC `pathstart(s2:real^1->real^M)`];
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `pathstart(s4:real^1->real^M)` THEN
    CONJ_TAC THENL
     [MOI_LTW_EQ1_TAC; MOI_LTW_EQ2_TAC `pathfinish(s4:real^1->real^M)`];
    MOI_LTW_EQ2_TAC `pathfinish(s4:real^1->real^M)`;
    MATCH_MP_TAC MOI_LTW_CANCEL THEN
    EXISTS_TAC `pathstart(s1:real^1->real^M)` THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `pathstart(s2:real^1->real^M)` THEN
      CONJ_TAC THENL
       [MOI_LTW_EQ1_TAC; MOI_LTW_EQ2_TAC `pathfinish(s2:real^1->real^M)`];
      FIRST_X_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_HOMOTOPIC_PATHS_NULL o
        check (fun th -> try rator(concl th) =
          `homotopic_loops (s:real^M->bool) (s1 ++ s3)` with Failure _ -> false)) THEN
      REWRITE_TAC[PATHSTART_JOIN]];
    FIRST_X_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_HOMOTOPIC_PATHS_NULL o
      check (fun th -> try rator(concl th) =
        `homotopic_loops (s:real^M->bool)
           (s1 ++ reversepath s2 ++ s3 ++ reversepath s4)` with Failure _ -> false)) THEN
    REWRITE_TAC[PATHSTART_JOIN]]);;


(* ========================================================================= *)
(* pc_moi_s34_residstmt: the statements that split s34_resid (Moise Sec     *)
(* 34, pp.244-245, the tetra balls C''(r)) into a local and a global part.  *)
(*   moi_s4x_local tt kk f1 car dd r b : the per-3-simplex clauses of       *)
(*     moi_s34_resid (pc_moi_s34_stmt.ml) for one ball b = C''(r);          *)
(*   MOI_S4X_RESID_A : Schoenflies ==> every 3-simplex r of kk has such a  *)
(*     ball (unit pc_moi_s34_resida, the book's W, X, Y construction);      *)
(*   MOI_S4Y_RESID_B : Schoenflies ==> any family rr of such balls also     *)
(*     satisfies the global clauses (pairwise intersections, the patches    *)
(*     and rim arcs covering A_v and the rims at interior vertices and      *)
(*     edges), so it is a moi_s34_resid family (unit pc_moi_s34_residb);    *)
(*   MOI_S4X_GLUE : |- MOI_S4X_RESID_A ==> MOI_S4Y_RESID_B ==> MOI_S34_RESID *)
(*     (the statement of pc_moi_s34_stmt.ml), proved here by choice.        *)
(* ========================================================================= *)

needs "src/pc_moi_s34_stmt.ml";;

prioritize_real();;
type_invention_error := true;;

let moi_s4x_local = new_definition
 `moi_s4x_local (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool)
                (f1:real^N->real^3) (car:(real^N->bool)->real^3->bool)
                (dd:(real^N->bool)->real^3->bool) (r:real^N->bool) (b:real^3->bool) <=>
   pl_ball 3 b /\
   b SUBSET convex hull (car r) /\
   frontier b =
   UNIONS {dd s | s | s IN moi_s34_simp kk (&2) /\ s SUBSET r} UNION
   (b INTER IMAGE f1 (moi_s34_bd tt kk)) /\
   b INTER IMAGE f1 (moi_s34_nb tt kk) = b INTER IMAGE f1 (moi_s34_bd tt kk) /\
   (!v. {v} IN kk /\ v IN r
        ==> pl_cell_with_boundary 2 (b INTER IMAGE f1 (moi_s34_vb tt kk v))
              (UNIONS {dd s INTER IMAGE f1 (moi_s34_vb tt kk v) | s |
                       s IN moi_s34_simp kk (&2) /\ v IN s /\ s SUBSET r} UNION
               UNIONS {b INTER IMAGE f1 (moi_s34_sd tt kk g) | g |
                       g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET r})) /\
   (!g. g IN moi_s34_simp kk (&1) /\ g SUBSET r
        ==> pl_cell_with_boundary 1 (b INTER IMAGE f1 (moi_s34_sd tt kk g))
              (UNIONS {dd s INTER IMAGE f1 (moi_s34_sd tt kk g) | s |
                       s IN moi_s34_simp kk (&2) /\ g SUBSET s /\ s SUBSET r})) /\
   (!w. {w} IN kk /\ ~(w IN r) ==> DISJOINT b (IMAGE f1 (moi_s34_vb tt kk w))) /\
   (!s. s IN moi_s34_simp kk (&2) /\ ~(s SUBSET r) ==> DISJOINT b (dd s))`;;

let MOI_S4X_RESID_A =
  mk_imp(`PL_SCHOENFLIES_3_STATEMENT`,
 `!(tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool) (h:real^N->real^3)
   (ep:real^N->real) (f1:real^N->real^3) (car:(real^N->bool)->real^3->bool)
   (dd:(real^N->bool)->real^3->bool) r.
     moi_s34_tube tt kk /\ moi_s34_emb h (UNIONS tt) /\
     moi_s34_frame tt kk h ep f1 car /\ moi_s34_fdisk tt kk f1 car dd /\
     r IN moi_s34_simp kk (&3)
     ==> ?b. moi_s4x_local tt kk f1 car dd r b`);;

let MOI_S4Y_RESID_B =
  mk_imp(`PL_SCHOENFLIES_3_STATEMENT`,
 `!(tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool) (h:real^N->real^3)
   (ep:real^N->real) (f1:real^N->real^3) (car:(real^N->bool)->real^3->bool)
   (dd:(real^N->bool)->real^3->bool) (rr:(real^N->bool)->real^3->bool).
     moi_s34_tube tt kk /\ moi_s34_emb h (UNIONS tt) /\
     moi_s34_frame tt kk h ep f1 car /\ moi_s34_fdisk tt kk f1 car dd /\
     (!r. r IN moi_s34_simp kk (&3) ==> moi_s4x_local tt kk f1 car dd r (rr r))
     ==> moi_s34_resid tt kk f1 car dd rr`);;

(* ------------------------------------------------------------------------- *)
(* The glue MOI_S4X_GLUE and sanity checks.                                  *)
(* ------------------------------------------------------------------------- *)

let MOI_S4X_LOCAL_RESID = prove
 (`!(tt:(real^N->bool)->bool) kk (f1:real^N->real^3) car dd rr.
     moi_s34_resid tt kk f1 car dd rr
     ==> !r. r IN moi_s34_simp kk (&3) ==> moi_s4x_local tt kk f1 car dd r (rr r)`,
  REWRITE_TAC[moi_s34_resid; moi_s4x_local] THEN MESON_TAC[]);;

let MOI_S4X_GLUE = prove
 (mk_imp(MOI_S4X_RESID_A,mk_imp(MOI_S4Y_RESID_B,MOI_S34_RESID)),
  DISCH_THEN(LABEL_TAC "a") THEN DISCH_THEN(LABEL_TAC "b") THEN
  DISCH_THEN(LABEL_TAC "sch") THEN
  MAP_EVERY X_GEN_TAC
   [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
    `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
    `dd:(real^N->bool)->real^3->bool`] THEN
  STRIP_TAC THEN
  EXISTS_TAC `\r:real^N->bool. @b:real^3->bool. moi_s4x_local tt kk f1 car dd r b` THEN
  USE_THEN "sch" (fun sch -> USE_THEN "b" (fun b -> MATCH_MP_TAC (MP b sch))) THEN
  MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN CONV_TAC SELECT_CONV THEN
  USE_THEN "sch" (fun sch -> USE_THEN "a" (fun a -> MATCH_MP_TAC (MP a sch))) THEN
  MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`] THEN
  ASM_REWRITE_TAC[]);;

let _ = Printf.printf "RESIDSTMT_GLUE %b\n%!"
  (aconv (concl MOI_S4X_GLUE) (mk_imp(MOI_S4X_RESID_A,mk_imp(MOI_S4Y_RESID_B,MOI_S34_RESID))) &&
   hyp MOI_S4X_GLUE = []);;


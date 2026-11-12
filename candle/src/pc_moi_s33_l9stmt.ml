(* ========================================================================= *)
(* pc_moi_s33_l9stmt: the statements of the three parts of the proof of     *)
(* Lemma 9 (Moise GTM 47, p.234).                                           *)
(*   moi_s39_pcs l e: the union of the pseudo-cells of the edges.           *)
(*   moi_s39_family l e x d cs: d meets the pseudo-cells in a finite family *)
(*   cs of pairwise disjoint PL circles missing Bd X and PL arcs whose      *)
(*   ends are their intersection with Bd X.                                 *)
(*   MOI_S39_GP_BODY (proved in pc_moi_s33_gp; DG                           *)
(*   exists_isLoopTheoremDisk_levelSet): every loop theorem disk can be     *)
(*   replaced by one in general position against the pseudo-cells.          *)
(*   MOI_S39_PUSH_BODY (proved in pc_moi_s33_push; DG                       *)
(*   exists_isLoopTheoremDisk_pushOff): the part of a loop theorem disk     *)
(*   inside an open u in W that lies in one piece c v and meets the         *)
(*   pseudo-cells only in a compact z can be pushed off the pseudo-cells    *)
(*   inside u.                                                              *)
(*   MOI_S39_L9_FROM (proved in pc_moi_s33_l9):                             *)
(*   GP /\ PUSH ==> MOI_S33_L9.                                             *)
(* Glue MOI_S39D_L9; sanity MOI_S39D_SAN_FAMILY_EMPTY.                      *)
(* ========================================================================= *)

needs "src/pc_moi_s33_stmt.ml";;

prioritize_real();;
type_invention_error := true;;

let moi_s39_pcs = new_definition
 `moi_s39_pcs (l:(real^3->bool)->bool) (e:(real^3->bool)->real^3->bool) =
    UNIONS {e s | s IN l /\ aff_dim s = &1}`;;

let moi_s39_family = new_definition
 `moi_s39_family (l:(real^3->bool)->bool) (e:(real^3->bool)->real^3->bool)
                 (x:(real^3->bool)->bool) (d:real^3->bool) (cs:(real^3->bool)->bool) <=>
    FINITE cs /\ pairwise DISJOINT cs /\
    d INTER moi_s39_pcs l e = UNIONS cs /\
    !a. a IN cs
        ==> (pl_sphere 1 a /\ DISJOINT a (frontier (UNIONS x))) \/
            pl_cell_with_boundary 1 a (a INTER frontier (UNIONS x))`;;

let MOI_S39_GP_BODY =
 `!(t:(real^3->bool)->bool) (l:(real^3->bool)->bool) (h:real^3->real^3)
   (e:(real^3->bool)->real^3->bool) (c:real^3->real^3->bool)
   (x:(real^3->bool)->bool) (d:real^3->bool).
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\ moi_s33_ltd t l h x d
     ==> ?d' cs. moi_s33_ltd t l h x d' /\ moi_s39_family l e x d' cs`;;

let MOI_S39_PUSH_BODY =
 `!(t:(real^3->bool)->bool) (l:(real^3->bool)->bool) (h:real^3->real^3)
   (e:(real^3->bool)->real^3->bool) (c:real^3->real^3->bool)
   (x:(real^3->bool)->bool) (v:real^3) (d:real^3->bool) (u:real^3->bool)
   (z:real^3->bool).
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\ {v} IN l /\
     moi_s33_ltd t l h x d /\ open u /\ u SUBSET moi_s33_ww t l h /\
     compact z /\ z SUBSET u INTER c v /\ d INTER u SUBSET c v /\
     d INTER u INTER moi_s39_pcs l e SUBSET z
     ==> ?d'. moi_s33_ltd t l h x d' /\
              d' INTER moi_s39_pcs l e = (d DIFF u) INTER moi_s39_pcs l e`;;

let MOI_S39_L9_FROM =
  mk_imp(mk_conj(MOI_S39_GP_BODY,MOI_S39_PUSH_BODY), MOI_S33_L9);;

let MOI_S39_UNIT_TARGETS = [MOI_S39_GP_BODY; MOI_S39_PUSH_BODY; MOI_S39_L9_FROM];;

if not (forall (fun t -> type_of t = bool_ty && frees t = []) MOI_S39_UNIT_TARGETS)
then failwith "MOI_S39_UNIT_TARGETS: not closed booleans";;

(* Glue: the three statements give Lemma 9, MOI_S33_L9.                     *)

let MOI_S39D_L9 = prove
 (mk_imp(list_mk_conj MOI_S39_UNIT_TARGETS, MOI_S33_L9),
  DISCH_THEN(fun th ->
    let gp,rest = CONJ_PAIR th in
    let pu,fr = CONJ_PAIR rest in
    ACCEPT_TAC(MP fr (CONJ gp pu))));;

(* Sanity: a disk missing the pseudo-cells is in general position with the *)
(* empty family (the degenerate case of GP: d' = d, cs = {}).              *)

let MOI_S39D_SAN_FAMILY_EMPTY = prove
 (`!(l:(real^3->bool)->bool) (e:(real^3->bool)->real^3->bool)
    (x:(real^3->bool)->bool) (d:real^3->bool).
     d INTER moi_s39_pcs l e = {} ==> moi_s39_family l e x d {}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[moi_s39_family; FINITE_EMPTY; PAIRWISE_EMPTY; UNIONS_0;
                  NOT_IN_EMPTY]);;

let moi_s39_check =
  hyp MOI_S39D_L9 = [] && hyp MOI_S39D_SAN_FAMILY_EMPTY = [] &&
  aconv (rand (concl MOI_S39D_L9)) MOI_S33_L9 &&
  length MOI_S39_UNIT_TARGETS = 3;;

if not moi_s39_check then failwith "moi_s39_check";;

print_string ("S39 " ^
   string_of_bool (moi_s39_check) ^
   "\n");;


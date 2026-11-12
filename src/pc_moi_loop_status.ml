(* ========================================================================= *)
(* pc_moi_loop_status: the loop theorem (C25) in the form the PL core needs. *)
(* The PL core (pc_moi_core_status.ml) uses five loop items: the producers   *)
(* n7 MOI_CORE_GLUE_LOOPN and nm7 MOI_PROD_LOOP_NS and the leaves            *)
(* LOOP_SPHERE_CASE (:7) (:7), DOUBLE_COVER (:7) and LOOP_DESCENT (:7) (:7). *)
(* For each item this file derives the item from the statements of the loop  *)
(* files (at :7) through the glue of pc_moi_loop_stmt (MOI_LTD_...),         *)
(* pc_moi_loop_stmt2 (MOI_LT2D_...), pc_moi_loop_stmt3 (MOI_LT3D_...) and    *)
(* pc_moi_fnd_stmt (MOI_FD_...), and discharges these statements by the      *)
(* theorems of the files loaded below (MOI_LTST_PROVED_THMS), so that every  *)
(* item is a theorem with no hypotheses. The double-arc cut goes through the *)
(* buffered terms of pc_moi_loop_stmt4 and their split in pc_moi_lt_cutbstmt *)
(* (ARC_FROM_SEAM, SEAM).  MOI_LTST_LOOP_THEOREM_3 :                         *)
(*   |- LOOP_THEOREM_3_STATEMENT,                                            *)
(* through the C25 closure of pc_moi_loop_stmt4 with no hypothesis left.     *)
(* ========================================================================= *)

needs "src/pc_moi_lt_cutbstmt.ml";;
needs "src/pc_moi_lt_gpbstmt.ml";;
needs "src/pc_moi_lt_cova.ml";;
needs "src/pc_moi_lt_coverb.ml";;
needs "src/pc_moi_lt_tower.ml";;
needs "src/pc_moi_lt_cuta1.ml";;
needs "src/pc_moi_lt_gpa.ml";;
needs "src/pc_moi_lt_nsys.ml";;
needs "src/pc_moi_lt_words.ml";;
needs "src/pc_moi_fnd_m3b.ml";;
needs "src/pc_moi_lt_gpc.ml";;
needs "src/pc_moi_lt_cuta2.ml";;
needs "src/pc_moi_lt_orient.ml";;
needs "src/pc_moi_lt_sphere.ml";;
needs "src/pc_moi_fnd_z2.ml";;
needs "src/pc_moi_fnd_cover.ml";;
needs "src/pc_moi_lt_case1.ml";;
needs "src/pc_moi_lt_cap.ml";;
needs "src/pc_moi_lt_gpb2.ml";;
needs "src/pc_moi_lt_gpb1.ml";;
needs "src/pc_moi_lt_seam.ml";;
needs "src/pc_moi_lt_cutb.ml";;
needs "src/pc_moi_lt_fill.ml";;
needs "src/pc_moi_cglue.ml";;

prioritize_real();;
type_invention_error := true;;

(* The type instance of the core (:7 for both N and M), the theorems of the  *)
(* loop files, and the lookup of a statement among them.                     *)

let moi_ltst_ity = [`:7`,`:N`; `:7`,`:M`];;

let MOI_LTST_PROVED_THMS =
  [COVER_LIFT_CELLWISE; COVER_BOUNDARY; DESCENT_INPUT;
   NO_SECTION; COMPLEXITY_LIFT; CELLWISE_FINITE; NEXT_SYSTEM;
   FROZEN_TO_CELL; SPHERE_STEP;
   INNERMOST_FROM_EXCL; GP_SIMPLICIAL; NSYS;
   MOI_LTW_WORD_3; MOI_LTW_WORD_4;
   COMBINATORIAL_WB_BARYCENTRIC; CM_WB_DIM;
   CROSSINGS_NORMAL; SWAP_FROM_CAP; ORIENT_SIGN; SPHERE_HOLE; PUSH_IN_DISK;
   Z2_COCYCLE_NONSPHERE_BOUNDARY; DOUBLE_COVER_OF_COCYCLE;
   CASE1_FROM_ORIENT; CLEAN_CAP; GP_FROM_STEP; CHART_STEP; ARC_FROM_SEAM; SEAM;
   LT_FILL];;

let moi_ltst_proved7 = map (INST_TYPE moi_ltst_ity) MOI_LTST_PROVED_THMS;;

let moi_ltst_lookup t =
  let t7 = inst moi_ltst_ity t in
  try Some (find (fun th -> aconv (concl th) t7) moi_ltst_proved7)
  with Failure _ -> None;;

(* Split a theorem of list_mk_conj [t1; ...; tn] into exactly n theorems,  *)
(* also when tn is itself a conjunction.                                    *)

let rec moi_ltst_split n th =
  if n <= 1 then [th] else
  let a,b = CONJ_PAIR th in a :: moi_ltst_split (n - 1) b;;

(* An item: the statements it needs (in the order derive expects them) and   *)
(* the derivation from their theorems at :7. The result is the item with the *)
(* conjunction of the statements that have no theorem in                     *)
(* MOI_LTST_PROVED_THMS (at :7) as its only antecedent, or the item itself   *)
(* when there are none, as for every item here; those statements are         *)
(* returned too.                                                             *)

let moi_ltst_item (needed:term list) (derive:thm list -> thm) =
  let opens = filter (fun t -> moi_ltst_lookup t = None) needed in
  let opens7 = map (inst moi_ltst_ity) opens in
  if opens7 = [] then
    derive (map (fun t -> match moi_ltst_lookup t with
                            Some th -> th | None -> failwith "moi_ltst_item") needed), []
  else
    let hconj = list_mk_conj opens7 in
    let asm = moi_ltst_split (length opens7) (ASSUME hconj) in
    let get t = match moi_ltst_lookup t with
                  Some th -> th
                | None -> let t7 = inst moi_ltst_ity t in
                          find (fun th -> aconv (concl th) t7) asm in
    DISCH hconj (derive (map get needed)), opens;;

let moi_ltst_it th = INST_TYPE moi_ltst_ity th;;
let moi_ltst_u7 = `(:7)`;;

(* Item 1: n7 MOI_CORE_GLUE_LOOPN from FILL (lt_fill), NSYS (lt_nsys) and   *)
(* the barycentric subdivision of a combinatorial 3-manifold (fnd_m3b).     *)

let moi_ltst_glue_loopn_pair =
  moi_ltst_item [MOI_LT_FILL; MOI_LT_NSYS; MOI_FND_BARYCENTRIC_CM_WB]
   (fun ths -> MP (moi_ltst_it MOI_LTD_LOOPN) (end_itlist CONJ ths));;

let MOI_LTST_GLUE_LOOPN = fst moi_ltst_glue_loopn_pair;;
let MOI_LTST_GLUE_LOOPN_OPEN = snd moi_ltst_glue_loopn_pair;;

(* Item 2: nm7 MOI_PROD_LOOP_NS from the cover and tower statements.        *)

let moi_ltst_prod_loop_ns_pair =
  moi_ltst_item
   [MOI_LT_COVER_LIFT_CELLWISE; MOI_LT_COVER_BOUNDARY;
    MOI_LT_NO_SECTION; MOI_LT_COMPLEXITY_LIFT;
    MOI_LT_CELLWISE_FINITE; MOI_LT_NEXT_SYSTEM;
    MOI_LT_SPHERE_STEP; MOI_LT_DESCENT_INPUT;
    MOI_LT_FROZEN_TO_CELL]
   (fun ths -> MP (moi_ltst_it MOI_LTD_PROD_LOOP_NS) (end_itlist CONJ ths));;

let MOI_LTST_PROD_LOOP_NS = fst moi_ltst_prod_loop_ns_pair;;
let MOI_LTST_PROD_LOOP_NS_OPEN = snd moi_ltst_prod_loop_ns_pair;;

(* Item 3: LOOP_SPHERE_CASE (:7) (:7) from the two statements of lt_sphere. *)

let moi_ltst_sphere_pair =
  moi_ltst_item [MOI_LT_SPHERE_HOLE; MOI_LT_PUSH_IN_DISK]
   (fun ths -> SPECL [moi_ltst_u7; moi_ltst_u7]
                 (MP (moi_ltst_it MOI_LTD_SPHERE) (end_itlist CONJ ths)));;

let MOI_LTST_SPHERE = fst moi_ltst_sphere_pair;;
let MOI_LTST_SPHERE_OPEN = snd moi_ltst_sphere_pair;;

(* Item 4: DOUBLE_COVER (:7) from fnd_z2, fnd_cover and CM_WB_DIM.          *)

let moi_ltst_double_cover_pair =
  moi_ltst_item
   [MOI_FND_COCYCLE_NONSPHERE_BOUNDARY; MOI_FND_DOUBLE_COVER_OF_COCYCLE;
    MOI_FND_CM_WB_DIM]
   (fun ths -> MP (INST_TYPE [`:7`,`:N`] MOI_FD_DOUBLE_COVER_GLUE)
                  (end_itlist CONJ ths));;

let MOI_LTST_DOUBLE_COVER = fst moi_ltst_double_cover_pair;;
let MOI_LTST_DOUBLE_COVER_OPEN = snd moi_ltst_double_cover_pair;;

(* Item 5: LOOP_DESCENT (:7) (:7) from the general position, closed-cut and  *)
(* arc-cut statements (the refinements of pc_moi_loop_stmt2 and              *)
(* pc_moi_loop_stmt3).                                                       *)

let moi_ltst_descent_pair =
  moi_ltst_item
   [MOI_LT_GP_SIMPLICIAL; MOI_LGB_CHART_STEP; MOI_LGB_GP_FROM_STEP;
    MOI_LT_CROSSINGS_NORMAL;
    MOI_LT3_INNERMOST_FROM_EXCL; MOI_LT3_CASE1_FROM_ORIENT; MOI_LT_ORIENT_SIGN;
    MOI_LT3_SWAP_FROM_CAP; MOI_LT3_CLEAN_CAP;
    MOI_LCUS_ARC_FROM_SEAM; MOI_LCUS_SEAM; MOI_LT_WORD_3; MOI_LT_WORD_4]
   (fun ths ->
      match ths with
        [gps; chs; gfs; crn; inx; c1o; ors; swc; cap; afs; sea; w3; w4] ->
          let it = moi_ltst_it in
          let gpcr = MP gfs chs in
          let crn2 = MP (it MOI_LT2D_CROSSINGS_NORMAL_BRIDGE) crn in
          let gp = MP (it MOI_LT2D_GP) (CONJ gps (CONJ gpcr crn2)) in
          let inn = MP (it MOI_LT3D_CUT_INNERMOST) (CONJ inx (CONJ c1o ors)) in
          let swp = MP (it MOI_LT3D_CUT_SWAP) (CONJ swc cap) in
          let cc = MP (it MOI_LT2D_CUT_CLOSED) (CONJ inn swp) in
          let arc = MP (it MOI_LCUSD_CUT_ARC_SPLIT) (CONJ afs sea) in
          let ca = MP (it MOI_LT4D_CUT_ARC) (CONJ arc (CONJ w3 w4)) in
          let ld = MP (it MOI_LT4D_DESCENT) (CONJ gp (CONJ cc ca)) in
          SPECL [moi_ltst_u7; moi_ltst_u7] ld
      | _ -> failwith "MOI_LTST_DESCENT");;

let MOI_LTST_DESCENT = fst moi_ltst_descent_pair;;
let MOI_LTST_DESCENT_OPEN = snd moi_ltst_descent_pair;;

(* Item 6: LOOP_THEOREM_3_STATEMENT itself, through the C25 closure          *)
(* MOI_LT4D_C25_CLOSURE of pc_moi_loop_stmt4 with every hypothesis           *)
(* discharged: the statements of MOI_LT4_UNIT_TARGETS by                     *)
(* MOI_LTST_PROVED_THMS, the three derived ones (GP_CROSSINGS from the chart *)
(* step, CROSSINGS_NORMAL by the bridge, CUT_ARC_SPLIT from the b1/b2 split, *)
(* as in item 5) and the core glue MOI_CGL_LOOP3 of pc_moi_cglue. Fails,     *)
(* naming the term, if a theorem is missing.                                 *)

let MOI_LTST_LOOP_THEOREM_3 =
  let it = moi_ltst_it in
  let get t = match moi_ltst_lookup t with
                Some th -> th
              | None -> failwith ("MOI_LTST_LOOP_THEOREM_3: open " ^ string_of_term t) in
  let gpcr = MP (get MOI_LGB_GP_FROM_STEP) (get MOI_LGB_CHART_STEP) in
  let crn2 = MP (it MOI_LT2D_CROSSINGS_NORMAL_BRIDGE) (get MOI_LT_CROSSINGS_NORMAL) in
  let arc = MP (it MOI_LCUSD_CUT_ARC_SPLIT)
               (CONJ (get MOI_LCUS_ARC_FROM_SEAM) (get MOI_LCUS_SEAM)) in
  let pool = moi_ltst_proved7 @ [gpcr; crn2; arc; MOI_CGL_LOOP3] in
  let hs = map (inst moi_ltst_ity) (MOI_LT4_UNIT_TARGETS @ MOI_LT_FND_TERMS) @
           [MOI_CORE_GLUE_LOOP3] in
  let find_h h =
    try find (fun th -> aconv (concl th) h) pool
    with Failure _ -> failwith ("MOI_LTST_LOOP_THEOREM_3: no theorem for " ^
                                string_of_term h) in
  MP MOI_LT4D_C25_CLOSURE (end_itlist CONJ (map find_h hs));;

(* The five items: their core terms, theorems and lists of missing           *)
(* statements (all empty).                                                   *)

let MOI_LTST_ITEMS =
  [n7 MOI_CORE_GLUE_LOOPN, MOI_LTST_GLUE_LOOPN, MOI_LTST_GLUE_LOOPN_OPEN;
   nm7 MOI_PROD_LOOP_NS, MOI_LTST_PROD_LOOP_NS, MOI_LTST_PROD_LOOP_NS_OPEN;
   `LOOP_SPHERE_CASE_STATEMENT (:7) (:7)`, MOI_LTST_SPHERE, MOI_LTST_SPHERE_OPEN;
   `DOUBLE_COVER_STATEMENT (:7)`, MOI_LTST_DOUBLE_COVER, MOI_LTST_DOUBLE_COVER_OPEN;
   `LOOP_DESCENT_STATEMENT (:7) (:7)`, MOI_LTST_DESCENT, MOI_LTST_DESCENT_OPEN];;

(* Shape check: each item theorem has no hypotheses and concludes its core   *)
(* term, directly when no statement is missing (as here), else under exactly *)
(* the conjunction of the missing statements at :7.                          *)

let moi_ltst_item_ok (t,th,opens) =
  hyp th = [] &&
  (if opens = [] then aconv (concl th) t
   else aconv (concl th)
          (mk_imp(list_mk_conj (map (inst moi_ltst_ity) opens), t)));;

let MOI_LTST_CHECK = forall moi_ltst_item_ok MOI_LTST_ITEMS;;

let MOI_LTST_OPEN =
  itlist (fun (_,_,opn) acc -> union' aconv opn acc) MOI_LTST_ITEMS [];;

Printf.printf "LTST %b items %d open %d [%s]\n%!" MOI_LTST_CHECK
  (length MOI_LTST_ITEMS) (length MOI_LTST_OPEN)
  (String.concat "; " (map (fun (_,_,opn) -> string_of_int (length opn)) MOI_LTST_ITEMS));;


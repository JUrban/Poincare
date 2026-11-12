(* ========================================================================= *)
(* Tracing the development in parts.  Loaded right after HOL Light's core,   *)
(* in the repository root, by the tracing sessions (trace_part0.ml,          *)
(* trace_part.ml) and by the untraced recording session (record_counter.ml). *)
(*                                                                            *)
(* Each file is loaded in full mode or in stub mode.  In stub mode every      *)
(* top-level prove (and each of the derived rules wrapped below) returns an   *)
(* axiom of the same statement instead of proving it; in full mode every such *)
(* theorem is named HTLINK_k in the trace.  The replay (replay.ml) matches    *)
(* each stub axiom with the theorem of the same statement restored from an    *)
(* earlier part, so no axiom is added there.                                  *)
(*   - the base library (Multivariate up to cauchy.ml, lpspaces.ml and        *)
(*     100/green.ml): full in part 0, stub in the other parts;                *)
(*   - files of src/: full in the part they belong to, stub in later parts;   *)
(*   - other library files (loaded by files of src/): full.                   *)
(* After the base library, a statement is stubbed only if a full load proved  *)
(* it (recorded by record_counter.ml); any other proof is done in full, so    *)
(* that a proof that fails in a full load also fails here.  A file of src/ in *)
(* stub mode is loaded from a copy in which each prove (t, tac) reads         *)
(* ht_prove_lazy (t, (fun () -> tac)): the tactic, and the terms and rules in *)
(* it, are built only if the proof is done in full.                          *)
(*                                                                            *)
(* Names made from counters.  A definition must be the same in every part,   *)
(* and two kinds of names in definitions come from counters that skipped      *)
(* proofs would leave behind: type variables invented by the parser (?N),     *)
(* which many constants of the base library have, and the names of the       *)
(* auxiliary constants of define_type (_N, from genvar).  So                  *)
(*   - in the base library, after each skipped proof the parser's counter is  *)
(*     set to its value in a full load (recorded once by record_counter.ml);  *)
(*   - after the base library, each library file loaded starts with the       *)
(*     parser's counter at a fixed value (some, such as 100/pick.ml, are       *)
(*     loaded with invented types allowed), and each define_type starts with  *)
(*     the genvar counter at a fixed value.                                    *)
(* Both counters are local to HOL Light, so they are reached through the      *)
(* closures of retypecheck and genvar (module Obj).  They only affect names:  *)
(* a wrong value would make the replay reject a trace, not accept a theorem.  *)
(* ========================================================================= *)

let ht_base_full = ref false;;
let ht_in_base = ref true;;
let ht_home = ref ([] : string list);;
let ht_root = Sys.getcwd ();;
let ht_stack = ref ([] : bool list);;
let ht_record_file = Sys.getenv_opt "HT_RECORD";;
let ht_stub () =
  ht_record_file = None && (match !ht_stack with b :: _ -> b | [] -> false);;
let ht_count = ref 0 and ht_stubs = ref 0;;
let ht_name th =
  incr ht_count; holtrace_nameonethm (Printf.sprintf "HTLINK_%d" !ht_count, th);;
let ht_stub_thm t = incr ht_stubs; new_axiom t;;
let ht_rel p =
  let pre = ht_root ^ "/" in
  let n = String.length pre in
  if String.length p > n && String.sub p 0 n = pre then Some (String.sub p n (String.length p - n))
  else None;;
let ht_is_project p =
  match ht_rel p with
  | Some r -> (String.length r > 4 && String.sub r 0 4 = "src/") ||
              (String.length r > 6 && String.sub r 0 6 = "audit/")
  | None -> false;;
let ht_stub_mode p =
  if !ht_in_base then not !ht_base_full
  else if ht_is_project p then
    (match ht_rel p with Some r -> not (List.mem r !ht_home) | None -> true)
  else false;;

(* The int refs reachable from a closure; the counter is the one that a call  *)
(* advances by 1.  Finding it calls the function once, so the counter is put  *)
(* back afterwards: loading this file leaves both counters unchanged.         *)
let ht_int_refs (f : Obj.t) =
  let cands = ref [] and seen = ref [] in
  let rec walk depth (ob : Obj.t) =
    if depth > 3 || Obj.is_int ob || List.memq ob !seen then () else begin
      seen := ob :: !seen;
      let tag = Obj.tag ob in
      if tag = 0 && Obj.size ob = 1 && Obj.is_int (Obj.field ob 0) then cands := ob :: !cands;
      if tag = Obj.closure_tag || tag = 0 then
        for i = 0 to Obj.size ob - 1 do
          let fl = Obj.field ob i in
          if not (Obj.is_int fl) then walk (depth + 1) fl
        done
    end in
  walk 0 f; !cands;;
let ht_find_counter f (call : unit -> int) =
  let cands = ht_int_refs f in
  let value c = (Obj.obj (Obj.field c 0) : int) in
  let before = List.map value cands in
  let n = call () in
  let hits = List.filter (fun (c,b) -> b = n && value c = n + 1) (List.combine cands before) in
  match hits with
  | [c,_] -> let r = (Obj.obj c : int ref) in r := n; r
  | _ -> failwith "ht_find_counter: counter not found";;
(* The parser's counter of invented type variables. *)
let ht_counter = ht_find_counter (Obj.repr retypecheck)
  (fun () -> match retypecheck [] (Varp("x",dpty)) with
             | Varp(_,Stv n) -> n | _ -> failwith "ht_counter: unexpected parse");;
(* The genvar counter. *)
let ht_gv_counter = ht_find_counter (Obj.repr genvar)
  (fun () -> let s = fst (dest_var (genvar bool_ty)) in
             int_of_string (String.sub s 1 (String.length s - 1)));;

(* The text of a file with each  prove (A, B)  replaced by                   *)
(* ht_prove_lazy (A, (fun () -> B)), so that the tactic B is built only if   *)
(* the proof is done.  Comments, strings, quotations and character literals *)
(* are skipped; a call whose argument has no comma at its top level is left  *)
(* as it is.                                                                  *)
let ht_lazy_text (s : string) : string * int =
  let n = String.length s in
  let is_id c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
                (c >= '0' && c <= '9') || c = '_' || c = '\'' in
  let rec skip_comment i d =
    if i >= n then n
    else if i + 1 < n && s.[i] = '(' && s.[i+1] = '*' then skip_comment (i + 2) (d + 1)
    else if i + 1 < n && s.[i] = '*' && s.[i+1] = ')' then
      (if d = 1 then i + 2 else skip_comment (i + 2) (d - 1))
    else if s.[i] = '"' then skip_comment (skip_string (i + 1)) d
    else skip_comment (i + 1) d
  and skip_string i =
    if i >= n then n else if s.[i] = '\\' then skip_string (i + 2)
    else if s.[i] = '"' then i + 1 else skip_string (i + 1) in
  let skip_quot i = match String.index_from_opt s i '`' with Some j -> j + 1 | None -> n in
  (* the index after the token starting at i that is not code: a comment, a  *)
  (* string, a quotation or a character literal; i itself otherwise.          *)
  let skip_noncode i =
    let c = s.[i] in
    if c = '(' && i + 1 < n && s.[i+1] = '*' then skip_comment (i + 2) 1
    else if c = '"' then skip_string (i + 1)
    else if c = '`' then skip_quot (i + 1)
    else if c = '\'' && (i = 0 || not (is_id s.[i-1])) then
      (if i + 2 < n && s.[i+1] <> '\\' && s.[i+2] = '\'' then i + 3
       else if i + 1 < n && s.[i+1] = '\\' then
         (match String.index_from_opt s (i + 2) '\'' with Some j -> j + 1 | None -> n)
       else i)
    else i in
  let count = ref 0 in
  (* write the lazy text of the characters a to b - 1 of s to buf *)
  let rec emit buf a b =
    let i = ref a in
    while !i < b do
      let j = skip_noncode !i in
      if j > !i then (Buffer.add_string buf (String.sub s !i (j - !i)); i := j)
      else if !i + 5 <= b && String.sub s !i 5 = "prove" &&
              (!i = 0 || not (is_id s.[!i - 1])) &&
              (!i + 5 >= n || not (is_id s.[!i + 5])) then begin
        (* find the opening parenthesis after optional white space *)
        let k = ref (!i + 5) in
        while !k < b && (s.[!k] = ' ' || s.[!k] = '\n' || s.[!k] = '\t' || s.[!k] = '\r') do incr k done;
        if !k < b && s.[!k] = '(' && not (!k + 1 < n && s.[!k + 1] = '*') then begin
          (* find the matching parenthesis and the first comma at depth 1 *)
          let d = ref 1 and p = ref (!k + 1) and comma = ref (-1) in
          while !d > 0 && !p < b do
            let q = skip_noncode !p in
            if q > !p then p := q else begin
              (match s.[!p] with
               | '(' | '[' | '{' -> incr d
               | ')' | ']' | '}' -> decr d
               | ',' -> if !d = 1 && !comma < 0 then comma := !p
               | _ -> ());
              incr p
            end
          done;
          if !d = 0 && !comma > 0 then begin
            incr count;
            Buffer.add_string buf "ht_prove_lazy";
            Buffer.add_string buf (String.sub s (!i + 5) (!k - !i - 5));
            Buffer.add_char buf '(';
            emit buf (!k + 1) !comma;
            Buffer.add_string buf ",(fun () ->";
            emit buf (!comma + 1) (!p - 1);
            Buffer.add_string buf "))";
            i := !p
          end else (Buffer.add_string buf "prove"; i := !i + 5)
        end else (Buffer.add_string buf "prove"; i := !i + 5)
      end else begin
        (* copy an identifier whole, so that a suffix of it is not matched *)
        if is_id s.[!i] then begin
          let k = ref !i in
          while !k < b && is_id s.[!k] do incr k done;
          Buffer.add_string buf (String.sub s !i (!k - !i)); i := !k
        end else (Buffer.add_char buf s.[!i]; incr i)
      end
    done in
  let buf = Buffer.create (n + n / 8) in
  emit buf 0 n;
  (Buffer.contents buf, !count);;

(* Load file p from its lazy text (a temporary copy), and mark p loaded.     *)
let ht_lazy_loads = ref 0;;
let ht_load_lazy p =
  let ic = Stdlib.open_in_bin p in
  let s = really_input_string ic (in_channel_length ic) in
  Stdlib.close_in ic;
  let t, _ = ht_lazy_text s in
  let tmp = Filename.temp_file "ht_lazy_" ("_" ^ Filename.basename p) in
  let oc = Stdlib.open_out_bin tmp in
  output_string oc t; Stdlib.close_out oc;
  incr ht_lazy_loads;
  (try use_file tmp with e -> (Sys.remove tmp; raise e));
  Sys.remove tmp;
  loaded_files := (Filename.basename p, Digest.file p) :: !loaded_files;;

(* After the base library, each library file starts with the parser's counter *)
(* at a fixed value, larger than the counter ever gets otherwise.             *)
let ht_lib_loads = ref 0;;
let ht_with_mode p f x =
  if not !ht_in_base && not (ht_is_project p) then
    (incr ht_lib_loads; ht_counter := max !ht_counter (1000000000 + 10000000 * !ht_lib_loads));
  let stub = ht_stub_mode p in
  ht_stack := stub :: !ht_stack;
  (try if stub && not !ht_in_base && ht_is_project p then ht_load_lazy p else f x
   with e -> (ht_stack := List.tl !ht_stack; raise e));
  ht_stack := List.tl !ht_stack;;
let ht_orig_needs = needs and ht_orig_loadt = loadt and ht_orig_loads = loads;;
let needs s =
  let p = file_on_path (!load_path) s in
  if List.mem (Filename.basename p, Digest.file p) !loaded_files then ht_orig_needs s
  else ht_with_mode p ht_orig_needs s;;
let loadt s = ht_with_mode (file_on_path (!load_path) s) ht_orig_loadt s;;
let loads s = ht_with_mode (file_on_path ["$"] s) ht_orig_loads s;;
(* After the base library, each define_type starts with the genvar counter at *)
(* a fixed value, larger than the counter ever gets otherwise.               *)
let ht_define_types = ref 0;;
let ht_orig_define_type = define_type;;
let define_type s =
  if not !ht_in_base then
    (incr ht_define_types;
     ht_gv_counter := max !ht_gv_counter (1000000000000 + 10000000000 * !ht_define_types));
  ht_orig_define_type s;;

(* An alpha-invariant hash of a term that ignores types (as in replay.ml), to *)
(* check that a session and the recording are at the same proof, and one     *)
(* that includes types, for the statements proved in a full load.           *)
let rec ht_ahash bvs tm =
  if is_var tm then
    (try 2 * index tm bvs + 1 with Failure _ -> 2 * Hashtbl.hash (fst (dest_var tm)))
  else if is_const tm then 2 * Hashtbl.hash (fst (dest_const tm))
  else if is_comb tm then
    let f, x = dest_comb tm in (31 * ht_ahash bvs f + 17 * ht_ahash bvs x + 3) land max_int
  else let v, b = dest_abs tm in (13 * ht_ahash (v :: bvs) b + 5) land max_int;;
let rec ht_tyhash ty =
  if is_vartype ty then Hashtbl.hash (dest_vartype ty) else
  let s, args = dest_type ty in
  List.fold_left (fun a t -> (37 * a + ht_tyhash t + 1) land max_int) (Hashtbl.hash s) args;;
let rec ht_thash bvs tm =
  if is_var tm then
    (try 2 * index tm bvs + 1 with Failure _ ->
       (2 * Hashtbl.hash (fst (dest_var tm)) + 7 * ht_tyhash (type_of tm)) land max_int)
  else if is_const tm then
    (2 * Hashtbl.hash (fst (dest_const tm)) + 11 * ht_tyhash (type_of tm)) land max_int
  else if is_comb tm then
    let f, x = dest_comb tm in (31 * ht_thash bvs f + 17 * ht_thash bvs x + 3) land max_int
  else let v, b = dest_abs tm in
       (13 * ht_thash (v :: bvs) b + 19 * ht_tyhash (type_of v) + 5) land max_int;;

(* Top-level proofs are numbered in load order (ht_seq).  In the base         *)
(* library the recording session writes "k counter hash" after the k-th, and *)
(* a tracing session sets the counter after each skipped proof (and checks   *)
(* it after each proof done in full: ht_tv_off counts the differences).      *)
(* After the base library the recording session writes "P hash" for the      *)
(* statement of every proof that succeeds, at any depth (ht_proved).         *)
let ht_seq = ref 0 and ht_depth = ref 0 and ht_tv_off = ref 0 and ht_unproved = ref 0;;
let ht_rec_out = match ht_record_file with Some f -> Some (Stdlib.open_out f) | None -> None;;
let ht_counts = (Hashtbl.create 200000 : (int, int * int) Hashtbl.t);;
let ht_proved = (Hashtbl.create 200000 : (int, unit) Hashtbl.t);;
(* HT_COUNTS is read up to its last complete line; trace_spine.ml reads the *)
(* lines that the running record adds later.                                *)
let ht_counts_pos = ref 0;;
let ht_read_counts () =
  match Sys.getenv_opt "HT_COUNTS" with
  | None -> ()
  | Some f ->
      let ic = Stdlib.open_in_bin f in
      let len = in_channel_length ic in
      let s = if len > !ht_counts_pos then
                (seek_in ic !ht_counts_pos; really_input_string ic (len - !ht_counts_pos))
              else "" in
      Stdlib.close_in ic;
      match String.rindex_opt s '\n' with
      | None -> ()
      | Some last ->
          List.iter (fun l -> match String.split_on_char ' ' l with
              | [k; v; h] -> Hashtbl.replace ht_counts (int_of_string k) (int_of_string v, int_of_string h)
              | ["P"; h] -> Hashtbl.replace ht_proved (int_of_string h) ()
              | _ -> ())
            (String.split_on_char '\n' (String.sub s 0 last));
          ht_counts_pos := !ht_counts_pos + last + 1;;
ht_read_counts ();;
let ht_point t stubbed =
  if !ht_in_base then
  match ht_rec_out with
  | Some oc -> Printf.fprintf oc "%d %d %d\n%!" !ht_seq !ht_counter (ht_ahash [] t)
  | None ->
      if Hashtbl.length ht_counts > 0 then
        match (try Some (Hashtbl.find ht_counts !ht_seq) with Not_found -> None) with
        | None -> if stubbed then failwith (Printf.sprintf "HT_COUNTS has no entry %d" !ht_seq)
        | Some (v, h) ->
            if h <> ht_ahash [] t then
              (if stubbed then failwith (Printf.sprintf "HT_COUNTS out of step at %d" !ht_seq)
               else incr ht_tv_off)
            else if !ht_counter <> v then
              (if not stubbed then incr ht_tv_off; ht_counter := v);;
let ht_record_proved t =
  match ht_rec_out with
  | Some oc when not !ht_in_base -> Printf.fprintf oc "P %d\n%!" (ht_thash [] t)
  | _ -> ();;
let ht_stub_ok t =
  !ht_in_base || Hashtbl.mem ht_proved (ht_thash [] t) ||
  (incr ht_unproved; false);;
let ht_call_gen full t (f : unit -> thm) =
  if !ht_depth > 0 then (let th = f () in ht_name th; ht_record_proved t; th) else begin
    incr ht_seq;
    if ht_stub () && not full && ht_stub_ok t then
      (let th = ht_stub_thm t in ht_point t true; th)
    else begin
      ht_depth := 1;
      let th = (try f () with e -> (ht_depth := 0; ht_point t false; raise e)) in
      ht_depth := 0; ht_name th; ht_point t false; ht_record_proved t; th
    end
  end;;
let ht_call t f = ht_call_gen false t f;;
let ht_rule1 (f : term -> thm) = fun t -> ht_call t (fun () -> f t);;
let ht_orig_prove = prove;;
let prove (t, (tac:tactic)) = ht_call t (fun () -> ht_orig_prove (t, tac));;
let ht_prove_lazy (t, (f : unit -> tactic)) = ht_call t (fun () -> ht_orig_prove (t, f ()));;
(* MESON with a theorem that has hypotheses among its arguments proves a     *)
(* theorem with hypotheses, which an axiom cannot stand for: always in full. *)
let MESON = let f = MESON in fun ths t ->
  ht_call_gen (exists (fun th -> hyp th <> []) ths) t (fun () -> f ths t);;
let ARITH_RULE = ht_rule1 ARITH_RULE;;
let REAL_ARITH = ht_rule1 REAL_ARITH;;
let INT_ARITH = ht_rule1 INT_ARITH;;
let SET_RULE = ht_rule1 SET_RULE;;
let TAUT = ht_rule1 TAUT;;
let REAL_FIELD = ht_rule1 REAL_FIELD;;
let REAL_RING = ht_rule1 REAL_RING;;
(* Called after the base library. *)
let ht_after_base () = ht_in_base := false;;
(* The files of make.ml in order, from holtrace/parts/part1.txt, ... partK.txt *)
let ht_part_list k =
  let read f =
    let ic = Stdlib.open_in f in
    let rec go acc = match (try Some (Stdlib.input_line ic) with End_of_file -> None) with
      | Some l -> go (if String.trim l = "" then acc else String.trim l :: acc)
      | None -> Stdlib.close_in ic; List.rev acc in
    go [] in
  read (Printf.sprintf "holtrace/parts/part%d.txt" k);;

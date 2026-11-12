(* ========================================================================= *)
(* HOLTrace parts HT_FIRST to HT_LAST from one session (Linux).  The session *)
(* loads the base library and the files of the parts in stub mode, as        *)
(* trace_part.ml does, but only once: before loading the files of part k it  *)
(* forks a process that traces part k.  The forked process continues the     *)
(* trace in WORK/partk.50 (a copy of this session's trace so far), writes    *)
(* its output to WORK/tracek.log, loads the files of part k in full mode and *)
(* stops; so WORK/partk.50 is the trace that trace_part.ml with HT_PART=k    *)
(* would write.  A part whose trace is complete is not traced again.  This   *)
(* session may run while the record is being made                            *)
(* (record_counter.ml): before loading a file in stub mode it waits until    *)
(* the record has passed that file (HT_RECORD_LOG) and reads the new lines   *)
(* of HT_COUNTS.  Run in the repository root with HOLTRACE_SAVE (an absolute *)
(* path, for this session's own trace), HT_COUNTS, HT_RECORD_LOG, HT_WORK,   *)
(* HT_FIRST and HT_LAST set; holtrace/run_holtrace.sh does this.             *)
(* ========================================================================= *)

#load "unix.cma";;
loadt "holtrace/link_prelude.ml";;
needs "Multivariate/cauchy.ml";;
needs "Multivariate/lpspaces.ml";;
needs "100/green.ml";;
ht_after_base ();;
let VECTOR_ARITH = ht_rule1 VECTOR_ARITH;;
let NORM_ARITH = ht_rule1 NORM_ARITH;;

let ht_work = Sys.getenv "HT_WORK";;
let ht_first = int_of_string (Sys.getenv "HT_FIRST");;
let ht_last = int_of_string (Sys.getenv "HT_LAST");;
let ht_trace_path = Sys.getenv "HOLTRACE_SAVE";;
Sys.set_signal Sys.sigchld Sys.Signal_ignore;;

(* Wait until the record has passed file f, then read the new lines of       *)
(* HT_COUNTS.                                                                *)
let ht_rec_files = (Hashtbl.create 2000 : (string, unit) Hashtbl.t);;
let ht_rec_pos = ref 0 and ht_rec_done = ref false;;
let ht_poll_record () =
  let f = Sys.getenv "HT_RECORD_LOG" in
  let ic = Stdlib.open_in_bin f in
  let len = in_channel_length ic in
  let s = if len > !ht_rec_pos then
            (seek_in ic !ht_rec_pos; really_input_string ic (len - !ht_rec_pos))
          else "" in
  Stdlib.close_in ic;
  match String.rindex_opt s '\n' with
  | None -> ()
  | Some last ->
      List.iter (fun l ->
          let ws = List.filter (fun w -> w <> "") (String.split_on_char ' ' l) in
          let rec scan = function
            | "RECORD_FILE_DONE" :: g :: _ -> Hashtbl.replace ht_rec_files g ()
            | "RECORD_DONE" :: _ -> ht_rec_done := true
            | _ :: r -> scan r
            | [] -> () in
          scan ws)
        (String.split_on_char '\n' (String.sub s 0 last));
      ht_rec_pos := !ht_rec_pos + last + 1;;
let ht_wait_record f =
  ht_poll_record ();
  while not (!ht_rec_done || Hashtbl.mem ht_rec_files f) do
    Unix.sleep 20; ht_poll_record ()
  done;
  ht_read_counts ();;

(* The file descriptor of this session's trace, found through /proc.         *)
let ht_trace_fd () =
  let d = "/proc/self/fd" in
  let fds = List.filter (fun e -> try Unix.readlink (d ^ "/" ^ e) = ht_trace_path with _ -> false)
              (Array.to_list (Sys.readdir d)) in
  match fds with
  | [e] -> (Obj.magic (int_of_string e) : Unix.file_descr)
  | _ -> failwith "ht_trace_fd: trace file not found";;

(* In the forked process: copy the trace so far to file g, and continue the  *)
(* trace there (HOLTrace writes each line at once, so nothing is buffered).  *)
let ht_continue_trace_in g =
  let fd = ht_trace_fd () in
  let ic = Stdlib.open_in_bin ht_trace_path in
  let n = in_channel_length ic in
  let oc = Stdlib.open_out_bin g in
  let buf = Bytes.create 1048576 in
  let rec copy left =
    if left > 0 then begin
      let k = input ic buf 0 (min left (Bytes.length buf)) in
      if k = 0 then failwith "ht_continue_trace_in: short trace";
      output oc buf 0 k; copy (left - k)
    end in
  copy n;
  Stdlib.close_in ic;
  Stdlib.flush oc;
  Unix.dup2 (Unix.descr_of_out_channel oc) fd;
  Stdlib.close_out oc;;

(* A part is complete if its trace log has its PART_DONE line.              *)
let ht_part_complete k =
  let f = Printf.sprintf "%s/trace%d.log" ht_work k in
  Sys.file_exists f && Sys.file_exists (Printf.sprintf "%s/part%d.50" ht_work k) &&
  (let ic = Stdlib.open_in_bin f in
   let s = really_input_string ic (in_channel_length ic) in
   Stdlib.close_in ic;
   let pat = Printf.sprintf "PART_DONE part=%d " k in
   let n = String.length s and m = String.length pat in
   let rec find i = i + m <= n && (String.sub s i m = pat || find (i + 1)) in
   find 0);;

let ht_trace_part k =
  if ht_part_complete k then Printf.printf "SPINE_SKIP part=%d (complete)\n%!" k else begin
  Format.print_flush (); flush stdout; flush stderr;
  match Unix.fork () with
  | 0 ->
      (try
         let lc = Stdlib.open_out_bin (Printf.sprintf "%s/trace%d.log" ht_work k) in
         Unix.dup2 (Unix.descr_of_out_channel lc) Unix.stdout;
         Unix.dup2 (Unix.descr_of_out_channel lc) Unix.stderr;
         Stdlib.close_out lc;
         ht_continue_trace_in (Printf.sprintf "%s/part%d.50" ht_work k);
         Printf.printf "PART_FORKED part=%d proofs_before=%d cpu=%.0f\n%!" k !ht_seq (Sys.time());
         ht_home := ht_part_list k;
         List.iter needs !ht_home;
         if List.mem "src/pc_poincare_top.ml" !ht_home then loadt "holtrace/name_headlines.ml";
         Printf.printf "PART_DONE part=%d links=%d stubs=%d axioms=%d proofs=%d counter_corrections=%d unproved=%d cpu=%.0f\n%!"
           k !ht_count !ht_stubs (List.length (axioms())) !ht_seq !ht_tv_off !ht_unproved (Sys.time());
         holtrace_stop ();
         exit 0
       with e -> (Printf.printf "PART_FAILED part=%d %s\n%!" k (Printexc.to_string e); exit 1))
  | pid -> Printf.printf "SPINE_FORKED part=%d pid=%d cpu=%.0f\n%!" k pid (Sys.time())
  end;;

for k = 1 to ht_last do
  if k >= ht_first then ht_trace_part k;
  if k < ht_last then
    List.iter (fun f -> ht_wait_record f; needs f;
                        Printf.printf "SPINE_FILE_DONE %s cpu=%.0f\n%!" f (Sys.time()))
      (ht_part_list k)
done;;
Printf.printf "SPINE_DONE stubs=%d unproved=%d lazy_loads=%d cpu=%.0f\n%!"
  !ht_stubs !ht_unproved !ht_lazy_loads (Sys.time());;
holtrace_stop ();;

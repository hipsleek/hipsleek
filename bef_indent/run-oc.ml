#include "xdebug.cppo"
let results = ref ([] : (float * string) list)
let sorted_results = ref ([] : (float * string) list)

let get_formula (fr : int) (input : string) : (string * int) =
  let s = String.index_from input fr '#' in
  let e = String.index_from input fr ';' in
  let res = (String.sub input s (e - s + 1), e + 1) in
	res


let rec run_helper (fr : int) (input : string) : unit =
  if (fr < String.length input) then
	let oc_chn = open_out "/tmp/oc.input" in
	let formula, next_fr = get_formula fr input in
	let () = output_string oc_chn formula in
	let () = close_out oc_chn in
	let ptime1 = Unix.times () in
	let t1 = ptime1.Unix.tms_utime +. ptime1.Unix.tms_cutime in
	let () = Sys.command "oc /tmp/oc.input" in
	let ptime2 = Unix.times () in
	let t2 = ptime2.Unix.tms_utime +. ptime2.Unix.tms_cutime in
	  results := (t2 -. t1, formula) :: !results;
	  run_helper next_fr input

let run (ifile : string) =
  let ichn = open_in ifile in
  let contents = Buffer.create 10240 in
	try
	  while (true) do
		let line = input_line ichn in
		  Buffer.add_string contents line;
		  Buffer.add_char contents '\n';
	  done
	with
	  | _ -> run_helper 0 (Buffer.contents contents)
	

let sort_result () =
  let comp (t1, _) (t2, _) =
	if (t1 < t2) then 1
	else if (t1 = t2) then 0
	else -1 
  in
	sorted_results := List.fast_sort comp !results 

let rec print_result n0 =
  let rec helper n r =
	if (n > 0) then begin
	  print_string (string_of_float (fst (List.hd r)));
	  print_string "\n";
	  print_string (snd (List.hd r));
	  helper (n-1) (List.tl r)
	end
  in
	helper n0 !sorted_results

let compete_mode = ref false
let trace_failure = ref false
let verbose_num = ref 0

let last_posn = ref (None:string option)

let suppress_warning_msg = ref false
let en_warning_msg = ref true

let sap = ref false

type loc =  {
    start_pos : Lexing.position (* might be expanded to contain more information *);
    mid_pos : Lexing.position;
    end_pos : Lexing.position;
  }

type primed =
  | Primed
  | Unprimed

let no_pos = 
	let no_pos1 = { Lexing.pos_fname = "";
				   Lexing.pos_lnum = 0;
				   Lexing.pos_bol = 0; 
				   Lexing.pos_cnum = 0 } in
	{start_pos = no_pos1; mid_pos = no_pos1; end_pos = no_pos1;}


let is_no_pos l = (l.start_pos.Lexing.pos_cnum == 0)

let print_endline_q s =
  if !compete_mode then ()
  else print_endline s

let print_backtrace_quiet () =
  if !compete_mode then ()
  else
    Printexc.print_backtrace stdout

let get_backtrace_quiet () =
  if !compete_mode then ""
  else
    Printexc.get_backtrace ()

let record_backtrace_quite () =
  if !compete_mode then ()
  else
    Printexc.record_backtrace !trace_failure

let string_of_loc (p : loc) = 
  p.start_pos.Lexing.pos_fname ^ "_" ^ 
  (string_of_int p.start_pos.Lexing.pos_lnum) ^ ":" ^
  (string_of_int (p.start_pos.Lexing.pos_cnum-p.start_pos.Lexing.pos_bol)) ^ "_" ^
  (string_of_int p.end_pos.Lexing.pos_lnum) ^ ":" ^
  (string_of_int (p.end_pos.Lexing.pos_cnum-p.end_pos.Lexing.pos_bol))

let string_of_pos (p : Lexing.position) = "("^string_of_int(p.Lexing.pos_lnum) ^","^string_of_int(p.Lexing.pos_cnum-p.Lexing.pos_bol) ^")"
;;

let string_of_full_loc (l : loc) = "{"^(string_of_pos l.start_pos)^","^(string_of_pos l.end_pos)^"}";;

let string_of_loc_by_char_num (l : loc) = 
  Printf.sprintf "(%d-%d)"
    l.start_pos.Lexing.pos_cnum
    l.end_pos.Lexing.pos_cnum

(*Proof logging facilities*)
class ['a] store (x_init:'a) (epr:'a->string) =
   object (self)
     val emp_val = x_init
     val mutable lc = None
     method is_avail : bool = match lc with
       | None -> false
       | Some _ -> true
     method set (nl:'a) = lc <- Some nl
     method get :'a = match lc with
       | None -> emp_val
       | Some p -> p
     method reset = lc <- None
     method get_rm :'a = match lc with
       | None -> emp_val
       | Some p -> (self#reset; p)
     method string_of : string = match lc with
       | None -> "Why None?"
       | Some l -> (epr l)
     method dump = print_endline ("\n store dump :"^(self#string_of))
   end;;

(* this will be set to true when we are in error explanation module *)
class failure_mode =
object
  inherit [bool] store false string_of_bool
end;;

class prog_loc =
object
  inherit [loc] store no_pos string_of_loc
     method string_of_pos : string = match lc with
       | None -> "None"
       | Some l -> (string_of_pos l.start_pos)
end;;

let last_posn = new store "" (fun x -> "("^x^")")

(*Some global vars for logging*)
let proving_loc  = new prog_loc
let post_pos = new prog_loc

let entail_pos = ref no_pos
let set_entail_pos p = entail_pos := p

let z_debug_flag = ref false

let buildA s i = s^"#"^(string_of_int i);;
let build_loc_str s i = "**"^(buildA s i)^":";;
let store_loc_str s i =
  if !z_debug_flag then
    let n = buildA s i 
    in last_posn # set n ;;

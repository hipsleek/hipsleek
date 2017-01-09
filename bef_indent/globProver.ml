#include "xdebug.cppo"
let tmp_files_path = ref ""

(*path for the temporary files used by the prover. If you change this path here it is 
  mandatory to also change the value of TMP_FILES_PATH in Makefile accordingly to the changes made here*)
let set_tmp_files_path () = 	
	begin
      (try
		ignore (Unix.mkdir ("/tmp/" ^ Unix.getlogin()) 0o766;)		 
      with
		Unix.Unix_error (_, _, _) -> (); );
	  (try
		ignore (Unix.chmod ("/tmp/" ^ Unix.getlogin()) 0o766;)		 
      with
		Unix.Unix_error (_, _, _) -> (); );
      (try
		ignore (Unix.mkdir ("/tmp/" ^ Unix.getlogin() ^ "/prover_tmp_files/") 0o766) 
      with
		Unix.Unix_error (_, _, _) -> (););
	  (try
		ignore (Unix.chmod ("/tmp/" ^ Unix.getlogin() ^ "/prover_tmp_files/") 0o766;)		 
      with
		Unix.Unix_error (_, _, _) -> (););
	tmp_files_path := ("/tmp/" ^ Unix.getlogin() ^ "/prover_tmp_files/")
	end

(*type of process used for communicating with the prover*)
type prover_process_t = {
  name:string; 
  pid: int; 
  inchannel: in_channel; 
  outchannel: out_channel; 
  errchannel: in_channel }

(*methods that need to be defined in order to use a prover incrementally - if the prover provides this functionality*)
class type ['a] incremMethodsType = object
  val process: prover_process_t option ref
  method start_p: unit -> prover_process_t
  method stop_p:  prover_process_t -> unit
  method push: prover_process_t -> unit
  method pop: prover_process_t -> unit
  method popto: prover_process_t -> int -> unit
  method imply: (prover_process_t option * bool) option -> 'a -> 'a -> string -> bool
  method set_process: prover_process_t -> unit
  method get_process: unit -> prover_process_t option
  (* method add_to_context: 'a -> unit *)
end

let open_log_out s = 
 (try
	Unix.mkdir "logs" 0o750
 with _ -> ());
 open_out ("logs/"^s)


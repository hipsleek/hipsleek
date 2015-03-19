#include "xdebug.cppo"
(* open VarGen *)
open Gen
(* open Basic *)
(* open Globals *)

let proc_files = new stack_noexc "__no_file" pr_id (fun s1 s2 -> s1=s2) 

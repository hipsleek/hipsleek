(* util.ml - utilities *)

module X = Lexing
module L = Listx
module S = Strx

(* increase line number in the lexer by one *)
let line lexbuf = 
  let p = Compat.lex_get lexbuf in
  Compat.lex_set lexbuf { p with 
    X.pos_lnum = p.X.pos_lnum + 1;
    X.pos_bol = p.X.pos_cnum
  }

(* make a lex from a filename *)
let lex (x:string) : X.lexbuf = 
  let lex = X.from_channel (open_in x) in
  let p = Compat.lex_get lex in
  Compat.lex_set lex { p with X.pos_fname = x }; lex

(* make file info from the current lex state *)
let info lexbuf : string =
  let p0 = Compat.lex_start lexbuf  in
  let p1 = Compat.lex_get lexbuf in
  let l = p1.X.pos_lnum in
  let c = p0.X.pos_cnum - p0.X.pos_bol in
  Std.showf "%s:%02d:%02d" p0.X.pos_fname l c

let info_filename (x:string) : string = Strx.upto ':' x

(* parsing info during parser abort *)
let pinfo i =
  let p = Parsing.rhs_start_pos i in
  let l = p.X.pos_lnum in
  let c = p.X.pos_cnum - p.X.pos_bol in
  Std.showf "%s:%02d:%02d" p.X.pos_fname l c

(* parser abort with a list of possible rules *)
let abort i l =
  let prefix s2 n = String.sub s2 0 n in
  let f (s2,n) = Std.showf "  prefix:  %s\n  rule  :  %s" (prefix s2 n) s2 in
  let sl = L.show "\nor\n" f l in
  Std.printf 
"%s: Parse error: premature prefix of possible rules\n%s\n" 
(pinfo i) sl; exit 1


(* timing *)

let _timers : float list ref = ref []

let timers_push () : unit = _timers := Sys.time () :: !_timers

let timers_pop () : float =
  assert (L.size !_timers > 0);
  let t = L.head !_timers in 
  _timers := L.tail !_timers;
  Sys.time () -. t

let timers_renew () : float =
  let t = timers_pop () in
  timers_push (); t

(*-- command-line argument processing *)

(* any string that does not start with '-' is a filename *)
let arg_list () : string list =
  let s0 = L.tail (Arrayx.to_list Sys.argv) in (* skip executable filename *)
  let s1 = L.take (fun s -> Strx.head s <> '-') s0 in
  Std.check (s1<>[]) "Error: missing filenames in the command line"; s1
  
(* if a string is passed *)
let arg_bool (x:string) : bool = (Arrayx.some ((=) x) Sys.argv)

(* if a string is passed *)
let arg_str (x:string) : string = 
  let y = Arrayx.findx (S.is_prefix x) Sys.argv in
  S.skip (S.size x + 1) y


(*-- shell *)

(* the shell command 'which' thats locates the full path of a program *)
let locate (x:string) : string =
  let ps = Strx.read ':' (Sys.getenv "PATH") in
  let f p = Sys.file_exists (p ^ "/" ^ x) in
  match Listx.find f ps with
  | None -> Std.error "Program '%s' does not exist in path" x
  | Some p -> Compat.realpath (p ^ "/java")

(* strip the last path component and return the rest of directory components *)
let dirname (x:string) : string =
  Strx.subj x 0 (Strx.rev_find '/' x)

(* ocfg.ml - ordered context free grammar *)

open Osyntax 
open Std

module A = Arrayx 
module C = Cfg 
module H = Hashx 
module L = Listx 
module P = Pda 
module S = Strx 
module X = Setx 


let is_literal = function Literal _ -> true | _ -> false

let tbuiltin = ["Char"; "Double"; "Float"; "Ident"; 
  "Int"; "Int32"; "Int64"; "String"]
let xbuiltin = ["_char"; "_double"; "_float"; "_ident";
  "_int"; "_int32"; "_int64"; "_string"]
let ybuiltin = ["string"; "float"; "float"; "string"; 
  "int"; "int32"; "int64"; "string"]

let token_name1 : char -> string = function
  | '!' -> "bang"
  | '\034' -> "dqoute"
  | '#' -> "sharp"
  | '$' -> "dollar"
  | '%' -> "percent"
  | '&' -> "and"
  | '\'' -> "quote"
  | '(' -> "lparen"
  | ')' -> "rparen"
  | '*' -> "star"
  | '+' -> "plus"
  | ',' -> "comma"
  | '-' -> "minus"
  | '.' -> "dot"
  | '/' -> "slash"
  | ':' -> "colon"
  | ';' -> "semi"
  | '<' -> "langle"
  | '=' -> "eq"
  | '>' -> "rangle"
  | '?' -> "question"
  | '@' -> "at"
  | '[' -> "lbracket"
  | '\\' -> "bslash"
  | ']' -> "rbracket"
  | '^' -> "caret"
  | '_' -> "under"
  | '`' -> "bquote"
  | '{' -> "lbrace"
  | '|' -> "bar"
  | '}' -> "rbrace"
  | '~' -> "tilde"
  | c -> char_show c

(* capitalized name for token *)
let token_cname (s:string) : string = 
  if S.is_alpha s then "K" ^ s else     (* namespace for keywords *)
  S.mapc (fun c -> S.capitalize (token_name1 c)) s

(* underscored name for token *)
let token_uname (s:string) : string = 
  if S.is_alpha s then "k_" ^ s else
  S.mapc_with token_name1 "_" s

let x_of_r : r -> x = function
  | Alias (x,_,_) -> x
  | Union (x,_,_) -> x

let x0_of_g ((rs,_):g) : x = assert (rs<>[]); x_of_r (L.head rs)

let us_arg (info:bool) (us:u list) : string = 
  let us2 = L.index (L.drop is_literal us) in
  let s1 = L.map (fun (i,_) -> "x" ^ int_show i) us2 in
  match L.if_cat info "z" s1 with
  | [] -> ""
  | [a] -> " " ^ a
  | s2 -> " (" ^ S.cat "," s2 ^ ")"


(*------------------------------------------------------------

Item map.
 
--------------------------------------------------------------*)

let citemmap (f:u -> 'a list) ((_,us):c) : 'a list = L.mapc f us
let pitemmap (f:u -> 'a list) ((_,cs):p) : 'a list = L.mapc (citemmap f) cs
let ritemmap (f:u -> 'a list) : r -> 'a list = function
  | Alias (_,_,us) -> L.mapc f us
  | Union (_,_,ps) -> L.mapc (pitemmap f) ps
let gitemmap (f:u -> 'a list) ((rs,_):g) : 'a X.t = 
  X.of_list (L.mapc (ritemmap f) rs)


(*------------------------------------------------------------

Literal sets.

--------------------------------------------------------------*)

let uliteral : u -> q list = function
  | Literal q -> [q]
  | Ident _ -> []
  | Marker q -> [q]
  | Option _ -> []
  | Star _ -> []
  | Plus _ -> []
  | Sstar (_,q) -> [q]
  | Pplus (_,q) -> [q]

let gliteral (g:g) : q list = X.to_list (gitemmap uliteral g)


(*------------------------------------------------------------

Item sets.

--------------------------------------------------------------*)

let uitem : u -> u list = function
  | Sstar (x,q) -> [Sstar (x,q); Pplus (x,q)]
  | u -> [u]

let gitem : g -> u X.t = gitemmap uitem


(*------------------------------------------------------------

Tag identifier list.

--------------------------------------------------------------*)

let ctagid ((x,_):c) : x = x
let ptagid ((_,cs):p) : x list = L.map ctagid cs
let rtagid : r -> 'a list = function
  | Alias _ -> []
  | Union (_,_,ps) -> L.mapc ptagid ps
let gtagid ((rs,_):g) : x list = L.mapc rtagid rs


(*------------------------------------------------------------

Variable sets.

--------------------------------------------------------------*)

let uvariable : u -> x list = function
  | Literal _ -> []
  | Ident x -> [x]
  | Marker q -> [token_uname q ^ "_marker"]
  | Option x -> [x; x ^ "_option"]
  | Star x -> [x; x ^ "_star"]
  | Plus x -> [x; x ^ "_plus"]
  | Sstar (x,q) -> 
    [x; x ^ "_star_" ^ token_uname q; x ^ "_plus_" ^ token_uname q]
  | Pplus (x,q) -> [x; x ^ "_plus_" ^ token_uname q]

let gvariable : g -> x X.t = gitemmap uvariable

let uident : u -> x list = function
  | Literal _ -> []
  | Ident x -> [x]
  | Marker _ -> []
  | Option x -> [x]
  | Star x -> [x]
  | Plus x -> [x]
  | Sstar (x,_) -> [x]
  | Pplus (x,_) -> [x]

let gident : g -> x X.t = gitemmap uident


(*---- Abstract syntax tree definitions (syntax). *)

let usyntax : u -> string = function
  | Literal s -> ""
  | Ident s -> s
  | Marker _ -> showf "bool" 
  | Option s -> showf "%s option" s
  | Star s -> showf "%s list" s
  | Plus s -> showf "%s list" s
  | Sstar (s,_) -> showf "%s list" s
  | Pplus (s,_) -> showf "%s list" s

let ussyntax (info:bool) (us:u list) : string =
  let us2 = L.map usyntax (L.drop is_literal us) in
  S.cat " * " (L.if_cat info "_info" us2)

let csyntax (info:bool) ((x,us):c) : string = 
  let s = ussyntax info us in
  showf "  | %s%s" x (if s="" then "" else " of " ^ s)

let psyntax (info:bool) ((_,cs):p) : string = L.show1 (csyntax info) cs

let rsyntax (f:out_channel) : r -> unit = function
  | Alias (x,b,us) -> fprintf f "and %s = %s\n\n" x (S.if_null "unit" (ussyntax b us))
  | Union (x,b,ps) -> fprintf f "and %s =\n%s\n\n" x (L.show1 (psyntax b) ps)

let gsyntax (f:out_channel) ((rs,_):g) : unit = L.iter (rsyntax f) rs


(*---- Grammar definitions for Cfg module (grammar). *) 

type aa = T of string | X of string
type ss = aa list

let name (x:x) (i:int) = x ^ "/" ^ (int_show i)

let ugrammar (x0:x) (i:int) : u -> aa = function
  | Literal q -> T q
  | Ident x -> if i=0 || x<>x0 then X x else X (name x i)
  | Marker q -> X (token_uname q ^ "_marker")
  | Option x -> X (x ^ "_option")
  | Star x -> X (x ^ "_star")
  | Plus x -> X (x ^ "_plus")
  | Sstar (x,q) -> X (x ^ "_star_" ^ token_uname q)
  | Pplus (x,q) -> X (x ^ "_plus_" ^ token_uname q)

let cgrammar (x0:x) (i:int) (a:a) ((_,us):c) : ss =
  let f = ugrammar x0 in
  if L.size us < 2 then L.map (f 0) us else
  (* split 's' into 'u1 us2 u3' (first, body, last) *)
  let (u1,s) = L.head_tail us in
  let (us2,u3) = L.tail_head s in
  match a with 
  | Non -> f (i+1) u1 :: L.map (f 0) us2 @ [f (i+1) u3]
  | Left -> f i u1 :: L.map (f 0) us2 @ [f (i+1) u3]
  | Right -> f (i+1) u1 :: L.map (f 0) us2 @ [f i u3]

let pgrammar (x0:x) (n:int) ((i,(a,cs)):int * p) : x * ss list =   
  let p = if i=n-1 then [] else [[X (name x0 (i+1))]] in
  (name x0 i, p @ L.map (cgrammar x0 i a) cs)

let rgrammar : r -> (string * ss list) list = function
  | Alias (x,_,us) -> [(x, [L.map (ugrammar x 0) us])]
  | Union (x,_,ps) -> 
    (x, [[X (x ^ "/0")]]) 
    :: L.map (pgrammar x (L.size ps)) (L.index ps)

let ggrammar ((rs,_):g) : (string * ss list) list = L.mapc rgrammar rs

(* grammar for extended bnf notations: ?, *, +, **, ++ *)
let grammar_ext : u -> (string * ss list) option = function
  | Literal q -> None
  | Ident x -> None
  | Marker q -> Some (token_uname q ^ "_marker", [[];[T q]])
  | Option x -> Some (x ^ "_option", [[];[X x]])
  | Star x -> Some (x ^ "_star", [[];[X x; X (x ^ "_star")]])
  | Plus x -> Some (x ^ "_plus", [[X x];[X x; X (x ^ "_plus")]])  
  | Sstar (x,q) ->                      (* xq = x ** q = . | x ++ q *)
    let xq1 = x ^ "_star_" ^ (token_uname q) in
    let xq2 = x ^ "_plus_" ^ (token_uname q) in
    Some (xq1, [[]; [X xq2]])  
  | Pplus (x,q) ->                      (* xq = x ++ q = x | x q xq *)
    let xq = x ^ "_plus_" ^ (token_uname q) in
    Some (xq, [[X x]; [X x; T q; X xq]])

let grammar ((rs,_) as g:g) (qs:q list) (us:u X.t) : (string, string) C.g =
  assert (L.size rs > 0);
  let ts = A.of_list (tbuiltin @ "Eof" :: qs) in
  let ps0 = [("_start", [[X (x0_of_g g); T "Eof"]])] in (* augmented start symbol *)
  let ps1 = L.map2 (fun x t -> (x, [[T t]])) xbuiltin tbuiltin in
  let ps2 = ggrammar g in
  let ps3 = X.to_list (X.collect grammar_ext us) in
  let ps4 = ps0 @ ps1 @ ps2 @ ps3 in
  let xs = A.of_list (L.domain ps4) in
  let ps = A.make (A.size xs) [] in
  let tindex = H.index_array ts in
  let xindex = H.index_array xs in
  let xindex2 x = 
    try xindex x with Not_found -> error "unbound symbol: %s" (show x) in
  let aindex = function T t -> C.T (tindex t) | X x -> C.X (xindex2 x) in
  L.iter (fun (x,p) -> ps.(xindex x) <- L.map (L.map aindex) p) ps4;
  (ts, xs, ps, xindex "_start")


(*---- Show tags of parsing tree (fshow). *)

type pindex = string * ss -> int        (* production index *)

let cfshow (pindex:pindex) (x0:x) (i:int) (a:a) 
  (f:out_channel) ((x,us):c) : unit = 
  let i = pindex (name x0 i, cgrammar x0 i a (x,us)) in
  fprintf f "  | P.Node (%d,z,_) -> %s_tag (%s_of f)" i x0 x0

let pfshow (pindex:pindex) (x0:x) (n:int) (f:out_channel)
    ((i,(a,cs)):int * p) : unit = 
  L.fprint_sep (cfshow pindex x0 i a) "\n" f cs;
  if i <> n-1 then 
    let j = pindex (name x0 i, [X (name x0 (i+1))]) in
    fprintf f "\n  | P.Node (%d,z,_) -> %s_tag (%s_of f)" j x0 x0

let rfshow (pindex:pindex) (f:out_channel) : r -> unit = function
  | Alias (x,b,us) -> 
    let i = pindex (x, L.map (ugrammar x 0) us) in
    fprintf f "  | P.Node (%d,z,_) -> %s_tag (%s_of f)" i x x

  | Union (x,b,ps) -> 
    let j = pindex (x, [X (name x 0)]) in
    fprintf f "  | P.Node (%d,z,_) -> %s_tag (%s_of f)\n" j x x;
    L.fprint_sep (pfshow pindex x (L.size ps)) "\n" f (L.index ps)

let gfshow (pindex:pindex) (f:out_channel) ((rs,_):g) : unit = 
  L.fprint_sep (rfshow pindex) "\n" f rs

let fshow (us:u X.t) (pindex:pindex) (f:out_channel) (g:g) : unit =
  gfshow pindex f g


(*---- Disambiguation of parsing tree (ffilter). *)

let cffilter (pindex:pindex) (x0:x) (i:int) (a:a) 
  (f:out_channel) ((x,us):c) : unit = 
  let i = pindex (name x0 i, cgrammar x0 i a (x,us)) in
  fprintf f "  | P.Node (%d,z,_) -> %s_filter (%s_of f)" i x0 x0

let pffilter (pindex:pindex) (x0:x) (n:int) (f:out_channel)
  ((i,(a,cs)):int * p) : unit = 
  L.fprint_sep (cffilter pindex x0 i a) "\n" f cs;
  if i <> n-1 then 
    let j = pindex (name x0 i, [X (name x0 (i+1))]) in
    fprintf f "\n  | P.Node (%d,z,_) -> %s_filter (%s_of f)" j x0 x0

let rffilter (pindex:pindex) (f:out_channel) : r -> unit = function
  | Alias (x,b,us) -> 
    let i = pindex (x, L.map (ugrammar x 0) us) in
    fprintf f "  | P.Node (%d,z,_) -> %s_filter (%s_of f)" i x x

  | Union (x,b,ps) -> 
    let j = pindex (x, [X (name x 0)]) in
    fprintf f "  | P.Node (%d,z,_) -> %s_filter (%s_of f)\n" j x x;
    L.fprint_sep (pffilter pindex x (L.size ps)) "\n" f (L.index ps)

let gffilter (pindex:pindex) (f:out_channel) ((rs,_):g) : unit = 
  L.fprint_sep (rffilter pindex) "\n" f rs

let ffilter (us:u X.t) (pindex:pindex) (f:out_channel) (g:g) : unit =
  gffilter pindex f g


(*---- Build abstract syntax tree from parse stacks (build). *)

(* FIXME: restructure code to do grammar and build together, so that
the hack 'pindex' is not needed for generating production rules and
their filters . *)

let ubuild : u -> string = function
  | Literal q -> token_uname q
  | Ident x -> x
  | Marker q -> token_uname q ^ "_marker"
  | Option x -> x ^ "_option"
  | Star x -> x ^ "_star"
  | Plus x -> x ^ "_plus"
  | Sstar (x,q) -> x ^ "_star_" ^ token_uname q
  | Pplus (x,q) -> x ^ "_plus_" ^ token_uname q

let us_build_var (us:u list) : string =
  let f (i,u) = "x" ^ int_show i in
  L.show ";" f (L.index us)

let us_build_fun (info:bool) (us:u list) : string =
  let us2 = L.drop (fun (_,u) -> is_literal u) (L.index us) in
  let f (i,u) = showf "%s_of !x%d" (ubuild u) i in
  let s = S.cat ", " (L.if_cat info "z" (L.map f us2)) in
  if s="" then "" else "(" ^ s ^ ")"

let cbuild (info:bool) (pindex:pindex) (x0:x) (i:int) (a:a) 
  (f:out_channel) ((x,us):c) : unit = 
  let i = pindex (name x0 i, cgrammar x0 i a (x,us)) in
  fprintf f "  | P.Node (%d,z,[%s]) -> %s %s" 
    i (us_build_var us) x (us_build_fun info us)

let pbuild (info:bool) (pindex:pindex) (x0:x) (n:int) (f:out_channel)
  ((i,(a,cs)):int * p) : unit = 
  L.fprint_sep (cbuild info pindex x0 i a) "\n" f cs;
  if i <> n-1 then 
    let j = pindex (name x0 i, [X (name x0 (i+1))]) in
    fprintf f "\n  | P.Node (%d,z,[x]) -> %s_of !x" j x0

let rbuild (pindex:pindex) (f:out_channel) : r -> unit = function
  | Alias (x,b,us) -> 
  let i = pindex (x, L.map (ugrammar x 0) us) in
    fprintf f "and %s_of = function
  | P.Node (%d,z,[%s]) -> %s
  | _ -> Std.assert_false ()\n\n" x i (us_build_var us) 
    (S.if_null "()" (us_build_fun b us))

  | Union (x,b,ps) -> 
    let j = pindex (x, [X (name x 0)]) in
    fprintf f "and %s_of = function
  | P.Node (%d,z,[x]) -> %s_of !x
%a
  | _ -> Std.assert_false ()\n\n" x j x
      (L.fprint_sep (pbuild b pindex x (L.size ps)) "\n") (L.index ps)

let gbuild (pindex:pindex) (f:out_channel) ((rs,_):g) : unit = 
  L.iter (rbuild pindex f) rs

(* build for extended bnf notations: ?, *, +, **, ++ *)
let build_ext (pindex:pindex) (f:out_channel) : u -> unit = function
  | Literal _ -> ()
  | Ident _ -> ()

  | Marker q ->
    let x2 = token_uname q ^ "_marker" in
    let i = pindex (x2, []) in
    fprintf f "and %s_of = function
  | P.Node (%d,_,[]) -> false
  | _ -> true\n\n" x2 i

  | Option x -> 
    let x2 = x ^ "_option" in
    let i = pindex (x2, []) in
    fprintf f "and %s_of = function
  | P.Node (%d,_,[]) -> None
  | P.Node (%d,_,[a]) -> Some (%s_of !a)
  | _ -> Std.assert_false ()\n\n" x2 i (i+1) x

  | Star x -> 
    let x2 = x ^ "_star" in
    let i = pindex (x2, []) in
    fprintf f "and %s_of = function
  | P.Node (%d,_,[]) -> []
  | P.Node (%d,_,[a;s]) -> (%s_of !a) :: (%s_of !s)
  | _ -> Std.assert_false ()\n\n" x2 i (i+1) x x2

  | Plus x -> 
    let x2 = x ^ "_plus" in
    let i = pindex (x2, [X x]) in
    fprintf f "and %s_of = function
  | P.Node (%d,_,[a]) -> [%s_of !a]
  | P.Node (%d,_,[a;s]) -> (%s_of !a) :: (%s_of !s)
  | _ -> Std.assert_false ()\n\n" x2 i x (i+1) x x2

  | Sstar (x,q) -> 
    let x2 = x ^ "_star_" ^ token_uname q in
    let x3 = x ^ "_plus_" ^ token_uname q in
    let i = pindex (x2, []) in
    fprintf f "and %s_of = function
  | P.Node (%d,_,[]) -> []
  | P.Node (%d,_,[s]) -> %s_of !s
  | _ -> Std.assert_false ()\n\n" x2 i (i+1) x3

  | Pplus (x,q) -> 
    let x2 = x ^ "_plus_" ^ token_uname q in
    let i = pindex (x2, [X x]) in
    fprintf f "and %s_of = function
  | P.Node (%d,_,[a]) -> [%s_of !a]
  | P.Node (%d,_,[a;_;s]) -> (%s_of !a) :: (%s_of !s)
  | _ -> Std.assert_false ()\n\n" x2 i x (i+1) x x2

let build (us:u X.t) (pindex:pindex) (f:out_channel) (g:g) : unit =
  gbuild pindex f g;
  X.iter (build_ext pindex f) us


(*---- Show as tag expressions (tag). *)

let utag : u -> string = function
  | Literal q -> ""
  | Ident x -> x ^ "_tag"
  | Marker q -> "bool_tag"
  | Option x -> "option_tag " ^ x ^ "_tag"
  | Star x -> "list_tag " ^ x ^ "_tag"
  | Plus x -> "list_tag " ^ x ^ "_tag"
  | Sstar (x,_) -> "list_tag " ^ x ^ "_tag"
  | Pplus (x,_) -> "list_tag " ^ x ^ "_tag"

let us_tag (info:bool) ((x,us):c) : string * string =
  let us2 = L.index (L.drop is_literal us) in
  let s2 = S.repeat (L.size us2) " %s" in
  let s3 = L.showz (fun (i,u) -> showf "(%s x%d)" (utag u) i) us2 in
  (us_arg info us, showf "showf \"(%s%s)\" %s" x s2 s3)

let us0_tag (info:bool) (us:u list) : string * string =
  let us2 = L.index (L.drop is_literal us) in
  let s2 = L.showz (fun _ -> "%s") us2 in
  let s3 = L.showz (fun (i,u) -> showf "(%s x%d)" (utag u) i) us2 in
  (us_arg info us, showf "showf \"%s\" %s" s2 s3)

let ctag (info:bool) ((x,us):c) : string = 
  let (s1,s2) = us_tag info (x,us) in
  showf "  | %s%s -> %s" x s1 s2

let ptag (info:bool) ((_,cs):p) : string = L.show1 (ctag info) cs

let rtag (f:out_channel) : r -> unit = function
  | Alias (x,b,us) -> 
    let (s1,s2) = us0_tag b us in
    fprintf f "and %s_tag%s = %s\n\n" x (S.if_null "()" s1) s2
  | Union (x,b,ps) -> 
    fprintf f "and %s_tag = function
%s\n\n" x (L.show1 (ptag b) ps)

let gtag (f:out_channel) ((rs,_):g) : unit = L.iter (rtag f) rs


(*---- Show as symbolic expressions (sexp). *)

let usexp : u -> string = function
  | Literal q -> ""
  | Ident x -> x ^ "_sexp"
  | Marker q -> "bool_sexp"
  | Option x -> "option_sexp " ^ x ^ "_sexp"
  | Star x -> "list_sexp " ^ x ^ "_sexp"
  | Plus x -> "list_sexp " ^ x ^ "_sexp"
  | Sstar (x,_) -> "list_sexp " ^ x ^ "_sexp"
  | Pplus (x,_) -> "list_sexp " ^ x ^ "_sexp"

let us_sexp (info:bool) ((x,us):c) : string * string =
  let us2 = L.index (L.drop is_literal us) in
  let s2 = S.repeat (L.size us2) " %s" in
(*  let s2 = S.repeat (L.size us2 + if info then 1 else 0) " %s" in *)
  let s3 = L.showz (fun (i,u) -> showf "(%s x%d)" (usexp u) i) us2 in
(*  let s3z = S.if_cat info "z " s3 in *)
  (us_arg info us, showf "showf \"(%s%s)\" %s" x s2 s3)

let csexp (info:bool) ((x,us):c) : string = 
  let (s1,s2) = us_sexp info (x,us) in
  showf "  | %s%s -> %s" x s1 s2

let psexp (info:bool) ((_,cs):p) : string = L.show1 (csexp info) cs

let rsexp (f:out_channel) : r -> unit = function
  | Alias (x,b,us) -> 
    let (s1,s2) = us_sexp b (x,us) in
    fprintf f "and %s_sexp%s = %s\n\n" x (S.if_null " ()" s1) s2
  | Union (x,b,ps) -> 
    fprintf f "and %s_sexp = function
%s\n\n" x (L.show1 (psexp b) ps)

let gsexp (f:out_channel) ((rs,_):g) : unit = L.iter (rsexp f) rs


(*---- Show as source code (src). *)

let usrc : u -> string = function
  | Literal q -> ""
  | Ident x -> x ^ "_src"
  | Marker q -> "bool_src " ^ (S.code q)
  | Option x -> "option_src " ^ x ^ "_src"
  | Star x -> "list_src " ^ x ^ "_src"
  | Plus x -> "list_src " ^ x ^ "_src"
  | Sstar (x,q) -> "list_src_sep " ^ S.code q ^ x ^ "_src "
  | Pplus (x,q) -> "list_src_sep " ^ S.code q ^ x ^ "_src "

let us_src (info:bool) ((x,us):c) : string * string =
  let us2 = L.index (L.drop is_literal us) in
  let s2 = L.showz (function Literal q -> S.showf q | _ -> "%s") us in
  let s3 = L.showz (fun (i,u) -> showf "(%s x%d)" (usrc u) i) us2 in
  (us_arg info us, showf "showf \"%s\" %s" s2 s3)
  
let csrc (info:bool) ((x,us):c) : string = 
  let (s1,s2) = us_src info (x,us) in
  showf "  | %s%s -> %s" x s1 s2

let psrc (info:bool) ((_,cs):p) : string = L.show1 (csrc info) cs

let rsrc (f:out_channel) : r -> unit = function
  | Alias (x,b,us) -> 
    let (s1,s2) = us_src b (x,us) in
    fprintf f "and %s_src%s = %s\n\n" x (S.if_null " ()" s1) s2
  | Union (x,b,ps) -> 
    fprintf f "and %s_src = function
%s\n\n" x (L.show1 (psrc b) ps)

let gsrc (f:out_channel) ((rs,_):g) : unit = L.iter (rsrc f) rs


(*---- Iterators (iter). *)

let uiter : u -> string = function
  | Literal q -> ""
  | Ident x -> x ^ "_iter"
  | Marker q -> "bool_iter"
  | Option x -> "option_iter " ^ x ^ "_iter"
  | Star x -> "list_iter " ^ x ^ "_iter"
  | Plus x -> "list_iter " ^ x ^ "_iter"
  | Sstar (x,_) -> "list_iter " ^ x ^ "_iter"
  | Pplus (x,_) -> "list_iter " ^ x ^ "_iter"

let us_iter (info:bool) ((x,us):c) : string * string =
  let us2 = L.index (L.drop is_literal us) in
  let s2 = S.if_null "()" (L.show "; " (fun (i,u) -> showf "%s x%d" (uiter u) i) us2) in
  (us_arg info us, s2)
    
let citer (info:bool) ((x,us):c) : string = 
  let (s1,s2) = us_iter info (x,us) in
  showf "  | %s%s -> %s" x s1 s2

let piter (info:bool) ((_,cs):p) : string = L.show1 (citer info) cs

let riter (f:out_channel) : r -> unit = function
  | Alias (x,b,us) -> 
    let (s1,s2) = us_iter b (x,us) in
    fprintf f "and %s_iter%s = %s\n\n" x (S.if_null " ()" s1) s2
  | Union (x,b,ps) -> 
    fprintf f "and %s_iter = function
%s\n\n" x (L.show1 (piter b) ps)

let giter (f:out_channel) ((rs,_):g) : unit = L.iter (riter f) rs


(*---- Disambiguation (filter). *)

let ufilter : u -> string = function
  | Literal q -> ""
  | Ident x -> x ^ "_filter"
  | Marker q -> "bool_filter"
  | Option x -> "option_filter " ^ x ^ "_filter"
  | Star x -> "list_filter " ^ x ^ "_filter"
  | Plus x -> "list_filter " ^ x ^ "_filter"
  | Sstar (x,_) -> "list_filter " ^ x ^ "_filter"
  | Pplus (x,_) -> "list_filter " ^ x ^ "_filter"

let us_filter (info:bool) ((x,us):c) : string * string =
  let us2 = L.index (L.drop is_literal us) in
  let s2 = L.show "; " (fun (i,u) -> showf "%s x%d" (ufilter u) i) us2 in
  (us_arg info us, S.if_null "()" s2)
    
let cfilter (info:bool) ((x,us):c) : string = 
  let (s1,s2) = us_filter info (x,us) in
  showf "  | %s%s -> %s" x s1 s2

let pfilter (info:bool) ((_,cs):p) : string = L.show1 (cfilter info) cs

let rfilter (f:out_channel) (fs:f list) : r -> unit = function
  | Alias (x,b,us) -> 
    let (s1,s2) = us_filter b (x,us) in
    fprintf f "and %s_filter%s = %s\n\n" x (S.if_null " ()" s1) s2
  | Union (x,b,ps) -> 
    fprintf f "and %s_filter = function" x;
    L.iter (fun (x2,q) -> if x=x2 then 
      fprintf f "\n  | %s -> raise Parse.Invalid" q) fs;
    fprintf f "\n%s\n\n" (L.show1 (pfilter b) ps)

(* TODO: handle filter lists 'fs' for 'Alias' and 'Equal' as well? *)
let gfilter (f:out_channel) ((rs,fs):g) : unit = L.iter (rfilter f fs) rs


(*---- Maps (map). *)

let umap : u -> string = function
  | Literal q -> ""
  | Ident x -> x ^ "_map"
  | Marker q -> "bool_map"
  | Option x -> "option_map " ^ x ^ "_map"
  | Star x -> "list_map " ^ x ^ "_map"
  | Plus x -> "list_map " ^ x ^ "_map"
  | Sstar (x,_) -> "list_map " ^ x ^ "_map"
  | Pplus (x,_) -> "list_map " ^ x ^ "_map"

let us_map (info:bool) ((x,us):c) : string * string =
  let us2 = L.index (L.drop is_literal us) in
  let s2 = L.map (fun (i,u) -> showf "%s x%d" (umap u) i) us2 in
  (us_arg info us, S.cat ", " (L.if_cat info "z" s2))
    
let cmap (info:bool) ((x,us):c) : string = 
  let (s1,s2) = us_map info (x,us) in
  showf "  | %s%s -> %s%s" x s1 x (if s2="" then "" else " (" ^ s2 ^ ")")

let pmap (info:bool) ((_,cs):p) : string = L.show1 (cmap info) cs

let rmap (f:out_channel) : r -> unit = function
  | Alias (x,b,us) -> 
    let (s1,s2) = us_map b (x,us) in
    fprintf f "and %s_map%s = (%s)\n\n" x (S.if_null " ()" s1) s2
  | Union (x,b,ps) -> 
    fprintf f "and %s_map = function
%s\n\n" x (L.show1 (pmap b) ps)

let gmap (f:out_channel) ((rs,_):g) : unit = L.iter (rmap f) rs


(*------------------------------------------------------------

  Generate syntax definitions in file in ?syntax.ml.
  TODO: rename ?syntax.ml to ?source.ml

  1. Syntax definitions
  2. Show as symbolic expressions 'sexp'
  3. Show as source code 'src'
  4. Maps 'map'
  5. Iterators 'iter'
  6. Disambiguation Filter 'filter'

  TODO: 'sexp' and 'src' use stream instead of string concats
  (use %a instead of direct applications with %s)
  TODO: structural equality modulo line information?
  Other boilerplate code from Peyton Jones's paper.
--------------------------------------------------------------*)

let gen_syntax ((rs,_) as g:g) (src:string) (prefix:string) : unit =
  let ch = open_out (prefix ^ "syntax.ml") in
  printf_flush "Generating syntax definitions in file %ssyntax.ml...\n" prefix;
  Syntaxx.f ch src prefix gsyntax g gsexp g gtag g gsrc g gmap g giter g;
  close_out ch


(*------------------------------------------------------------

Generate scanner definitions in file ?scan.mll.

TODO: profile to see whether using a keyword hashtable (vs. explicitly
listing out all keywords as identifiers now) will improve performance
(for real examples like java.g). But there are only 51 keywords in
Java 5 anyway.

--------------------------------------------------------------*)

let gen_scan (qs:q list) (us:u X.t) (src:string) (prefix:string) : unit =
  let ch = open_out (prefix ^ "scan.mll") in
  printf_flush "Generating scanner definitions in file %sscan.mll...\n" prefix;

  let b1 = X.mem (Ident "_int") us in
  let b2 = X.mem (Ident "_int32") us in
  check (not b1 || not b2) "Cannot scan integers as both \
small integers '_int' and 32-bit integers '_int32'";

(* (* Pattern bindings unsupported in F# *)
  let s1 = "| int as x { Int (int_of_string x) }" in
  let s2 = "| int as x { Int32 (Int32.of_string x) }" in *)

  let s1 = "| int { Int (int_of_string (trim 0 0 lexbuf)) }" in
  let s2 = "| int { Int32 (Int32.of_string (trim 0 0 lexbuf)) }" in 
  let s = if b1 then s1 else s2 in

  let qs2 = L.map token_cname (L.sort qs) in
  let f1 ch (t,y) = fprintf ch "  | %s of %s\n" t y in
  let f2 ch x = fprintf ch "  | %s\n" x in
  let f3 ch q = fprintf ch "| \"%s\" { %s }\n" (S.show q) (token_cname q) in
  Scanx.f ch src prefix (L.fprint f1) (L.zip tbuiltin ybuiltin) 
    (L.fprint f2) qs2 (L.fprint f3) qs s;
  close_out ch


(*------------------------------------------------------------

  Generate parser definitions in file ?parse.ml.

--------------------------------------------------------------*)

let gen_parse ((rs,_) as g:g) (qs:q list) (us:u X.t) 
  (src:string) (prefix:string) : unit =
  (* todo: generate statistics about pda: states, ambiguity... *)
  printf_flush "Generating parser definitions in file %sparse.ml...\n" prefix;
  let ((_,_,ps,_) as cg) = grammar g qs us in
  if debug then C.check cg;

  let a = Pda.of_cfg cg prefix in
  let ch = open_out (prefix ^ "parse.ml") in
  let f1 ch (s,i) = fprintf ch "  | S.%s _ -> %d\n" s i in
  let f2 ch (q,i) = fprintf ch "  | S.%s -> %d\n" (token_cname q) i in
  let n = L.size tbuiltin in
  let qs2 = L.zip (L.sort qs) (L.interval (n+1) (L.size qs + n))  in

  let tindex = H.index_array a.P.ts in
  let xindex = H.index_array a.P.xs in
  let aindex = function T t -> C.T (tindex t) | X x -> C.X (xindex x) in
  let pindex0 = H.index_array a.P.ps in (* index of production rule *)
  let pindex (x,s) = pindex0 (xindex x, L.map aindex s) in
  let x0 = x0_of_g g in                 (* start symbol *)
  let q = S.capitalize prefix in

  Parsex.f ch src prefix q q (build us pindex) g 
    (L.fprint f1) (L.rindex tbuiltin)
    (L.size tbuiltin) (L.fprint f2) qs2
    (fshow us pindex) g gfilter g (ffilter us pindex) g
    (* S.to_dec (Compat.to_binary a) q q x0 x0; *)
    Pda.fcode a q q x0 x0;
  if Util.arg_bool "--debug-pda" then 
    fprintf ch "\n\n(*\nlet a = %a\n*)\n\n" Pda.fprint a;
  close_out ch


(*------------------------------------------------------------

Check grammar well-formedness.

TODO: give warning when the rule contains nullable terminals on the
end of left/right associative case, that is, (i<>0 && x<>x0) for
repetitions. Also give warning to see if two rules are
mutual-recursively dependent (such as types and expressions in Java),
in which case many ambiguous trees will be generated.

TODO: when a rule is of the form 't : t s' where 's' is a nullable
strings then the parse will diverge! For example, in java.g, 'Tarray'
is specified as 'Tarray: typ dimen*'. It should be 'Tarray: typ
dimen+' instead.

--------------------------------------------------------------*)

let rdomain : r -> x = function
  | Alias (x,_,_) -> x
  | Union (x,_,_) -> x

let domain ((rs,_):g) : x list = L.map rdomain rs

let ocaml_kw = X.of_list [              (* OCaml's reserved keywords *)
  "int"; "char"; "string"; "bool"; "unit"; "exn";
  "array"; "list"; "option"; "int32"; "int64"; "nativeint";

  "and"; "as"; "assert"; "asr"; "begin"; "class"; "constraint"; "do";
  "done"; "downto"; "else"; "end"; "exception"; "external"; "false";
  "for"; "fun"; "function"; "functor"; "if"; "in"; "include"; "inherit";
  "initializer"; "land"; "lazy"; "let"; "lor"; "lsl"; "lsr"; "lxor";
  "match"; "method"; "mod"; "module"; "mutable"; "new"; "object"; "of";
  "open"; "or"; "private"; "rec"; "sig"; "struct"; "then"; "to"; "true";
  "try"; "type"; "val"; "virtual"; "when"; "while"; "with"] 

let fsharp_kw = X.of_list [             (* F#'s reserved keywords *)
  "abstract"; "and"; "as"; "asr"; "asr"; "assert"; "async"; "atomic";
  "begin"; "break"; "checked"; "class"; "component"; "const";
  "constraint"; "constructor"; "continue"; "decimal"; "default";
  "delegate"; "do"; "done"; "downcast"; "downto"; "eager"; "else";
  "end"; "enum"; "exception"; "extern"; "false"; "finally"; "fixed";
  "for"; "fun"; "function"; "functor"; "if"; "in"; "include"; "inherit";
  "inline"; "interface"; "land"; "land"; "lazy"; "let"; "lor"; "lor";
  "lsl"; "lsl"; "lsr"; "lsr"; "lxor"; "lxor"; "match"; "member";
  "method"; "mixin"; "mod"; "mod"; "module"; "mutable"; "namespace";
  "new"; "null"; "object"; "of"; "open"; "or"; "override"; "params";
  "private"; "process"; "property"; "protected"; "public"; "pure";
  "readonly"; "rec"; "return"; "sealed"; "sig"; "static"; "struct";
  "switch"; "then"; "to"; "true"; "try"; "type"; "upcast"; "val";
  "virtual"; "void"; "volatile"; "when"; "while"; "with"]

let check ((rs,_) as g:g) : unit =
  if rs=[] then error "empty grammar";
  let xs1 = domain g in                 (* defined types *)
  let xs2 = X.of_list xs1 in            
  let xs3 = X.of_list xbuiltin in
  let xs4 = X.add (x0_of_g g) (gident g) in (* used types *)
  let xs5 = X.union xs2 xs3 in          (* bound types *)
  let xs6 = gtagid g in                   (* defined tags *)
  let xs7 = X.of_list xs6 in
  check (X.disjoint xs2 ocaml_kw)
    "error: these types are reserved keywords in ocaml: %s\n"
    (X.showx ", " (X.intersect xs2 ocaml_kw));
  check (X.disjoint xs2 xs3)
    "error: these types are reserved keywords in ocfgc: %s\n"
    (X.showx ", " (X.intersect xs2 xs3));
  check (X.disjoint xs2 fsharp_kw)
    "error: these types are reserved keywords in fsharp: %s\n"
    (X.showx ", " (X.intersect xs2 fsharp_kw));
  check (X.disjoint xs2 xs3)
    "error: these types are reserved keywords in ocfgc: %s\n"
    (X.showx ", " (X.intersect xs2 xs3));
  check (L.is_uniq xs1)
    "error: these types have more than one definitions: %s\n"
    (L.showx ", " (L.minus xs1 (L.uniq xs1)));  
  check (X.subset xs4 xs5)
    "error: unbound types: %s\n" (X.showx ", " (X.minus xs4 xs5));
  warn_if (X.subset xs2 xs4)
    "warning: unused types: %s\n" (X.showx ", " (X.minus xs2 xs4));
  check (L.is_uniq xs6)
    "error: these tags are used more than once: %s\n"
    (L.showx ", " (L.minus xs6 (L.uniq xs6)));  
  check (X.disjoint xs7 (X.of_list ["Some"; "None"]))
    "error: these types are reserved tags in ocaml: %s\n"
    (X.showx ", " (X.intersect xs7 (X.of_list ["Some"; "None"])))


(* REFERENCES

Concise Concrete Syntax, Stephen Tse and Steve Zdancewic. Submitted, 2006. 

A bug in that paper: for non-associative, recursive with x[i+1] on the
first and last symbol, instead of simply x (implemented in
'cgrammar').

Conjecture: combine a name with optional arguments into the same name,
see 'ty' in 'java.g' for combining basic types with vararg types,
instantiated types, and array types. For example:

  x : x0 x1? x2?

is equivalent to

  x : (= X2: x x2) (= X1: x x1) (= X0: x0)

*)

(* ocfgc.ml - ocfg (ordered context free grammar) compiler *)

module O = Ocfg

let main src prefix =
  let og = Oparse.parse src in
  O.check og;
  let qs = O.gliteral og in
  let us = O.gitem og in
  O.gen_scan qs us src prefix;
  O.gen_syntax og src prefix;
  O.gen_parse og qs us src prefix

let _ = 
  match Util.arg_list () with
  | [x;y] -> main x y
  | _ -> print_string "ocfgc: missing input filename or prefix\n"

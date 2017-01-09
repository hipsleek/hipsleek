open VarGen
open Camlp4.PreCast
open Iformula
open Globals
open Lexing
open Gen

let loc = no_pos;;

let command = Gram.Entry.mk "command";;

let un_option s d = match s with
  | Some v -> v
  | None -> d

EXTEND Gram
GLOBAL: command;
  command:
  [ "command" LEFTA
    [ "infer_spec"; x=id; "["; cmd=cmd; "]" -> 
      (x, cmd) 
    | "exit" -> ("", (false, None, None))
    ]
  ];

  cmd:
  [[ "<"; x=id; ","; "shape"; ">" -> (true, None, Some x)
   | transpec=opt_transpec; postx=infer_xpost -> (false, Some (mkEInfer postx transpec loc), None)
  ]];

  infer_xpost : 
  [[ "pre" -> Some false
   | "post" -> Some true
   | "both" -> None
  ]];

  opt_transpec: [[t=OPT transpec -> un_option t None ]];

  transpec:
  [[ old_view_name=id; "->"; new_view_name=id; "," -> Some (old_view_name, new_view_name)
  ]];

  id:
  [[ x=LIDENT -> x
   | x=UIDENT -> x
  ]];

END
	
let parse_cmd s = Gram.parse_string command (Loc.mk "<string>") s

(*let parse_cmd_i = *)
(*  print_string "# ";*)
(*  Gram.parse_string command (Loc.mk "<string>") (read_line ())*)









open VarGen
open Globals
open Gen.Basic
open Iast

module IF = Iformula

let parse_ints (file_name: string): Iast.prog_decl option =
  let in_chnl = open_in file_name in
  let lexbuf = Lexing.from_channel in_chnl in
  let iprog = Iparser.program Ilexer.tokenizer lexbuf in
  let () = close_in in_chnl in
  iprog

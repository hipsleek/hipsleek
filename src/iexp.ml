open VarGen
open Globals
open Iast

type ints_loc =
  | NumLoc of (int * loc)
  | NameLoc of (string * loc)

type ints_exp = 
  | Assume of ints_exp_assume
  | Assign of ints_exp_assign

and ints_exp_assume = {
  ints_exp_assume_formula: exp;
  ints_exp_assume_pos: loc;
}

and ints_exp_assign = {
  ints_exp_assign_lhs: exp;
  ints_exp_assign_rhs: exp;
  ints_exp_assign_pos: loc;
}

and ints_block = {
  ints_block_from: ints_loc;
  ints_block_to: ints_loc;
  ints_block_commands: ints_exp list;
  ints_block_pos: loc;
}

and ints_prog = {
  ints_prog_start: ints_loc;
  ints_prog_blocks: ints_block list;
}

let mkAssume e pos = 
  Assume {
    ints_exp_assume_formula = e;
    ints_exp_assume_pos = pos; }

let mkAssign lhs rhs pos = 
  Assign {
    ints_exp_assign_lhs = lhs;
    ints_exp_assign_rhs = rhs;
    ints_exp_assign_pos = pos; }

let mkBlock f t cmds pos = 
  { ints_block_from = f;
    ints_block_to = t;
    ints_block_commands = cmds;
    ints_block_pos = pos; }

let mkProg s blks =
  { ints_prog_start = s;
    ints_prog_blocks = blks; }
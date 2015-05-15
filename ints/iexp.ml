open VarGen
open Globals
open Iast

type parsedLoc =
  | NumLoc of int
  | NameLoc of string

type ints_exp = 
  | Assume of ints_exp_assume
  | Assign of ints_exp_assign
  | Block of ints_exp_block

and ints_exp_assume = {
  ints_exp_assume_formula: exp;
  ints_exp_assume_pos: loc;
}

and ints_exp_assign = {
  ints_exp_assign_lhs: exp;
  ints_exp_assign_rhs: exp;
  ints_exp_assign_pos: loc;
}

and ints_exp_block = {
  ints_exp_block_from: parsedLoc;
  ints_exp_block_to: parsedLoc;
  ints_exp_block_commands: ints_exp list;
  ints_exp_block_pos: loc;
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
  Block {
    ints_exp_block_from = f;
    ints_exp_block_to = t;
    ints_exp_block_commands = cmds;
    ints_exp_block_pos = pos;
  }
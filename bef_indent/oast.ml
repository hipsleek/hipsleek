#include "xdebug.cppo"
(*
open Oarith

type constr = 
  | Data node | View node refers to data/view definition or just names?
  | Ptr 
  | Arith

type data = refers to primitives and other data types

type view = refers to constr

type program = refers to data, view, and method definitions

type method = refers to constr (pre/post), expressions

type expression = refers to expressions, constr (assert/assume, loop annotations)

*)

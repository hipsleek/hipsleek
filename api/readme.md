# Building API as opam package

```sh
dune build
opam install .
```

# HIPSLEEK docs

---

## Core Language
The following is an incomplete grammar of the core language.

```
Spec_var ::= string ;

Ident ::= string ;

Type ::= string ;

Ghost ::= | "assert" Formula ; assertion
          | "dprint" ; print current state (?)
          | "unfold" Spec_var ; unfold specification variables

Ident_tuple ::= "()" | "(" Ident ("," Ident)* ")"

Expr ::= | integer ; integer constant
         | float ; float constant
         | "true" | "false" ; boolean constant
         | "if" Ident "[" Expr "]" "else" "[" Expr "]" ; conditional
         | "bind" Ident "to" Ident_tuple "in" Expr ; bind
         | Ident Ident_tuple ; function application
         | Ident "=" Expr ; assignment
         | Expr ";" Expr ; sequence
         | Ghost ; ghost expressions
         | "{" Expr "}" ; block
         | Type " " Ident ; variable declaration
         | "(" Type ")" Expr ; type casting (?)
         | "debug on" | "debug off" ; turning on or off devel debug
         | "while" (" Ident ")" Expr ; loop
         | "try" Expr "catch" "(" Type " " Ident ")" Expr ; try-catch
```
(Note that for `bind`, the number of bound variables must be equal to the number of
fields in the data declaration.)

## Some important files
- `solver.ml`
- `typechecker.ml`
- `astsimp.ml`

## General Flow

Input file -- Parse --> Input Ast (Iast) -- Normalization --> Iast
-- Translation --> Core Ast (Cast) -- Forward verification --> Cast
-- Entailment checking --> Done.

### Normalization
Relevant files : `astsimp.ml`  
Relevant functions : `case_normalize_program`, `case_normalize_proc`,
`case_normalize_struc_formula`

The following is a non-exhaustive list of normalization performed:

- While loops.
```
while Cond { Body }
->
let v_bool = Cond in
while v_bool { Body }
```

- Function application.
```
function_ident(expresssion_1,...,expression_n)
->
let v1 = expression_1 in
...
let vn = expression_n in
function_ident(v1,...,vn)
```
(Note the left to right evaluation of arguments)

### Translation
Relevant files : `astsimp.ml`  
Relevant functions : `trans_prog`, `trans_proc`, `trans_views`, `trans_axiom`,
`trans_I2C_struc_formula`, `trans_exp`

To have simpler rules for forward verification, HIPSLEEK first performs some
transformation on the Iast before translating it to Cast which is a simplified version
of Iast.

The following is a non-exhaustive list of transformation performed:

- Transform while statements to tail recursive top level functions.
```
while Cond { Body }
->
while_rec = if Cond [ Body; while_rec ]
            else []
```
(Note that `while_rec` is the new tail recursive function introduced during
transformation.)

- Transform break/continue to try-catch block.
```
while Cond {... break; ...}
->
while_rec =
try ( if Cond [ try { ... throw brk_default ... }
                catch (cnt_default) { };
                while_rec ]
     else [] )
catch (brk_default) { }
```

```
while Cond {... continue; ...}
->
while_rec =
try ( if Cond [ try { ... throw cnt_default ... }
                catch (cnt_default) { };
                while_rec ]
     else [] )
catch (brk_default) { }
```

- Transform field accesses to bind.
```
x.f_i
->
bind x to (v_1,...,v_i,...,v_n) in v_i
```

```
x.f_i = v
->
bind x to (v_1,...,v_i,...,v_n) in v_i = v
```

- Transform primitive operations to function calls.
```
x + y
->
add___$int~int(x, y)
```
(Note that these primitive functions are defined in `prelude.ss`.)

These transformations are done in `trans_exp` before translating to Cast.

### Forward verification
Relevant files : `typechecker.ml`  
Relevant functions : `check_proc`, `check_specs_infer`, `check_exp`

`check_proc` is applied to every procedure/function in the program to be verified.

`check_exp` essentially implements the forward verification rules. It will initialize
a proof state (`Cformula.list_failesc_context`) that contains the pre condition of 
the function and walk through the body of the function.
While walking through the body of the function, it will update the proof state
according to the forward verification rules and the kind of expression in the body.

If there is a function call within the body of the function, `check_exp` will check
whether the proof state at the call site entails the pre condition of the
function being called. If it does, then the proof state after the call will be the
composition of the residue from the entailment checking and the post condition of the
function being called.

### Entailment checking
Relevant files : `typechecker.ml`, `solver.ml`  
Relevant functions : `check_proc`, `check_specs_infer`, `check_post`,
`heap_entail_struc_list_partial_context_init`

After `check_exp` returns the final proof state after walking through the entire body
of the function, `check_post` will be called with the final proof state.
It will then call `heap_entail_struc_list_partial_context_init` which will check whether
the final proof state entails the post condition of the function. It it does, then the
verification of the function succeeds. Otherwise, verification of the function fails.

# API docs

---

## Limitations of API/ Possible improvements
- Ghost statements (e.g. `assert`)
- OOP
- Termination checking
- Better handling of failed proving than just throwing an exception

# Miscellaneous

---

**Q: What is a view?**

**A:** Views are predicates.

**Q: What is Iast.proc_decl.proc_ho_arg?**

**A:** Higher order arguments. They are currently not supported in the api.
Check out `rho/web/cdl-ex3-fm.ss` for example of these higher order arguments.
They are variables prefixed with `%` symbol. (e.g. `%P`).

**Q: What is the difference between dynamic and static specs?**

**A:** Dynamic specs are used for OOP where dynamic binding is used to resolve method
calls at runtime and therefore function specs. Static specs should be used most of the
time.

**Q: What are instance call (Cast.ICall) and static calls (Cast.SCall)?

**A:** Instance calls are used for method calls in OOP and static calls are used for
both static method calls in OOP and regular function calls.

**Q: What is para continuation analysis?**

**A:** Continuation analysis for views. To find out the continuation parameters
for each view in the program and insert them into the `Cast.view_cont_vars` field
of `Cast.view_decl`.
Examples for views with continuation parameters are `WFSegN` and `WFSeg` in
`prelude.ss`.

**Q: What does Astsimp.compute_view_x_formula do?**

**A:** Uses Xpure approximation on predicate to compute predicate invariant.

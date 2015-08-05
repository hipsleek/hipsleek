This dir will contain a variety of demos with examples.

# running SLEEK prover
../sleek demo.slk

# running HIP verifier
../hip demo.ss

Debugging (by tracing selected methods)
=======================================
../sleek demo.slk -dre "heap_entail"

(==solver.ml#8359==)
heap_entail_build_mix_formula_check#2@9@8@7@6@5@4@3@2@1
heap_entail_build_mix_formula_check#2 inp1 :evars:[]
heap_entail_build_mix_formula_check#2 inp2 :ante: ((self=null & n=0) | (1<=n & self!=null))
heap_entail_build_mix_formula_check#2 inp3 :conseq: 0<=n
heap_entail_build_mix_formula_check#2@9 EXIT:( ((self=null & n=0) | (1<=n & self!=null)), 0<=n)

(==solver.ml#7619==)
heap_entail_empty_rhs_heap#1@8@7@6@5@4@3@2@1
heap_entail_empty_rhs_heap#1 inp1 :es:  emp&((self=null & n=0) | (1<=n & self!=null))&{FLOW,(1,26)=__flow#E}[]
 
heap_entail_empty_rhs_heap#1 inp2 :lhs: emp&((self=null & n=0) | (1<=n & self!=null))&{FLOW,(1,26)=__flow#E}[]
heap_entail_empty_rhs_heap#1 inp3 :rhs: 0<=n
heap_entail_empty_rhs_heap#1 inp4 :is_folding:false
heap_entail_empty_rhs_heap#1@8 EXIT: [
   emp&((self=null & n=0) | (1<=n & self!=null))&{FLOW,(1,26)=__flow#E}[]
  ]

# calling hierarchy

../sleek demo.slk -dre "heap_entail" --dd-calls-all

%%%        heap_entail_conjunct@6.
%%%         isTrivTerm
%%%         heap_entail_conjunct_helper@7.
%%%          ptr_equations_without_null
%%%           get_int_equality
%%%           pure_ptr_equations_aux
%%%          simplify_htrue
%%%          infer_collect_hp_rel_empty_rhs
%%%          heap_entail_empty_rhs_heap@8.
%%%           keep_hrel
%%%           merge_alias_nodes_formula
%%%           xpure_heap
%%%            xpure_heap_mem_enum
%%%             h_formula_2_mem
%%%              build_eset_of_imm_formula


# Wrapping a call to be debug traced..

  Debug.no_3_num hec_num "heap_entail_conjunct" string_of_bool Cprinter.string_of_context Cprinter.string_of_formula
    (fun (c,_) -> Cprinter.string_of_list_context c)
    hec is_folding ctx0 conseq


Lexer
=====
lexer.mll

   ("pred", PRED);
  | "." { DOT }

Parser
======
parser.ml

# hip view_header

view_decl: 
  [[ vh= view_header; `EQEQ; vb=view_body; oi= opt_inv; obi = opt_baga_inv; obui = opt_baga_under_inv; li= opt_inv_lock; mpb = opt_mem_perm_set
          (* let f = (fst vb) in *)
          ->  let (oi, oboi) = oi in

# sleek view header?

...


Detailed Trace Debugging
========================
Create a log file, say dd.log

#heap_entail_conjunct_helper,Loop
#heap_entail_conjunct,Trace
#translate_tup2_imply,Trace
heap_entail_empty_rhs,Trace
heap_entail_non_empty_rhs_heap

@29! **solver.ml#2797:Omega unsat:end 36 invocations
@29! **solver.ml#2882:es_formula: emp&((self=p & n=0) | (1<=n & self!=null))&{FLOW,(1,29)=__flow#E}[]
@29! **solver.ml#2885:es_formula: emp&((self=p & n=0) | (1<=n & self!=null))&{FLOW,(1,29)=__flow#E}[]
@29! **solver.ml#2887:es_formula(2): emp&((self=p & n=0) | (1<=n & self!=null))&{FLOW,(1,29)=__flow#E}[]

(==solver.ml#7619==)
heap_entail_empty_rhs_heap#1@29@28
heap_entail_empty_rhs_heap#1 inp1 :es:  emp&((self=p & n=0) | (1<=n & self!=null))&{FLOW,(1,29)=__flow#E}[]
 
heap_entail_empty_rhs_heap#1 inp2 :lhs: emp&((self=p & n=0) | (1<=n & self!=null))&{FLOW,(1,29)=__flow#E}[]
heap_entail_empty_rhs_heap#1 inp3 :rhs: 0<=n
heap_entail_empty_rhs_heap#1 inp4 :is_folding:false
heap_entail_empty_rhs_heap#1@29 EXIT: [
   emp&((self=p & n=0) | (1<=n & self!=null))&{FLOW,(1,29)=__flow#E}[]
  ]

pred_prim nondet<>
  inv true;

int nondeterm()
  requires true
  ensures res::nondet<>;

bool nondet_bool()
  requires true
  ensures res::nondet<>;

void foo() 
  requires Loop
  ensures Loop;
{ 
  bool b = nondet_bool();
  if (b) {
    foo();
    dprint;
  }
}

/*
# nondet/ex3a.ss

ERROR: at _0:0_0:0
Message: [term.ml][strip_lexvar_lhs]: More than one LexVar to be stripped. es_formula: 
  (exists b_35': b_35'::nondet{}<>&Loop{ 12:0}[] & b_35'&
  {FLOW,(4,5)=__norm#E}[]
 es_history: [emp; emp; emp; emp]
 es_cond_path: [1; 0]
 es_var_measures 1: Some(MayLoop[]{})
 es_infer_vars_rel: []

Procedure foo$ FAIL.(2)



*/

data cell{
 int fst;
}

relation P(ann v1).
//relation P3(ann v1, int v,int r, int s).


int foo2(cell c)
//  infer [P]
//  infer [@term]
//  infer [ @imm_post]
  infer [ @imm_pre]
//  infer [@post_n, @imm_post]
//  infer [@post_n]
//  requires c::cell<v>
  requires c::cell<v>@a //& P(a)
  ensures c::cell<w>@b  ;
{
  int x = c.fst;
  if (x>0) c.fst = 5;
  return x;
}

/*
../../hip ex15c1-inf-post.ss --dis-imm-norm -dre "infer_imm_ann_proc\|add_post" -dd --trace-exc 

!!!:0: 0: **typechecker.ml#654:vars_rel1:[P__1434]Exception(check_specs_infer):Not_found
Exception(check_proc):Not_found
Exception Not_found Occurred!


*/


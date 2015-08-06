
/*
Immutability Annotation Inference
Precondition
*/

data cell {
 int fst;
 int snd;
}

void simple_read_write(cell c)
  infer [@imm_pre]
  requires c::cell<f,h>
  ensures c::cell<g,h> & (g = f + 1);
{
  c.fst = c.fst + 1;
}


/*
!!! **infer.ml#1428:RelInferred (rel_ass):[RELASS [P__1397]: ( P__1397(ann_1396,ann_1395)) -->  ann_1395<:@L]push_list:[RELASS [P__1397]: ( P__1397(ann_1396,ann_1395)) -->  ann_1395<:@L]
push_list:[(stk_rel_ass):RELASS [P__1397]: ( P__1397(ann_1396,ann_1395)) -->  ann_1395<:@L]

WARNING: _0:0_0:0:Z3 error message: (error "line 661 column 34: unknown function/constant P__1397")

WARNING: _0:0_0:0:Z3 error message: (error "line 682 column 34: unknown function/constant P__1397")

WARNING: _0:0_0:0:Z3 error message: (error "line 700 column 35: unknown function/constant P__1397")
*/

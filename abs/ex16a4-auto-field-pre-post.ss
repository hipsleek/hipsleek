
/*
Immutability Annotation Inference
Precondition
*/

data cell {
 int fst;
 int snd;
}

void simple_read_write(cell c)
  infer [@imm_pre,@imm_post]
  requires c::cell<f,h>
  ensures c::cell<g,h> & (g = f + 1);
{
  c.fst = c.fst + 1;
}

/*
# ex16a4.ss

# Why did we have three push?
# Why is there WARNING after push. Did the relation
  table for z3 came from somewhere else?

XXXX push_list(rel_decls}[ relation P__1395(AnnT ann_1396:AnnT).
, relation P__1397(AnnT ann_1398:AnnT).
]

XXXX push_list(rel_decls}[ relation P__1419(AnnT ann_1420:AnnT).
]

WARNING: _0:0_0:0:Z3 error message: (error "line 1724 column 31: unknown function/constant P__1419")

XXXX push_list(rel_decls}[ relation nondet_int__(int r:int).
, relation waitS(bag(tup2(Object,Object)) g:bag(tup2(Object,Object)), bag(Object) S:bag(Object), Object d:Object).
, relation acyclic(bag(tup2(Object,Object)) g:bag(tup2(Object,Object))).
, relation cyclic(bag(tup2(Object,Object)) g:bag(tup2(Object,Object))).
, relation concrete(bag(Object) g:bag(Object)).
, relation set_comp(bag(tup2(Object,Object)) g:bag(tup2(Object,Object)), bag(Object) S:bag(Object), Object d:Object).
, relation amodr(int[] a:int[], int[] b:int[], int i:int, int j:int).
, relation update_array_2d(int[][] a:int[][], int[][] r:int[][], int val:int, int i:int, int j:int).
, relation update_array_1d(int[] a:int[], int[] r:int[], int val:int, int i:int).
, relation update_array_1d_b(boolean[] a:boolean[], boolean[] b:boolean[], boolean val:boolean, int i:int).
, relation domb(boolean[] a:boolean[], int low:int, int high:int).
, relation dom(int[] a:int[], int low:int, int high:int).
, relation induce(int value:int).
]

------
smt warning


1:4327:XXXX push_list(global_rel_defs:1)[nondet_int__[r]]
1:4329:XXXX push_list(global_rel_defs:1)[waitS[g,S,d]]
1:4331:XXXX push_list(global_rel_defs:1)[acyclic[g]]
1:4333:XXXX push_list(global_rel_defs:1)[cyclic[g]]
1:4335:XXXX push_list(global_rel_defs:1)[concrete[g]]
1:4337:XXXX push_list(global_rel_defs:1)[set_comp[g,S,d]]
1:4339:XXXX push_list(global_rel_defs:1)[amodr[a,b,i,j]]
1:4341:XXXX push_list(global_rel_defs:7)[amodr[a,b,i,j],set_comp[g,S,d],concrete[g],cyclic[g],acyclic[g],waitS[g,S,d],nondet_int__[r]]
1:4355:XXXX push_list(global_rel_defs:1)[domb[a,low,high]]
1:4357:XXXX push_list(global_rel_defs:1)[dom[a,low,high]]
1:4359:XXXX push_list(global_rel_defs:1)[induce[value]]
1:4361:XXXX push_list(global_rel_defs:10)[induce[value],dom[a,low,high],domb[a,low,high],amodr[a,b,i,j],set_comp[g,S,d],concrete[g],cyclic[g],acyclic[g],waitS[g,S,d],nondet_int__[r]]
1:4369:XXXX push_list(global_rel_defs:10)[induce[value],dom[a,low,high],domb[a,low,high],amodr[a,b,i,j],set_comp[g,S,d],concrete[g],cyclic[g],acyclic[g],waitS[g,S,d],nondet_int__[r]]
1:4377:XXXX push_list(global_rel_defs:10)[induce[value],dom[a,low,high],domb[a,low,high],amodr[a,b,i,j],set_comp[g,S,d],concrete[g],cyclic[g],acyclic[g],waitS[g,S,d],nondet_int__[r]]
1:6477:XXXX push_list(global_rel_defs:10)[induce[value],dom[a,low,high],domb[a,low,high],amodr[a,b,i,j],set_comp[g,S,d],concrete[g],cyclic[g],acyclic[g],waitS[g,S,d],nondet_int__[r]]
1:6491:XXXX push_list(global_rel_defs:10)[induce[value],dom[a,low,high],domb[a,low,high],amodr[a,b,i,j],set_comp[g,S,d],concrete[g],cyclic[g],acyclic[g],waitS[g,S,d],nondet_int__[r]]
1:6505:XXXX push_list(global_rel_defs:10)[induce[value],dom[a,low,high],domb[a,low,high],amodr[a,b,i,j],set_comp[g,S,d],concrete[g],cyclic[g],acyclic[g],waitS[g,S,d],nondet_int__[r]]


*/

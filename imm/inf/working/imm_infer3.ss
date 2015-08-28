
data tree {
 int node;
 tree left;
 tree right;
}

/* Working, but right tree should be @A in both cases
 * Check again after fixing
 */

int left_read(tree t)
   infer [@imm_pre]
   requires t::tree<_,l,r> * l::tree<_,_,_> * r::tree<_,_,_>
   ensures t::tree<_,l,r> * l::tree<_,_,_> * r::tree<_,_,_>;
{
  return t.left.node;
}
/*
int left_write(tree t)
   infer [@imm_pre]
   requires t::tree<_,l,r> * l::tree<_,_,_> * r::tree<_,_,_>
   ensures t::tree<_,l,r> * l::tree<_,_,_> * r::tree<_,_,_>;
{
  t.left.node = t.left.node + 3;
  return 0;
}
*/

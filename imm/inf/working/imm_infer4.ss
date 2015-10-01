
data tree {
 int node;
 tree left;
 tree right;
}

/* Working, but right tree should be @A in both cases
 * Check again after fixing
 */

int no_read(tree t)
   infer [@imm_pre]
   requires t::tree<_,l,r> * l::tree<_,_,_> * r::tree<_,_,_>
   ensures t::tree<_,l,r> * l::tree<_,_,_> * r::tree<_,_,_>;
{
  return 3;
}

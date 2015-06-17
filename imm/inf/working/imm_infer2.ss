
data tree {
 int node;
 tree left;
 tree right;
}

void recursive_read_only(tree t)
   infer [@imm_pre]
   requires t::tree<_,_,_>
   ensures t::tree<_,_,_>;
{
  if (t.left != null) recursive_read_only(t.left);
  int c = t.node;
  if (t.right != null) recursive_read_only(t.right);
}

void recursive_write(tree t)
   infer [@imm_pre]
   requires t::tree<_,_,_>
   ensures t::tree<_,_,_>;
{
  if (t.left != null) recursive_write(t.left);
  t.node = t.node + 1;
  if (t.right != null) recursive_write(t.right);
 }

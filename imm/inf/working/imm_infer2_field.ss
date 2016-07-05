
data tree {
 int node;
 tree left;
 tree right;
}

void recursive_read_only(tree t)
   infer [@imm_pre]
   requires t::tree<_,l,r>
   ensures t::tree<_,_,_>;
{
  if (t.left != null) recursive_read_only(t.left);
  int c = t.node;
}

/*
To find why @ann_1241 is @A

Post Inference result:
recursive_read_only$tree
EBase 
exists (Expl)[](Impl)[Anon_13; l; 
                      r](ex)[]t::tree<Anon_13@ann_1241,l@ann_1242,r@ann_1243>@M&ann_1243=@A & 
ann_1242=@L & ann_1241=@A & MayLoop[]&{FLOW,(4,5)=__norm#E}[]
EAssume 
(exists Anon_1235,Anon_1236,Anon_1237,ann_1240,ann_1239,
        ann_1238: t::tree<Anon_1235@ann_1238,Anon_1236@ann_1239,Anon_1237@ann_1240>@M&
        {FLOW,(4,5)=__norm#E}[]
*/

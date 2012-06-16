data cell{int val;}
data tree{tree left; tree right; int val;}
data node{int v; node n;}

// simple tree and list constructors
// for data structures that keep track of the total ownership shares available in the structure 

void combine_tree(tree leftT, tree rightT, tree combT)
  requires leftT::tree@s1<l1,l2,v1> * rightT::tree@s2<r1,r2,v2> * combT::tree@s3<c1,c2,v3> & join(s1,s2,s3) ensures combT::tree@s3<leftT,rightT,v3>;
{
  combT.left = leftT;
  combT.right = rightT;
}

tree combine_tree_2(tree leftT, tree rightT, int v)
  requires [s3] leftT::tree@s1<l1,l2,v1> * rightT::tree@s2<r1,r2,v2> & join(s1,s2,s3) ensures exists combT : combT::tree@s3<leftT,rightT,v> & res = combT;
{
  tree t = new tree(leftT,rightT,v);
  return t;
}

node append(node n1, node n2)
  requires [s3] n1::node@s1<v1,n11> * n2::node@s2<v2,n22> & join(s1,s2,s3) ensures exists nres: nres::node@s3<v1,n2> & res = nres;
{
  node n3 = new node(n1.v,n2);
  return n3;
}

node deleteAfter(node n1)
  requires [s3] n1::node@s1<v1,n11> * n11::node@s2<v11,n111> & join(s1,s2,s3) ensures exists nres: nres::node@s3<v1,n111> & res = nres;
{
  node n2 = new node(n1.v,n1.n.n);
  return n2;
} 

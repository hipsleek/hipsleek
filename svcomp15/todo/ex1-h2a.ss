

data node {
  int val;
  node next;
}

GG<m> ==
 case { m>=0 -> [] self::node<0,null>;
        m<0 -> [] self = null;
};

PostPred G(node a, int b).

node NewNode(int a)
//  requires true ensures res::GG<a>;
  infer [G] requires emp &true ensures G(res,a);
{
  node x = null;
  if (a >=0) x=new node(0,null);

  return x;
}

/*
void main()
 requires true ensures true;
{
  node tmp = NewNode(1);
  tmp.val = 0;

  return;
}
*/

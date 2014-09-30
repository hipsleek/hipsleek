data node {
  int val;
  node left;
  node right;
}

node get_min(node x)
{
  if (x == null)
    return null;
  else if (x.left == null)
    return x;
  else
    return get_min(x.left);
}

/*
case {
   x=null -> 
     ensures emp & x1=null & res=null & res=x1;; 
   left=null & x!=null -> 
     requires x::node<val,left,DP>@M & left=null
     ensures x1::node<val,left,DP>@M & res=x1 & left=null;; 
   left!=null & x!=null -> 
     requires x::node<val,left,DP>@M * HP_13(left) & left!=null
     ensures x1::node<val,left,DP>@M * GP_14(left,res) & left!=null;; 
   }
*/

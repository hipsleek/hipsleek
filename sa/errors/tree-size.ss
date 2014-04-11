data node {
  int val;
  node left;
  node right;
}

int get_size(node x)
{
  if (x == null)
    return 0;
  else
    return get_size(x.left) + get_size(x.right);
}

/*
case {
   x=null -> 
     ensures emp & res=0 & x1=null;; 
   x!=null -> 
     requires HP_13(left1) * HP_13(right1) * x::node<val1,left1,right1>@M & true
     ensures x1::node<val,left,right>@M * GP_14(left,v1) * GP_14(right,v) & res=v+v1;; 
   }
*/



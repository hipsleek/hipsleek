data node {
  int val;
  node next;
}

HeapPred H(node a, node b).
  HeapPred G(node a, node b, node c).

node get_last(node x)
{
  if (x != null)
    {
      while (x.next != null)
        {
          x = x.next;
        }
    }
  return x;
}

node append(node x, int d)
  infer[H,G]
  requires H(x,y)
     ensures G(x,y,res);
{
  node new_list = new node(d, null);
  if (x != null)
    {
      node last = get_last(x);
      last.next = new_list;
      return x;
    }
  else
    return new_list;
}

/*
*************************************
**************case specs*************
*************************************
 case {
   x=null -> 
     ensures res::node<d',v>@M & v=null & x1=null;; 
   x!=null -> 
     requires x::HP_12<> & x!=null
     ensures new::node<d',v1>@M * x1::GP_1000<last> * last::node<val,new>@M & res=x1 & v1=null;; 
   }
*************************************

*************************************
*******relational definition ********
*************************************
[ H(x,y) ::=(1;0) x::HP_12<>@M&x!=null \/ (2;0) emp&x=null,
 G(x,y,res) ::=(1;0) x::GP_1000<last>@M * last::node<val,new>@M * new::node<d',v1>@M&res=x & 
v1=null
   \/ (2;0) res::node<d',v>@M&v=null & x=null]
*************************************
*/

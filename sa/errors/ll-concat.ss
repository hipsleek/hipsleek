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

  node concat (node x, node y)
    infer[H,G]
    requires H(x,y)
       ensures G(x,y,res);//'
{
  if (y != null)
    {
      if (x != null)
        {
          node last = get_last(x);
          last.next = y;
        }
      else
        x = y;
    }

  return x;
}

/*
*************************************
**************case specs*************
*************************************
 case {
   y=null -> 
     ensures emp & res=x & y1=null;; 
   y!=null & x1=null -> 
     ensures emp & res!=null & res=y1 & x=null;; 
   x1!=null & y!=null -> 
     requires x1::HP_12<> & x1!=null & y!=null
     ensures x::GP_998<last> * last::node<val,y1>@M & y1!=null & res=x;; 
   }
*************************************

*************************************
*******relational definition ********
*************************************
[ H(x,y) ::=(1;1;0) x::HP_12<>@M&x!=null & y!=null
   \/ (2;1;0) emp&y!=null & x=null \/ (2;0) emp&y=null,
 G(x,y,res) ::=(1;1;0) x::GP_998<last>@M * last::node<val,y>@M&y!=null & res=x
   \/ (2;1;0) emp&res!=null & res=y & x=null \/ (2;0) emp&res=x & y=null]
*************************************
*/

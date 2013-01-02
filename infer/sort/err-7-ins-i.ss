/* selection sort */

data node {
	int val; 
	node next; 
}

relation R0(node x, node y, node z).

ll<> == self=null
  or self::node<_,p> * p::ll<>
inv true;

node insert(node x, node y)
  infer [R0]
  requires x::ll<> * y::node<v,null>
  ensures  res::ll<> & R0(res,x,y);

/*
  //expecting res=x | res=y

[RELDEFN R0: ( res=y & x=null & y!=null) 
          -->  R0(res,x,y),
RELDEFN R0: ( (res=y & x!=null & x<res) | (res=y & res!=null & res<x)) 
          -->  R0(res,x,y),
RELASS [R0]: ( R0(tmp_681,p_633,y)) -->  y=null,
RELDEFN R0: ( res=x & x!=null & y!=null & R0(tmp_681,p_633,y)) 
          -->  R0(res,x,y)]

You derived the above:
By hand, I could only spot the following:
  // x=null & y!=null & res=y --> R0(res,x,y)
  // x!=null & y!=null & res=y (& x!=y) --> R0(res,x,y)
  // x!=null & y!=null & res=x & R(_,_,y) --> R0(res,x,y)

Thus, the following two derived obligations seem wrong!
RELDEFN R0: ( (res=y & x!=null & x<res) | (res=y & res!=null & res<x)) 
          -->  R0(res,x,y),
RELASS [R0]: ( R0(tmp_681,p_633,y)) -->  y=null,

Can you see how we may fix these errors?

*/

{
  if (x==null) return y;
  // x=null & y!=null & res=y --> R0(res,x,y)
  else {
    int t = x.val;
    if (y.val<=x.val) {
        y.next = x;
        return y;
        // x!=null & y!=null & res=y --> R0(res,x,y)
    } else {
      node tmp;
      tmp = insert(x.next,y);
      //assume tmp'=null or tmp'!=null;
      x.next=tmp;
      return x;
        // x!=null & y!=null & res=x & R(_,_,y) --> R0(res,x,y)
    }
   }
}











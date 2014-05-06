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

OK NOW

  requires x::ll<> * y::node<v,null>
  ensures  res::ll<> & (res=x & x!=null & y!=null 
           | res=y & y!=null);

!!! REL POST :  R0(res,x,y)
!!! POST:  (res=x & x!=null & y!=null) | (res=y & y!=null)
!!! REL PRE :  true
!!! PRE :  true
  //expecting res=x | res=y

[RELDEFN R0: ( res=y & x=null & y!=null) -->  R0(res,x,y),
RELDEFN R0: ( (res=y & x!=null & x<res) | (res=y & res!=null & res<x)) 
   -->  R0(res,x,y),
RELDEFN R0: ( res=x & x!=null & y!=null & R0(tmp_627,p_579,y)) 
    -->  R0(res,x,y)]

*/

{
  if (x==null) return y;
  // x=null & y!=null & res=y --> R0(res,x,y)
  else {
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











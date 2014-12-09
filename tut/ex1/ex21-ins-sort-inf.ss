data node {
  int val;
  node next;
}

/*
lsortI<m> == self::node<m,null>
  or self::node<m,q>*q::lsortI<m2> & m<=m2
  inv self!=null;
*/

lsortI<m> == self=null & m=\inf
  or self::node<m,q>*q::lsortI<m2> & m<=m2 
  inv true;

node insert(node x, node y)
  requires x::node<v,null> * y::lsortI<mm> 
  ensures res::lsortI<r> & r=min(v,mm);

{
  if (y==null) {
    //assume false;
     return x;
  }
  else 
    if (x.val<=y.val) {
      x.next=y; return x;
    } else {
      node tmp = insert(x,y.next);
      y.next = tmp;
      return y;
    }
}

/*
# ex21-ins-sort-inf.ss --en-inf

Can we handle arbitrary null case?

Checking procedure insert$node~node... 
Post condition cannot be derived:
  (may) cause:  (((x=1 & null=2) | (x=1 & null=null & mm=\inf))) 
      & v<=(\inf) |-  v=min(v,mm). LOCS:[23;17;21;0;13;12;19] (may-bug)

 Is this lsortI xpure correct

 xform: (0-(\inf))<(\inf) & (((self=null & \inf=m & 0<(m+(\inf))) | (true & 
           self!=null)))
 
*/

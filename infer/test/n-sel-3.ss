/* selection sort */

data node {
	int val; 
	node next; 
}


llMM<mi,mx> == self::node<v,null> & mi=v  & mx=v
  or self::node<v, p> * p::llMM<mi2,mx2> & mi=min(v,mi2) & mx=max(v,mx2)
  //& v<=mi2
inv self!=null & mi<=mx;

sortMM<mi,mx> == self::node<v,null> & mi=v  & mx=v
  or self::node<v, p> * p::sortMM<mi2,mx2> & mi=min(v,mi2) & mx=max(v,mx2)
  & v<=mi2
inv self!=null & mi<=mx;

relation P3(int a1, int a2,int a3).
relation P4(int a1, int a2,int a3).
relation P5(int a1, int a2,int a3).
relation P6(int a1, int a2,int a3).

node sel(ref node x)
     requires x::llMM<mi,mx> 
     ensures  res::node<mi,_> & x'=null & mi=mx
           or res::node<mi,_> * x'::llMM<mi2,mx> & mi<=mi2
     ;
{
  node tmp;
  if (x.next==null)
    { tmp=x; x=null; return tmp;}
  else {
    tmp = x.next;
    node n = sel(tmp);
    if (n.val<=x.val) {
       x.next = tmp;
       return n;
    } else {
      node r = x;
      n.next = tmp;
      x = n;
      return r;
    }
  }
}



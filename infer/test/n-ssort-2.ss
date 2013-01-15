/* selection sort */

data node {
	int val; 
	node next; 
}


llMM<v,mi,mx> == self::node<v,null> & mi=v  & mx=v
  or self::node<v, p> * p::llMM<_,mi2,mx2> & mi=min(v,mi2) & mx=max(v,mx2)
  //& v<=mi2
inv self!=null & mi<=v<=mx;

sortMM<mi,mx> == self::node<v,null> & mi=v  & mx=v
  or self::node<v, p> * p::sortMM<mi2,mx2> & mi=min(v,mi2) & mx=max(v,mx2)
  & v<=mi2
inv self!=null & mi<=mx;

node sel(ref node x)
     requires x::llMM<v,mi,mx> 
     ensures  res::node<mi,_> & x'=null & mi=mx & mi=v
           or res::node<mi,_> * x'::llMM<v2,mi2,mx> & mi<=mi2
     ;
/*
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
*/

relation P(int a1, int a2,int a3,int a4).

node sort(node x)
     //infer [P]
     requires x::llMM<_,mi,mx> 
     ensures  res::llMM<v,mi2,mx2> & mx=mx2 & mi=mi2 & mi2<=mx & mi=v
     //ensures  res::sortMM<mi2,mx2> & mx=mx2 & mi=mi2 & mi2<=mx
     ;
{
  node hd1;
  hd1 = sel(x);
  if (x==null)
    { hd1.next=null; return hd1;}
  else {
    node tmp;
    tmp=sort(x);
    hd1.next=tmp;
    return hd1;
  }
} 
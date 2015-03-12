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

node sel(ref node x)
     requires x::llMM<mi,mx> 
     ensures  res::node<mi,_> & x'=null & mi=mx
           or res::node<mi,_> * x'::llMM<mi2,mx> & mi<=mi2
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
     infer [P]
     requires x::llMM<mi,mx> 
     ensures  res::llMM<mi2,mx2> & P(mi,mx,mi2,mx2)
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

/*
!!! REL POST :  P(mi,mx,mi2,mx2)
!!! POST:  mx=mx2 & mi=mi2 & mi2<=mx
!!! REL PRE :  true
!!! PRE :  true

[RELDEFN P: ( mi2=mx & mx=mx2 & mi=mx) -->  P(mi,mx,mi2,mx2),
RELDEFN P: ( mi2<=mx2_646 & P(mi_632,mx,mi2,mx2_646) & mi=mx2 & mx2_646<=mi & 
mi<=mi_632 & mi_632<=mx) -->  P(mi,mx,mi2,mx2),
RELDEFN P: ( P(mi_632,mx,mi2,mx2) & mi2<=mi & mi<=mi_632 & mi_632<=mx & mi<mx2) -->  P(mi,mx,mi2,mx2),
RELDEFN P: ( mi2_645<=mx2 & P(mi_632,mx,mi2_645,mx2) & mi=mi2 & (mi+1)<=mi2_645 & 
mi<=mi_632 & mi_632<=mx) -->  P(mi,mx,mi2,mx2)]
*/
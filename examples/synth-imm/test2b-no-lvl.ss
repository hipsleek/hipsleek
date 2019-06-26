data node{
     int key;
     node down;
     node fwd;
}


pred skl0<p> ==
    self = null or
    self = p    or
    self::node<val,down,fwd> * down::skl0<fwd> * fwd::skl0<p>
    & self!=p
    inv true.

pred skl1<p,n> ==
    self = null & n=0 or
    self = p    & n=0 or
    self::node<val,down,fwd> * down::skl1<fwd,m1> * fwd::skl1<p,m2>
    & self!=p & n = m1 + m2 + 1
    inv n>=0.

pred skl2<p,n,mn,mx> ==
    self = null & n=0  & mn<=mx or
    self = p    & n=0  & mn<=mx or
    self::node<mn,down,fwd> *
    down::skl2<fwd,n1,mn1,mx1> *
    fwd::skl2<p,n2,mn2,mx>
    & self!=p & n = n1 + n2 + 1
    & mx1<=mn2 & mn<=mn1
    inv n>=0 & mn<=mx.

int length(node x, node y)
     requires x::skl0<y>@L
     ensures  true;
     requires x::skl1<y,n>@L
     ensures  res=n;
     requires x::skl2<y,n,mn,mx>@L
     ensures  res=n;
{
 if (x==null || x==y){ return 0; }
 else {
    int m2 = length(x.fwd, y);
    int m1 = length(x.down, x.fwd);
    return m1 + m2 + 1;
 }
}

node append(node x, node y, node a)
   requires  x::skl0<y> * a::node<_,null,y>@L & a!=y
   ensures   res::skl0<a>;
   // without x=res in post we can't prove the last case (down ptr loses info)
   /*
      below spec is not correct since it materializes a from the down ptr
      requires  x::skl0<y> * a::node<_,null,y> & a!=y
      ensures   res::skl0<y>;
   */
   /*
   requires  x::skl1<y,n> * a::node<_,null,y>@L & a!=y
   ensures   res::skl1<a,n>;
   */
{
   if(x == null) return null;
   else if (x == y ) { x = a; return a;}
   else {
      if(x.fwd == y) {
        if(x.down != null){ x.down = append(x.down,y,a); }
        x.fwd = a;
      } else {
        dprint;
        x.fwd = append(x.fwd,y,a);
        dprint;
      }
      return x;
   }
}


/*

 x::skl0<y> * a::node<_,null,y>@L & a!=y & x!=null & x!=y & x.fwd!=y
 |-
 x.fwd::skl0<y> * a::node<_,null,y>@L & a!=y

---------- (UNFOLD)

 x::node<_,down,fwd> * down::skl0<fwd> *
 fwd::skl0<y> * a::node<_,null,y>@L & a!=y & x!=null & x!=y & x.fwd!=y
 |-
 x.fwd::skl0<y> * a::node<_,null,y>@L & a!=y

 x::node<_,down,fwd> * down::skl0<fwd> *
 fwd::skl0<a> * a::node<_,null,y>@L & a!=y & x!=null & x!=y & x.fwd!=y
  |-
  x::skl0<a>
*/

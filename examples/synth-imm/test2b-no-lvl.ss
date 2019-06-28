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
    down::skl2<fwd,m1,mn1,mx1> *
    fwd::skl2<p,m2,mn2,mx>
    & self!=p & n = m1 + m2 + 1
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

void foo(node x, node y)
     requires x::skl0<y>@L
     ensures  true;

node append_helper(node x, node y, node a)
   /*
   requires  x::skl0<y> * a::skl0<z>@L
   ensures   res::skl0<a>;
   requires  x::skl1<y,n> * a::skl1<z,_>@L
   ensures   res::skl1<a,n>;
   */
   requires  x::skl2<y,n,mn1,mx1> * a::skl2<z,_,mn2,mx2>@L & mx1<=mn2
   ensures   res::skl2<a,n,mn1,mx1>;

node append1(node x, node y, node a)
   // requires  x::skl0<y> * a::node<_,null,y>@L & a!=y
   // y and z may be aliased
   requires  x::skl0<y> * a::skl0<z>@L & x!=a & a!=y & a!=z & a!=null
   ensures   res::skl0<a>; // & res=x;
   /*
   requires  x::skl1<y,n> * a::skl1<z,_>@L  & x!=a & a!=y & a!=z & a!=null
   ensures   res::skl1<a,n>;
   */
   /*
      below spec is not correct since it materializes a from the down ptr
      requires  x::skl0<y> * a::node<_,null,y>@L & a!=y
      ensures   res::skl0<y>;
   */
{
   node temp;
   if(x == null || x == y) { x = a ; return x; }
   else {
      if(x.fwd == y || x.fwd == null) {
        temp = x.fwd;
        x.fwd = a;
        if (x.down != null )
            x.down = append_helper(x.down,temp,x.fwd);
      } else {
        temp = x.fwd;
        x.fwd  = append1(x.fwd,y,a);
        if (x.down != null )
            x.down = append_helper(x.down,temp,x.fwd);
      }
      return x;
   }
}

node append2(node x, node y, node a)
   // requires  x::skl0<y> * a::node<_,null,y>@L & a!=y
   // y and z may be aliased
   requires  x::skl0<y> * a::skl0<z>@L & x!=a & a!=y & a!=z & a!=null
   ensures   res::skl0<a>; // & res=x;
   requires  x::skl1<y,n> * a::skl1<z,_>@L  & x!=a & a!=y & a!=z & a!=null
   ensures   res::skl1<a,n>;
   /*
      below spec is not correct since it materializes a from the down ptr
      requires  x::skl0<y> * a::node<_,null,y>@L & a!=y
      ensures   res::skl0<y>;
   */
{
   node temp;
   if(x == null || x == y) { x = a ; return x; }
   else {
      temp = x.fwd;
      if(x.fwd == y || x.fwd == null) x.fwd = a;
      else x.fwd  = append2(x.fwd,y,a);
      if (x.down != null )
            x.down = append_helper(x.down,temp,x.fwd);
      return x;
   }
}

node append3(node x, node y, node a)
   // requires  x::skl0<y> * a::node<_,null,y>@L & a!=y
   // y and z may be aliased
   /*
   requires  x::skl0<y> * a::skl0<z>@L & a!=z & a!=null
   ensures   res::skl0<a>;
   requires  x::skl1<y,n> * a::skl1<z,_>@L & a!=z & a!=null
   ensures   res::skl1<a,n>;
   */
   requires  x::skl2<y,n,mn1,mx1> * a::skl2<z,m,mn2,mx2>@L & a!=z & a!=null & mx1<=mn2 & x!=null & x!=y & y!=null
   ensures   res::skl2<a,n,mn1,mx1>;
{
   node temp;
   if(x == null || x == y) { x = a ; return x; }
   else {
      temp = x.fwd;
      if(x.fwd == y || x.fwd == null) x.fwd = a;
      else x.fwd  = append3(x.fwd,y,a);
      if (x.down != null ){
            //assume x.fwd!=null;
            x.down = append_helper(x.down,temp,x.fwd);
      }
      dprint;
      return x;
   }
}

/*
pred lseg<p,S> == self=p & S={}
               or self::node<val,null,q> * q::lseg<p,S1> & S=union({val},S1)
               & forall(y: (y notin S1 | val <= y));


node search(node x, node y, int k)
     requires x::lseg<y,S> & k in S
     ensures  res=null or res::node<k,_,_>;
              // x::lseg<z,S1>*z::node<k,null,p>*p::lseg<y,S2> & res=z;
{
 if(x==y) return null;
 else if (x.key == k) return x;
 else return search(x.fwd,y,k);
}

*/

pred lseg0<p,mn,mx> == self=p & mn<=mx
               or self::node<mn,null,q> * q::lseg0<p,mn1,mx> & mn<=mn1 & mn1<=mx
               inv mn<=mx;


node search0(node x, node y, int k)
     requires x::lseg0<y,mn,mx> & mn<=k<=mx
     ensures  res=null or res::node<kk,_,_> & mn<=kk<=k;
              // x::lseg<z,S1>*z::node<k,null,p>*p::lseg<y,S2> & res=z;
{
 if(x==y) return null;
 else if (x.key == k) return null;
 else return search0(x.fwd,y,k);
}

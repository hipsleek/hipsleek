data node{
     int key;
     node down;
     node fwd;
}

pred skl0<p> ==
    self = p    or
    self::node<val,down,fwd> * down::skl00<fwd> * fwd::skl0<p>
    & self!=p
    inv true.

pred skl00<p> ==
    self = null or
    self::skl0<p> & self!=null & self!=p
    inv true.


pred skl1<p,n> ==
    self = p    & n=0 or
    self::node<val,down,fwd> * down::skl11<fwd,m1> * fwd::skl1<p,m2>
    & self!=p & n = m1 + m2 + 1
    inv n>=0.

pred skl11<p,n> ==
    self = null & n=0 or
    self::skl1<p,n> & self!=null & self!=p
    inv n>=0.

pred skl2<p,n,mn,mx> ==
    self = p    & n=0  & mn<=mx or
    self::node<mn,down,fwd> *
    down::skl22<fwd,n1,mn1,mx1> *
    fwd::skl2<p,n2,mn2,mx>
    & self!=p & n = n1 + n2 + 1
    & mx1<=mn2 & mn<=mn1
    inv n>=0 & mn<=mx.

pred skl22<p,n,mn,mx> ==
    self = null & n=0  & mn<=mx or
    self::skl2<p,n,mn,mx>
    & self!=p & self!=null
    inv n>=0 & mn<=mx.


int length(node x, node y)
/*   requires x::skl0<y>@L
     ensures  true;
     requires x::skl1<y,n>@L
     ensures  res=n;
*/
     requires x::skl2<y,n,mn,mx>@L
     ensures  res=n;
{
 if (x==null || x==y){ return 0; }
 else {
    int m2 = length(x.fwd, y);
    int m1;
    if (x.down == null) m1 = 0;
    else m1 = length(x.down, x.fwd);
    return m1 + m2 + 1;
 }
}

node append(node x, node y, node a)
   // requires  x::skl0<y> * a::node<_,null,y>@L & a!=y
   requires  x::skl0<y> * a::skl0<z>@L // y and z may be aliased
   ensures   res::skl0<a>; // & res=x;
   /*
   requires  x::skl1<y,n> * a::skl1<z,_>@L // & a!=y
   ensures   res::skl1<a,m>;
   */
{
   node temp;
   // if(x == a) return x;
   // else if(x == null) { x = a; return x;} //return null;
   // else if(x == y)    { x = a; return x;}
   if(x == null || x == y) { x = a ; return x; }
   else {
      if(x.fwd == y) {
        // assume x!= a;
        //     x::node<_,down,y> * down::skl0<y>
        // * y::skl0<y> * a::skl0<z> &  x!=y
        dprint;
        temp = x.fwd;
        //     x::node<_,down,y> * down::skl0<y>
        // * y::skl<y> * a::skl0<z> & x!=y & y=temp
        dprint;
        x.fwd = a;
        //     x::node<_,down,a> * down::skl0<y>
        // * y::skl<y> * a::skl0<z> & x!=y & y=temp
        dprint;
        if(x.down != null)
                //     x::node<_,down,a> * down::skl0<y>
                // * y::skl<y> * a::skl0<z> & x!=y & y=temp & down!=null
               { x.down = append(x.down,temp,x.fwd); }
      } else {
        // assume x!= a;
        temp = x.fwd;
        x.fwd  = append(x.fwd,y,a);
        if (x.down != null )
            x.down = append(x.down,temp,x.fwd);
      }
      return x;
   }
}

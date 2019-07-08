data node{
     int key;
     node down;
     node fwd;
}


pred skl0<p> ==
    self = p    or
    self::node<_,p,p> & self!=p or //can comment out
    self::node<val,down,fwd> * down::skl0<fwd> * fwd::skl0<p>
    & self!=p & self!=fwd
    inv true.

pred skl1<p,n> ==
    self=p & n=0 or
    self::node<_,p,p> & self!=p & n = 1 or //can comment out
    self::node<val,down,fwd> * down::skl1<fwd,m1> * fwd::skl1<p,m2>
    & self!=p & self!=fwd  & self!=down
    & n = m1 + m2 + 1 & n > 1
    inv n>=0.

pred skl2<p,n,mn,mx> ==
    self = p    & n=0
    or
    /* empty down & fwd */
    self::node<mn,p,p> & self!=p & n = 1 & mn=mx
    or
    /* empty down */
    self::node<mn,fwd,fwd> *
    fwd::skl2<p,m2,mn2,mx>
    & self!=p & self!=fwd
    & n = m2 + 1 & n > 1
    & mn<=mn2 & mn2<=mx
    /* empty fwd */
    or
    self::node<mn,down,p> *
    down::skl2<p,m1,mn1,mx> *
    & self!=p & self!=down
    & n = m1 + 1 & n > 1
    & mn<=mn1 & mn1<=mx
    /* non-empty down & non-empty fwd*/
    or
    self::node<mn,down,fwd> *
    down::skl2<fwd,m1,mn1,mx1> *
    fwd::skl2<p,m2,mn2,mx>
    & self!=p
    & n = m1 + m2 + 1 & n > 1
    & mx1<=mn2 & mn<=mn1 & mn1<=mx1 & mn2<=mx
    inv n>=0.


int length(node x, node y)
     requires x::skl0<y>@L
     ensures  true;
     requires x::skl1<y,n>@L
     ensures  res=n;
     requires x::skl2<y,n,mn,mx>@L
     ensures  res=n;
{
 if (x==y){ return 0; }
 else {
    int m2 = length(x.fwd, y);
    int m1 = length(x.down, x.fwd);
    return m1 + m2 + 1;
 }
}


node append3(node x, node y, node a)
   // y and z may be aliased
  /*
  requires  x::skl0<y> * a::skl0<z>@L & a!=z
  case {
     x=y  -> ensures   res=a;
     x!=y -> ensures   res::skl0<a> & res!=a;
  }
  requires  x::skl1<y,n> * a::skl1<z,_>@L & a!=z
  case {
     x=y  -> ensures   res=a;
     x!=y -> ensures   res::skl1<a,n> & res!=a;
  }
  */
  requires  x::skl2<y,n,mn1,mx1> * a::skl2<z,_,mn2,mx2>@L & a!=z
  case {
     x=y  -> ensures  res=a;
     x!=y -> requires mx1<=mn2
             ensures  res::skl2<a,n,mn1,mx1> & res!=a;
  }
{
   node temp;
   if(x == y) x = a ;
   else {
      temp = x.fwd;
      //update fwd
      // x::skl2<y,n,mn1,mx1> * a::skl2<z,_,mn2,mx2>@L & a!=z & mx1<=mn2
      if(x.fwd == y) x.fwd  = a;
      else x.fwd  = append3(x.fwd,y,a);
      // x::node<mn1,down,fwd'> * down::skl<temp,mn1',mx1'>
      // * a::skl2<z,_,mn2,mx2>@L & a!=z & mx1<=mn2
      // fwd'::skl<a,mn2',mx1> & mx1'<=mn2' & mn1<=mn1'
      // or
      // fwd'=a
//      skl2<y,n,mn1,mx1>
      //update dwn
      if (x.down == temp) x.down = x.fwd;
      else x.down = append3(x.down,temp,x.fwd); // |-mx1' <= mn2'
                                                // | mx1' <= mn2
   }
   return x;
}


pred lseg<p,n> == self=p & n=0 or
                  self::node<_,null,q> * q::lseg<p,n-1> & self!=p
                  inv n>=0.

/*
pred lsort<p,n,B> == self=p & n=0 & B={} or
                  self::node<v,null,q> * q::lsort<p,n-1,B1>
                  & B=union(B1,{v})
                  & forall (w: w notin B1 | v<=w)
                  & self!=p
                  inv n>=0.
*/

pred lsort2<p,n,mn,mx> ==
                  self=p & n=0 or
                  self::node<mn,null,p>  & mn=mx & n=1 & self!=p or
                  self::node<mn,null,q> * q::lsort2<p,n-1,mn1,mx> & n>1 & mn<=mn1 & self!=p & self!=q
                  inv n>=0.

int length_ls(node x, node y)
     requires x::lseg<y,n>@L
     ensures  res=n;
{
 if (x==y) return 0;
 else return 1+length_ls(x.fwd,y);
}

node append_ls(node x, node y, node a)
     requires x::lseg<y,n> * a::lseg<q,m>@L & a!=q
     ensures  res::lseg<a,n>;
/*     requires x::lsort2<y,n,mn1,mx1> * a::lsort2<q,m,mn2,mx2>@L & a!=q & mx1<=mn2
       ensures  res::lsort2<a,n,mn1,mx1>;
*/
     requires x::lsort2<y,n,mn1,mx1> * a::lsort2<q,m,mn2,mx2>@L & a!=q
     case{
       n=0  ->  ensures res=a;
       n!=0 ->  requires mx1<=mn2  ensures res::lsort2<a,n,mn1,mx1>;
     }
{
 if(x==y) x=a;
 else
   if(x.fwd == y) x.fwd = a;
   else x.fwd = append_ls(x.fwd,y,a);
 return x;
}

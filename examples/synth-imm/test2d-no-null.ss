data node{
     int key;
     node down;
     node fwd;
}


pred skl0<p> ==
    self = p    or
    self::node<val,down,fwd> * down::skl0<fwd> * fwd::skl0<p>
    & self!=p
    inv true.

pred skl1<p,n> ==
    self = p    & n=0 or
    self::node<val,down,fwd> * down::skl1<fwd,m1> * fwd::skl1<p,m2>
    & self!=p
    & n = m1 + m2 + 1
    inv n>=0.

pred skl2<p,n,mn,mx> ==
    self = p    & n=0  & mn<=mx or
    self::node<mn,down,fwd> *
    down::skl2<fwd,m1,mn1,mx1> *
    fwd::skl2<p,m2,mn2,mx>
    & self!=p
    & n = m1 + m2 + 1
    & mx1<=mn2 & mn<=mn1
    inv n>=0 & mn<=mx.

/*
pred skl2<p,n,mn,mx> ==
    self = p    & n=0  & mn<=mx
    or
    self::node<mn,p,p> & n=1 & mn=mx & self!=p
    or
    self::node<mn,down,fwd> *
    down::skl2<fwd,m1,mn1,mx1> *
    fwd::skl2<p,m2,mn2,mx>
    & self!=p & n = m1 + m2 + 1
    & mx1<=mn2 & mn<=mn1
    inv n>=0 & mn<=mx.
*/

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
   /*
   requires  x::skl0<y> * a::skl0<z>@L & a!=z //& a!=null
   ensures   x=y & res=a or res::skl0<a> & x!=y & res!=a;
   requires  x::skl1<y,n> * a::skl1<z,_>@L & a!=z
   ensures   res::skl1<a,n>;
   */
   // y and z may be aliased
  /* case {
     x=y  -> requires  a::skl0<z>@L & a!=z
             ensures   res=a;
     x!=y -> requires  x::skl0<y> * a::skl0<z>@L & a!=z
             ensures   res::skl0<a> & x!=y & res!=a;
   }
   case {
     x=y  -> requires  a::skl1<z,_>@L & a!=z
             ensures   res=a;
     x!=y -> requires  x::skl1<y,n> * a::skl1<z,_>@L & a!=z
             ensures   res::skl1<a,n> & res!=a;
   }*/
   case {
     x=y  -> requires  a::skl2<z,_,mn2,mx2>@L & a!=z
             ensures   res=a;
     x!=y -> requires  x::skl2<y,n,mn1,mx1> * a::skl2<z,_,mn2,mx2>@L & a!=z & mx1<=mn2
             ensures   res::skl2<a,n,mn1,mx1> & res!=a;
   }
{
   node temp;
   if(x == y) { x = a ; return x; }
   else {
      temp = x.fwd;
      if(x.fwd == y){
           x.fwd = a;
           x.down = append3(x.down,temp,x.fwd);
      }else{
           x.fwd = append3(x.fwd,y,a);
           x.down = append3(x.down,temp,x.fwd);
      }
      return x;
   }
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
                  self::node<mn,null,q> * q::lsort2<p,n-1,mn1,mx> & n>1 & mn<=mn1 & mn1<=mx & self!=p & self!=q
                  inv n>=0.

pred lsort3<p,n,mn,mx> ==
                  self::node<mn,null,p> & mn=mx & n=1 & self!=p or
                  self::node<mn,null,q> * q::lsort3<p,n-1,mn1,mx>
                  & mn<=mn1 & self!=q & self!=p
                  inv self!=p & n>=1.


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
     /*
     requires x::lsort<y,n,B1> * a::lsort<q,m,B2>@L & a!=q & forall (b1,b2: b1 notin B1 | b2 notin B2 | b1<=b2)
     ensures  res::lsort<a,n,B1>;
     */
{
 if(x==y) x=a;
 else
   if(x.fwd == y) x.fwd = a;
   else x.fwd = append_ls(x.fwd,y,a);
 return x;
}

node append_ls3(node x, node y, node a)
     requires x::lsort3<y,n,mn1,mx1> * a::lsort3<q,m,mn2,mx2>@L & mx1<=mn2
     ensures  res::lsort3<a,n,mn1,mx1>;
     /*
     requires x::lsort<y,n,B1> * a::lsort<q,m,B2>@L & a!=q & forall (b1,b2: b1 notin B1 | b2 notin B2 | b1<=b2)
     ensures  res::lsort<a,n,B1>;
     */
{
  if(x.fwd == y) x.fwd = a;
  else x.fwd = append_ls3(x.fwd,y,a);
  return x;
}

data node{
     int key;
     node next;
     node sk;
}

pred lseg0<p> == self=p or
                 self::node<_,q,null> * q::lseg0<p> & self!=p. //& self!=q.

pred lseg1<p,n> == self=p & n=0 or
                  self::node<_,q,null> * q::lseg1<p,n-1> & self!=p //& self!=q
                  inv n>=0.

pred lseg2<p,n,mn,mx> == self=p & n=0 & mx<=mn or
                  self::node<mn,p,null> & mn=mx & n=1 & self!=p or
                  self::node<mn,q,null> * q::lseg2<p,n-1,mn1,mx> & self!=p //& self!=q
                  & mn<=mn1  & n>1 & mn1<=mx
                  inv n=0 & self=p | n>0 & self!=p.

pred skl0<p> ==
    self = p    or
    self::node<val,next,sk> * next::lseg0<sk> * sk::skl0<p>
    & self!=p
    inv true.

pred skl1<p,n> ==
    self=p & n=0
    or
    self::node<val,next,sk> * next::lseg1<sk,m1> * sk::skl1<p,m2>
    & self!=p & n = m1 + m2 + 1 & n >=1
    inv n>=0.

pred skl2<p,n,mn,mx> ==
    self = p    & n=0 & mx<=mn
    or
    /* empty down & fwd */
    self::node<mn,p,p> & self!=p & n = 1 & mn=mx
    or
    /* empty down */
    self::node<mn,sk,sk> *
    sk::skl2<p,m2,mn2,mx>
    & self!=p & sk!=p
    & n = m2 + 1
    & mn<=mn2 & mn2<=mx
    /* empty fwd */
    or
    self::node<mn,next,p> *
    next::lseg2<p,m1,mn1,mx>
    & self!=p & next!=p
    & n = m1 + 1
    & mn<=mn1 & mn1<=mx
    /* non-empty down & non-empty fwd*/
    or
    self::node<mn,next,sk> *
    next::lseg2<sk,m1,mn1,mx1> *
    sk::skl2<p,m2,mn2,mx>
    & self!=p & next!=sk & sk!=p
    & n = m1 + m2 + 1
    & mx1<=mn2 & mn<=mn1 & mn1<=mx1 & mn2<=mx
    inv n>=0.

int length_ls(node x, node y)
     requires x::lseg0<y>@L
     ensures  true;
     requires x::lseg1<y,n>@L
     ensures  res=n;
     requires x::lseg2<y,n,_,_>@L
     ensures  res=n;
{
   if(x == y) return 0 ;
   else  return 1 + length_ls(x.next,y);
}

node append_ls(node x, node y, node a)
     requires x::lseg0<y> * a::node<_,_,_>@L
     ensures res::lseg0<a>;
     requires x::lseg1<y,n> * a::node<_,_,_>@L
     ensures res::lseg1<a,n>;
     requires x::lseg2<y,n,mn1,mx1> * a::node<mn2,_,_>@L
     case{
       n=0  ->  ensures res=a;
       n!=0 ->  requires mx1<=mn2  ensures res::lseg2<a,n,mn1,mx1> & res!=a;
     }
{
 if(x==y) x=a;
 else
   if(x.next == y) x.next = a;
   else x.next = append_ls(x.next,y,a);
 return x;
}


node search_ls(node x, node y, int val)
     requires x::lseg2<y,n,mn,mx>
     case{
       n=0 -> ensures x::lseg2<y,n,mn,mx> & res = null;
       n=1 -> case{
           val<=mn -> ensures x::lseg2<y,n,mn,mx> & res = null;// & mn=mx;
           val>mn  -> ensures x::lseg2<y,n,mn,mx> & res = x   ;// & mn=mx;
       }
       n>1 -> case{
           val<=mn -> ensures x::lseg2<y,n,mn,mx> & res = null ;
           val>mn  -> ensures x::lseg2<res,n1,mn,mx1> * res::node<mn1,q,_> * q::lseg2<y,n2,mn2,mx> & mx1<=mn1
           & (n2=0 & mn1=mx & mn2=mn1 | n2>0 & mn1<=mn2) & n=n1+1+n2 & x!=res;

       }
       n<0 -> ensures false;
     }
{
 if(x == y)  return null;
 else
      if(val<=x.key)  return null;
      else if(x.next == y) return x;
      else if(x.next.key<val) return search_ls(x.next,y,val);
      else
      // x.key<val & val<=x.next.key
      return x;
}

int length(node x, node y)
     requires x::skl0<y>@L
     ensures  true;
     requires x::skl1<y,n>@L
     ensures  res=n;
     requires x::skl2<y,n,mn,mx>@L
     ensures  res=n;
{
   if(x == y) return 0 ;
   else {
      int m1,m2;
      m1 = length_ls(x.next, x.sk);
      if (x.sk == y) m2 = 0;
      else m2 = length(x.sk, y);
      return m1 + m2 + 1;
   }
}


//SUCCESS (684.250724 second(s))
node append(node x, node y, node a)
   // y and z may be aliased
 /* requires  x::skl0<y> * a::skl0<z>@L & a!=z
  ensures   res::skl0<a>;
  requires  x::skl1<y,n> * a::skl1<z,_>@L & a!=z
  ensures   res::skl1<a,n>;// & res!=a; */
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
      temp = x.sk;
      //update fwd
      if(x.sk == y) x.sk  = a;
      else x.sk  = append(x.sk,y,a);
      //update dwn
      if (x.next == temp) x.next = x.sk;
      else x.next = append_ls(x.next,temp,x.sk); //dprint;}
   }
   return x;
}


// node search(node x, node y, int val)
//   // requires  x::skl2<y,n,mn,mx>
//   // case {
//   //    x=y  -> ensures  x::skl2<y,n,mn1,mx1> & res=null;
//   //    x!=y ->
//   //         case {
//   //           val<mn   ->  ensurs res = null;
//   //           val>=mn  ->  ensures
//   //           x::skl2<res,n1,mn1,mx1>
//   //           * res::node<val0,dn,fw>
//   //           * dn::skl2<fw,n2,mn2,mx2>
//   //           * fw::skl2<y,n3,mn3,mx>
//   //         }
//   // }
// {
//  if(x==y) return null;
//  else {
//     if (x.key == val) return x;
//     else
//       if (x.fwd == y)
//          { if (x.down == x.fwd) return x;
//            else return search(x.down,y,val);
//          }
//      else {
//          node temp = x.fwd;
//          if(temp.val <= val) return search(x.fwd,y,val);
//          else
//           { if (x.down == x.fwd) return x
//             else return search(x.down,y,val);
//           }
//      }
//  }
// }

/*
pred lsort<p,n,B> == self=p & n=0 & B={} or
                  self::node<v,null,q> * q::lsort<p,n-1,B1>
                  & B=union(B1,{v})
                  & forall (w: w notin B1 | v<=w)
                  & self!=p
                  inv n>=0.
*/

// pred lsort2<p,n,mn,mx> ==
//                   self=p & n=0 or
//                   self::node<mn,null,p>  & mn=mx & n=1 & self!=p or
//                   self::node<mn,null,q> * q::lsort2<p,n-1,mn1,mx> & n>1 & mn<=mn1 & self!=p & self!=q
//                   inv n>=0.

// int length_ls(node x, node y)
//      requires x::lseg<y,n>@L
//      ensures  res=n;
// {
//  if (x==y) return 0;
//  else return 1+length_ls(x.fwd,y);
// }

// node append_ls(node x, node y, node a)
//      requires x::lseg<y,n> * a::lseg<q,m>@L & a!=q
//      ensures  res::lseg<a,n>;
// /*     requires x::lsort2<y,n,mn1,mx1> * a::lsort2<q,m,mn2,mx2>@L & a!=q & mx1<=mn2
//        ensures  res::lsort2<a,n,mn1,mx1>;
// */
//      requires x::lsort2<y,n,mn1,mx1> * a::lsort2<q,m,mn2,mx2>@L & a!=q
//      case{
//        n=0  ->  ensures res=a;
//        n!=0 ->  requires mx1<=mn2  ensures res::lsort2<a,n,mn1,mx1>;
//      }
// {
//  if(x==y) x=a;
//  else
//    if(x.fwd == y) x.fwd = a;
//    else x.fwd = append_ls(x.fwd,y,a);
//  return x;
// }

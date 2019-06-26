data lnode{
     lnode next;
}

data node{
     int key;
     int lvl;
     node down;
     node fwd;
}


pred skl0<lvl,p> ==
    /* only the down ptr can be null */
    self = null & lvl >= 0 or  //not necessarily true
    /* empty skl cannot have a 0 lvl */
    self = p    & lvl > 0 or
    self::node<val,lvl,down,fwd> * down::skl0<lvl-1,fwd> * fwd::skl0<lvl,p>
    & self!=p
    inv lvl>=0.


pred skl1<lvl,p,n> ==
    self = null & lvl >= 0 & n=0 or
    self = p    & lvl > 0 & n=0 or
    self::node<val,lvl,down,fwd> * down::skl1<lvl-1,fwd,m1> * fwd::skl1<lvl,p,m2>
    & self!=p & n = m1 + m2 + 1
    inv lvl>=0 & n>=0.

pred skl2<lvl,p,n,mn,mx> ==
    self = null & lvl >= 0 & n=0  & mn<=mx or
    self = p    & lvl > 0 & n=0  & mn<=mx or
    self::node<mn,lvl,down,fwd> *
    down::skl2<lvl-1,fwd,n1,mn1,mx1> *
    fwd::skl2<lvl,p,n2,mn2,mx>
    & self!=p & n = n1 + n2 + 1
    & mx1<=mn2 & mn<=mn1
    inv lvl>=0 & n>=0 & mn<=mx.


int length(node x, node y, int lvl)
     requires x::skl0<lvl,y>@L
     ensures  true;
     requires x::skl1<lvl,y,n>@L
     ensures  res=n;
     requires x::skl2<lvl,y,n,mn,mx>@L
     ensures  res=n;
{
 if (x==null || x==y){ return 0; }
 else {
    int m2 = length(x.fwd, y, lvl);
    int m1 = length(x.down, x.fwd, lvl-1);
    return m1 + m2 + 1;
 }
}


void append(node x, node y, node a, int lvl)
   requires  x::skl0<lvl,y> * a::node<_,_,null,y>@L & a!=y
   ensures   x::skl0<lvl,a>;
{
   if(x == null || x==y) {x = a;}
   else {
     // x!=null & x!=y
      if(x.fwd == y) {
        x.fwd = a;
        if(x.down != null){ append(x.down,y,a,lvl-1); }
      } else append(x.fwd,y,a,lvl);
   }
   dprint;
}

// lemma self::skl0<lvl,pp> * pp::node<_,_,null,fw>  ->
//       self::skl0<lvl,fw>;

node append_res(node x, node y, node a, int lvl)
   // requires  x::skl0<lvl,y> * a::node<_,_,null,y>@L & a!=y
   // ensures   res::skl0<lvl,a>;
   requires  x::skl0<lvl,y> * a::node<_,_,null,y> & a!=y
   ensures   res::skl0<lvl,y>;
   // requires  x::skl1<lvl,y,n> * a::node<_,_,null,y>@L & a!=y
   // ensures   res::skl1<lvl,a,n>;
{
   if(x == null || lvl==0) return null;
   else if (x==y && lvl>0) {return a;}
   else {
      if(x.fwd == y) {
        x.fwd = a;
        if(x.down != null){ x.down = append_res(x.down,y,a,lvl-1); }
        return x;
      } else {x.fwd = append_res(x.fwd,y,a,lvl); return x;}
   }
   dprint;
}


void call_append(ref node x, node y, int lvl, int val)
     requires  x::skl0<lvl,y> & x!=null & x!=y
     ensures  x'::skl0<lvl,y> ;
{
  if(x.fwd == y) {
     node a = new node(val, lvl, null, y);
     append(x,y,a,lvl);
  } else {
     call_append(x.fwd,y,lvl,val);
  }
}


pred ls<p> == self=p or self::lnode<q> * q::ls<p> & self!=p;

void append_lst(lnode x, lnode p, lnode a)
     requires x::ls<p> * a::lnode<p> & x!=p & a!=p
     ensures  x::ls<p>;
{
  if(x.next == p) {x.next = a;}
  else append_lst(x.next,p,a);
}

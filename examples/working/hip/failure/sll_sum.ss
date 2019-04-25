data node {
  int val;
  node next;
}

lsSum<y,n,s> == self=y & n=0 & s=0
  or self::node<a, r> * r::lsSum<y,n2,s2> & n=1+n2 & s=s2+a
  inv n>=0;

// int length(node x)
//   requires x::lsSum<null,n,s>
//   ensures x::lsSum<null,n,s> & res = n;
// {
//   if (x == null) return 0;
//   else {
//     int k;
//     k = 1 + length(x.next);
//     return k;
//   }
// }

// int sum(node x)
//   requires x::lsSum<null,n,s>
//   ensures x::lsSum<null,n,s> & res = s;
// {
//   if (x == null) return 0;
//   else {
//     int k;
//     k = x.val + sum(x.next);
//     return k;
//   }
// }

// node insert_first(node x , int a)
//   requires x::lsSum<null,n,s>
//   ensures res::lsSum<null,n+1,s+a>;
// {
//   node u = new node(a, null);
//   u.next = x;
//   return u;
// }

// node insert_first2(node x , int a)
//   requires x::lsSum<null,n,s>
//   ensures res::node<a,x> * x::lsSum<null,n,s>;
// {
//   node u = new node(a, null);
//   u.next = x;
//   return u;
// }

// node insert_last(node x , int a)
//   requires x=null ensures res::lsSum<null,1,a>;
//   requires x::lsSum<null,n,s> & x!=null ensures x::lsSum<null,n+1,s+a> & res=x;
// {
//   if (x == null) {
//     node u = new node(a, null);
//     return u;
//   }
//   else if (x.next == null) {
//     node u = new node(a, null);
//     x.next = u;
//     return x;
//   }
//   else {
//     insert_last(x.next, a);
//     return x;
//   }
// }

// node insert_last2(node x , int a)
//   requires x=null ensures res::node<a,null>;
//   requires x::lsSum<null,n,s> & n>0
//     ensures x::lsSum<y,n,s> * y::node<a,null> & res=x;
// {
//   if (x == null) {
//     node u = new node(a, null);
//     return u;
//   }
//   else if (x.next == null) {
//     node u = new node(a, null);
//     x.next = u;
//     return x;
//   }
//   else {
//     insert_last2(x.next, a);
//     return x;
//   }
// }

// node concat(node x, node y)
//   requires y::lsSum<null,m,s2> & x=null
//     ensures res::lsSum<null,m,s2> & res=y;
//   requires x::lsSum<null,n,s1> * y::lsSum<null,m,s2> & x!=null
//     ensures res::lsSum<null,n+m,s1+s2> & res=x;
// {
//   if (x == null)
//     return y;
//   else if (x.next == null) {
//     x.next = y;
//     return x;
//   }
//   else {
//     concat(x.next, y);
//     return x;
//   }
// }

// node reverse(node x)
//   requires x=null ensures res=null;
//   requires x::lsSum<null,n,s> & x!=null
//     ensures res::lsSum<null,n,s> & res!=null;
// {
//   if (x == null)
//     return x;
//   else if (x.next == null)
//     return x;
//   else {
//     node u = x.next;
//     x.next = null;
//     node y = reverse(u);
//     node z = concat(y, x);
//     return z;
//   }
// }

// void main () {
//   node x = new node(10, null);
//   node y = new node(11, null);
//   node z = new node(12, null);
//   x.next = y;
//   y.next = z;
//   z.next = null;
// }

node main3 (node x, node y)
  requires x::lsSum<y,n,10> * y::node<1,z> & n>2
  ensures res::lsSum<z,n+1,s> & x=res;
{
  return x;
}

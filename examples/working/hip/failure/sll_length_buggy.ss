data node {
  int val;
  node next;
}

ls<y,n> == self=y & n=0
  or self::node<_, r> * r::ls<y,n2> & n=1+n2;




// node reverse(node x)
//   requires x=null ensures res=null;
//   requires x::ls<null,n> & x!=null ensures res::ls<null,n> & res!=null;
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

//   // dprint;

//   // int n = length(x);
//   // dprint;
//   // assert (n' = 3);

//   // dprint;
//   // node t = delete_first(x);
//   // dprint;
//   // int m = length(t);
//   // dprint;
//   // assert (m' = 2);

//   // node u = delete_first(t);
//   // int l = length(u);
//   // assert (l' = 1);
// }

data node {
  int val;
  node next;
}

ll<n> == self=null & n=0
  or self::node<_,q> * q::ll<n-1>
  inv n>=0;

void insert2(node x, int a)
  infer [@pre_n,@post_n]
  requires x::ll<n>
  ensures x::ll<r>;
{
  if (x.next == null) {
    x.next = new node(a,null);
  } else {
    insert2(x.next,a);
  }
}

/*

# ll-insert2.ss

Why can't we get a more precise post-cond?
Why so many n!=0 for pre?
Why isn't pre inference printed before hand?

Post Inference result:
insert2$node~int
 requires x::ll<n> & n!=0 & n!=0 & n!=0 & n!=0 
     & n!=0 & n!=0 & n!=0 & n!=0 & n!=0 & n!=0 & n!=0 & n!=0 & MayLoop[]
 ensures x::ll<r_1193> & 0<=n & (((3<=n & 2<=r_1193) | (n=1 & r_1193=2)));
Stop Omega... 40 invocations 
0 false contexts at: ()

[RELDEFN pre_1210: ( n=n_1243+1 & 1<=n_1243 & pre_1210(r_1193,n,a')) -->  pre_1210(r_1242,n_1243,a'),
RELASS [pre_1210]: ( pre_1210(r_1193,n,a)) -->  n!=0,
RELDEFN post_1211: ( r_1193=2 & n=1 & pre_1210(r_1193,n,a)) -->  post_1211(r_1193,n,a),
RELDEFN post_1211: ( 0<=n_1243 & n=n_1243+1 & r_1268=r_1193-1 & 2<=r_1193 & 
pre_1210(r_1193,n,a) & post_1211(r_1268,n_1243,a)) -->  post_1211(r_1193,n,a)]
*************************************

*************************************
*******fixcalc of pure relation *******
*************************************
[( post_1211(r_1193,n,a), ((3<=n & 2<=r_1193) | (n=1 & r_1193=2)), true, true)]
*************************************

*/



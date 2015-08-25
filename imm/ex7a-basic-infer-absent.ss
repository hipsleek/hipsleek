data node {
 int val;
 node next;
}


relation R(ann x, ann y).

int join(node x, node y)
  infer [R]
  requires x::node<a1,_>@z1*y::node<a2,_>@z2 & R(z1,z2)
  ensures x::node<_,_>*y::node<_,_> & res=a1+a2;
{ 
  return x.val+y.val;
} 

/*
# ex7a.ss

  infer [R]
  requires x::node<a1,_>@z1*y::node<a2,_>@z2 & R(z1,z2)
  ensures x::node<_,_>*y::node<_,_> & res=a1+a2;

# latest ann_2

Expects z1=@L and z2=@L be inferred, but got nothing:

# ann_2 before merge with default:

[RELASS [R]: ( R(z1,z2)) -->  z1<:@L,
RELASS [R]: ( R(z1,z2)) -->  (z2<:@L | z1=@A),
RELASS [R]: ( R(z1,z2)) -->  ((z2=@M & z1=@M) | z1=@A)]

!!! top_down_fp:[( R(z1,z2,pz1,pz2), z2=@M & z1=@M)]


*/

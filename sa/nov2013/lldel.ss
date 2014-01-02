data node{
  int val;
  node next;
}


pred_extn size[R]<k> ==
   k=0 // base case
   or R::size<i> & k=1+i // recursive case
  inv k>=0;


ll<p> == self = p or self::node<_, q> * q::ll<p>;
ll1<p,n> == self = p & n=0 or self::node<_, q> * q::ll1<p,n-1>;
lls<n> == self = null & n=0 or self::node<_, q> * q::lls<n-1>;

HeapPred H1(node a).
  PostPred G1(node a).
  PostPred G2(node a).
  PostPred G3(int a).
  relation P(int a, int b).
  relation Q(int a, int b, int c).
int delete (node x, int n)
// infer [P,G]  requires x::lls<m> & P(m,n)  ensures  G(x);
  infer [H1,G3]  requires H1(x)  ensures  G3(res);
//  infer [P,Q]  requires x::ll<n>*y::ll<m> & P(m,n)  ensures res::ll<k>*x::ll<n>*y::ll<m> & Q(m,n,k);
// requires x::lls<n> & m=n  ensures x::lls<m>;
//  requires x::ll1<q,n>   ensures x::ll1<q,n>;
{
  if (x==null) return n;
  else return delete (x.next, n-1);
}


/*
 H1(x) ::= x::node<val,next>@M * H1(next),
 G1(x) ::=
 x::node<val,next>@M * G1(next)
 or H1(x)

===>
 H1(x,q ) ::= x=q & HP(q) \/ x::node<val,next>@M * H1(next),
 G1(x) ::=
 x::node<val,next>@M * G1(next)
 or x=q & HP(q)

 */

node create_list(int m)
  infer [G2]  requires true  ensures G2(res);
//  requires true ensures res::ll1<null,m>;
{
  if (m==0) return null;
  else {
    node tmp = create_list(m-1);
    return new node(0,tmp);
  }
}


void foo(int n)
requires true
  ensures true;
{
  node tmp = create_list (n);
  //dprint;
  int k = delete (tmp, n);
  assert k=n;
}

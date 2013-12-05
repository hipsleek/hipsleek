data node {
  int val;
  node next;
}


HeapPred G1(node a).
HeapPred G2(node a, node b).
HeapPred G3(node b,node c, node d).

HeapPred H1(node a).
HeapPred H2(node a,node b).
HeapPred HP1(node a, node b).
//HeapPred G1(node a, node b, node c).


ll<> == self=null
  or self::node<_,q>*q::ll<>
  inv true;

lseg<p> == self=p
  or self::node<_,q>*q::lseg<p>
  inv true;

l2<y> == self::node<a,null> & y=self
  or self::node<_,q>*q::l2<y> 
  inv y!=null;
/*
 GG2<x> == 
   self::node<val,next>@M * next::GG2<n>&x=null
 or emp&self=null & x=null
   inv true;
*/

//lemma_safe self::GG2<x> <-> self::ll<> & x=null;

void dispose(node@R x)
  requires x::node<_,_>
  ensures x'=null;//'

void delete(node@R x)

  infer[H1,G2]
  requires H1(x)
  ensures G2(x,x');//'

/*
  requires x::ll<>
  ensures x::ll<> & x'=null;//';
*/
{
  if (x == null)
    return;
  else {
    node n = x.next ;
    x=null;
    delete(n);
  }
}

/*
../hip ll-append5.ss --pred-en-equiv --pred-en-dangling --pred-en-useless-para --en-syn-mode 

[ H1(x) ::=x::ll<>@M,
 G2(x1,x) ::= 
 x1::node<val,next>@M * G2(next,n)&x=null
 or emp&x1=null & x=null
 ]

It seems that only the syntactic equiv mode is working.

Also, I wonder what command will split G2(x1,x)?
Adding: --pred-en-split results in incorrect splitting
with unknown predicate. This seems to be buggy!

!!!  pred_split (syn):G2([next_54_1022,n_1031]) :==  HP_1062(next_54_1022) * HP_1063(n_1031)
*************************************
*******relational definition ********
*************************************
[ H1(x) ::=x::ll<>@M,
 G2(x,x1) ::= HP_1062(next) * HP_1063(n)]
*************************************
*/

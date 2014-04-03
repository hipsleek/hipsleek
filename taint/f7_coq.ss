data Node {
  int val;
  Node next;
}


// Attempt to use Coq LinkedList library
same_ll_coq<o,L1,L2> ==
  self=null & o=null & L1=[||] & L2=[||]
  or
  self::Node<v,n1> * o::Node<v,n2> * n1::same_ll_coq<n2,La,Lb> & L1=v:::La & L2=v:::Lb & L1=L2
  inv true;

ll_coq<L> ==
  self=null & L=[||]
  or
  self::Node<v,q> * q::ll_coq<L1> & L=v:::L1
  inv true;

/*
// Non-Coq
same_ll<o, B1, B2> ==
  self=null & o=null & B1={} & B2={}
  or
  self::Node<v,n1> * o::Node<v,n2> * n1::same_ll<n2,Bn1,Bn2> & B1=union({v},Bn1) & B2=union({v},Bn2)
  inv true;

ll<B> ==
  self=null & B={}
  or
  self::Node<v,n> * n::ll<B1> & B=union({v},B1)
  inv true;
*/

// LEMMAS
lemma_safe self::same_ll_coq<o,L,L> <-> self::ll_coq<L> * o::ll_coq<L>;
//lemma_safe self::same_ll_coq<o,L,L> -> self::ll_coq<L> * o::ll_coq<L>;
//lemma_safe self::same_ll_coq<o,L,L> <- self::ll_coq<L> * o::ll_coq<L>;

// - This causes infinite loop
//lemma_safe self::same_ll_coq<o,L,L> <-> o::same_ll_coq<self,L,L>;

/*
lemma_unsafe self::same_ll<o, B, B> -> self::ll<B> * o::ll<B>;
lemma_unsafe self::same_ll<o, B, B> <- self::ll<B> * o::ll<B>;
*/

/* CANNOT DERIVE POST-CONDITION
   because h1 may not be the same as h2 */
void concat(Node l1, Node l2, Node h1, Node h2)
  requires l1::same_ll_coq<l2, L1, L1> * h1::ll_coq<_> * h2::ll_coq<_> & len(L1) > 0
  ensures l1::same_ll_coq<l2, L3, L3> & L3=app(L1,L2); // * l21::same_ll_coq<L22, L4, L4> & len(L3) > 0;
//requires l11::same_ll<l12, B1, B1> * l21::same_ll<l22, B2, B2> & B1!={}
//ensures  l11::same_ll<l12, _, _>; // * l21::same_ll<l22, _, _>;
{
  //assume l11::same_ll<l12> * l21::same_ll<l22>;
  //assume false;

  //must_assert l11::ll_coq<_> * l21::ll_coq<_>;
  //must_assert l11::ll<_>;
  //must_assert l21::ll<_>;
  //must_assert l12::ll<_>;
  //must_assert l22::ll<_>;

  append(l1, h1);
  dprint;

  append(l2, h2);
  dprint;

  //must_assert l11::same_ll<l12> * l21::same_ll<l22>;
}


void append(Node x, Node y)
  requires x::ll_coq<L1> * y::ll_coq<L2> & len(L1) > 0
  ensures x::ll_coq<L> & L=app(L1,L2);
//requires x::ll<B1> * y::ll<B2> & B1!={}
//ensures  x::ll<B> & B=union(B1,B2);
{
  if(x.next == null) {
    //assume false;
    x.next = y;
  } else {
    append(x.next, y);
  }
}

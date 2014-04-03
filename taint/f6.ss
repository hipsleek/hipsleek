data Node {
  int val;
  Node next;
}

/*
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
*/

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


/*
lemma_safe self::same_ll_coq<o,L,L> -> self::ll_coq<L> * o::ll_coq<L>;
lemma_unsafe self::same_ll_coq<o,L,L> <- self::ll_coq<L> * o::ll_coq<L>;
*/

// LEMMAS
lemma_unsafe self::same_ll<o, B, B> <-> self::ll<B> * o::ll<B>;
//lemma_safe self::same_ll<o, B, B> -> self::ll<B> * o::ll<B>; // cannot be proven by omega
//lemma_safe self::same_ll<o, B, B> <- self::ll<B> * o::ll<B>;

// - This causes infinite loop
//lemma_safe self::same_ll<o, B, B> <-> o::same_ll<self, B, B>;


void concat(Node l11, Node l12, Node l21, Node l22)
//requires l11::same_ll_coq<l12, L1, L1> * l21::same_ll_coq<l22, L2, L2> & len(L1) > 0
//ensures l11::same_ll_coq<l12, L3, L3> * l21::same_ll_coq<L22, L4, L4> & len(L3) > 0;
  requires l11::same_ll<l12, B1, B1> * l21::same_ll<l22, B2, B2> & B1!={}
ensures  l11::same_ll<l12, B3, B3> & B3=union(B1,B2); // * l21::same_ll<l22, _, _>;
{
  //assume l11::same_ll<l12> * l21::same_ll<l22>;
  //assume false;

  //must_assert l11::ll_coq<_> * l21::ll_coq<_>;
  //must_assert l11::ll<_>;
  //must_assert l21::ll<_>;
  //must_assert l12::ll<_>;
  //must_assert l22::ll<_>;

  append(l11, l21);
  dprint;

  append(l12, l22);
  dprint;

  //must_assert l11::same_ll<l12> * l21::same_ll<l22>;
}


void append(Node x, Node y)
//requires x::ll_coq<L1> * y::ll_coq<L2> & len(L1) > 0
//ensures x::ll_coq<L> & L=app(L1,L2);
  requires x::ll<B1> * y::ll<B2> & B1!={}
  ensures  x::ll<B> & B=union(B1,B2);
{
  if(x.next == null) {
    //assume false;
    x.next = y;
  } else {
    append(x.next, y);
  }
}

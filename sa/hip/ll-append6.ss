data node {
  int val;
  node next;
}


HeapPred H(node a).
//HeapPred H1(node a).
HeapPred G2(node a, node b).
HeapPred G1(node a).
  HeapPred G3(node b,node c, node d).

HeapPred H1(node a).
  HeapPred H2(node a, node b).
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

void append(node x, node y)


  infer[H1,G2]
  requires H1(x)*y::node<a,null>
  ensures G2(x,y);//*y::node<a,null>;
{
  if (x.next == null)
    x.next = y;
  else
    append(x.next, y);
}

/*
expecting:
 H1(x) = x::node<_,q>*q::ll<>
 G2(x,y) = x::node<_,q>*HP<q,y>*y::node<_,_>
 HP<q,y> = q=y
     \/ q::node<_,r>* HP<r,y>
 
[ HP_RELDEFN HP_625
HP_625(flted_34_624,y) ::=
 emp&flted_34_624=null
 or y::node<val_37_594,y> * y::node<a_623,flted_34_628> *
    HP_625(flted_34_628,y)&flted_34_624=null //WRONG from generalization
 ,
 HP_RELDEFN H1
H1(x) ::= x::node<val_37_630,next_37_631> * next_37_631::ll[LHSCase]&true,
 HP_RELDEFN G2
G2(x,y) ::= x::node<val_37_594,y> * y::node<a_623,flted_34_624> *
HP_625(flted_34_624,y)&true]

 */

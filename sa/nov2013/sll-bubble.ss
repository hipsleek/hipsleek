data node {
	int val; 
	node next;	
}

sll<n, sm, lg> ==
  self::node<sm, null> & sm=lg & n=1 
  or	self::node<sm, q> * q::sll<n-1, qs, lg> & q!=null & sm<=qs 
  inv n>=1 & sm<=lg;

/* view for a singly linked list */

ll<> == self = null
	or self::node<_, q> * q::ll<>
  inv true;

HeapPred H1(node a).
HeapPred G1(node a).

HeapPred H2(node a).
HeapPred G2(node a).

bool bubble(node xs)
  /* requires xs::node<_,p> * p::ll<> */
  /* ensures xs::node<_,p1> * p1::ll<>; */
/*
requires xs::ll<n> & n>0
ensures xs::sll<n, s, l> & !res
or  xs::ll<n> & res;
 */

  infer[H1,G1]
  requires H1(xs)
  ensures G1(xs) ;
{
  int aux, tmp1;
  bool tmp, flag; 

  if (xs.next == null) {
    return false;
  }
  else {
    tmp = bubble(xs.next);
    int xv = xs.val;
    int xnv = xs.next.val;
    if (xv <= xnv) 
      flag = false;
    else {
      xs.val = xnv;
      xs.next.val = xv; //ERROR: lhs and rhs do not match
      flag = true; 
    }
    //dprint;
    return (flag || tmp);
  }
}

/* void bsort(node xs) */
/*   /\* requires xs::node<_,p>*p::ll<> *\/ */
/*   /\* ensures xs::node<_,p1> * p1::ll<>; *\/ */
/*   infer[H2,G2] */
/*   requires H2(xs) */
/*   ensures G2(xs); */
/* { */
/*   bool b; */

/*   b = bubble(xs); */
/*   if (b) { */
/*     bsort(xs); */
/*   } */
/* } */

/*

[ // BIND
(0)H1(xs) --> xs::node<val,next>@M * HP_935(val@NI) * 
                                     ^^^^^^^^^^^^^
HP_936(next),
 // PRE_REC
(2;0)HP_936(next)&
next!=null --> H1(next),
 // BIND
(2;0)G1(next)&next!=null --> next::node<val,next1>@M * HP_963(val@NI) * 
                                                       ^^^^^^^^^^^^^
HP_964(next1),
 // POST
(1;0)xs::node<val,next>@M * HP_935(val@NI) * HP_936(next)&
                            ^^^^^^^^^^^
next=null --> G1(xs),
 // POST
(1;2;0)xs::node<val,next>@M * HP_935(val@NI) * next::node<val1,next1>@M * 
                              ^^^^^^^^^^^^^
HP_963(val1@NI) * HP_964(next1)&
^^^^^^^^^^^^
val<=val1 --> G1(xs),
 // POST
(2;2;0)xs::node<val,next>@M * HP_963(val@NI) * next::node<val1,next1>@M * 
HP_935(val1@NI) * HP_964(next1)&
val<val1 --> G1(xs)]

 */

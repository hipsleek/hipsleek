/* Build a list of the form 1->...->1->0 */

data node {
 node next;
 node prev;
}

bool bool_nondet()
  requires emp & true ensures emp & true;

node new_node()
  requires emp & true ensures res::node<_,_>;

//HeapPred H(node x, node b). // non-ptrs are @NI by default
//  PostPred G(node x,  node b,  node c, node d). // non-ptrs are @NI by default

HeapPred H(node x, node@NI y). // non-ptrs are @NI by default
PostPred G(node x,  node b).



  dllseg<p,l> == self::node<p,l>
  or self::node<p,q>*q::dllseg<self,l>
  ;

 dllseg1<p,l> == self::node<p,l>
  or self::node<p,q>*q::dllseg1<self,l>
  ;

lseg<p> == self::node<_,p>
  or self::node<_,q>*q::lseg<p>
  ;


void create_dll (ref node list, ref node t)

//infer [H,G] requires H(list)   ensures G(list,list');
//  infer [H] requires H(list,t)   ensures true;

  requires list::dllseg<_,_> ensures list'::dllseg<_,l> ; //'


{
  if (bool_nondet()) {
    //list::node<_,q> * q::lseg<l>
    t = new_node();
    //t'::node<_,_> * list::node<_,q> * q::lseg<l>
    t.next = list;
    //t'::node<_,list> * list::node<_,q> * q::lseg<l>
    list.prev = t;
    // t'::node<_,list> * list::node<t',q> * q::lseg<l>
    list = t;
    // list'::node<_,list> * list::node<t',q> * q::lseg<l> & list'=t'
    // pre-rec list'::node<_,list> * list::node<t',q> * q::lseg<l> & list'=t' |- list'::lseg<l>
    create_dll(list,t);
  }
}

/*
list::node<_,q> * q::lseg<>
 */


/* void create_dll1 (node list, node t) */

/* //infer [H,G] requires H(list)   ensures G(list,list'); */
/*   infer [H] requires H(list,t)   ensures true; */

/* //requires list::dllseg<_> ensures list'::dllseg<_> ; //' */
/* { */
/*   if (bool_nondet()) { */
/*      t = new_node(); */
/*     list.prev = t; */
/*     create_dll1(list.next,list); */
/*   } */
/* } */

/*
*************************************
*******shape relational assumptions ********
*************************************
[ // BIND
(1;0)H(list)&
true --> list::node<next_37_1477,prev_37_1478>@M * HP_1479(next_37_1477) *
         HP_1480(prev_37_1478)&
true,
 // PRE_REC
(1;0)list'::node<list_1482,Anon_1473>@M * HP_1479(next_37_1477) *
     list_1482::node<next_37_1477,list'>@M&true --> H(list')&
true]


 */

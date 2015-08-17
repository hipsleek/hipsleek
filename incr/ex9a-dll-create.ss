/* Build a list of the form 1->...->1->0 */

data node {
  node prev;
  node next;
}

bool bool_nondet()
  requires emp & true ensures emp & true;

node new_node()
  requires emp & true ensures res::node<_,_>;

//HeapPred H(node x, node b). // non-ptrs are @NI by default
  PostPred G1(node x,  node b,  node@NI c, node@NI d). // non-ptrs are @NI by default

HeapPred H(node x). // non-ptrs are @NI by default
PostPred G(node x,  node b).



  dllseg<p,l> == self::node<p,l>
  or self::node<p,q>*q::dllseg<self,l>
  ;

 dllseg1<p> == self::node<_,_> & self=p
  or p::node<prev,_>*self::dllseg1<prev>
  ;

lseg<p> == self::node<_,p>
  or self::node<_,q>*q::lseg<p>
  ;

rlseg<p> == self=p
  or p::node<q,_>*self::rlseg<q>
  ;

lemma_safe self::dllseg1<list>  -> self::rlseg<list> * list::node<_,_>.

void create_dll (ref node list)

//infer [H,G] requires H(list)   ensures G(list,list');
//  infer [H] requires H(list)   ensures true;
//  infer [G1] requires list::node<pre,n>   ensures G1(list,list',pre,n);
//infer [G] requires list::node<pre,n>   ensures G(list,list');
  requires list::node<_,_> ensures list'::dllseg1<list> ; //'
// requires list::node<_,_> ensures list'::rlseg<list> * list::node<_,_> ;

{
  node t;
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
    create_dll(list);
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

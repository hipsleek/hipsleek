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

HeapPred H(node x). // non-ptrs are @NI by default
PostPred G(node x,  node b).



  dllseg<p,n> == self::node<p,n>
  or self::node<p,q>*q::dllseg<self,p>
  ;


void create_dll (ref node list, ref node t)

//infer [H,G] requires H(list)   ensures G(list,list');
infer [H] requires H(list)   ensures true;

// requires list::dllseg<_,_> ensures list'::dllseg<_,_> ; //'
{
  if (bool_nondet()) {
    t = new_node();
    t.next = list;
    list.prev = t;
    list = t;
    create_dll(list,t);
  }
}

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

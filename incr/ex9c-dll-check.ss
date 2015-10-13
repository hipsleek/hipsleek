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



  dllseg<p> == self=p
  or self::node<_,q>*q::dllseg<p>
  ;

 ll<> == self=null
  or self::node<_,q>*q::ll<>
  ;

 dllseg1<p> == self::node<_,_> & self=p
  or p::node<_,prev>*self::dllseg1<prev>
  ;

lseg<p> == self::node<_,p>
  or self::node<_,q>*q::lseg<p>
  ;


void check_dll (ref node list)

//  infer [H] requires H(list)   ensures true;
// infer [G] requires list::ll<>   ensures G(list,list');
  requires list::ll<> ensures list::lseg<list'> & list'=null; //'


{
  if (list!=null) {
    list = list.next;
    check_dll(list);
  }
}


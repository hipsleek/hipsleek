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
  or p::node<prev,_>*self::dllseg1<prev>
  ;

rlseg<p> == self=p
  or p::node<q,_>*self::rlseg<q>
  ;

lseg<p> == self=p
  or self::node<_,q>*q::lseg<p>
  ;

dll_seg3<a,last,pp> == self=pp & a=last
  or self::node<a,q>*q::dll_seg3<self,last,pp>;

lemma_safe self::dll_seg3<a,last,pp>  
      <- self::dll_seg3<a,r,last>*last::node<r,pp>.

lemma_safe self::dll_seg3<a,last,pp>  * pp::node<_,null>
      -> self::ll<>.


void create_dll (ref node list)

//infer [H,G] requires H(list)   ensures G(list,list');
//  infer [H] requires H(list)   ensures true;
//  infer [G] requires list::node<pre,n>   ensures G(list,list');
//  requires list::node<_,_> ensures list'::rlseg<list> * list::node<_,_> ; //'
 requires list::node<_,pp>
  ensures list'::dll_seg3<_,r,list> * list::node<r,pp>; //'

{
  node t;
  if (bool_nondet()) {
    t = new_node();
    t.next = list;
    list.prev = t;
    list = t;
    create_dll(list);
  }
}

void check_dll (ref node list)

//  infer [H] requires H(list)   ensures true;
//  infer [G] requires list::ll<>   ensures G(list,list');
    requires list::ll<> ensures list::lseg<list'> & list'=null; //'


{
  if (list!=null) {
    list = list.next;
    check_dll(list);
  }
}


int main()
  requires true ensures true;
{
  node list, y;

  y =new_node();
  y.next = null;
  y.prev = null;
  list=y;

  //dprint;
  create_dll(list);

  //dprint;
  check_dll(list);

  return 0;
}

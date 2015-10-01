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


dll_seg<a,pp> == self::node<a,pp>
  or self::node<a,q>*q::dll_seg<self,pp>;


dll_seg2<a,last,pp> == self::node<a,pp> & last=self
  or self::node<a,q>*q::dll_seg2<self,last,pp>;

lemma_safe self::dll_seg2<a,last,pp>  
      <- self::dll_seg2<a,r,last>*last::node<r,pp>.

void create_dll (ref node list)
//infer [H] requires H(list)   ensures true;
  requires list::node<_,pp>
  ensures list'::dll_seg2<_,list,pp>;
{
  node t;
  if (bool_nondet()) {
    assume false;
    //list::node<_,pp> 
    t = new_node();
    //t'::node<_,_> * list::node<_,pp> 
    t.next = list;
    //t'::node<_,list> * list::node<_,pp> 
    list.prev = t;
    // t'::node<_,list> * list::node<t',pp> 
    list = t;
    // list'::node<_,list> * list::node<t',pp> 
    create_dll(list);
    // list'::dll_seg2<_,_,list> * list::node<t',pp> 
  }
}

/*
# ex9b5.ss

# verifies!

  requires list::node<_,pp>
  ensures list'::dll_seg2<_,list,pp>;

dll_seg2<a,last,pp> == self::node<a,pp> & last=self
  or self::node<a,q>*q::dll_seg2<self,last,pp>;

lemma_safe self::dll_seg2<a,last,pp>  
      <- self::dll_seg2<a,r,last>*last::node<r,pp>.



*/


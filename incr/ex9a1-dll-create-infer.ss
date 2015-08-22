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

rlseg1<prev> == self=prev
  or self::node<prev,n>*n::rlseg1<self>
  ;

dll_seg3<a,last,pp> == self=pp & a=last
  or self::node<a,q>*q::dll_seg3<self,last,pp>;


lemma_safe self::dll_seg3<a,last,pp>  
      <- self::dll_seg3<a,r,last>*last::node<r,pp>.


void create_dll (ref node list)

//infer [H,G] requires H(list)   ensures G(list,list');
//  infer [H] requires H(list)   ensures true;
//  infer [G1] requires list::node<pre,n>   ensures G1(list,list',pre,n);
// infer [G] requires list::node<pre,n>   ensures G(list,list');

requires list::node<_,pp>   ensures list'::dll_seg3<_,r,list> * list::node<r,pp>;
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

 G(list_1568,list_1569) ::= list_1569::node<pre,n>@M&list_1569=list_1568
 or list_1568::node<t_1567,n>@M * G(t_1567,list_1569)&t_1567!=null

 */


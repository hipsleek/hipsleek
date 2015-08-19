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

//lemma_safe self::dllseg1<list>  -> self::rlseg<list> * list::node<_,_>.

void create_dll (ref node list)
//infer [H] requires H(list)   ensures true;
  requires list::dll_seg<a,pp>
  ensures list'::dll_seg<_,pp>;
{
  node t;
  if (bool_nondet()) {
    //list::node<_,pp> 
    t = new_node();
    //t'::node<_,_> * list::node<_,pp> 
    t.next = list;
    //t'::node<_,list> * list::node<_,pp> 
    list.prev = t;
    // t'::node<_,list> * list::node<t',pp> 
    list = t;
    // list'::node<_,list> * list::node<t',pp> & list'=y'
    create_dll(list);
  }
}

/*
# ex9b3.ss

  requires list::dll_seg<a,pp>
  ensures list'::dll_seg<_,pp>;

 G(list_1568,list_1569) ::= list_1569::node<pre,n>@M&list_1569=list_1568
 or list_1568::node<t_1567,n>@M * G(t_1567,list_1569)&t_1567!=null

=====================
Obtained:

[ // BIND
(1;0)H(list)& true --> list::node<prev_62_1561,next_62_1562>@M 
  * HP_1563(prev_62_1561) * HP_1564(next_62_1562)&
true,
 // PRE_REC
(1;0)list'::node<Anon_1556,list_1566>@M * HP_1564(next_62_1562) * 
     list_1566::node<list',next_62_1562>@M&true --> H(list')&
true,
 // POST
(1;0)HP_1563(prev_62_1561) * (htrue)&true --> emp&
true]

Can we infer:

dll_seg<a,pp> == self::node<a,pp>
  or self::node<a,q>*q::dll_seg<self,pp>;


*/


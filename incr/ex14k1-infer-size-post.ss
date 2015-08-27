/* singly linked lists */
//../hip ex14-infer-shape-pre-post.ss --classic
/* representation of a node */
data node {
	int val;
	node next;
}

pred_extn size[R]<k> ==
   k=0 // base case
   or R::size<i> & k=1+i // recursive case
  inv k>=0;

/* view for a singly linked list */
ll<n> == self = null & n = 0
	or self::node<_, q> * q::ll<n-1>
  inv n >= 0;

sll<> == self = null 
	or self::node<_, q> * q::sll<>
  inv true;

HeapPred H(node a).
//HeapPred G(node a, node b).
HeapPred H1(node a).

  relation R(int a,int b, int c).

int size_helper(node x)
/*
  infer[H]
  requires H(x)  ensures true;//H1(x);
*/
//  infer[@shape_prepost,@classic] requires true ensures true;
  infer[@size,@post_n] requires x::sll<> ensures x::sll<>;
//  infer[@post_n] requires x::ll<aa> ensures x::ll<bb>;

{
  if (x==null) 
    return 0;
  else {
    return 1+ size_helper(x.next);
  }
}

/*
# ex14k1.ss

  infer[@size,@post_n] requires x::sll<> ensures x::sll<>;

# Print the view definition sll_size

!!! **derive.ml#344:new view:
 view sll_size<size_1651:int>= 
  EList
    :EBase 
       (* lbl: *){261}->emp&self=null & size_1651=0&{FLOW,(1,28)=__flow#E}[]
    || :EBase 
          exists (Impl)[Anon_1652; 
          q_1653](* lbl: *){262}->(exists size_1654: (* lbl: *){262}->
          self::node<Anon_1652,q_1653>@M * q_1653::sll_size<size_1654>@M&
          size_1651=size_1654+1 & 0<=size_1654&{FLOW,(1,28)=__flow#E}[])
 
# Why did we get, and not also size_1676=0 ?

RELDEFN post_1678: ( res=0 & size_1676=size_1675 & 0<=size_1675) -->  post_1678(size_1676,size_1675,res,flow)]

# below is sleek proof, is it due to lack of invariant?

id: 15; caller: []; line: 0; classic: false; kind: POST; hec_num: 1; evars: []; infer_vars: [ post_1678]; c_heap: emp; others: [@post] globals: [@flow,@ver_post]
 checkentail x::sll_size<size_1675>@M&
v_bool_39_1645' & x'=null & x'=x & v_int_40_1636'=0 & res=v_int_40_1636' & 
MayLoop[]&{FLOW,(4,5)=__norm#E}[]
 |-  : x::sll_size<size_1676>@M&post_1678(size_1676,size_1675,res,flow)&
{FLOW,(4,5)=__norm#E}[]. 
ho_vars: nothing?
res:  1[
    emp&
v_bool_39_1645' & x'=null & x'=x & v_int_40_1636'=0 & res=v_int_40_1636' & 
size_1676=size_1675&{FLOW,(4,5)=__norm#E}[]
   es_infer_rel: [RELDEFN post_1678: ( res=0 & size_1676=size_1675 & 0<=size_1675) -->  post_1678(size_1676,size_1675,res,flow)]
   ]

 EBase 
   exists (Impl)[size_1675]x::sll_size<size_1675>@M&MayLoop[]&
   {FLOW,(4,5)=__norm#E}[]
   EAssume 
     (exists size_1676: x::sll_size<size_1676>@M&
     res>=0 & size_1676>=res & size_1676=size_1675&{FLOW,(4,5)=__norm#E}[])

# Why did we not get res=size_1673?
  Below, we did obtain res=a

  infer[@post_n] requires x::ll<a> ensures x::ll<b>;

size_helper$node
 EBase 
   exists (Impl)[aa]x::ll<aa>@M&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
   EAssume 
     (exists bb: x::ll<bb>@M&res>=0 & res=bb & res=aa&
     {FLOW,(4,5)=__norm#E}[])

*/



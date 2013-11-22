// simpler tll working example

data node{
	node left;
	node right;
	node next;
}

/* predicate for a non-empty tree with chained leaf list */
 tll<ll,lr> == self::node<null,null,lr> & self = ll
	or self::node<l,r,null> * l::tll<ll,z> * r::tll<z,lr>
	inv self!=null;

/* predicate for a non-empty tree  */
 tree<> == self::node<null,null,_>
	or self::node<l,r,null> * l::tree<> * r::tree<>
	inv self!=null;


// initializes the linked list fields

HeapPred H(node a, node@NI b).
  HeapPred G(node a, node b).

bool check_tll(node x,node t, node@R r)
  infer [H,G] requires H(x,t) ensures G(x,t) & res;
// requires x::tll<t,ggg>@L ensures res & r'=ggg;//'
{
  if (x.right==null)
    {
          r = x.next;
      return t==x;
    }
  else
    {
      node r_most;
      //if (x.left==null) return false;
      bool b = check_tll(x.left, t, r_most);
      return b && check_tll(x.right, r_most, r);
    }
}


/*
# check-tll.ss --sa-dnc --pred-en-dangling

[ H(x_1045,t_1046) ::= x_1045::node<left_29_980,right_29_981,__DP_HP_985>@M 
    * H(left_29_980,t_1046) * H(right_29_981,r_1044)&right_29_981!=null & left_29_980!=null
     \/  x_1045::node<__DP_HP_983,right_29_981,__DP_HP_985>@M&right_29_981=null,
 
G(x_1051,t_1052) ::= x_1051::node<left_29_980,right_29_981,__DP_HP_985>@M * G(left_29_980,t_1052) 
     * G(right_29_981,r_1032)&left_29_980!=null & right_29_981!=null
   \/  t_1052::node<__DP_HP_983,right_29_981,__DP_HP_985>@M&right_29_981=null & t_1052=x_1051

*/


  /*


  // BIND
(0)H(x,t@NI) --> x::node<left_29_944,right_29_945,next_29_946>@M *
HP_947(left_29_944,t@NI) * HP_948(right_29_945,t@NI) *
HP_949(next_29_946,t@NI),
 // PRE_REC
(2;2;0)HP_947(left_29_944,t@NI)&
left_29_944!=null --> H(left_29_944,t@NI),
 // PRE_REC
(2;2;0)HP_948(right_29_945,t@NI)&
right_29_945!=null --> H(right_29_945,r_996@NI),
 // POST
HP_948(right_29_945,t@NI) --> emp&
right_29_945=null,
 // POST
(1;0)HP_947(left_29_944,t@NI) * HP_949(next_29_946,t@NI) *
x::node<left_29_944,right_29_945,next_29_946>@M&t=x &
right_29_945=null --> G(x,t@NI),
 // POST
HP_948(right_29_945,t@NI) --> emp&
right_29_945!=null,
 // POST
(2;2;0)HP_949(next_29_946,t@NI) *
x::node<left_29_944,right_29_945,next_29_946>@M * G(left_29_944,t@NI) *
G(right_29_945,r_996@NI)&right_29_945!=null &
left_29_944!=null --> G(x,t@NI)]


   */

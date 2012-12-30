/* doubly linked lists */

/* representation of a node */
data node2 {
	int val; 
	node2 prev;
	node2 next;	
}

/* view for a doubly linked list with size */
dll<p,n> == self = null & n = 0 
  or self::node2<_ ,p , q> * q::dll<self, n-1> // = q1 
	inv n >= 0;



void insert(node2 x, int a)
  requires x::dll<p, n> & n>0 //&  x!=null  
  ensures x::dll<p, m> & m>n; 
{
  bool l = x.next == null;
  if (l)
		{	x.next = new node2(a, x, null);
		
          //dprint;
}else 
      insert(x.next, a);
}

/*
Successful States:
[
 Label: [(129::,0 ); (129::,0 )]
 State:EXISTS(v_node2_23_553': q_595::dll<self_592,flted_12_593>@M[Orig] * v_node2_23_553'::node2<a',x',v_null_23_610>@M[Orig] * x'::node2<Anon_594,p_591,v_node2_23_553'>@M[Orig]&flted_12_593+1=n & p_591=p & self_592=x' & x'=x & a'=a & 0<n & q_595=null & l_26' & q_595=null & l_26' & v_null_23_610=null&{FLOW,(22,23)=__norm})[]
       es_var_measures: MayLoop

 ]

*/

/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}

llS<S> == self = null & S = {} 
	or self::node<v, q> * q::llS<S1> & S = union(S1, {v});


	
void dispatch(node lst, ref node gtl, ref node ltl)

   requires lst::llS<B> 
  ensures gtl'::llS<B1> * ltl'::llS<B2> 
     & B=union(B1,B2) 
     & forall (x:(x notin B1 | x>=3))
    & forall (x:(x notin B2 | x<3)); 

// File "bug1-dispatch.ss", line 21, col 6: x shallows outer name

{
  if (lst == null) {
     gtl=null; 
     ltl =null;
     }
   else {
     node tmp = lst.next;
     node gt; node lt;
     if (lst.val>=3) {
          dispatch(tmp,gt,lt);         
          lst.next = gt;
          gtl = lst;
          ltl=lt;
     } else {
          dispatch(tmp,gt,lt);
          lst.next = lt;
          ltl = lst;
          gtl=gt;
     }
   }
}


	




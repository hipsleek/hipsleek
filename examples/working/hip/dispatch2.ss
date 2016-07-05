/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}


/* view for a singly linked list */
llH<n,"s":sum,"B":B> == self = null 
         &  n = 0 &
 [ "n":n=0; "s": sum=0]//; "B": B={}] 
  or self::node<v, q> * q::llH<n1, sum1,B1> & v>=0 &
  ["n":n=1+n1; "s":n=1+n1 & sum=sum1+v ; "B":B=union(B1,{v})]
  inv true & n>=0 & ["s": sum>=0 ];

	
void dispatch(node lst, ref node gtl, ref node ltl)
  requires lst::llH<n,s,B> 
  ensures gtl'::llH<n1,s1,B1> * ltl'::llH<n2,s2,B2> 
  & n=n1+n2 & 
    ["s":s=s1+s2 & s1>=3*n1 & s2<=2*n2; 
     "B":B=union(B1,B2) 
     & forall (x:(x notin B1 | x>=3))
     & forall (y:(y notin B2 | y<3))
  ]
  ;
{
  dprint;
  bool b = (lst==null);
  dprint;
  if (b) { gtl=null; ltl =null; assert false;}
   else {
     assume true;
     //assume false;
   }
}


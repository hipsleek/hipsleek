data node {
	int val; 
	node next;	
}


/* view for a singly linked list */

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
	inv n >= 0;

node app2(node x, node y)
 requires x::ll<n> * y::ll<m> & n>=0
 // variance [n@1]
 ensures res::ll<n+m>;
{
 if (x==null) return y;
 else {
   node w=x.next;
   assert w'::ll<a> & n>a; //'
   assert n>=1;
   return new node(x.val,app2(w,y));
 }
}


int length (node xs)
 requires xs::ll<n>
 //variance [n]
 ensures xs::ll<n> & res=n;
 case {
   xs=null ->  //variance [] => false
              ensures res=0;
  xs!=null -> requires xs::ll<n>
 	      //variance [n]
              ensures xs::ll<n> & res=n;
 }
 requires x::ll<n>
 //variance [n]
 case {
   xs=null -> ensures res=0;
   xs!=null -> ensures x::ll<n> & res=n;
 }
{
  if (xs==null) return 0;
  else return 1+length(xs.next);
}



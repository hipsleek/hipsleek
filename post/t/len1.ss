/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}


/* view for a singly linked list */

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

	
	
/*ll1<S> == self = null & S = {} 
	or self::node<v, q> * q::ll1<S1> & S = union(S1, {v});*/

/*ll2<n, S> == self=null & n=0 & S={}
	or self::node<v, r> * r::ll2<m, S1> & n=m+1   & S=union(S1, {v});*/

relation R(int x, int y, int z).

int length(node x)
  infer [R] requires x::ll<n> 
  ensures x::ll<m> & R(n,m,res) & n>=0  ;
{    
  if (x==null) return 0;
  else return 1+length(x.next);
}

/*
# len1.ss

  infer [R] requires x::ll<n> 
  ensures x::ll<m> & R(n,m,res)  ;

Above works, as cna be seen:

*************************************
*******fixcalc of pure relation *******
*************************************
[( R(n,m_1209,res), m_1209=n & res=n, true, true)]
*************************************

Post Inference result:
length$node
 requires x::ll<n> & MayLoop[]
 ensures x::ll<m_1209> & 0<=n & m_1209=n & 
res=n;



*/







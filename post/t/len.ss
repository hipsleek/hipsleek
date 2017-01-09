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

int length(node x)
 infer [@post_n]
  requires x::ll<n> ensures x::ll<m>  ;
{    
  if (x==null) return 0;
  else return 1+length(x.next);
}

/*
# len.ss

Below works:
  requires x::ll<n> ensures x::ll<m>  ;

However:
  infer [@post_n]
  requires x::ll<n> ensures x::ll<m>  ;

Questions:
 (1) why only base-case inferred
 (2) Why perform re-verification when all
     the flags false
 (3) encountered a reverification problem:

*************************************
*******fixcalc of pure relation *******
*************************************
[( post_1206(x,res), x=0 & res=0, true, true)]
*************************************

Post Inference result:
length$node
 requires x::ll<n> & MayLoop[]
 ensures x::ll<m_1205> & 0<=n & x=0 & res=0;

Checking procedure length$node... 
Post condition cannot be derived:
  (must) cause: AndR[ (((0=1 & x=2 & 1<=m_1328) | (x=1 & 0=null & m_1328=0))) & x!=null |-  x=0. LOCS:[1;13;29;25;0];  res=0+1 |-  res=0. LOCS:[30;0] (must-bug).]

Context of Verification Failure: 1 File "",Line:0,Col:0
Last Proving Location: 1 File "len.ss",Line:30,Col:14

ERROR: at _0:0_0:0 
Message: Post condition cannot be derived.
 
ExceptionFailure("Post condition cannot be derived.")Occurred!

Error1(s) detected at main 
Stop Omega... 21 invocations caught
(Program not linked with -g, cannot print stack backtrace)

Exception occurred: Failure("Post condition cannot be derived.")



*/







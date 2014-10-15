data node {
  int val; 
  node next;
}


/* view for a singly linked list */

ll<n> == self = null & n = 0 
  or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;
  
lseg<n, p> ==
  self = p & n = 0 or
  self::node<v, q> * q::lseg<n-1, p> 
  inv n>=0;

clist<n> ==
  self::node<v, q> * q::lseg<n-1, self>
  inv n>0;

lemma self::clist<n> <- self::lseg<n-1, q> * q::node<v, self>;

//lemma self::lseg<n, q> <- self::lseg<n-1, p> * p::node<v, q>;

//lemma self::node<v, q> * q::lseg<n, self> -> q::node<v1, s> * s::lseg<n, q>;


/* append two singly linked lists */

void append2(node x, node y)
//infer [@term]
  //requires x::ll<n1> * y::ll<n2> & n1>0 
  //ensures x::ll<n1+n2>;
  
  //requires x::ll<n1> * y::ll<n2> & n1>0 
  //ensures true;
  
  //requires x::clist<n1> * y::ll<n2> 
  //ensures x::lseg<n, x> & n < n1;
  
  //requires x::ll<n1> * y::clist<n2> & n1>0 
  //ensures true;
  
//requires x::lseg<n,null> & n > 0
//ensures x::lseg<n, y>;

  infer [@term]
  requires x::clist<n> 
  ensures true;
{    
  if (x.next == null) 
    x.next = y;
  else
    append2(x.next, y);
}

/*

Base/Rec Case Splitting:
[	append2: [[2] 1<=n@R]
]
Termination Inference Result:
append2:  requires x::clist<n> & truecase {
                             1<=n -> requires emp & Loop[]
 ensures false & false;
                             
                             }

*/

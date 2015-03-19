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
 
  infer [@term]
  requires x::lseg<n,null> & n > 0
  ensures x::lseg<n, y>;

  //infer [@term]
  requires x::lseg<n,null> & x=y & n > 0
  ensures x::clist<n>;
  
{    
  if (x.next == null) 
    x.next = y;
  else
    append2(x.next, y);
}

/*
# ll-app1.ss

What happen to the circular list spec?

Termination Inference Result:
append2:  requires x::lseg<n,flted_34_62> & flted_34_62=null & 
0<ncase {
    n=1 -> requires emp & Term[7,1]
 ensures x::lseg<n_1283,y_1284> & 0<=n & 
    y_1284=y & n_1283=n; 
    2<=n -> requires emp & Term[7,2,0+(1*n)+(0*
    n)]
 ensures x::lseg<n_1283,y_1284> & 0<=n & y_1284=y & n_1283=n; 
    }


*/

data node {
  int val;
  node next;
}

lseg<n, p> ==
  self = p & n = 0 or
  self::node<v, q> * q::lseg<n-1, p> 
  inv n>=0;

clist<n> ==
  self::node<v, q> * q::lseg<n-1, self>
  inv n>0;

lemma self::clist<n> <- self::lseg<n-1, q> * q::node<v, self>;

lemma self::lseg<n, q> <- self::lseg<n-1, p> * p::node<v, q>;

//lemma self::lseg<n, q> -> self::lseg<n-1, p> * p::node<v, q>;

lemma self::node<v, q> * q::lseg<n, self> -> (exists q1: q1::node<v1, self> * self::lseg<n, q1>);


int length (node x)


//  infer [@term]
  requires x::clist<n> ensures false;

//infer [@term]
//  requires x::lseg<n,null>@L ensures res=n;

/*
  infer [@term]
  requires x::lseg<n,null>
  ensures x::lseg<n,null> & res=n;
*/
{
  if (x == null)
    return 0;
  else
    return 1 + length(x.next);
}
/*
# clist1.ss

  requires x::clist<n> ensures false;

Why did we have imm failure which also occurs with --imm

Checking procedure length$node... 
Proving precondition in method length$node Failed.
  (must) cause:  mismatched imm annotation for data node

Context of Verification Failure: 1 File "clist.ss",Line:25,Col:33
Last Proving Location: 1 File "clist.ss",Line:39,Col:15

Procedure length$node FAIL.(2)

Exception Failure("Proving precond failed") Occurred!
(Program not linked with -g, cannot print stack backtrace)


*/

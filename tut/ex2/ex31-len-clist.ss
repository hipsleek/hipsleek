data node {
  int val;
  node next;
}

/*
ll<n> == emp & self=null & n=0
  or self::node<_,q>*q::ll<n-1>
  inv n>=0;
*/

HeapPred PP(node x,node@NI y).
PostPred QQ(node x, node y).

ls_nt<p> == emp & self=p
  or self::node<_,q>*q::ls_nt<p> & self!=p
  inv true;

cll<> == self::node<_,q>*q::ls_nt<self> 
  inv self!=null;


/*
int len_cll(node x)
  requires x::cll<>
  ensures x::cll<> & res>0;
{
  node n=x.next;
  return 1+length(n,x);
}
*/



int length(node x,node p)
  infer [PP,QQ]
  requires PP(x,p)
  ensures QQ(x,p);
{
  if (x==p) return 0;
  else return 1+length(x.next,p);
}

/*
# ex31-len-clist.ss

PROBLEM 1 : Why is there double "requires"?

infer[ PP,QQ]requires PP(x,p@NI)&truerequires emp
 ensures QQ(x,p)&
true{,(4,5)=__norm#E};

PROBLEM 2 : Why did we not reuse ll_nt which is identical?

[ PP(x_1441,p_1442) ::= 
 PP(next_38_1438,p_1442) * x_1441::node<val_38_1437,next_38_1438>&
 x_1441!=p_1442
 or emp&x_1441=p_1442
 (4,5),
 QQ(x_1443,p_1444) ::= PP(x_1443,p_1444)(4,5)]

PROBLEM 3 : Why did we have verification failure? Is it due
to the double requires?


!!! INFERRED SHAPE SPEC: EBase x::PP{}<p>&{FLOW,(4,5)=__norm#E}[]
         EBase emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
                 EAssume 
                   x::PP{}<p>&{FLOW,(1,28)=__flow#E}[]
                   
Checking procedure len_cll$node... 
Proving precondition in method length$node~node Failed.
Empty list_failesc_context

Context of Verification Failure: 1 File "",Line:0,Col:0

Last Proving Location: 1 File "ex31-len-clist.ss",Line:28,Col:11

Procedure len_cll$node FAIL.(2)

Exception Failure("Proving precond failed") Occurred!

*/


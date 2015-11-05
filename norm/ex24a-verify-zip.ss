data node {
  int val;
  node next;
}

ll<n> == self=null & n=0 
  or self::node<_,q>*q::ll<n-1>
inv n>=0;

lseg<n,p> == self=p & n=0 
  or self::node<_,q>*q::lseg<n-1,p>
inv n>=0;

relation P(int a,int b).
relation Q(int a,int b, int c).

HeapPred Z(node x, node y).
node zip(node x,node y)
/*
 requires x::ll<a>*y::ll<b> & a=b
 ensures res::ll<n> & n=a;
 infer[P,Q]
 requires x::ll<a>*y::ll<b> & P(a,b)
 ensures res::ll<n> & Q(a,b,n);
  requires x::ll<a>@L*y::lseg<b,p>@L & a<=b
 ensures res::ll<n> & a=n ;
*/
  infer [Z,@classic]
  requires Z(x,y)
  ensures true;
{
  if (x==null) return x;
  else {
    node r = new node(x.val+y.val,null);
    r.next = zip(x.next,y.next);
    return r;
  }
}

/*
# ex24a
[ // BIND
(2;0)Z(x,y)&
x!=null --> x::node<val_34_1682,next_34_1683>@M * 
            HP_1684(next_34_1683,y,x@NI)&
true,
 // BIND
(2;0)HP_1684(next_34_1683,y,x@NI)&
true |#| x::node<val_34_1682,next_34_1683>@M&
true --> y::node<val_34_1693,next_34_1694>@M * 
         HP_1695(next_34_1694,next_34_1683,x@NI,y@NI)&
true,
 // PRE_REC
(2;0)HP_1695(next_34_1694,next_34_1683,x@NI,y@NI)&
true |#| x::node<val_34_1682,next_34_1683>@M * 
         y::node<val_34_1693,next_34_1694>@M&
true --> Z(next_34_1683,next_34_1694)&
true,
 // POST
(1;0)Z(x,y)&y'=y & x'=x & res=x' & x'=null --> emp&
true]

--------

Context of Verification Failure: ex24a-verify-zip.ss_30:10_30:14

Last Proving Location: ex24a-verify-zip.ss_35:4_35:10

ERROR: at _0:0_0:0
Message: HP_1695 is neither 2 a data nor view name

ExceptionFailure("HP_1695 is neither 2 a data nor view name")Occurred!

Error1(s) detected at main 
Stop z3... 113 invocations 
Stop Omega... 66 invocations caught

Exception occurred: Failure("HP_1695 is neither 2 a data nor view name")
Error3(s) detected at main 

--ops

[ Z(x_1742,y_1743) ::= y_1743::node<val_34_1745,next_34_1694>@M * 
 x_1742::node<val_34_1744,next_34_1735>@M * Z(next_34_1735,next_34_1694)
 or emp&x_1742=null
 (4,5)]

*/

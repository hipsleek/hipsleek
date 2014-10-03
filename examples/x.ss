data node {
	int val;
	node next;
}

//global int a;

ll<n> == self=null & n=0
	or self::node<_, r> * r::ll<n-1>
	inv n>=0;

/*
int length(node x)
	requires x::ll<n>
	ensures x::ll<n> & res = n;
{
    int z;
	if (x==null) return 0;
	else return 1 + length(x.next);
}
*/

/*
int foo(node x)
	requires x::ll<n> & n>3
	ensures true;
{
  int z=x.next.next.val;
  return z;
}
*/
int foo2(node x)
	requires x::ll<n> & n>3
	ensures true;
{
  node x2=x.next;
  int z;
  bind x2 to (v,n) in { z= v; } 
  return z;
}

/*

  z=(
   bind x to (_,n1)
   bind n1 to (_,n2)
   bind n2 to (v,_)
    in v )

   ( Var r1; Node n1;
     r1=
     (bindnode(x,_,n1);
     (Var r2; Node n2;
      bindnode(n1,_,n2)
      r2=(Var r3; int v;
        bindnode(n2,v,_)
        r3=z;
        formnode(...)
        r3;
       )
      formnode(...);
      r2;
     formnode(...);
     r1;
    )
   

   bind x to (v,w) in e
   ==> ( Var res;v,w;
         bindnode(x,v,w);
         res=e;
         formnode(x,v,w)
         res
        )
        


  n1=x.next;
  n2=n1.next;
  z=n2.val;
 

 */

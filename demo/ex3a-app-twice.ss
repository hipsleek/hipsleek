data node {
	int val;
	node next;
}

ll<n> == self=null & n=0
	or self::node<_, q> * q::ll<n-1>
	inv n>=0;


void append(node x, node y)
  requires x::ll<nnn> * y::ll<mmm> & x!=null //nnn>0
  ensures x::ll<eee>& eee=nnn+mmm;

node appendthree(node x, node y,node z)
  requires x::ll<nn> * y::ll<mm> * z::ll<kk> & x!=null
  ensures x::ll<ee>& ee=nn+mm+kk & nn>0;
{
  append(x,y);
  append(x,z);
  return x;
}


/*
# ex3a

node appendthree(node x, node y,node z)
  requires x::ll<nn> * y::ll<mm> * z::ll<kk> & x!=null
  ensures x::ll<ee>& ee=nn+mm+kk & nn>0;

Why did post nn>0 fail?

Procedure appendthree$node~node~node FAIL.(2)

Exception Failure("Post condition cannot be derived.") Occurred!

Error(s) detected when checking procedure appendthree$node~node~node
Stop Omega... 122 invocations 
0 false contexts at: ()

*/

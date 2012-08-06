data node {
	int val; 
	node next;	
}

int ierror()
  requires true
  ensures true & flow __Error;

int foo1(node x)
  requires x::node<v,q> & q = null
  ensures x::node<v,q> & q = null & res=v;
/*
case
{
x = null -> ensures true & flow __Error;
x != null ->
//should be (extend case for heap)
//x::node<v,q> & q = null
  requires x::node<v,q> & q = null
  ensures x::node<v,q> & q = null & res=v;
}
*/
{
  if (x==null)
    return ierror();
  else
    return x.val;
}


int foo2(node x)
  requires x = null
  ensures true & flow __Error;
/*
case
{
x = null -> ensures true & flow __Error;
x != null ->
//should be (extend case for heap)
//x::node<v,q>
  requires x::node<v,q>
  ensures x::node<v,q> & res=v;
}
*/
{
  if (x==null)
    return ierror();
  else
    return x.val;
}



node foo4(node x)
  requires x::node<v,q>
  ensures x::node<v,q> & res=q;
/*
case
{
x = null -> ensures true & flow __Error;
x != null ->
//should be (extend case for heap)
//x::node<v,q>
  ensures x::node<v,q> & res=q;
}
*/
{
  if (x==null)
    return ierror();
  else
    return x.next;
}



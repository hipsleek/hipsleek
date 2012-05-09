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

/*
This example is similar to foo2 but it tries to bind
x with ll predicate, and returns the same result.

used for foo3
ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;
 */

int foo3(node x)
  requires x = null
  ensures true & flow __Error;
/*
case
{
x = null -> ensures true & flow __Error;
x != null ->
//should be (extend case for heap)
//x::node<v,q>
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


/*
used for foo5
ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;
 */

node foo5(node x)
  requires x = null
  ensures true & flow __Error;
/*
case
{
x = null -> ensures true & flow __Error;
x != null ->
//should be (extend case for heap)
//x::node<v,q>
  ensures x::node<v,q> & res=q;
}
//try another search
requires x::ll<n>
case {
  n = 0 -> ensures true & flow __Error;
  n != 0 -> requires x:node<_,q> * q::ll<n-1>
            ensures x:node<_,q> * q::ll<n-1> & res=q
}
*/
{
  if (x==null)
    return ierror();
  else
    return x.next;
}

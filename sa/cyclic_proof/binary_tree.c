bool nondeterm()
 requires true
 ensures !res or res;

data node {
        int val;
        node left;
	node right
}

//infer predicate
p<> == self = null
	or self::node<_,l,r> * l::p<> * r::p<>
	inv true;

void traverse(ref node x)
// Ex 4.1
requires x::p<>
ensures x::p<> & x'=null;
{
	while(x != null)
	requires x::p<>
	ensures x::p<> & x'=null;
	{
		if(nondeterm()) x = x.left;
		else x = x.right;
	}
}

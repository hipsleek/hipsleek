data node {
        int val;
        node next;
}

//infer predicate
p<> == self = null
	or self::node<_,t> * t::p<>
	inv true;

void ex41 (ref node x)
// Ex 4.1
requires x::p<>
ensures x::p<> & x'=null;
{
  //if (x!=null) ex41(x);
 while(x!=null)
	requires x::p<>
	ensures x::p<> & x'=null;
	{
		x = x.next;
	}


}

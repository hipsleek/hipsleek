data node {
	int val; 
	node next;	
}

ll<v,M> == self = null & M = {} or self::node<value@v,p> * p::ll<v,Mp> & M = union(Mp,{self})
		inv true
		mem M->(node<@L,@M> | node<@A,@M>);

int length(node x)
requires x::ll<@A,M>
ensures x::ll<@A,M>; 
{
if(x==null) return 0;
else 
{int m = 1 + length(x.next);
return m;}
}

int sum(node x)
requires x::ll<@L,M>
ensures x::ll<@L,M>;  
{
if(x==null) return 0;
else 
{int m = x.val;
 node n = x.next;
 m = m + sum(n);
return m;}
}

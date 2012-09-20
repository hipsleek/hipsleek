data node {
	int val; 
	node next;	
}

ll<v,M> == self = null & M = {} or self::node<value@v,p> * p::ll<v,Mp> & M = union(Mp,{self})
		inv true
		mem M->(node<@I,@M> | node<@A,@M>);

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
requires x::ll<@I,M>
ensures x::ll<@I,M>; 
{
if(x==null) return 0;
else 
{int m = x.val + sum(x.next);
return m;}
}

data node {
	int val; 
	node next;	
}

ll<v,M,n,S> == self = null & n = 0 & S = 0 
	// & M = {} 
	or self::node<value@v,p> * p::ll<v,Mp,n-1,Sp> & S = value + Sp & v = @L
	// & M = union(Mp,{self}) 
	or self::node<value@v,p> * p::ll<v,Mp,n-1,Sp> & S = value + Sp & v != @L
	// & M = union(Mp,{self}) 
	inv n >= 0 & S >= 0
	memE M->();
	//memE M->(node<@L,@M> & v = @L; node<@A,@M> & v != @L);

int length(node x)
requires x::ll<@A,M,n,S>
ensures x::ll<@A,M,n,S> & res = n; 
{
if(x==null) return 0;
else 
{int m = 1 + length(x.next);
return m;}
}

int sum(node x)
requires x::ll<@L,M,n,S>
ensures x::ll<@L,M,n,S> & res = S; 
{
if(x==null) return 0;
else 
{int m = x.val;
 node n = x.next;
 m = m + sum(n);
return m;}
}

data node { int i; }

void m (int n, ref node x)
requires x::node<v> & Term
ensures x'::node<v1> & v1>=n;
{
	while (x.i < n)
	requires x::node<v> 
	case {
		v>=n -> requires Term ensures x'::node<v>;
		v<n -> requires Term[n-v] ensures x'::node<n>;
	}
	{
		x.i++;
	}
}

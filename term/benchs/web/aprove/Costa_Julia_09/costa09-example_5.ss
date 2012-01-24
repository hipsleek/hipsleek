data node { int i; }

void m (int n, ref node x)
requires x::node<v> & Term
ensures x'::node<_>;
{
	while (x.v < n)
	requires x::node<v> 
	case {
		v>=n -> requires Term ensures x'=x;
		v<n -> requires Term[n-v] ensures x'::node<n>;
	}
	{
		x.i++;
	}
}

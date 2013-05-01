data Examples { int f; }

int getF (Examples x)
requires x::Examples<v> & Term
ensures res=v;
{
	return x.f;
}

void setF (ref Examples x, int val)
requires x::Examples<_> & Term
ensures x'::Examples<val>;
{
	x.f = val;
}

void exampleMethods (Examples x, Examples y)
requires x::Examples<v1> * y::Examples<v2> & Term
ensures true;
{
	int i = 0;

	while (getF(x) > 0)
	requires x::Examples<v1> * y::Examples<v2>
	case {
		v1<=0 -> requires Term ensures x'::Examples<v1> * y'::Examples<v2>;
		v1>0 -> requires Term[v1] ensures x'::Examples<0> * y'::Examples<v2>;
	}
	{
		i = i + getF(y);
		setF(x, getF(x) - 1);
	}
}

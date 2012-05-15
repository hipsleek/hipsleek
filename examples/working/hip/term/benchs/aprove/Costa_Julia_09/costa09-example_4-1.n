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
	loop(i, x, y);
}

void loop (int i, ref Examples x, ref Examples y)
requires x::Examples<v1> * y::Examples<v2> 
case {
	v1<=0 -> requires Term ensures x'::Examples<v1> * y'::Examples<v2>;
	v1>0 -> requires Term[v1] ensures x'::Examples<0> * y'::Examples<v2>;
}
{
	int v_x = getF(x);
	if (v_x > 0) {
		i = i + getF(y);
		setF(x, v_x - 1);
		loop(i, x, y);
	}
}

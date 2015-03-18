int parts (int p, int q)
case {
	p<=0 -> requires Term ensures true;
	p>0 -> case {
		q<=0 -> requires Term ensures true;
		q>0 -> requires Term[p, q] ensures true;
	}
}
{
	if (p <= 0)
		return 1;
	else if (q <= 0)
		return 0;
	else if (q > p)
		return parts(p, p);
	else
		return parts(p-q, q) + parts(p, q-1);
}

void main ()
requires Term
ensures true;
{
	int l = length();
	for_1(0, l, 1); 
}

void for_1 (int l, int u, int s)
case {
	l>u -> requires Term ensures true;
	l<=u -> case {
		s>0 -> requires Term ensures true;
		s<=0 -> requires Loop ensures false;
	}
}
{
	int p = l;
	loop_1(p, u, s);
}

void loop_1 (ref int p, ref int u, int s)
case {
	p>u -> requires Term ensures true;
	p<=u -> case {
		s>0 -> requires Term[u-p] ensures true;
		s<=0 -> requires Loop ensures false;
	}
}
{
	if (p <= u) {
		for_2(p, 0, u, 1);
		p = p + s;
		loop_1(p, u, s);
	}
}

void for_2 (ref int p, int l, int u, int s)
case {
	l>u -> requires Term ensures p'=p;
	l<=u -> case {
		s>0 -> requires Term ensures p'=p;
		s<=0 -> requires Loop ensures false;
	}
}
{
	int q = l;
	loop_2(p, q, u, s); 
}

void loop_2 (ref int p, ref int q, ref int u, int s)
case {
	q>u -> requires Term ensures p'=p;
	q<=u -> case {
		s>0 -> requires Term[u-q] ensures p'=p;
		s<=0 -> requires Loop ensures false;
	}
}
{
	if (q <= u) {
		parts(p, q);
		q = q + s;
		loop_2(p, q, u, s);
	}
}

int length ()
requires Term
ensures res>=0;

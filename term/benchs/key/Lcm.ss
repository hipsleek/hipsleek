/*
int lcm (int a, int b)

{
	return loop(a, b, a, b);
}
*/
int loop (int a, int b, int am, int bm)
infer[a,b]
case {
	am=bm -> requires Term ensures true;
	am!=bm -> requires Term[-am, am-bm] ensures true;
}
{
	if (am != bm) {
		if (am > bm)
			bm = bm + b;
		else
			am = am + a;
		loop(a, b, am, bm);
	}
	return am;
}

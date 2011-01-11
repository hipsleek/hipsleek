int foo (int x)
//variance [x@0]
case {
	x<0 -> ensures false;
	x>=0 ->	variance (1) [x@0]
			ensures res = 0;
	//x>0 -> //variance [x@0]
	//	   ensures res = 0;
}
{
	if (x == 0) return x;
	else {
		assert x'>=2;
		return foo(x-1);
	}
}

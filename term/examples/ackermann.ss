int ack(int m, int n)
/*
	requires m>=0 & n>=0
	variance [m, n]
	ensures res>0;
*/
	case {
		m=0 -> 	requires n>=0 
						variance (0)
						ensures res>0;
		m!=0 -> requires m>0 & n>=0
						variance (1) [m, n]
						ensures res>0;
	}
{
	if (m == 0) {
		dprint;
		return n+1;
	} 
	else if (n == 0) {
		dprint;
		return ack(m-1, 1);
	} 
	else {
		return ack(m-1, ack(m, n-1));
	}
}

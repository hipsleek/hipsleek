int power (int a, int n) 
case {
	n<=1 -> requires Term ensures true;
	n>1 -> requires Term[n] ensures true;
}
{
	if (n <= 0) return 1;
	else if (n == 1) return a;
	else {
		int r = power(a * a, n/2);
	  if (n % 2 == 0) return r;
	  else return a * r;
	}
}

bool even(int n) 
case {
	n<=0 -> requires Term ensures res;
	n=1 -> requires Term ensures !res;
	n>1 -> requires Term[n] 
	case {
		exists (e1: n=2*e1) -> ensures res;
		exists (e2: n=2*e2+1) -> ensures !res;
	}
}
{
	if (n <= 0) return true;
	else if (n == 1) return false;
	else return odd(n - 1);
}

bool odd(int n) 
case {
	n<=0 -> requires Term ensures !res;
	n=1 -> requires Term ensures res;
	n>1 -> requires Term[n] 
	case {
		exists (o1: n=2*o1) -> ensures !res;
		exists (o2: n=2*o2+1) -> ensures res;
	}
}
{
	if (n <= 0) return false;
	else if (n == 1) return true;
	else return even(n - 1);
}


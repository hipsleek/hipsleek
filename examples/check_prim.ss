
void swap(ref int a, ref int b) 
	requires true ensures a'=b & b'=a;
{
	//dprint;
	int tmp = a;
	//dprint;
	a = b;
	//dprint;
	b = tmp;
	//dprint;
}

void test_swap(ref int x, ref int y)
	requires true ensures x'=x & y'=y;
{
	dprint;
	swap(x, y);
	dprint;
	swap(x, y);
	dprint;
	swap(y, x);
	dprint;
	swap(x, y);
	dprint;
}

int test1(int x) 
	requires x<0 ensures x<0;
	requires 10>x>0 ensures 11>res>0;
{
	//dprint;
	return x;
}

int test2(ref int x)
	requires true ensures res=x+9;
	requires x=10 ensures res=19 & x'=x;
{
	int a = x;
	a = a + 10;
	a--;
	return a;
}

int sum(int n)
	requires true ensures res=n; //if n < 0, the function never stops
{
	if (n == 0)
		return n;
	else 
		return 1 + sum(n-1);
}


int sum_loop(int n) 
	requires n>0 ensures res=n;
{
	int i = 0, s = 0;
	while (i <= n) requires true ensures i>n & s'=s or i'=n & s'=n;
	{
		s++;
		i=i+2;
	}
	return s;
}

bool test_bool(int x) 
	requires true
	ensures x>0 & res or x<=0 & !res;
{
	if (x>0) return true;
	else return false;
}

bool test_not(bool b)
	requires true
	ensures b & !res or !b & res;
{
	return !b;
}

bool test_not1(int x)
	requires true
	ensures x<0 & !res or x>=0 & res;
{
	if (!(x<0)) return true;
	else return false;
}

int test_uminus(int x)
	requires true
	ensures res = -x;
{
	return -x+1-1;
}


global int n;
global int t;

void increase_n(int k)
{
	n = n+k;
}

void main()
{
	n = 1;
	t = 2;
	increase_n(t);
}

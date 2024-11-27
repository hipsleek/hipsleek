
global int n;
global int t;

void increase_n(int k)
	requires k > 0
	ensures n'=k+n;
        // writes n
{
	n = n+k;
}

void main()
	requires true
	ensures t'=2 & n'=3;
        // writes n,t
{
	n = 1;
	t = 2;
	increase_n(t);
}


data cell {
  int val;
}

global cell kc;
global int n;

void increase()
        requires k::cell<ctrue
	ensures k'=k+1 & n'=n+1;
        // writes k,n
{
	k = k+1;
	n = n+1;
}

void increase_n(int k)
	requires k > 0
	ensures n'=k+n;
        // writes n
{
	n = n+k;
}

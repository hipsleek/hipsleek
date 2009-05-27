
global int k;
global int n;

void increase()
	requires true
	ensures k'=k+n & n'=n;
        // writes k; read n
{
	k = k+n;
}
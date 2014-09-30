
global int k;
global int n;

void increase()
	requires true
	ensures k'=k+n;
        // writes k; read n
{
	k = k+n;
}

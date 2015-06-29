
global int k;
global int nnnn;

void increase()
	requires true
	ensures k'=k+nnnn;
        // writes k; read n
{
	k = k+nnnn;
}

void main ()
    requires true
    ensures k'=k+nnnn & nnnn'=nnnn;
{
    increase();
}


global int k;
global int nnnn;


void main ()
    requires true
    ensures k'=k+nnnn ;
{
    increase(5);
}

void increase(int c)
	requires true
	ensures k'=k+nnnn;
        // writes k; read n
{
	k = k+nnnn;
}

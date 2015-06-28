
global int k;
global int nnnn;


void main ()
    requires true
    ensures k'=k+nnnn ;
{
    increase();
}

void increase()
	requires true
	ensures k'=k+nnnn;
        // writes k; read n
{
	k = k+nnnn;
}

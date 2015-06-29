
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
	ensures k'=k+nnnn & nnnn'=nnnn;
        // writes k; read n
{
	k = k+nnnn;
}

/*
# ex3e1.ss --pcp

# good no-renaming

void main(int@R nnnn, int@R k)[]
static EBase: [][](htrue) * ([] & true)( FLOW __norm) {EAssume: 1,:(emp) * ([] & k' = k+nnnn)( FLOW __norm)}
dynamic EBase: [][](hfalse) * ([] & false)( FLOW __false) 
{
{increase(5, nnnn, k)}
}
void increase(int c, int@R nnnn, int@R k)[]
static EBase: [][](htrue) * ([] & true)( FLOW __norm) {EAssume: 2,:(emp) * ([] & (k' = k+nnnn) & (nnnn' = nnnn))( FLOW __norm)}
dynamic EBase: [][](hfalse) * ([] & false)( FLOW __false) 
{
{k = k + nnnn}
}
*/

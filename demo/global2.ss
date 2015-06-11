
global int k;
global int n;

void increase()
	requires true
	ensures k'=k+n;
        // writes k; read n
{
	k = k+n;
}

/*
# global2.ss

How come n is not pass-by-value?

void increase(int@R n_15, int@R k_14)[]
static EBase: [][](htrue) * ([] & true)( FLOW __norm) {EAssume: 1,:(emp) * ([] & k_14' = k_14+n_15)( FLOW __norm)}
dynamic EBase: [][](hfalse) * ([] & false)( FLOW __false) 
{
{k_14 = k_14 + n_15}
}

void increase$int~int(  int n_15,  int k_14)
@ref n_15, k_14
static  EBase htrue&{FLOW,(4,5)=__norm#E}[]
         EBase emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
                 EAssume ref [n_15;k_14]
                   emp&k_14'=n_15+k_14&{FLOW,(4,5)=__norm#E}[]
                   
dynamic  EBase hfalse&false&{FLOW,(4,5)=__norm#E}[]
{k_14 = {add___$int~int(k_14,n_15)}}

{(5,0),(0,-1)}



*/

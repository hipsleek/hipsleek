global int globA;
global int globB;
global int globC;


int alt()
  requires  true
  ensures  true;
{
  int a = 0;
  globC = globA+1;
  return a;
}


int main(int argc)
  requires  true
  ensures  true;
{

    if(argc < 13)
    { 

	return 1;
    }
    assert(globB' >= 0 & globB' <=3);
    alt();
    return 0;
}

/*
int main(int argc, ref int globA_11, ref int globC_12)
static 

(None,[]): EBase: [][](emp)*(true)( FLOW __norm) {EAssume: 62,:(emp)*(true)( FLOW __norm)}
dynamic EBase: [][](hfalse)*(false)( FLOW __false) 
{
{(117, ):if (argc < 13) { 
  (117, ):{(118, ):return 1}
;
}
else { 
  (117, ):;
};
 :assert EBase: [][](emp)*((globB' >= 0) & (globB' <= 3))( FLOW __norm) 
 assume: 
;;
(121, ):alt(globA_11, globC_12);;
(122, ):return 0;}

}

PROBLEMS : 
 (i) renamed globA --> globA_12
 (ii) read-only parameter globA
 (iii) global used is assert/assume not
   picked up as parameter

int alt(ref int globA_13, ref int globC_14)
static 

(None,[]): EBase: [][](emp)*(true)( FLOW __norm) {EAssume: 59,:(emp)*(true)( FLOW __norm)}
dynamic EBase: [][](hfalse)*(false)( FLOW __false) 
{
{local: int a
int a = 0;;
globC_14 = globA_13 + 1;;
(125, ):return a;}

}

}
*/

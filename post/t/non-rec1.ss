
int nrec()
  infer [@post_n]
  requires true
  ensures true;
//ensures res=10;
{
  int y = 10;
  return y; 
}

/*
# non-rec1.ss

[RELDEFN post_1172: ( res=10) -->  post_1172(res)]
*************************************

*************************************
*******fixcalc of pure relation *******
*************************************
[( post_1172(res), res=10, true, true)]

*/

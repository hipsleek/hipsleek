
void nrec()
  infer [@post_n]
  requires true  ensures true;
//ensures res=10;
{
  int y = 10;
  return; 
}

/*
# non-rec2.ss

  infer [@post_n]
  requires true  ensures true;
//ensures res=10;
{
  int y = 10;
  return; 
}

Two problems:
  1. why is printing without a closing ")"
     namely "post_1172("
  2. Why did we get a false post-cond? 
     It should be true.Also, fixcalc isn't
     called, so the problem is likely not there.

# non-rec1.ss is OK

[RELDEFN post_1172: ( true) -->  post_1172(]
*************************************
*************************************
*******fixcalc of pure relation *******
*************************************
[( post_1172(, false, true, true)]
*************************************
!!! REL POST :  post_1172(
!!! POST:  false
!!! REL PRE :  true
!!! PRE :  false

*/

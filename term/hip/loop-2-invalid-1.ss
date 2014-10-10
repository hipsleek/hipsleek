// TODO: this example should result in a Loop unsoundness error?

int foo (int x)
 case {
    x<0 -> requires Loop
           ensures false;
	x=0 -> requires Loop 
           ensures true; /* poststate of Loop must be unreachable */
	x>0 -> requires MayLoop 
           ensures true;
 }
{
  if (x==0) {
        //assume false;
		return 0;
      }
	else
		return 2+foo(x-1);
}
/*
TODO : should fail due to detect LOOP.
*/


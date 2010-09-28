
void loop(ref int x) 
 case {
  x>11 ->  requires xx=1 & x>=0 ensures xx=1 & x'=10; //'
   x<=11 ->  requires xx=0 ensures x'=x-1; //'
  }
// variance x
{
  int z=x;
  x=x-1;
  dprint;
  /*
   why isn't xx present in state?
   true & x<=11 & z_27'=x & (93, ):x'+1=x & {FLOW,(13,14)=__norm,
  */
  if (x>10) {
    //assert xinit'-x'>1;
    assert x-x'>0 & x'>=0;
    assert z_27'-x'>1; // z & z' should be renamed..
    loop(x);
  }
}





void loop(ref int x)
 variance [0,1,x]
 case {
	x>11 -> requires true ensures x'=10; //'
  x<=11 -> requires true ensures x'=x-1; //'
 }
 {
 int xinit=x;
 x=x-1;
 if (x>10) {
   assert x-x'>0 & x>0;
   loop(x);
 }
}


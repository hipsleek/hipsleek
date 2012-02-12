void loop(ref int x)
 requires Term[x]
 case {
	x>11 -> ensures x'=10; //'
  x<=11 -> ensures x'=x-1; //'
 }
 {
 int xinit=x;
 x=x-1;
 if (x>10) {
   //assert x-x'>0 & x>0;
   loop(x);
 }
}


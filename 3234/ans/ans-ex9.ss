// Below is a loop version of mcCarthy function
// expressed using a tail-recursive function
// (i) add strongest postcondition involving
//     [res,x] for mcCarthy and [x,x',c,x'] for loop
//     methods below.
// (ii) VERY HARD : find a ranking function that
//      completes termination property below!


int mcCarthy (int x)
case {
  x>100 -> requires Term[] ensures res=x-10;
  x<=100 -> requires Term[] ensures res=91;
}
{
	int c = 1;
	loop(x, c);
	return x;
}

void loop (ref int x, ref int c)
case {
 c<=0 -> requires Term[] ensures x'=x & c'=c ;
 c=1 ->
   case {
	x>100 -> requires Term[] ensures x'=x-10 & c'=0 ;
	x<=100 -> requires Term[200+21*c-2*x]  ensures x'=91 & c'=0 ;
   }
 c>1 -> requires x<=111 & Term[200+21*c-2*x]
        ensures x'=91 & c'=0;
}
{
	if (c > 0) {
		if (x > 100) {
			x = x - 10;
			c--;
		} else {
			x = x + 11;
			c++;
		}
		loop(x, c);
	}
}

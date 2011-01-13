void inc_loop(ref int x)
 case {
  x>=9 -> ensures "base":x'=x+1;
  x<9 ->  variance (1) [-x@-9]
		  ensures "loop":x'=10;
 }
{
	x = x + 1;
 	if (x<10) {
        inc_loop(x);
 	}
}

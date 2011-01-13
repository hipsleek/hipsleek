void loop(ref int x)
 case {
  x>11 -> 
     variance (1) [x@11]
     ensures "loop":x'=10;
   x<=11 -> 
     ensures "base":x'=x-1;
 }
{
	x = x - 1;
	if (x>10) {
		loop(x);
		return;
   	}
	else return;
}


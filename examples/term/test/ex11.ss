void loop(ref int x)
case {
  x<0 -> // variance 0,false (base case)
         ensures "r1":x'=x;
  x>=0 -> case {
         x>5 ->		variance (1)
					ensures "r2":x'<0;
         x<=2 ->	variance (2)
					ensures "r3":x'<0;
         x=3 ->		variance (4)
					ensures "r4":x'<0;
         4<=x<=5 -> variance (5)
                    ensures "r8":x'<0;
   }
}
{
	if (x >= 0) {
		x = -2*x + 10;
        loop(x);
	}
}

void loop2(ref int x)
case {
	x<0 -> ensures "r1": x'=x;
	x>=0 -> case {
				x>10 -> variance (1)
						ensures "r2":x'<0;
				x<=10 -> ensures "r3":false;
			}
}
{
	if (x >= 0) {
		x = -x + 10;
		loop2(x);
   }
}

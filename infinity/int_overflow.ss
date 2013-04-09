/*
As-If Infinitely Ranged Integer Model,
http://www.sei.cmu.edu/reports/10tn008.pdf
*/
/* Initialize si1 and si2 
if (si1 > 0){
if (si2 > 0) {
if (si1 > \inf - si2) {
}
}
else { 
if (si2 < (-\inf - si1)) {
}
}
} 
else {
if (si2 > 0) { 
if (si1 < (-\inf - si2)) {
}
}
else { 
if ((si1!=0) && (si2<(\inf -si1))) {
}
}
}*/

int add(int si1, int si2)
case { si1 > 0 -> case { si2 > 0 -> case { si1 > (\inf - si2) -> 
					ensures true & flow __Error;
				     si1 <= (\inf - si2) -> ensures res = si1 + si2;
				}
		   si2 <= 0 ->  case{ si2 < (-\inf - si1) ->
					ensures true & flow __Error;
				si2 >= (-\inf - si1) -> ensures res = si1 + si2;
				}
		}
 	si1 <= 0 -> case { si2 > 0 -> case { si1 < (-\inf - si2) -> 
				ensures true & flow __Error;
				     si1 >= (-\inf - si2) -> ensures res = si1 + si2;
				}
		     si2 <= 0 -> case { si1!=0 & si2 < (\inf - si1) -> 
				ensures true & flow __Error;
					si1=0 | si2 >= (\inf - si1) -> 
					ensures res = si1 + si2;}
		}
}
//requires true
//ensures res = si1 + si2;
{
int result;
result = si1 + si2;
return result;
}

int ex0(int x)
  requires x < 100
ensures res = x + 1;
{
	return x + 1;
}

int ex1(int x, int y)
requires x >0 & y > 0 & x + y < \inf
ensures res = x + y;
{
	return x + y;
}

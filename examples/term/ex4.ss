void inc_loop(ref int x)
 case {
 	x>=9 ->  requires true ensures x'=x+1; //'
  	x<9 ->  requires true ensures x'=10; //'
 }
// variance 10-x
{
	x=x+1;
 	if (x<10) {
   		assert (10-x)-(10-x')>0 & (10-x)>0;
   		inc_loop(x);
 	}
}

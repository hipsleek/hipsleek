void inc_loop(ref int x)
 case {
  x>=9 ->  requires true ensures "base":x'=x+1; //'
  x<9 ->  requires 10-x>=0
          // variance 10-x
          ensures "lp":x'=10; //'
 }
// variance 10-x
{
	x=x+1;
 	if (x<10) {
        assert "lp":(10-x)-(10-x')>0 /* & (10-x)>=0  */;
   		inc_loop(x);
 	}
}

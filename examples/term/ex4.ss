void inc_loop(ref int x)
 case {
  x>=9 ->  requires true ensures "base":x'=x+1; //'
  x<9 ->  requires 10-x>=0
          // variance -x
          // bound -10
          ensures "lp":x'=10; //'
 }
// variance 10-x
{
	x=x+1;
 	if (x<10) {
        assert "lp":-x + x' >0 /* & (10-x)>=0  */;
        assert "lp":-x'>-10;
   		inc_loop(x);
 	}
}

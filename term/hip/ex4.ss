void inc_loop(ref int x)
 case {
	 x>=9 -> requires true 
		 			 variance [0,0]
		 			 //variance
		 			 ensures "base":x'=x+1; //'
  	x<9 -> requires 10-x>=0
					 variance [0,1,10-x]
					 //variance [10-x]
           ensures "lp":x'=10; //'
 }
{
	x=x+1;
 	if (x<10) {
		assert "lp":-x + x' >0 /* & (10-x)>=0  */;
    assert "lp":-x'>-10;
   	inc_loop(x);
 	}
	//else return;
}

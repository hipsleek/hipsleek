void loop(ref int x, ref int y, int z)
case { 
  x<=0 -> // varterm false
          ensures "base":x'=x & y'=y;
  x>0 -> case {
   y>=0 -> case {
    z>=0 -> // varnonterm -1
            ensures "nt":false;
    z<0  -> //variance y 
            //varterm x>0 & y'<0 & z'<=0
      ensures "tm1":y'<0 & x'<=0 & y'<0; //'
    } 
   y<0 -> case {
     z>0 -> case {
       x+y<=0 -> // variance 0,x<=0
         ensures "dr":x'=x+y & y'=y+z;
       x+y>0  -> ensures "tm2":true;
       }
    z<=0 -> // variance x
            // varterm x<=0
      ensures "tm3":x'<x & y'<=y & x'<=0 & y'<0; 
    }
  }
}
{
   
	if (x > 0) {
      //if (y<0 && z<=0) loop_aux(x,y,z);
      //if (y<0 && z>=0 && x+y<0) loop_aux1(x,y,z);
		x = x + y;
		y = y + z;
        assert "tm3":x-x'>0;
        assert "tm3":true & (x'>=0 | x'<=0);
        // either well-founded or base case
       	assert "tm1":y-y'>0;
        assert "tm1":true & (y'>=0 | x'>0 & y'<0 & z'<=0);
        // either well-founded or terminating case tm3
        assert "dr": x'<=0;
        // indirect base case
		loop(x, y, z);
	}
}


 

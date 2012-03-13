void loop(ref int x, ref int y, int z)
case { 
  x<=0 -> requires Term 
          ensures "base": x'=x & y'=y;
  x>0 -> case {
  	y>=0 -> case {
    	z>=0 -> requires Loop
              ensures "nt": false;
    	z<0  -> requires Term[y]
              ensures "tm1":y'<0; //ensures x'<x & x'<=0; //true;
    } 
    y<0 -> case {
			z>=0 -> requires Term[-y] ensures "tm2": true;
      z<0 ->  requires Term[x]
              ensures "tm3":x'<x & y'<y & x'<=0;
    }
  }
}

{
	if (x > 0) {
    if (y<0 && z<=0) 
			loop_aux(x,y,z); // Terminating
		if (y<0 && z>=0 && x+y<0) 
			loop_aux1(x,y,z); // Terminating
		//dprint;	
		x = x + y;
		y = y + z;
    //assert "tm3":x-x'>0;
    //assert "tm1":y-y'>0;
		loop(x, y, z);
	}
}

void loop_aux(ref int x, ref int y, int z)
requires y<0 & z<=0
case {
	x>0 -> requires Term[x]
         ensures "dr":x'<x & y'<=y & x'<=0 & y'<0;
  x<=0 -> requires Term
          ensures "bs":x'=x & y'=y;
}
{   
	if (x > 0) {
		x = x + y;
		y = y + z;
    //assert "dr":x-x'>0;
		loop_aux(x, y, z);
	}
}

void loop_aux1(ref int x, ref int y, int z)
requires z>=0
case {
	x>0 -> requires y<0 & x+y<=0 & Term[x]
         ensures "dr":x'=x+y;
  x<=0 -> requires Term
					ensures "bs":x'=x & y'=y;
}
{   
	if (x > 0) {
		x = x + y;
		y = y + z;
    //assert "dr":x-x'>0;
		//if (y<0)
		loop_aux1(x, y, z);
	}
}

void loop(ref int x, int y)
case {
  x<=0 -> requires Term ensures x'=x;
  x>0 -> case {
		y>=0 -> requires Loop ensures false;
		y<0 -> requires Term[x] ensures x'<x & x'<=0;
	}
 
}
{
  if (x>0) {
      x=x+y; 
      loop(x,y); 
  }
}

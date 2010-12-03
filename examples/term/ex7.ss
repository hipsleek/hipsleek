void loop(ref int x, ref int y, int z)
case {
	x <= 0 ->
		//variance 0
		ensures x' = x;
	x > 0 -> case {
		y >= 0 -> case {
			z >= 0 -> 
				//variance -1
				ensures false;
			z < 0 ->
				//variance x
				ensures x' < x & x' <= 0;		
				//ensures false;
		}
		y < 0 -> case {
			z > 0 -> 
				//variance -1
				ensures false;
			z <= 0 ->
				//variance x
				ensures x' < x & x' <= 0;		
				//ensures false;
		}
	}
}
{
	if (x > 0) {
		x = x + y;
		y = y + z;
		loop(x, y, z);
	}
}

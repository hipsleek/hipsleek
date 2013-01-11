void loop(ref int x, ref int y, int z)
case {
	x<=0 -> requires Term ensures true;
	x>0 -> case {
		y<0 -> case {
			z<=0 -> requires Term[x] ensures true;
			z>0 -> requires MayLoop ensures true;
		}
		y>=0 -> case {
			z<0 -> requires Term[y] ensures true;
			z>=0 -> requires Loop ensures false;
		}
	}
}
{
	if (x > 0) {
		x = x + y;
		y = y + z;
		loop(x, y, z);
	} else return;
}

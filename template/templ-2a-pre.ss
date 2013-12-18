void loop (int x, int y)
	requires Term[y-x] // Verified with --term-dis-bnd-pre
	ensures true;
/*
	case {
		x >= y -> requires Term ensures true;
		x < y -> requires Term[y-x] ensures true;
	}
*/	
{
	if (x >= y) return;
  else loop (x+1, y);
}



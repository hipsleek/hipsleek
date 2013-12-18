template int r(int x, int y).

void loop (int x, int y)
	infer [r]
	requires Term[r(x, y)] // Inferred with --term-dis-bnd-pre
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



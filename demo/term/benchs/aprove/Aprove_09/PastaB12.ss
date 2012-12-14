int rand_int ()
requires Term
ensures true;

void main () 
requires Term
ensures true;
{
	int x = rand_int();
	int y = rand_int();
	loop(x, y);
}

void loop (ref int x, ref int y)
/*
case {
	!(x>0 | y>0) -> requires Term ensures true;
	(x>0 | y>0) -> case {
		x>0 -> requires Term[x] ensures true;
		x<=0 -> requires Term[y] ensures true;
	}
		//requires Term[x, y] ensures true; //ERR: not bounded
}
*/
/*
case {
	x<=0 -> case {
		y>0 -> requires Term[1,y] ensures true;
		y<=0 -> requires Term[0] ensures true;
	}
	x>0 -> requires Term[2,x] ensures true;
}
*/

case {
	x<=0 -> case {
		y>0 -> requires Term[y] ensures true;  // 0
		y<=0 -> requires Term ensures true;    // 0
	}
	x>0 -> case {
		y>0 -> requires Term[x] ensures true;  // 1
		y<=0 -> requires Term[x] ensures true; // 0
	}
}

{
	if (x > 0 || y > 0) {
		if (x > 0) {
			x--;
		} else if (y > 0) {
			y--;
		}
		loop(x, y);
	}
}

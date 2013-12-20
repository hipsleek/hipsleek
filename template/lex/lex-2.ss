/* Examples from "Ramsey vs. lexicographic termination proving " */

void loop (int x, int y, int d)
requires Term[y, x]
ensures true;
{
	if (x > 0 && y > 0 && d > 0) {
		if (rand_bool ()) { 
			x = x - 1;
			d = rand_int ();
			loop (x, y, d);
		} else {
			x = rand_int ();
			y = y - 1;
			d = d - 1;
			loop (x, y, d);
		}
	} else return;
}

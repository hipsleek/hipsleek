/* Examples from "Ramsey vs. lexicographic termination proving " */

void loop (int x, int y)
requires Term[y, x]
ensures true;
{
	if (x > 0 && y > 0) {
		if (rand_bool ()) { 
			x = x - 1;
			loop (x, y);
		} else {
			x = rand_int ();
			y = y - 1;
			loop (x, y);
		}
	} else return;
}

/* Examples from "Ramsey vs. lexicographic termination proving " */

void loop (int x, int y, int z)
requires Term[y, z, x]
ensures true;
{
	if (x > 0 && y > 0 && z > 0) {
		if (rand_bool ()) { 
			x = x - 1;
			loop (x, y, z);
		} else if (rand_bool ()) {
			y = y - 1;
			z = rand_int ();
			loop (x, y, z);
		} else {
			x = rand_int ();
			z = z - 1;
			loop (x, y, z);
		}
	} else return;
}

/* Examples from "Ramsey vs. lexicographic termination proving " */

template int r(int x, int y, int z).

void loop (int x, int y, int z)
infer [r]
requires Term[r(x, y, z)]
ensures true;
{
	if (x > 0 && y > 0 && z > 0) {
		if (rand_bool ()) { 
			x = x - 1;
			//z = rand_int ();
			loop (x, y, z);
		} else if (rand_bool ()) {
			x = rand_int ();
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

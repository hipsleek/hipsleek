int rand_int ()
requires Term
ensures true;

void main () 
requires Term
ensures true;
{
	int x = rand_int();
	int y = rand_int();
	int z = rand_int();
	iter(x, y, z);
}

void iter (int x, int y, int z) 
requires Term
ensures true;
{
	while (x + y + 3 * z >= 0) 
	case {
		x+y+3*z<0 -> requires Term ensures true;
		x+y+3*z>=0 -> requires Term[x+y+3*z] ensures true;
	}
	{
		if (x > y)
			x--;
	  else if (y > z) {
			x++;
			y -= 2;
	  }
	  else if (y <= z) {
			x = add(x, 1);
			y = add(y, 1);
			z = z - 1;
	  }
	}
}

int add(int v, int w) 
requires Term
ensures res = v+w;
{
	return v + w;
}


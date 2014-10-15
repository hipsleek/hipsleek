void loop (int i, int j, int n)
requires i+j=n+n & i<j & Loop
ensures false;
{
	if (i < j) {
		if (j > n + 1) {
			i++;
			j--;
		} else {
			i--;
			j++;
		}
		loop(i, j, n);
	}
}

void loop2 (int i, int j, int n)
requires i+j=n & i<j & Loop
ensures false;
{
	if (i < j) {
		if (j > n/2 + 1) {
			i++;
			j--;
		} else {
			i--;
			j++;
		}
		loop2(i, j, n);
	}
}

void main ()
requires MayLoop
ensures true;
{
	int i = 0;
	int j = rand_int();
	int n = j;

	while (i < j)
	case {
		i>=j -> requires Term ensures true;
		i<j -> requires i+j=n & Loop ensures false;
	}
	{
		if (j > n/2 + 1) {
			i++; 
			j--;
		} else {
			i--;
			j++;
		}
	}
}

int rand_int ()
requires Term
ensures true;

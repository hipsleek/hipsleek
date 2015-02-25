void main ()
requires Loop
ensures false;
{
	int j = 100;
	int i = 0;
	while (i < j)
	case {
		i>=j -> requires Term ensures true;
		i<j -> case {
			i=j-2 -> requires Loop ensures false;
			i>j-2 -> requires Term ensures true;
			i<j-2 -> requires Loop ensures false;
		}
	}
	{
		if (i < j - 2) {
			i++;
		} else if (i > j - 2) {
			return;
		} else {
			j++;
			i++;
		}
	}
}

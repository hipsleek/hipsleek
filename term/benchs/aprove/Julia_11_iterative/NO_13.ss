void main ()
requires MayLoop
ensures true;
{
	int j = 100;
	int i = 0;
	while (i < j)
	case {
		i>=j -> requires Term ensures true;
		i<j -> case {
			j>51 -> case {
				
			}
		}
	}
	{
		if (51 < j) {
			i++;
			j--;
		} else {
			i--;
			j++;
		}
	}
}

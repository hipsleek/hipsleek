void main ()
requires Loop
ensures false;
{
	int i = 0;
	while (i < 100)
	requires i>=0
	case {
		i>=100 -> requires Term ensures true;
		i<100 -> requires Loop ensures false;
	}
	{
		if (i < 0) {
			int j = 0;
			while (j < 15)
			case {
				j>=15 -> requires Term ensures true;
				j<15 -> requires Term[15-j] ensures true;
			}
			{
				j++;
			}
			return;
		} else {
			int j = 0;
			while (j < 15)
			case {
				j>=15 -> requires Term ensures true;
				j<15 -> requires Loop ensures false;
			}
			{
				j = j + 0;
			}
		}
		i++;
	}
}

void main ()
requires Term
ensures true;
{
	int i = 0;
	while (i < 10)
	case {
		i>=10 -> requires Term ensures true;
		i<10 -> requires Term[10-i] ensures true;
	}
	{
		int j = 3;
		while (j < 12)
        /* //the analysis finds out that i'=i seems to be redundant */
		/* case { */
		/* 	j>=12 -> requires Term ensures i'=i; */
		/* 	j<12 -> requires Term[12-j] ensures i'=i; */
		/* } */
		case {
			j>=12 -> requires Term ensures true;
			j<12 -> requires Term[12-j] ensures true;
		}
		{
			j = j - 1;
			j = j + 2;
		}
		i++;
	}
}

void for_5 (ref int i, ref int j, ref int k, ref int l)
requires i>=0 & j>=0 & k>=0 & l>=0 & Loop
ensures false;
{
	int m = i+j+k+l+1000;
	while (m >= 0)
	case {
		m<0 -> requires Term ensures true;
		m>=0 -> requires Loop ensures false;
	}
	{
		m = m - 0;
	}
}

void for_4 (ref int i, ref int j, ref int k, ref int b)
requires i>=0 & j>=0 & k>=0 & b>0 & Loop
ensures false;
{
	int l = 0;
	while (l < b)
	requires i>=0 & j>=0 & k>=0 & l>=0
	case {
		l>=b -> requires Term ensures true;
		l<b -> requires Loop ensures false;
	}
	{
		for_5(i, j, k, l);
		l++;
	}
}

void for_3 (ref int i, ref int j)
requires i>=0 & j>=0 & Loop
ensures false;
{
	int k = i+j+3;
	while (k >= 0)
	requires i>=0 & j>=0
	case {
		k<0 -> requires Term ensures true;
		k>=0 -> requires Loop ensures false;
	}
	{
		int b = i+j+k+4;
		for_4(i, j, k, b);
		k--;
	}
}

void for_2 (ref int i, ref int a)
requires i>=0 & a>0 & Loop
ensures false;
{
	int j = 0;
	while (j < a)
	requires i>=0 & j>=0
	case {
		j>=a -> requires Term ensures true;
		j<a -> requires Loop ensures false;
	}
	{
		for_3(i, j);
		j++;
	}
}

void for_1 ()
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
		int a = i+2;
		for_2(i, a);
		i++;
	}
}

void main ()
requires Loop
ensures false;
{
	for_1();
}

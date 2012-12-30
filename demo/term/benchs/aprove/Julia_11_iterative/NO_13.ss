void main ()
requires Loop
ensures false;
{
	int j = 100;
	int i = 0;
	while (i < j)
	requires i+j=100 & i<j & Loop
	ensures false;
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

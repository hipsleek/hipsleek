void loop (ref int i, ref int j, ref int k)
case {
	i>100 -> requires Term ensures true;
	i<=100 -> case {
		j>100 -> requires Term ensures true;
		j<=100 -> requires Term[200-i-j] ensures true;
	}
}
{
	if (i <= 100) {
		int t = i;
		i = j;
		j = t + 1;
		k--;
		loop(i, j, k);
	}
}

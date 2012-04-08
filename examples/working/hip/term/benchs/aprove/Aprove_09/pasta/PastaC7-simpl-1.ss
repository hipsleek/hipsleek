void loop (ref int i, ref int j, ref int k)
case {
	j>k -> requires Term ensures true;
	j<=k -> case {
		k<=i+1 -> requires Term ensures true;
		k>i+1 -> requires Term[2*k-i-j] ensures true;
	}
}
{
	if (j <= k) {
		int t = i;
		i = j;
		j = t + 1;
		k--;
		loop(i, j, k);
	}
}

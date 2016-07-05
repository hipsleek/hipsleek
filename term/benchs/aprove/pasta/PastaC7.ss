int rand_int ()
requires Term
ensures true;

void main ()
requires Term
ensures true;
{
	int i = rand_int();
	int j = rand_int();
	int	k = rand_int();
		
	loop(i, j, k);
}

void loop (ref int i, ref int j, ref int k)
case {
	!(i<=100 & j<=k) -> requires Term ensures true;
	(i<=100 & j<=k) -> case {
		(j>100 | k<=i+1) -> requires Term ensures true;
		!(j>100 | k<=i+1) -> requires Term[k+100-i-j] ensures true;
	}
}
{
	if (i <= 100 && j <= k) {
		int t = i;
		i = j;
		j = t + 1;
		k--;
		loop(i, j, k);
	}
}

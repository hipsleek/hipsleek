int middle (int i, int j)
case {
	i=j -> requires Term ensures res=i;
	i!=j -> case {
		i<j -> requires Loop ensures false;
		i>=j -> case {
			exists (m: i-j=2*m) -> requires Term[i-j] ensures res=(i+j)/2;
			exists (n: i-j=2*n+1) -> requires Loop ensures false;
		}
	}
}
{
	if (i != j) {
		i--;
		j++;
		return middle(i, j);
	}
	return i;
}

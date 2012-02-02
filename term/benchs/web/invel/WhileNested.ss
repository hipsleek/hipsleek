void increase (int i)
case {
	i>=10 -> requires Term ensures true;
	i<10 -> requires Loop ensures false;
}
{
	int j;
	loop_1 (i, j);
}

void loop_1 (ref int i, ref int j)
case {
	i>=10 -> requires Term ensures i'=i & j'=j;
	i<10 ->
		requires Loop ensures false; // OK
		//requires Term[10-i] ensures false; // ERR
}
{
	if (i < 10) {
		j = i;
		loop_2(i, j);
		i++;
		loop_1(i, j);
	}
}

void loop_2 (ref int i, ref int j)
case {
	j<=0 -> requires Term ensures i'=i & j'=j;
	j>0 -> requires Loop ensures false;
}
{
	if (j > 0) {
		j++;
		loop_2(i, j);
	}
}

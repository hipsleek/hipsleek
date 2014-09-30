void loop (int i, int j)
requires Loop 
ensures false;
{
	if (i < j)
		i = i + 4;
	else {
		j = j + 1;
		i = i + 2;
	}
	loop(i, j);
}


int loop (int i)
requires i=10 
ensures res = 9;
{
	while (true) 
	requires i=10
	ensures i'=9 ;
	{
		i--;
		break ;
	}
	return i;

}

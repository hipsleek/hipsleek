/*
 * When trying to assign a value to a matrix column,
 * the following exception occurs
 * int[][]~int has invalid argument types
 */
int main(void)
{
	int a[100][100], i, j;
	for (i = 0; i < 100; i++)
		for (j = 0; j < 100; j++)
			a[i][j] = i + j;
	return 0;
}

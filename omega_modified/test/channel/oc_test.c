#include <stdio.h>

int main()
{
	char buffer[100];
	fprintf(stdout, "oc_test==> hello\n");
	fflush(stdout);
	fscanf(stdin, "%s", buffer);
	
	fprintf(stdout, "oc_test==>%s\n", buffer);
	
	return 0;
}
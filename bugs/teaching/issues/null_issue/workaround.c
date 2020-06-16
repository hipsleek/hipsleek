#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include "annotations.h"

int main(void)
{	
	int *x = NULL;
	if (x != (int *)NULL)
		*x = 10;
	return 0;
}

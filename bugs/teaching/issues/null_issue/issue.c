#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include "annotations.h"

/* 
 * When comparing a pointer with NULL, the following exception occurs
 * int_star~void_star has invalid argument types
 * the solution is to cast NULL to the pointer type, in this case (int *)
 */
int main(void)
{	
	int *x = NULL;
	if (x != NULL)
		*x = 10;
	return 0;
}

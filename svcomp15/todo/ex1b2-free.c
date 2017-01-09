#include "stdlib.h"

typedef struct {
    int *lo;
} TData;

static void alloc_data(TData *pdata)
{
  //   pdata->lo = (int *)malloc(sizeof(int));
}

int main() {
    TData data;
     alloc_data(&data);
    return 0;
}

/*




*/

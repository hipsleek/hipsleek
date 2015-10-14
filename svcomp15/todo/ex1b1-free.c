#include "stdlib.h"


typedef struct {
    int *lo;
} TData;

static void free_data(TData data)
{
   free(data.lo);
}

int main() {
    TData data;
    free_data(data);
    return 0;
}

/*
ERROR: at ../todo/ex1b-free.c_26:4_26:12
Message: trans_exp :: case CallNRecv :: procedure call free$int_star has invalid argument types (exc)

 */

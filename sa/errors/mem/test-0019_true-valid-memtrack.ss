//extern void __VERIFIER_error() __attribute__ ((__noreturn__));

//#include <stdlib.h>

/*
typedef struct {
    void *lo;
    void *hi;
} TData;

 */
data int_ref {int v};

data TData {
    int_ref lo;
    int_ref hi;
};

/*

static void alloc_data(TData *pdata)
{
    pdata->lo = malloc(16);
    pdata->hi = malloc(24);
}

 */

void alloc_data(TData pdata)
{
    pdata.lo = new(16);
    pdata.hi = new(24);
}


/*
static void free_data(TData *data)
{
    void *lo = data->lo;
    void *hi = data->hi;

    if (lo == hi) {
        free(lo);
        free(hi);
    }

    data->lo = NULL;
    data->hi = NULL;
}

true
static void free_data(TData data)
{
    void *lo = data.lo;
    void *hi = data.hi;

    if (lo == hi)
        return;

    free(lo);
    free(hi);
}
 */
void free_data(TData data)
{
    int_ref lo = data.lo;
    int_ref hi = data.hi;

    if (lo == hi) {
      return;
    }

    free(lo);
    free(hi);
}

/*false
int main() {
    TData data;
    alloc_data(&data);
    free_data(&data);
    return 0;
}

//true
int main() {
    TData data;
    alloc_data(&data);
    free_data(data);
    return 0;
}

 */
int main() {
    TData data;
    alloc_data(data);
    free_data(data);
    return 0;
}

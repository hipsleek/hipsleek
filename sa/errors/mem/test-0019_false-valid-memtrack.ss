//extern void __VERIFIER_error() __attribute__ ((__noreturn__));

//#include <stdlib.h>

/*
typedef struct {
    void *lo;
    void *hi;
} TData;

 */

data int_ref {int v}

data TData {
  int_ref lo;
  int_ref hi;
}

void freei (ref int_ref a)
  requires a::int_ref<_> ensures emp & a'=null;//'

/*
static void alloc_data(TData *pdata)
{
    pdata->lo = malloc(16);
    pdata->hi = malloc(24);
}
*/

void alloc_data(TData pdata)
  requires pdata::TData<_,_>
  ensures pdata::TData<l,h> * l::int_ref<16> * h::int_ref<24>;
{
    pdata.lo = new int_ref(16);
    pdata.hi = new int_ref(24);
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

void free_data(TData pdata)
  requires pdata::TData<l,h>
 case {
  l=h -> requires  l::int_ref<_> ensures pdata::TData<null,null>;
  l!=h -> requires  l::int_ref<_> * h::int_ref<_> ensures pdata::TData<null,null>;
}
{
    int_ref lo = pdata.lo;
    int_ref hi = pdata.hi;

    if (lo == hi) {
        freei(lo);
        freei(hi);
    }

    pdata.lo = null;
    pdata.hi = null;
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
int main()
  requires true
  ensures emp & true;
{
    TData pdata;
    alloc_data(pdata);
    free_data(pdata);
    return 0;
}

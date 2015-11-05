//#include "stdlib.h"

data int_star_u {
  int val;
}

data TData {
    int_star_u lo;
    int_star_u hi;
}

HeapPred H1(TData a).
  PostPred G1(TData b).

  void alloc_data(TData@R pdata)
  infer[G1,@classic,@pure_field] requires pdata::TData<_,_> ensures G1(pdata'); //'
//  infer[G1] requires H1(pdata) ensures G1(pdata,pdata'); //'
{
  pdata.lo = new int_star_u(0);
  pdata.hi =  new int_star_u(0);

  pdata.lo.val = 4;
  pdata.hi.val = 8;
}

int_star_u free1(int_star_u x)
  requires x::int_star_u<_> ensures res=null;

HeapPred H2(TData a).
PostPred G2(TData a).

void free_data(TData@R data1)
                                                                       infer[G2,@classic,@pure_field] requires data1::TData<ia,ib>*ia::int_star_u<4>*ib::int_star_u<8> ensures G2(data1'); //'
                                                                  //  infer[H2,G2] requires H2(data1) ensures G2(data1, data1'); //'
{
    int_star_u lo = data1.lo;
    int_star_u hi = data1.hi;

    if (lo.val > hi.val)
        return;

    free1(lo);
    free1(hi);
}

int main( )
                                                                                                                                                                                  requires emp & true ensures emp & true;
 {
   TData data1 = new TData(null,null);
    alloc_data(data1);
    free_data(data1);
    return 0;
}

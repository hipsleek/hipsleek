//relation update_array(int[] a, int[] r, int v, int i).
// Any relation with prefix of "update_array" will be translated into "store".

/*
  
int[] update_arr(int[] a, int i, int v)
  requires true
  ensures update_array(a,res,v,i);

int array_get(int[] a, int i) 
   requires true 
   ensures res = a[i];
// a[i] will be translated into "select"

*/

// !!!! This function need to use -prelude "prelude_aux.ss" 
int foo(int x)
  requires true
  ensures res=x+1;
{
  int[] a;
  //a = update_arr(a,5,x+1);
  a[5] = x+1;
  //a = update___1d(x+1,a,5);
  int r;
  r = a[5];
  //dprint;
  return r;

}


void loop(ref int[] a)
  requires a[5] > 0
  ensures a'[5] = 0;
{
  //foo2(a);
  while(a[5]>0)
    requires true
    ensures (a[5]>0 & a'[5]=0) | (a[5]<=0 & a'[5]=a[5]);
    {
      a[5] = a[5] -1;
      //a = update_arr(a,5,a[5]-1);
      
  }

}

void foo2(ref int[] a)
  requires true
  ensures (a[5]>0 & a'[5]=0) | (a[5]<=0 & a'[5]=a[5]);
{ 
  if (a[5]>0) {
    //a = update_arr(a,5,0);
    a[5] = 0;
    foo2(a);
  }
}

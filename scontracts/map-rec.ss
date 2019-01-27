hip_include 'scontracts/mapprimitives.ss'

global int i = 0;
global mapping(int => int) test;
global int n = 100;

void foorec()
     case {
       i<n  ->
           requires [ts0] test::Map<ts0>
           ensures  (exists ts1: test::Map<ts1> & ts1[i] = 0);  //Store(ts0,ts1,i,0));
       i>=n ->
           requires true
           ensures  true;
     }
{
  if(i >= n) return;
  else{
    dprint;
    test[i] = 0;
    foorec(i+1);
  }
}

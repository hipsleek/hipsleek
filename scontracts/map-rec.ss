hip_include 'scontracts/mapprimitives.ss'

global int i = 0;
global mapping(int => int) test;
global int n = 100;

void foorec1()
     case {
       i<n  ->
           requires [ts0] test::Map<ts0>
           ensures  (exists ts1: test::Map<ts1> & ts1[i] = 0 & i < n); //& Store(ts0,ts1,i,0));
       i>=n ->
           requires true
           ensures  true;
     }
{
  if(i >= n) return;
  else{
    dprint;
    test[i] = 0;
    //dprint;
    i = i + 1;
    dprint;
    foorec1();
  }
}

void foorec2(int m)
     case {
       m<n  ->
           requires [ts0] test::Map<ts0>
           ensures  (exists ts1: test::Map<ts1> & ts1[m] = 0 & m<n); //& Store(ts0,ts1,i,0));
       m>=n ->
           requires true
           ensures  true;
     }
{
  if(m >= n) return;
  else{
    //dprint;
    test[m] = 0;
    //dprint;
    foorec2(m+1);
  }
}
// Post condition cannot be derived:
//   (may) cause:  Type(test_33,ts0) & Type(test_33,mp2_2125) & Type(test_33,ts1_2137) &
//  m<n_32 & m<n_32 & Store(ts0,mp2_2125,m,0) & (1+m)<n_32 & ts1_2137[1+m]=0 |-  ts1_2137[m]=0. LOCS:[40;11;27;29;37;22;42;31] (may-bug)


void foorec3(mapping(int => int) test, int m)
     case {
       m<n  ->
           requires [ts0] test::Map<ts0>
           ensures  (exists ts1: test::Map<ts1> & ts1[m] = 0); //& Store(ts0,ts1,i,0));
       m>=n ->
           requires true
           ensures  true;
     }
{
  if(m >= n) return;
  else{
    //dprint;
    test[m] = 0;
    //dprint;
    foorec3(test, m+1);
  }
}





/*
void foorec(mapping(int => int) test, int i)
     case {
       i<n  ->
           requires [ts0] test::Map<ts0>
           ensures  (exists ts1: test::Map<ts1> & ts1[i] = 0);  //Store(ts0,ts1,i,0));
       i>=n ->
           requires true
           ensures  true;
     }
{
// test::Map<ts0> & i<n
  if(i >= n) return;  // test::Map<ts0> & i<n & i>=n |- false
// test::Map<ts0> & i<n & i<n
  else{
    test[i] = 0; // test::Map<ts0> & i<n |- test[i]  (index i of test should have a value)  ----- field update
    //
    //i = i + 1;
    foorec(test, i+1);
  }
}
*/

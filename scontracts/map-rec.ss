hip_include 'scontracts/mapprimitives.ss'

global int i = 0;
global mapping(int => int) test;
global int n = 100;

void foorec1()
     case {
       i<n  ->
           requires [ts0] test::Map<ts0>
           ensures  (exists ts1: test::Map<ts1> & ts1[i] = 0 & i' = i+1); //& Store(ts0,ts1,i,0));
       i>=n ->
           requires true
           ensures  true;
     }
{
  if(i >= n) return;
  else{
    //dprint;
    test[i] = 0;
    //dprint;
    i = i + 1;
    foorec1();
  }
}
/*
Post condition cannot be derived:
  (may) cause:  i_29<n_30 & Type(test_31,ts0) & Store(ts0,mp2_2084,i_29,0) &
 (1+i_29)<n_30 & Type(test_31,mp2_2084) & Type(test_31,ts1_2096) &
 i_29<n_30 & ts1_2096[1+i_29]=0 |-  ts1_2096[i_29]=0. LOCS:[20;17;22;23;7;9;11] (may-bug)
*/

void foorec2(ref int m)
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
    m = m + 1;
    foorec2(m);
  }
}
/*
Post condition cannot be derived:
OrL[
  (may) cause:  n_33<=i_32 & Type(test_34,ts0) & m<n_33 |-  ts0[m]=0. LOCS:[37;11;27;29;31] (may-bug),
  (may) cause:  i_32<n_33 & Type(test_34,ts0) & Type(test_34,mp2_2126) &
 Type(test_34,ts1_2140) & m<n_33 & Store(ts0,mp2_2126,m,0) & i_32<(1+m) &
 ts1_2140[i_32]=0 |-  ts1_2140[m]=0. LOCS:[40;37;27;29;22;42;11;31] (may-bug)
]
*/


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

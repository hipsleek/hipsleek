hip_include 'scontracts/mapprimitives.ss'

global int i = 0;
global int m = 20; // The number of the values which need to be updated
global mapping(int => int) test;
global int n = 100; //

void foorec1()
     case {
       m<n  ->
            case {
               i<m  ->
                 requires [ts0] test::Map<ts0>
                 ensures  (exists ts1: test::Map<ts1> & ts1[i] = 0); //& Store(ts0,ts1,i,0));
               i>=m ->
                 requires true
                 ensures  true;
            }
       m>=n ->
            case {
               i<n  ->
                 requires [ts0] test::Map<ts0>
                 ensures  (exists ts1: test::Map<ts1> & ts1[i] = 0); //& Store(ts0,ts1,i,0));
               i>=n ->
                 requires true
                 ensures  true;
            }
     }
{
  if(i >= m || i >= n) return;
  else{
    dprint;
    test[i] = 0;
    //dprint;
    i = i + 1;
    dprint;
    foorec1();
  }
}

// dprint(simpl): map-rec.ss:19: ctx:  List of Failesc Context: [FEC(0, 0, 1  [(,1 ); (,2 )])]
//  Successful States:
//  [
//   Label: [(,1 ); (,2 )]
//   State:
//      test_31::Map<ts0>@M&test_31'=test_31 & i_29'=i_29 & n_30'=n_30 & i_29<n_30&
// {FLOW,(4,5)=__norm#E}
//   ]

// !!! **typechecker.ml#2468:NO REENTRANCY
// !!! **typechecker.ml#2468:NO REENTRANCY
// dprint(simpl): map-rec.ss:23: ctx:  List of Failesc Context: [FEC(0, 0, 1  [(,1 ); (,2 )])]
//  Successful States:
//  [
//   Label: [(,1 ); (,2 )]
//   State:
//      test_31'::Map<mp2_2144>@M&
// test_31'=test_31 & i_29'=i_29+1 & n_30'=n_30 & i_29<n_30 &
// Store(ts0,mp2_2144,i_29,0) & Type(test_31,ts0)&{FLOW,(4,5)=__norm#E}
//   ]

// Post condition cannot be derived:
//   (may) cause:  Store(ts0,mp2_2144,i_29,0) & Type(test_31,ts0) & Type(test_31,mp2_2144) &
//  Type(test_31,ts1_2158) & i_29<n_30 & i_29<n_30 & ts1_2158[1+i_29]=0 &
//  (1+i_29)<n_30 |-  ts1_2158[i_29]=0. LOCS:[20;24;22;17;9;7;11] (may-bug)


// dprint(simpl): map-rec.ss:69: ctx:  List of Failesc Context: [FEC(0, 0, 1  [(,1 ); (,2 )])]
//  Successful States:
//  [
//   Label: [(,1 ); (,2 )]
//   State:
//      test_33::Map<ts0>@M&test_33'=test_33 & m'=m & n_32'=n_32 & m<n_32&
// {FLOW,(4,5)=__norm#E}
//   ]

// !!! **typechecker.ml#2468:NO REENTRANCY
// dprint(simpl): map-rec.ss:72: ctx:  List of Failesc Context: [FEC(0, 0, 1  [(,1 ); (,2 )])]
//  Successful States:
//  [
//   Label: [(,1 ); (,2 )]
//   State:
//      (exists mp2_2138: test_33'::Map<mp2_2138>@M&
// test_33'=test_33 & m'=m & n_32'=n_32 & m<n_32 & Store(ts0,mp2_2138,m',0) &
// Type(test_33,ts0)&{FLOW,(4,5)=__norm#E})
//   ]

// Post condition cannot be derived:
//   (may) cause:  Type(test_33,ts0) & Type(test_33,mp2_2146) & Type(test_33,ts1_2156) &
//  Store(ts0,mp2_2146,m,0) & m<n_32 & m<n_32 & ts1_2156[1+m]=0 & (1+m)<n_32 |-  ts1_2156[m]=0. LOCS:[73;70;11;22;67;59;57;61] (may-bug)

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
    dprint;
    test[m] = 0;
    //dprint;
    dprint;
    foorec2(m+1);
  }
}

// dprint(simpl): map-rec.ss:69: ctx:  List of Failesc Context: [FEC(0, 0, 1  [(,1 ); (,2 )])]
//  Successful States:
//  [
//   Label: [(,1 ); (,2 )]
//   State:
//      test_33::Map<ts0>@M&test_33'=test_33 & m'=m & n_32'=n_32 & m<n_32&
// {FLOW,(4,5)=__norm#E}
//   ]

// !!! **typechecker.ml#2468:NO REENTRANCY
// dprint(simpl): map-rec.ss:72: ctx:  List of Failesc Context: [FEC(0, 0, 1  [(,1 ); (,2 )])]
//  Successful States:
//  [
//   Label: [(,1 ); (,2 )]
//   State:
//      (exists mp2_2138: test_33'::Map<mp2_2138>@M&
// test_33'=test_33 & m'=m & n_32'=n_32 & m<n_32 & Store(ts0,mp2_2138,m',0) &
// Type(test_33,ts0)&{FLOW,(4,5)=__norm#E})
//   ]

// Post condition cannot be derived:
//   (may) cause:  Type(test_33,ts0) & Type(test_33,mp2_2146) & Type(test_33,ts1_2156) &
//  Store(ts0,mp2_2146,m,0) & m<n_32 & m<n_32 & ts1_2156[1+m]=0 & (1+m)<n_32 |-  ts1_2156[m]=0. LOCS:[73;70;11;22;67;59;57;61] (may-bug)




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

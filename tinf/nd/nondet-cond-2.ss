void loop(int x)
{
  if (x>=0 && (__VERIFIER_nondet_int() > 0)) {
  //if (x >= 0) {
    x = x + 1;
    loop(x);
  }
}

/*
Temporal Assumptions:
 termAssume x'<0 & x'=x & !(v_boolean_3_1461) & x'<0 & v_int_3_1442<=0 & 
!(v_boolean_3_1462) & v_int_3_1442<=0 & !(v_bool_3_1397') & 
!(v_boolean_3_1461) & !(v_bool_3_1397') --> looppost_1389(x).

 termAssume x'<0 & x'=x & !(v_boolean_3_1459) & x'<0 & 0<v_int_3_1441 & 
v_boolean_3_1460 & 0<v_int_3_1441 & !(v_bool_3_1397') & 
!(v_boolean_3_1459) & !(v_bool_3_1397') --> looppost_1389(x).

 termAssume 0<=x' & x'=x & v_boolean_3_1457 & 0<=x' & v_int_3_1440<=0 & 
!(v_boolean_3_1458) & v_int_3_1440<=0 & !(v_bool_3_1397') & 
!(v_boolean_3_1458) & v_boolean_3_1457 & 
!(v_bool_3_1397') --> looppost_1389(x).

 termAssume x'=1+x_1454 & v_bool_3_1397' & v_boolean_3_1452 & 
v_boolean_3_1453 & v_bool_3_1397' & 0<v_int_3_1439 & v_boolean_3_1453 & 
0<v_int_3_1439 & 0<=x_1454 & v_boolean_3_1452 & x_1454=x & 
0<=x_1454 & looppost_1389(x') --> looppost_1389(x).

 termAssume 0<=x_1454 & x_1454=x & v_boolean_3_1452 & 0<=x_1454 & 
0<v_int_3_1439 & v_boolean_3_1453 & 0<v_int_3_1439 & v_bool_3_1397' & 
v_boolean_3_1453 & v_boolean_3_1452 & v_bool_3_1397' & x'=1+
x_1454 & looppre_0(x) --> looppre_0(x').

========================================================================
 termAssume x'<0 & x'=x & !(v_bool_4_1393') & x'<0 & 
!(v_bool_4_1393') --> looppost_1389(x).

 termAssume x'=1+x_1422 & v_bool_4_1393' & 0<=x_1422 & v_bool_4_1393' & 
x_1422=x & 0<=x_1422 & looppost_1389(x') --> looppost_1389(x).

 termAssume 0<=x_1422 & x_1422=x & v_bool_4_1393' & 0<=x_1422 & 
v_bool_4_1393' & x'=1+x_1422 & looppre_0(x) --> looppre_0(x').

*/

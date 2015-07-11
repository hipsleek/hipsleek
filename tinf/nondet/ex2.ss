void f(int x) 
/*
  case {
    x < 0 -> requires Term ensures true;
    x >= 0 -> requires Loop ensures true;
  }
*/
{
  if (x < 0) return;
  else {
    int bbb = __VERIFIER_nondet_int();
    int ccc = __VERIFIER_nondet_int();
    //assume ccc' <= 0;
    //assume bbb' <= 0;
    //infer_assume [bbb, ccc];
    dprint;
    if (bbb > 0) {dprint;
    //if (__VERIFIER_nondet_int() > 0)
      f(x - 1);}
    else
      f(x + 1);
    dprint;
  }
  dprint;
}

/*
termAssume not(v_bool_6_1408') & not(v_bool_2_1409') & 0<=x' & x'=x & 
            nondet_int__(b_1481) & b_1481<=0 & v_int_9_1482=1+x' & fpost{1447}(v_int_9_1482) --> fpost{1447}(x).

termAssume v_bool_6_1408' & not(v_bool_2_1409') & 0<=x' & x'=x & 
            nondet_int__(b_1479) & 0<b_1479 & v_int_7_1480+1=x' & fpost{1447}(v_int_7_1480) --> fpost{1447}(x).

termAssume v_bool_2_1409' & x'<0 & x'=x --> fpost{1447}(x).

termAssume not(v_bool_6_1408') & not(v_bool_2_1409') & 0<=x' & x'=x & 
            nondet_int__(b') & b'<=0 & v_int_9_1407'=1+x' & fpre{0}(x) --> fpre{0}(v_int_9_1407').

termAssume v_bool_6_1408' & not(v_bool_2_1409') & 0<=x' & x'=x & 
            nondet_int__(b') & 0<b' & v_int_7_1401'+1=x' & fpre{0}(x) --> fpre{0}(v_int_7_1401').

========================================================================

termAssume not(v_bool_6_1411') & b_1478<=0 & nondet_int__(b_1478) & x'=x & 
            0<=x' & not(v_bool_2_1412') & v_int_9_1479=1+x' & fpost{1447}(v_int_9_1479) --> fpost{1447}(x).

termAssume v_bool_2_1412' & x'<0 & x'=x --> fpost{1447}(x).

termAssume not(v_bool_6_1411') & b'<=0 & nondet_int__(b') & x'=x & 0<=x' & 
            not(v_bool_2_1412') & v_int_9_1410'=1+x' & fpre{0}(x) --> fpre{0}(v_int_9_1410').
            
========================================================================

not(v_bool_6_1408') & not(v_bool_2_1409') & 0<=x' & x'=x & 
 nondet_int__(b') & b'<=0 & v_int_10_1407'=1+x': fpre{14}(x) --> fpre{14}(v_int_10_1407')
 
v_bool_6_1408' & not(v_bool_2_1409') & 0<=x' & x'=x & nondet_int__(b') & 
 0<b' & v_int_8_1401'+1=x': fpre{14}(x) --> fpre{14}(v_int_8_1401')

v_bool_6_1408' & not(v_bool_2_1409') & 0<=x' & x'=x & nondet_int__(b') & 
 0<b' & v_int_8_1401'+1=x': fpre{14}(x) --> fpre{9}(v_int_8_1401')

*/

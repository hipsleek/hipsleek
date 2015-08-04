int rand()
  requires Term
  ensures true;

void f(int xx) 
/*
  case {
    xx < 0 -> requires Term ensures true;
    xx >= 0 -> requires Loop ensures true;
  }
*/
{
  if (xx < 0) return;
  else {
    xx = __VERIFIER_nondet_int();
    int yy = rand();
    //infer_assume [xx];
    //assume xx' >= 0;
    f(xx);
  }
}

/*

 termAssume not(v_bool_2_1396') & 0<=x_1431 & x_1431=x & 
            nondet_int__(v_int_4_1434) & x'=1+v_int_4_1434 & fpost{1417}(x') --> fpost{1417}(x).

 termAssume v_bool_2_1396' & x'<0 & x'=x --> fpost{1417}(x).

 termAssume not(v_bool_2_1396') & 0<=x_1431 & x_1431=x & 
            nondet_int__(v_int_4_1434) & x'=1+v_int_4_1434 & fpre{0}(x) --> fpre{0}(x').

========================================================================

 termAssume 0<=x' & x'=1+v_int_4_1436 & nondet_int__(v_int_4_1436) & 
            x_1433=x & 0<=x_1433 & not(v_bool_2_1398') & fpost{1419}(x') --> fpost{1419}(x).

 termAssume v_bool_2_1398' & x'<0 & x'=x --> fpost{1419}(x).

 termAssume 0<=x' & x'=1+v_int_4_1436 & nondet_int__(v_int_4_1436) & 
            x_1433=x & 0<=x_1433 & not(v_bool_2_1398') & fpre{0}(x) --> fpre{0}(x').

*/

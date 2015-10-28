
// ../hip ex1a-varclr.c --witness-gen "main:1,1"


extern void __VERIFIER_error();
extern int __VERIFIER_nondet_int();


int main(void) {
  int n = 3;
  int m = __VERIFIER_nondet_int();
  if (n>2 && m<1) {
  ERROR: __VERIFIER_error();
  }
  return 0;
}


/*

***********************************
********* input cil file **********
#line 3 "ex1b-if-complex.c"
extern void __VERIFIER_error() ;


#line 4
extern int __VERIFIER_nondet_int() ;


#line 7 "ex1b-if-complex.c"
int main(void)
{
  int n ;
  int m ;
  int tmp ;

  {
#line 8
  n = 3;
#line 9
  tmp = __VERIFIER_nondet_int();
#line 9
  m = tmp;
#line 10
  if (n > 2) {
#line 10
    if (m < 1) {
#line 11
      __VERIFIER_error();
    }
  }
#line 13
  return (0);
}
}

******** end of cil file **********



 */


// ../hip ex1a-varclr.c --witness-gen "main:"
extern void __VERIFIER_error();
extern int __VERIFIER_nondet_int();


int main(void) {
  int n = 3;
 ERROR: __VERIFIER_error();
}


/*
***********************************
********* input cil file **********
#line 3 "ex1a-varclr.c"
extern void __VERIFIER_error() ;


#line 7 "ex1a-varclr.c"
int main(void)
{
  int n ;

  {
#line 8
  n = 3;
#line 9
  __VERIFIER_error();
}
}

******** end of cil file **********


 */

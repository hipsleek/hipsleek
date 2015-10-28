extern void __VERIFIER_error() __attribute__ ((__noreturn__));

/*
 * Implementation the McCarthy 91 function.
 * http://en.wikipedia.org/wiki/McCarthy_91_function
 * 
 * Author: Matthias Heizmann
 * Date: 2013-07-13
 * 
 */

extern int __VERIFIER_nondet_int(void);


int f91(int x) {
    if (x > 100)
        return x -10;
    else {
        return f91(f91(x+11));
    }
}


int main() {
    int x = __VERIFIER_nondet_int();
    int result = f91(x);
    if (result == 91 || (x > 102 && result == x - 10)) {
        return 0;
    } else {
    ERROR:  __VERIFIER_error();
    }
    /* if (result == 91) */
    /*   return 0; */
    /*   else if (x > 102){ */
    /*     if (result == x - 10) { */
    /*     return 0; */
    /*     } */
    /*     else __VERIFIER_error(); */
    /*   } */
    /*   else { */
    /*     __VERIFIER_error(); */
    /*   } */
}

/*
int main(void) 
{ 
  int x ;
  int tmp ;
  int result ;
  int tmp___0 ;

  {
#line 25
  tmp = __VERIFIER_nondet_int();
#line 25
  x = tmp;
#line 26
  tmp___0 = f91(x);
#line 26
  result = tmp___0;
#line 27
  if (result == 91) {
#line 28
    return (0);
  } else
#line 27
  if (x > 102) {
#line 27
    if (result == x - 10) {
#line 28
      return (0);
    } else {
#line 27
      goto ERROR;
    }
  } else {
    ERROR: 
#line 30
    __VERIFIER_error();
  }
}
}
 */

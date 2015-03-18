/*
 * Date: 17.12.2013
 * Author: Thomas Ströder
 */
//#include <stdlib.h>

//extern int __VERIFIER_nondet_int(void);

/* Returns some null-terminated string. */

void* malloc(int size) __attribute__ ((noreturn))
/*@
  case {
    size <= 0 -> requires true ensures res = null;
    size >  0 -> requires true ensures res != null;
  }
*/;

char* __VERIFIER_nondet_String(void) {
    int length = __VERIFIER_nondet_int();
    if (length < 1) {
        length = 1;
    }
    char[] nondetString = (char*) malloc(length * sizeof(char));
    nondetString[length-1] = '\0';
    return nondetString;
}




int (cstrlen)(const char *s)
 {
   const char *p = s;
   
   /* Loop over the data in s.  */
    while (*p != 'a')
         *p = 0;
     return 0;
 }
/*
int main() {
    return cstrlen(__VERIFIER_nondet_String());
}
*/



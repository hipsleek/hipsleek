/*
 * Date: 17.12.2013
 * Author: Thomas Ströder
 */
#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

int (cstrlen)(const char *s)
 {
     const char *p = s;
     /* Loop over the data in s.  */
     while (*p != '\0')
       /*@
         requires s::arr_seg<a,b> * x::arrI<0> & x=s+b & p=s+a & a<=b & a>=0
         ensures s::arr_seg<a,b> * x::arrI<0> & x=s+b & p=s+a;
        */
         p++;
     return (int)(p - s);
 }


/*

while(s,p){
   if(*p != 0)
   {
      // How to conclude that a!=b from the fact that s[a]!=s[b]?
      // We need a<b so that the pre-condition of the recursive call can be entailed.
      while(s,p++);
   }
   else{
     return p;
   }
}

*/




int main() {
    int length1 = __VERIFIER_nondet_int();
    if (length1 < 1) {
        length1 = 1;
    }
    char* nondetString1 = (char*) alloca(length1 * sizeof(char));
    nondetString1[length1-1] = '\0';
    return cstrlen(nondetString1);
}



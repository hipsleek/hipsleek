
#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

/* Returns some null-terminated string. */
char* __VERIFIER_nondet_String(void) {
    int length = __VERIFIER_nondet_int();
    if (length < 1) {
        length = 1;
    }
    char* nondetString = (char*) malloc(length * sizeof(char));
    nondetString[length-1] = '\0';
    return nondetString;
}


char *(cstrchr)(const char *s, int c)
 {
     while (*s != '\0' && *s != (char)c)
         s++;
     return ( (*s == c) ? (char *) s : 0 );
 }

int main() {
    return *cstrchr(__VERIFIER_nondet_String(),__VERIFIER_nondet_int());
}

/*
# ex10.c

We cannot cast into char_pointer at the moment?

ERROR: at _0:0_0:0
Message: Can not find flow of char_star

Last Proving Location: void_pointer_casting_proc_1:0_6:3

ERROR: at _0:0_0:0
Message: Can not find flow of int_star

Last Proving Location: void_pointer_casting_proc_1:0_6:3

ERROR: at void_pointer_casting_proc_5:25_5:40
Message: UNIFICATION ERROR : at location {(Line:5,Col:25),(Line:5,Col:40)} types char_star and int_star are inconsistent


*/

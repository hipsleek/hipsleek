
void* malloc(int size) __attribute__ ((noreturn))
/*@
  case {
    size <= 0 -> requires true ensures res = null;
    size >  0 -> requires true ensures res != null;
  }
*/;

char* __VERIFIER_nondet_String(void) {
    int length = 10;
    char* nondetString = (char*) malloc(length * sizeof(char));
    *nondetString = 2;
    *(nondetString +2) = 2;
    nondetString[length-1] = 1;
    char aaaa[10];
    aaaa[3] = 3;
    return nondetString;
}


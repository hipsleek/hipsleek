/*
 * Date: 2014-06-01
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Ranking function: f(a[3], b[1+2], a[2+1]) = a[3]
 *
 */
extern int __VERIFIER_nondet_int(void);

void* malloc(int size) __attribute__ ((noreturn))
/*@
  case {
    size <= 0 -> requires true ensures res = null;
    size >  0 -> requires true ensures res::memLoc<h,s> & (res != null) & h;
  }
*/;


int main() {
	int a[1048];
        int* p = malloc(1);
        *p = 1;
        //@ assert p'::int*<1,_>;
        
        //a[3] = 1;
        //  assert a[3] > 0;
        int b = 1;
        //@ assert b'>0;
	/* while (a[3] >= 0) */
        /*   /\*@ */
        /*     requires true */
        /*     ensures true; */
        /*   *\/ */
        /* { */
        /*   //          b = -1; */
        /*   	a[3] = -1; */
        /* } */
        
	return 0;
}

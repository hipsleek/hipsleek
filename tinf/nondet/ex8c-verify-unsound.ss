/*
 * Date: 2014-06-08
 * Author: leike@informatik.uni-freiburg.de
 *
 *
 * This is Example 3.9 from the test suit used in
 *
 * Termination Proofs for Linear Simple Loops.
 * Hong Yi Chen, Shaked Flur, and Supratik Mukhopadhyay.
 * SAS 2012.
 *
 * The test suite is available at the following URL.
 * https://tigerbytes2.lsu.edu/users/hchen11/lsl/LSL_benchmark.txt
 *
 * Comment: terminating, non-linear
 */

/*
extern int __VERIFIER_nondet_int();

int main() {
    int x = __VERIFIER_nondet_int();
    int y = __VERIFIER_nondet_int();
    int z = __VERIFIER_nondet_int();
    while (x > 0 && x < y) {
        int old_x = x;
        x = __VERIFIER_nondet_int();
        if (x <= 2*old_x) {
            break;
        }
        y = z;
    }
    return 0;
}
*/

relation nd(int x).

int nondet()
  requires Term
  ensures nd(res);

void loop(int x, int y)
/*
  case {
    !(x > 0 & x < y) 
      -> requires Term ensures true;
    (x>0 & x<y)
      -> requires Term[y-x] ensures true;
  }
*/
{
  if (x > 0 && x < y) {
    int old_x = x;
    x = nondet(); //__VERIFIER_nondet_int();
    dprint;
    //assume z' > x';
    if (x <= old_x) {
      return;
    }
    //dprint;
    else {
    //y = z;
      loop(x, y);
      dprint;
    }
  }
}

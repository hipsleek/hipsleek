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

void loop(int x, int y, int z)
/*  
  case {
    x <= 0 | x >= y -> requires Term ensures true;
    x > 0 & x < y -> requires Loop ensures true;
  }
*/
{
  if (x > 0 && x < y) {
    int old_x = x;
    x = __VERIFIER_nondet_int();
    //assume z' > x';
    dprint;
    if (x <= old_x) {
      return;
    }
    else {
      y = z;
      loop(x, y, z);
    }
  }
}

/*
void loop$int~int~int(  int x,  int y,  int z) rec
static  EBase 
   emp&{FLOW,(4,5)=__norm#E}[]
   EBase 
     emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
     EAssume 
       emp&{FLOW,(4,5)=__norm#E}[]
dynamic  EBase 
   hfalse&false&{FLOW,(4,5)=__norm#E}[]
{(boolean v_bool_45_1417;
(v_bool_45_1417 = {((boolean v_boolean_45_1402;
(v_boolean_45_1402 = {((int v_int_45_1394;
v_int_45_1394 = 0);
gt___$int~int(x,v_int_45_1394))};
(boolean v_boolean_45_1401;
v_boolean_45_1401 = {lt___$int~int(x,y)})));
land___$boolean~boolean(v_boolean_45_1402,v_boolean_45_1401))};
if (v_bool_45_1417) [LABEL! 101,0: {((((int old_x;
old_x = x);
x = (int v_nd_47_1407;
(v_nd_47_1407 = __VERIFIER_nondet_int$();
v_nd_47_1407)));
dprint);
(boolean v_bool_50_1416;
(v_bool_50_1416 = {lte___$int~int(x,old_x)};
if (v_bool_50_1416) [LABEL! 104,0: {ret#}]
else [LABEL! 104,1: {(y = z;
{loop$int~int~int(x,y,z) rec})}]
)))}]
else [LABEL! 101,1: ]
))}

*/

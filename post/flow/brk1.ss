int main(int x)
  requires true
  ensures true;
{
  while (x > 0)
    infer [@post_n]
    requires true
      ensures true;
    //ensures x>=1 & x'=0 or x'>=2223 & x'=x or x'<=0 & x=x';
    // ensures true & flow __flow;
    // ensures x'<=x & x'<=0 & flow __norm or eres::ret_int<1> & x=x' & 2223<=x' & flow ret_int;
    //ensures x'=x;
    //ensures (x>2222 | x<=0) & x'=x or 0<x & x<=2222 & x'=0;
    //ensures  true & flow __flow;//x'<=x & x'<=0 & flow __norm or x'=x & eres::ret_int<2> & flow ret_int;
//true & flow __flow;
    {
      if (x > 2222) {
        break;
        //return 1;
      } else {
        x = x - 1;
      }
    }
  return 0;
}

/*

The relational assumption:

*************************************
******pure relation assumption*******
*************************************
[RELDEFN post_1345: ( x=x' & 2223<=x') -->  post_1345(x,x'),
RELDEFN post_1345: ( x_1369<=2221 & 0<=x_1369 & x=1+x_1369 & post_1345(x_1369,x')) -->  post_1345(x,x'),
RELDEFN post_1345: ( x=x' & x'<=0) -->  post_1345(x,x')]
*************************************

Fixcalc input:

post_1345:={[x] -> [PRIx] -> []: (((x=PRIx && PRIx<=0) || (x=PRIx && 2223<=PRIx)) || (( (exists (x_1369:(x_1369+1=x && post_1345(x_1369,PRIx))))  && 1<=x) && x<=2222))
};
bottomupgen([post_1345], [2], SimHeur);

The result: x'<=x

When change fixcalc input to [3] -> result: ((x >= 1 && 0 = PRIx) || (PRIx >= 2223 && PRIx = x) || (0 >= PRIx && PRIx = x))
but it is not correct.

*/

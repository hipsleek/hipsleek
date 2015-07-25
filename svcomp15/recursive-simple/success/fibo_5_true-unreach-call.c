extern int __VERIFIER_nondet_int();
extern void __VERIFIER_error();

void __error()
/*@
  requires emp & true
  ensures emp & true & flow __Error;
*/;

/*@
relation P1(int x).
relation Q1(int x, int y).
 */
int fibo(int n)
/*@
infer [P1,Q1]
  requires P1(n) ensures Q1(n,res);
 */
 {
    if (n < 1) {
        return 0;
    } else if (n == 1) {
        return 1;
    } else {
        return fibo(n-1) + fibo(n-2);
    }
}

// fibo 1-30
// 1, 1, 2, 3, 5,
// 8, 13, 21, 34, 55, 
// 89, 144, 233, 377, 610,
// 987, 1597, 2584, 4181, 6765,
// 10946, 17711, 28657, 46368, 75025,
// 121393, 196418, 317811, 514229, 832040

int main()
/*
requires true ensures true & flow __Error;
*/
 {
    int x = 5;
    int result = fibo(x);
    if (result != 5) {
      //  __VERIFIER_error();
      __error();
    }
    return 0;
}
/*
*************************************
******pure relation assumption 1 *******
*************************************
[RELDEFN P1: ( P1(n) & n=v_int_25_1413'+1 & 1<=v_int_25_1413') -->  P1(v_int_25_1413'),
RELDEFN P1: ( Q1(v_int_25_1473,tmp') & P1(n) & v_int_25_1473=v_int_25_1421'+1 & 
 n=v_int_25_1421'+2 & 0<=v_int_25_1421') -->  P1(v_int_25_1421'),
RELDEFN Q1: ( res=0 & n<=0 & P1(n)) -->  Q1(n,res),
RELDEFN Q1: ( n=1 & res=1 & P1(n)) -->  Q1(n,res),
RELDEFN Q1: ( Q1(v_int_25_1473,tmp_1489) & Q1(v_int_25_1484,tmp___1488) & tmp___1488=res-
 tmp_1489 & v_int_25_1473=n-1 & v_int_25_1484=n-2 & 2<=n & P1(n)) -->  Q1(n,res)]
*************************************


 */
/*
x=5 ==> P1(x)
x=5 & Q1(x,r1,fl1) & fl1=__Error ==> Q2(fl) & fl= __Error
x=5 & Q1(x,r1,fl1) & r1!=5 & fl1=__norm ==> Q2(fl) & fl= __Error
x=5 & Q1(x,r1,fl1) & r1=5 & fl1=__norm ==> Q2(fl) & fl= __norm

 */

/*
!!! **pi.ml#775:>>>>>>>>>>> (bef postprocess): <<<<<<<<<
!!! **pi.ml#776:>>REL POST:  Q1(n,res)
!!! **pi.ml#777:>>POST:  (((res+1)>=n & res>=1) | (0>=n & 0=res))
!!! **pi.ml#778:>>REL PRE :  P1(n)
!!! **pi.ml#779:>>PRE :  RECn>=0 & n>=(1+RECn) & n>=2
 */

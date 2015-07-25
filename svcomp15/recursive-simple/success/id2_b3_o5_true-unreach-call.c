// extern int __VERIFIER_nondet_int();
// extern void __VERIFIER_error();

int __nondet_int()
/*@
  requires true
  ensures true;
*/;

void __error()
/*@
  requires emp & true
  ensures emp & true & flow __Error;
*/;

/*@
relation P1(int x).
relation Q1(int x, int y).
 */

int id(int x)
/*
  case {
  x>=0 & x<=3 -> ensures emp & res=x;
  x>3 -> ensures emp & res=3;
  x<0 -> requires Loop ensures false;
  }
 */
/*@
infer [P1,Q1]
  requires P1(x) ensures Q1(x,res);
 */

{
  if (x==0) return 0;
  int ret = id2(x-1) + 1;
  if (ret > 3) return 3;
  return ret;
}

/*@
relation P2(int x).
relation Q2(int x, int y).
 */

int id2(int x)
/*
  case {
  x>=0 & x<=3 -> ensures emp & res=x;
  x>3 -> ensures emp & res=3;
  x<0 -> requires Loop ensures false;
  }
 */
/*@
infer [P2,Q2]
  requires P2(x) ensures Q2(x,res);
 */
{
  if (x==0) return 0;
  int ret = id(x-1) + 1;
  if (ret > 3) return 3;
  return ret;
}

/*@
relation P3(int x).
relation Q3(int x, int y).
 */

void main()
/*@
  requires true
  ensures true;
*/
{
  int input = __nondet_int();
  int result = id(input);
  if (result == 5) {
    __error();
  }
}


/*
*************************************
******pure relation assumption 1 *******
*************************************
[RELDEFN P2: ( P1(x) & x=1+v_int_36_1414' & (v_int_36_1414'+1)!=0) -->  P2(v_int_36_1414'),
RELDEFN Q1: ( 3<=tmp' & Q2(v_int_36_1497,tmp') & (v_int_36_1497+1)!=0 & res=3 & 
 x=1+v_int_36_1497 & P1(x)) -->  Q1(x,res),
RELDEFN Q1: ( x=0 & res=0 & P1(x)) -->  Q1(x,res),
RELDEFN Q1: ( Q2(v_int_36_1497,tmp_1510) & (v_int_36_1497+1)!=0 & tmp_1510+1=res & 
 x=1+v_int_36_1497 & res<=3 & P1(x)) -->  Q1(x,res),
RELDEFN P1: ( P2(x) & x=1+v_int_60_1443' & (v_int_60_1443'+1)!=0) -->  P1(v_int_60_1443'),
RELDEFN Q2: ( 3<=tmp' & Q1(v_int_60_1536,tmp') & (v_int_60_1536+1)!=0 & res=3 & 
 x=1+v_int_60_1536 & P2(x)) -->  Q2(x,res),
RELDEFN Q2: ( x=0 & res=0 & P2(x)) -->  Q2(x,res),
RELDEFN Q2: ( Q1(v_int_60_1536,tmp_1549) & (v_int_60_1536+1)!=0 & tmp_1549+1=res & 
 x=1+v_int_60_1536 & res<=3 & P2(x)) -->  Q2(x,res)]
*************************************


 */

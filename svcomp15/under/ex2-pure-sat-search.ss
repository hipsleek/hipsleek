int __nondet_int()
  requires true
  ensures true;

void __error()
  requires emp & true
  ensures emp & true & flow __Error;

/*
int id2(int x)
  case {
  x>=0 & x<=3 -> ensures emp & res=x;
  x>3 -> ensures emp & res=3;
  x<0 -> requires Loop ensures false;
  }
{
  if (x==0) return 0;
  int ret = id(x-1) + 1;
  if (ret > 3) return 3;
  return ret;
}
*/

int id(int x)
  case {
  x>=0 & x<=3 -> ensures emp & res=x;
  x>3 -> ensures emp & res=3;
  x<0 -> requires Loop ensures false;
  }
{
  if (x==0) return 0;
  int ret = id(x-1) + 1;
  if (ret > 3) return 3;
  return ret;
}

/*
id<x, res> == x=0 /\ res=0
  or id<x-1, r> /\ r1=r+1 /\ r1> 3 /\ res=3
  or id<x-1, r> /\ r1=r+1 /\ r1<=3 /\ res=r1
*/


void main()
  requires true
  ensures true;
{
  int input = __nondet_int();
  int result = id(input);
  if (result == 1) {
    __error();
  }
}

/*
\D0 == id<i, r>

\D1 == i=0 /\ r=0
  or id<i-1, r> /\ r1=r+1 /\ r1> 3 /\ r=3
  or id<i-1, r> /\ r1=r+1 /\ r1<=3 /\ r=r1

\D2 == i=0 /\ r=0

  or i-1=0 /\ r11=0 /\ r1=r11+1 /\ r1> 3 /\ r=3
    or id<i-1-1, r11> /\ r1=r11+1 /\ r1> 3 /\ r11=3 /\ r1=r11+1 /\ r1> 3 /\ r=3
    or id<i-1, r11> /\ r1=r11+1 /\ r1<=3 /\ r11=r1 /\ r1=r11+1 /\ r1<= 3 /\ r=3

  or i-1=0 /\ r11=0 /\ r1=r11+1 /\ r1<=3 /\ r=r1 //confirm

 */

relation R(int x).

bool isEven (ref int x)
     infer [R]
     requires R(x)
     ensures true;
{
  if (x < 2) {
    return x == 0;
  } else {
    return isEven(x - 2);
  }
}

relation R2(int x,int a).

int nondet_int()
  requires Term[]
  ensures true;

void loo (ref int x, int a)
     infer [R2]
     requires R2(x,a)
     ensures true;
{
  if (a == 10 && x > 0) {
    x = x - 1;
    loo(x, a);
  } else if (x > 0) {
    a = 10;
    loo(x, 10);
  }
}


/*
# ex24.ss

isEven:
[RELDEFN R: ( R(x) & x=v_int_11_1188'+2 & 0<=v_int_11_1188') -->  R(v_int_11_1188')]

note that, because uses `x + 2` there's a tmp variable v.

loo:
[RELDEFN R2: ( a=10 & a'=10 & x=x'+1 & 0<=x' & R2(x,a)) -->  R2(x',a'),
RELDEFN R2: ( a!=10 & v_int_31_1171'=10 & 1<=x' & R2(x',a)) -->  R2(x',v_int_31_1171')]

note that when using a constant, there's a tmp variable v

 */

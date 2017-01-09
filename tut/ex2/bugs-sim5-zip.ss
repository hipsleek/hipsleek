
relation P(int n,int m).
relation Q(int n,int m,int r).

void is_zero(int m)
  requires m=0
  ensures true;

void is_pos(int m)
  requires m>0 ensures true;


int zip(int n,int m)
  infer [P,Q]
  requires P(n,m) ensures Q(n,m,res);
{
  if (n==0) {
      is_zero(m);
      return 0;
  }
  else {
       is_pos(m);
       return 1;
  }
}


/*
# bugs-sim5-zip.ss

int zip(int n,int m)
  infer [P,Q]
  requires P(n,m) ensures Q(n,m,res);
{
  if (n==0) {
      is_zero(m);
      return 0;
  }
  else {
       is_pos(m);
       return 1;
  }
}

How did we form such a fixpoint with In_1,in_2?

!!! fixpoint:[( Q(n,m,res), ((n!=0 & res=1 & 1<=m) | (n=0 & m=0 & res=0)), P(n,m), ((In_1!=0 & n=In_1 & m=In_2 & 1<=In_2) | (In_1=0 & In_2=0 & n=0 & m=0)))]

RELDEFN Q: ( n=0 & m=0 & res=0 & P(n,m)) -->  Q(n,m,res),
RELDEFN Q: ( res=1 & 1<=m & n!=0 & P(n,m)) -->  Q(n,m,res)]
*************************************

!!! constraints:[( res=1 & 1<=m & n!=0, Q(n,m,res)),( n=0 & m=0 & res=0, Q(n,m,res))]
!!! bottom_up_fp:[( Q(n,m,res), ((n!=0 & res=1 & 1<=m) | (n=0 & m=0 & res=0)))]
!!! fixpoint:[( Q(n,m,res), ((n!=0 & res=1 & 1<=m) | (n=0 & m=0 & res=0)), P(n,m), ((In_1!=0 & n=In_1 & m=In_2 & 1<=In_2) | (In_1=0 & In_2=0 & n=0 & m=0)))]

*/


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
       is_pos(n);
       return 1+zip(n-1,m-1);
  }
}


/*
# sim5-zip.ss


[RELASS [P]: ( P(n,m)) -->  m=0,
RELASS [P]: ( P(n,m)) -->  1<=m,
RELDEFN P: ( P(n,m) & n=1+v_int_23_1318' & m=1+v_int_23_1317' & 0<=v_int_23_1317' & 
(v_int_23_1318'+1)!=0) -->  P(v_int_23_1318',v_int_23_1317'),
RELDEFN Q: ( n=0 & m=0 & res=0 & P(n,m)) -->  Q(n,m,res),
RELDEFN Q: ( Q(v_int_23_1379,v_int_23_1380,v_int_23_1383) & (v_int_23_1379+1)!=0 & 
0<=v_int_23_1380 & v_int_23_1383+1=res & m=1+v_int_23_1380 & n=1+
v_int_23_1379 & P(n,m)) -->  Q(n,m,res)]


*/

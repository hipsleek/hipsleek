
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

We get pre-condition:
 EBase emp&0<=n & (((1<=m & n!=0) | n=0)) & (((n!=0 & m!=0) | m=0)) & n=m 

If we send it to Omega.simplifier (e.g. PairWiseCheck), we will get:
n=m & m>=0.

   { [n,n]: 0 <= n}

Please send this to Omega. simplifier



[RELASS [P]: ( P(n,m)) -->  ((n!=0 & m!=0) | m=0),
RELASS [P]: ( P(n,m)) -->  ((1<=m & n!=0) | n=0),
RELASS [P]: ( P(n,m)) -->  0<=n,

RELDEFN P: ( P(n,m) & n=1+v_int_24_1318' & m=1+v_int_24_1317' & 0<=v_int_24_1318') -->  P(v_int_24_1318',v_int_24_1317'),

RELDEFN Q: ( n=0 & res=0 & P(n,m)) -->  Q(n,m,res),
RELDEFN Q: ( Q(v_int_24_1383,v_int_24_1384,v_int_24_1387) & 0<=v_int_24_1383 & m=1+
v_int_24_1384 & v_int_24_1387+1=res & n=1+v_int_24_1383 & P(n,m)) -->  Q(n,m,res)]

zip$int~int
 EBase emp&0<=n & (((1<=m & n!=0) | n=0)) & (((n!=0 & m!=0) | m=0)) & n=m & 
       MayLoop[]&{FLOW,(4,5)=__norm#E}[]
         EAssume 
           emp&n=res & 0<=res&{FLOW,(4,5)=__norm#E}[]


*/

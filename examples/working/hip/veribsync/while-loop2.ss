/*
 Examples for verifying while loop
 */

//SUCCESS
void fun(ref int i)
  requires i=0
  ensures i'=10; //'
{
  while(i<10)
    requires true
    ensures i<10 & i'=10
         or i>=10 & i'=i; //'
  {
    i=i+1;
  }
}


//SUCCESS
void fun3(int n,int bs, ref int j)
  requires (exists r: n=r*bs)
  ensures n>0 & j'=j+n*bs
          or n<=0 & j'=j; //'
{
  int i=0;
  while(i<n)
    requires (exists r: n=r*bs)
    ensures exists r: n=r*bs & i<n & i'=n & j'=j+(i'-i)*bs
         or i>=n & i'=i & j'=j; //'
  {
    i=i+1;
    j=j+bs;
  }
}

//SUCCESS
void fun4(int n,int bs, ref int j)
  requires (exists r: n=r*bs)
  ensures true;
{
  int i=0;
  while(i<n)
    requires true
      ensures i<n & i'>=n & bs'=bs
         or i>=n & i'=i & bs'=bs; //'
  {
    i=i+bs;
  }
}

//SUCCESS
void fun5(int n,int bs, ref int j)
  requires [r] n=r*bs
  ensures true;
{
  int i=0;
  while(i<n)
    requires true
    ensures i<n & i'>=n & bs'=bs & (i'-i)=(j'-j)*bs
         or i>=n & i'=i & j'=j & bs'=bs; //'
  {
    j=j+1;
    i=i+bs;
  }
}

//SUCCESS
void fun52(int n,int bs, ref int j)
  requires [r] n=r*bs & n>0
  ensures true;
{
  int i=0;
  while(i<n)
    requires (exists r: i=r*bs)
    ensures i<n & i'>=n & bs'=bs & (i'-i)=(j'-j)*bs
         or i>=n & i'=i & j'=j & bs'=bs; //'
  {
    j=j+1;
    i=i+bs;
    dprint;
  }
  dprint;
}


//SUCCESS
void fun6(int n,int bs, ref int j)
  requires [r] n=r*bs & n>0 & bs>0
  ensures j'-j=r; //'
{
  int i=0;
  while(i<n)
    requires (exists r1,r2: n=r1*bs & i=r2*bs & r1>=r2 & n>0 & bs>0)
    ensures i<n & i'=n & bs'=bs & (i'-i)=(j'-j)*bs
         or i>=n & i'=i & j'=j & bs'=bs; //'
  {
    j=j+1;
    i=i+bs;
    dprint;
  }
  dprint;
}


//SUCCESS
void fun7(int n,int bs, ref int j)
  requires [r] n=r*bs & n>0 & bs>0
  ensures j'-j=r; //'
{
  int i=0;
  while(i<n)
    requires (exists r1,r2: n=r1*bs & i=r2*bs & r1>=r2 & bs>0)
    ensures i<n & i'=n & bs'=bs & (i'-i)=(j'-j)*bs
         or i>=n & i'=i & j'=j & bs'=bs; //'
  {
    j=j+1;
    i=i+bs;
    dprint;
  }
  dprint;
}

//SUCCESS
void fun8(int n,int bs, ref int j)
  requires (exists r1: n=r1*bs & n>0 & bs>0)
  ensures (exists r2: n=r2*bs & j'-j=r2); //'
{
  int i=0;
  while(i<n)
    requires (exists r1,r2: n=r1*bs & i=r2*bs & r1>=r2 & bs>0)
    ensures i<n & i'=n & bs'=bs & (i'-i)=(j'-j)*bs
         or i>=n & i'=i & j'=j & bs'=bs; //'
  {
    j=j+1;
    i=i+bs;
    dprint;
  }
  dprint;
}

//SUCCESS
// this is the testing example for barrier-static-complex3
void fun9(int n,int bs, ref int j)
  requires (exists r1: n=r1*bs & n>0 & bs>0)
  ensures (exists r2: n=r2*bs & j'-j=r2*3); //'
{
  int i=0;
  while(i<n)
    requires (exists r1,r2: n=r1*bs & i=r2*bs & r1>=r2 & bs>0)
    ensures i<n & i'=n & bs'=bs & 3*(i'-i)=(j'-j)*bs
         or i>=n & i'=i & j'=j & bs'=bs; //'
  {
    j=j+3;
    i=i+bs;
  }
}

void foo1(ref int i)
 infer [i] // infer better pre/post
 requires true
 ensures true; //'
/*
  expecting 
   requires i>0
   ensures i'=i-1;
*/
{
  i = i-1;
  bnd(i);
}

void foo1a(ref int i)
 infer  [i] // infer better pre/post
 requires true
 ensures true; //'
/*
  expecting 
   requires i>0
   ensures i'=i-1;
*/
{
  i = i-1;
  bnd(i);
}

void foo1b(ref int i)
 infer @post [] // infer better pre/post
 requires i>0
 ensures true; //'
/*
  expecting 
   requires i>0
   ensures i'=i-1;
*/
{
  i = i-1;
  bnd(i);
}


void bnd(int i)
 requires i>=0
 ensures true;

void ass(ref int r)
 requires true
 ensures 1<=r'<=2;

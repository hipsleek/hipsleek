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
 infer [] // infer better pre/post
 requires i>0
 ensures true; //'
/*
  expecting 
   requires i>0
   ensures i'=i+1;
*/
{
  i = i-1;
  bnd(i);
}

void foo1b(ref int i)
 infer [i] // infer better pre/post
 requires i>0
 ensures true; //'
/*
  expecting 
   requires i>0
   ensures i'=i+1;
*/
{
  i = i-1;
  bnd(i);
}


void foo2(ref int i)
  infer [i]
  requires true
  ensures true;
/* expecting
 requires i>1
 ensures i-2<=i'<=i-1; //'
*/
{
  int r;
  //assume 1<=r<=2; 
  ass(r);
  i = i-r;
  //dprint;
  bnd(i);
}


void foo2a(ref int i)
  infer []
  requires true
  ensures true;
/* expecting to fail ...
*/
{
  int r;
  //assume 1<=r<=2; 
  ass(r);
  i = i-r;
  //dprint;
  bnd(i);
}

void bnd(int i)
 requires i>=0
 ensures true;

void ass(ref int r)
 requires true
 ensures 1<=r'<=2;

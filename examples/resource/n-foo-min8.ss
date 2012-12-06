// this used a single predicate to mark lower/upper stack bound
// for a given method; and it is specified in the post-condition

pred_prim RS<low:int>
  inv low>=0;

pred_prim RS_bnd<low:int,high:int>
  inv 0<=low<=high;

global RS_bnd stk_mark;
global RS stk;

// add back space into stack
void add_stk(int n)
  requires stk::RS<a> & n>=0
  ensures stk::RS<m> * stk_mark::RS_bnd<m,m> & m=a+n;

void sub_stk(int n)
  requires stk::RS<a> & n>=0 & a>=n
  ensures stk::RS<a-n>;

bool rand()
 requires true
 ensures res or !res;


void g() 
  requires stk::RS<n> 
  ensures  stk::RS<n> * stk_mark::RS_bnd<m,h> & h<=n+2 & m>=n+2;
{
  add_stk(2); //add stack frame used
  sub_stk(2); //add stack frame used
}

void h() 
  requires stk::RS<n> 
  ensures  stk::RS<n> * stk_mark::RS_bnd<m,h> 
    & h<=n+3 & m>=n+3;
{
  add_stk(3); //add stack frame used
  sub_stk(3); //add stack frame used
}

void f() 
  requires stk::RS<n>
  ensures  stk::RS<n> * stk_mark::RS_bnd<m,h> 
    & h<=n+5 & m>=n+5;
{
  add_stk(2); //add stack frame used
  g(); h();
  //h(); g();
  //dprint;
  sub_stk(2); //add stack frame used
}

void f2() 
  requires stk::RS<n>
  ensures  stk::RS<n> * stk_mark::RS_bnd<m,h> 
    & h<=n+5 & m>=n+4;
{
  add_stk(2); //add stack frame used
  if (rand()) h();
  else g();
  //dprint;
  sub_stk(2); //add stack frame used
}


int foo(int i)
  requires stk::RS<n> & i>=0
  ensures stk::RS<n> * stk_mark::RS_bnd<m,h> 
       & m>=n+2*(i+1) & h<=n+2*(i+1) & res=2*i;
{ 
  add_stk(2);
  int r;
  if (i==0) r=0;
  else r=2+foo(i-1);
  sub_stk(2);
  return r;
}


int tail_foo(int i,int acc)
  requires stk::RS<n> & i>=0
  ensures  stk::RS<n> * stk_mark::RS_bnd<m,h> 
     & m>=n+2 & h<=n+2 & res=2*i+acc;
{ 
  add_stk(2);
  int r;
  if (i==0) {
      sub_stk(2);
      r=acc;
  }
  else {
     sub_stk(2);
     r=tail_foo(i-1,acc+2);
  }
  return r;
}


void cond(int i)
  requires stk::RS<n> 
  ensures stk::RS<n> * stk_mark::RS_bnd<m,h> 
       & m>=n+4 & h<=n+4 & i<0
  or stk::RS<n> * stk_mark::RS_bnd<m,h> 
       & m>=n+5 & h<=n+5 & i>=0
  ;
{ 
  add_stk(2);
  if (i<0) g();
  else h();
  sub_stk(2);
}

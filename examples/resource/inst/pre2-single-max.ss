hip_include 'include_test.ss'

int g() 
  requires stk::RS<m> & m>=1 // m=\infinity
  ensures  stk::RS<m> 
    * mn::RS_mark<h> & h=m-1 & res=1;
{
  int f = save_stk();
  sub_stk(1);
  int r;
  r=1;
  restore_stk(f);
  return r;
}


int h() 
  requires stk::RS<m> & m>=2
  ensures  stk::RS<m> * mn::RS_mark<h> & h=m-2 & res=2;
{
  int f = save_stk();
  sub_stk(1);
  int r;
  int x=g();
  r=x+1;
  restore_stk(f);
  return r;
}


int f() 
  requires stk::RS<m> & m>=3
  ensures  stk::RS<m> * mn::RS_mark<h> & h=m-3 & res=3;
{
  int f = save_stk();
  sub_stk(1);
  int r=g();
  r = r+h();
  restore_stk(f);
  return r;
}

int f2() 
  requires stk::RS<m> & m>=3
  ensures  stk::RS<m> * mn::RS_mark<h> 
  // & m-3<=h ;
  & h<=m-2;
{
  int f = save_stk();
  sub_stk(1);
  int r;
  if (rand()) r=g();
  else r=h();
  restore_stk(f);
  return r;
}



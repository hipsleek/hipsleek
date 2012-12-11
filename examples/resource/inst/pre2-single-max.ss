pred_prim RS<high:int>
  inv high>=0;

pred_prim RS_mark<high:int>
  inv 0<=high;

//global RS_bnd stk_mark;
global RS stk;
global RS_mark mn;

lemma "combine2" 
self::RS_mark<m1>*self::RS_mark<m2> 
  -> self::RS_mark<m> & m=min(m1,m2);

bool rand()
 requires true
 ensures res or !res;

// add back space into stack
void add_stk(int n)
  requires stk::RS<a> & n>0
  ensures stk::RS<a+n> ;

void sub_stk(int n)
  requires stk::RS<a> & n>0 & a>=n
  ensures stk::RS<m> * mn::RS_mark<m> & m=a-n;

int save_stk()
  requires stk::RS<a>@L
  ensures res=a;

void restore_stk(int a)
  requires stk::RS<_> 
  ensures stk::RS<a>;

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



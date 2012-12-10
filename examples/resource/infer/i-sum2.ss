
pred_prim RS<high:int>
  inv high>=0;
pred_prim RS_mark<high:int>
  inv 0<=high;

//global RS_bnd stk_mark;
global RS stk;
global RS_mark mx;

// add back space into stack
void add_stk(int n)
  requires stk::RS<a> & n>=0
  ensures stk::RS<m> & m=a+n;
//ensures stk::RS<m> * mx::RS_mark<m> & m=a+n;

void sub_stk(int n)
  requires stk::RS<a> & n>=0 & a>=n
  ensures stk::RS<a-n>;

void add_mark()
  requires stk::RS<a>@L
  ensures  mx::RS_mark<a>;

lemma "combine2" self::RS_mark<m1>*self::RS_mark<m2> 
  -> self::RS_mark<m> & m=max(m1,m2);

relation R1(int h, int n, int m).
relation R2(int h, int n, int m).

int sum(int x)
  infer [R1]
  requires stk::RS<m> & x>=0
  ensures  stk::RS<m> 
  * mx::RS_mark<h> & res=2*x
   & R1(h,m,x);
//& h=m+2*x+2;
{
  add_stk(2); //subtract stack frame
  int r;
  if (x==0) {
     add_mark();
     r=0;
  }
  else {
    r=2+sum(x-1);
  }
  sub_stk(2); //add back stack frame prior to return
  return r;
}

/*

*************************************
[RELDEFN R1: ( x=0 & m=h-2 & 2<=h) -->  R1(h,m,x),
RELDEFN R1: ( h=h_635 & m=m_619-2 & x=v_int_46_636+1 & 0<=h_635 & 2<=m_619 & 
0<=v_int_46_636 & R1(h_635,m_619,v_int_46_636)) -->  R1(h,m,x)]
*

RELDEFN R1: (  0<=h & 0<=m & 1<=x & R1(h,m+2,x-1)) -->  R1(h,m,x)]
*


!!! IGNORING PROBLEM of fix-point calculation
Procedure sum$int~RS_mark~RS SUCCESS

 */

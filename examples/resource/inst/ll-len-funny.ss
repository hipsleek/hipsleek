data node {
  int val;
  node next;
}

ll<n> == self=null & n=0
  or self::node<_,q> * q::ll<n-1>
  inv n>=0;

pred_prim RS<high:int>
  inv high>=0;

pred_prim RS_mark<high:int>
  inv 0<=high;

//global RS_bnd stk_mark;
global RS stk;
global RS_mark mn;

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

lemma "combine2" self::RS_mark<m1>*self::RS_mark<m2> 
  -> self::RS_mark<m> & m=min(m1,m2);

relation R1(int h,int n, int m).

bool rand()
 requires true
 ensures res or !res;

int length(node l)
//infer [R1]
  requires stk::RS<m> * l::ll<n>@L & m>=3*n+3
  ensures  stk::RS<m> * mn::RS_mark<h> & res<=n 
//& R1(h,m,n);
  & h<=m-3;
{
  int f = save_stk();
  sub_stk(3); //add a stack frame
  int r;
  if (l==null) r=0;
  else {
    if (rand()) r=0;
    else r=1+length(l.next);
  }
  restore_stk(f); //restore stack frame prior to return
  return r;
}

/*
Obtained:

Not precise enough!

!!! REL :  R1(h,m,n)
!!! POST:  m>=h & n>=0 & m>=(3+(3*n))
!!! PRE :  true

*************************************
*******fixcalc of pure relation *******
*************************************
[( R1(h,m,n), n>=0 & m>=0 & h=n+m+1)]
*************************************

!!! REL :  R1(h,m,n)
!!! POST:  n>=0 & m>=0 & h=n+m+1

// PROBLEM :  maybe can remove ctr already present namely
    n>=0, m>=0, h>=0

 */

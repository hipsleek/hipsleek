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
global RS_mark mx;

// add back space into stack
void add_stk(int n)
  requires stk::RS<a> & n>=0
  ensures stk::RS<m> * mx::RS_mark<m> & m=a+n;

void sub_stk(int n)
  requires stk::RS<a> & n>=0 & a>=n
  ensures stk::RS<a-n>;

lemma "combine2" self::RS_mark<m1>*self::RS_mark<m2> 
  -> self::RS_mark<m> & m=max(m1,m2);

relation R1(int h,int n, int m).

int length(node l)
  infer [R1]
  requires stk::RS<m> * l::ll<n>@L 
  ensures  stk::RS<m> * mx::RS_mark<h> & res=n 
  & R1(h,m,n);
  //& h=m+n+1;
{
  add_stk(1); //add a stack frame
  int r;
  if (l==null) r=0;
  else {
    // node nx = l.next; 
    r=1+length(l.next);
  }
  sub_stk(1); //subtract a stack frame prior to return
  return r;
}

/*
Obtained:

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

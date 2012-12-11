data node {
  int val;
  node next;
}

ll<n> == self=null & n=0
  or self::node<_,q> * q::ll<n-1>
  inv n>=0;


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


relation R1(int h,int n, int m).

int len_tail(node l, int a)
  infer [R1]
  requires stk::RS<m> * l::ll<n>@L 
  ensures  stk::RS<m> * mx::RS_mark<h> & res=n+a 
  & R1(h,m,n);
  //& h=m+n+1;
{
  add_stk(3); //add a stack frame
  int r;
  if (l==null) {
       sub_stk(3);
       r=a;
  }
  else {
    // node nx = l.next; 
    sub_stk(3); //subtract a stack frame prior to return
    r=len_tail(l.next,1+a);
  }
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

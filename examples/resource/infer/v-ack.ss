
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
  //ensures stk::RS<m> & m=a+n;
  ensures stk::RS<m> * mx::RS_mark<m> & m=a+n;

void sub_stk(int n)
  requires stk::RS<a> & n>=0 & a>=n
  ensures stk::RS<a-n>;

lemma "combine2" self::RS_mark<m1>*self::RS_mark<m2> 
  -> self::RS_mark<m> & m=max(m1,m2);

/*
  infer [R1]
  requires stk::RS<m> & x>=0
  ensures  stk::RS<m> * mx::RS_mark<h> & res=2*x
   & R1(h,m,x);
  //& h=m+1*x+1;
{
  add_stk(1); //subtract stack frame
  int r;
  if (x==0) {
     r=0;
  }
  else {
    r=2+sum(x-1);
  }
  sub_stk(1); //add back stack frame prior to return
  return r;
}
*/

relation R1(int h, int n, int m,int z,int r).

int Ack(int m, int n) 
  //infer [R1]
  requires stk::RS<mm> & m>=0 & n>=0
  ensures  stk::RS<mm> * mx::RS_mark<h> 
//& res>=1
    & h>=(1+mm) & res>=(1+n)
// & h<=\inf
//& R1(h,mm,m,n,res)
  ;
{ 
  add_stk(1); //subtract stack frame
  int r;
	if (m==0) r=n+1;
    else if (n==0) r=Ack(m-1,1);
  	else r=Ack(m-1, Ack(m,n-1));
  sub_stk(1); //add back stack frame prior to return
  return r;
}
/*
*************************************
*******fixcalc of pure relation *******
*************************************
[( R1(h,mm,m,n,res), mm>=0 & h>=(1+mm) & n>=0 & res>=(1+n) & m>=0)]
*************************************

!!! REL :  R1(h,mm,m,n,res)
!!! POST:  mm>=0 & h>=(1+mm) & n>=0 & res>=(1+n) & m>=0
!!! PRE :  true

PROBLEM : can remove mm>=0, n>=0,m>=0
*/

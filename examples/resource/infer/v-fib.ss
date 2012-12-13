pred_prim RS<high:int>
  inv high>=0;

pred_prim RS_mark<high:int>
  inv 0<=high;

//global RS_bnd stk_mark;
global RS stk;
global RS_mark mx;

lemma "combine2" self::RS_mark<m1>*self::RS_mark<m2> 
  -> self::RS_mark<m> & m=max(m1,m2);

// add back space into stack
void add_stk(int n)
  requires stk::RS<a> & n>=0
  ensures stk::RS<m> * mx::RS_mark<m> & m=a+n;

void sub_stk(int n)
  requires stk::RS<a> & n>=0 & a>=n
  ensures stk::RS<a-n>;

bool rand()
 requires true
 ensures res or !res;

void g() 
  requires stk::RS<n> 
  ensures  stk::RS<n> * mx::RS_mark<h> & h=n+2 ;

relation R(int a,int b,int c).

int fib(int n)
 infer []
 requires stk::RS<m> & n>=0
 ensures stk::RS<m> * mx::RS_mark<h> & res>=1
//   & R(h,m,n);
     & h=m+max(2,2*n);
     //& m+max(2*n,2)<=h<=m+max(2,2*n);
 { int r;
   add_stk(2);
   if (n<=1) r=1;
   else r=fib(n-1)+fib(n-2);
   sub_stk(2);
   return r;
 }  

/*

PROBLEM : is disjunct below precise?

*************************************
[( R(res,m,n), (m>=0 & res>=(2+m) & res=n+m) | (n>=0 & 1>=n & m>=0 & res=m+1))]
*************************************



*/

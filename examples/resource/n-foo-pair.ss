// this used a single predicate to mark lower/upper stack bound
// for a given method; and it is specified in the post-condition

pred_prim RS<low:int>
  inv low>=0;

pred_prim RS_bnd<low:int,high:int>
  inv 0<=low & 0<=high;

global RS_bnd stk_mark;
global RS stk;

lemma "combine" 
self::RS_bnd<m1,n1>*self::RS_bnd<m2,n2> 
  -> self::RS_bnd<m,n> & m=max(m1,m2) & n=max(n1,n2);

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
  ensures  stk::RS<n> * stk_mark::RS_bnd<m,h> & m>=n+3 & h<=n+5 ;

void h() 
  requires stk::RS<n> 
  ensures  stk::RS<n> * stk_mark::RS_bnd<m,h> 
    & m>=n+2 & h<=n+6;

void f() 
  requires stk::RS<n>
  ensures  stk::RS<n> * stk_mark::RS_bnd<m,h> 
//    & m>=n+3+2 & h<=n+5+2;
  //& m>=n+3+2 & h<=n+5+2; // unsound if lemma not given
  & m>=n+3+2 & h<=n+6+2; //  if lemma not given
{
  add_stk(2); //add stack frame used
  g(); h();
  //h(); g();
  //dprint;
  sub_stk(2); //add stack frame used
}


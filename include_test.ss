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



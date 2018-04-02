relation Univ(int x).

class __DivByZeroErr extends __Error {}
class __ArrBoundErr extends __Error {}
class __RET extends __Exc {}

//////////////////////////////////////////////////////////////////
// <BASIC> INTEGER OPERATIONS
//////////////////////////////////////////////////////////////////
int add___(int a, int b)
  requires true
  ensures res = a+b %% res <? a |_| b;
int minus___(int a, int b)
  requires true
  ensures res = a-b %% res <? a |_| b;
int mult___(int a, int b)
  requires true
  ensures res = a*b %% res <? a |_| b;
int mults___(int a, int b)
  requires true
  ensures res = a*b %% res <? a |_| b;
int div___(int a, int b)
 case {
  a >= 0 -> case {
    b >=  1    -> ensures (exists r: a = b*res+r & res >= 0 & 0 <= r <=  b-1 %% res <? a |_| b & r <? a |_| b);
    b <= -1    -> ensures (exists r: a = b*res+r & res <= 0 & 0 <= r <= -b-1 %% res <? a |_| b & r <? a |_| b);
    -1 < b < 1 -> ensures true & flow __DivByZeroErr %% res <? a |_| b;
    }
  a <  0 -> case {
    b >=  1    -> ensures (exists r: a = b*res + r & res <= -1 & 0 <= r <=  b-1 %% res <? a |_| b & r <? a |_| b);
    b <= -1    -> ensures (exists r: a = b*res + r & res >=  1 & 0 <= r <= -b-1 %% res <? a |_| b & r <? a |_| b);
    -1 < b < 1 -> ensures true & flow __DivByZeroErr %% res <? a |_| b;
    }
}
int divs___(int a, int b)
  case {
    a = 0 -> case {
      b >=  1    -> ensures res = 0 %% res <? a |_| b;
      b <= -1    -> ensures res = 0 %% res <? a |_| b;
      -1 < b < 1 -> ensures true & flow __DivByZeroErr %% res <? a |_| b;
    }
    a > 0 -> case {
      b =  1     -> ensures res =  a %% res <? a |_| b;
      b = -1     -> ensures res = -a %% res <? a |_| b;
      b >  1     -> case {
        a <  b   -> ensures res = 0 %% res <? a |_| b;
        a >= b   -> ensures res >= 1 & res < a %% res <? a |_| b;
      }
      b < -1     -> case {
        -a >  b  -> ensures res = 0 %% res <? a |_| b;
        -a <= b  -> ensures res <= 1 & a + res > 0 %% res <? a |_| b;
      }
      -1 < b < 1 -> ensures true & flow __DivByZeroErr;
    }
    a < 0 -> case {
      b =  1     -> ensures res =  a %% res <? a |_| b;
      b = -1     -> ensures res = -a %% res <? a |_| b;
      b >  1     -> ensures res <= 0 & res > a %% res <? a |_| b;
      b < -1     -> ensures res >= 0 & a + res < 0 %% res <? a |_| b;
      -1 < b < 1 -> ensures true & flow __DivByZeroErr %% res <? a |_| b;
    }
}
int mod___(int a, int b) case {
  a >= 0         -> case {
	  b >= 1       -> case {
	    a <  b     -> ensures res = a %% res <? a |_| b;
	    a >= b     -> case {
		    a <  2*b -> ensures res = a - b %% res <? a |_| b;
		    a >= 2*b -> ensures (exists q: a = b*q + res & q >= 0 & 0 <= res <= b-1 %% res <? a |_| b & q <? a |_| b);
	    }
	  }
    b <= -1      -> ensures (exists q: a = b*q + res & q <= 0 & 0 <= res <= -b-1 %% res <? a |_| b & q <? a |_| b);
    -1 < b < 1   -> ensures true & flow __DivByZeroErr %% res <? a |_| b;
  }
  a < 0 -> case {
    b >=  1      -> ensures (exists q: a = b*q + res & q <= -1 & 0 <= res <= b-1 %% res <? a |_| b & q <? a |_| b);
    b <= -1      -> ensures (exists q: a = b*q + res & q >= 1 & 0 <= res <= -b-1 %% res <? a |_| b & q <? a |_| b);
    -1 < b < 1   -> ensures true & flow __DivByZeroErr %% res <? a |_| b;
  }
}
//////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////
// <BASIC> UNUSED INTEGER OPERATIONS ???
//////////////////////////////////////////////////////////////////
int div2(int a, int b)
 requires true
 case {
   b != 0 -> ensures true;
   b  = 0 -> ensures true & flow __DivByZeroErr;
 }
int div3(int a, int b)
 case {
  b = 0 -> requires false ensures false;
  b != 0 -> ensures true;
 }
int div4(int a, int b)
  requires b != 0
  ensures true;
int pow___(int a, int b)
  requires true
  ensures  true %% res <? a |_| b;
//////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////
// <BASIC> FLOATING POINT OPERATIONS
//////////////////////////////////////////////////////////////////
float add___(float a, float b)
  requires true
  ensures res = a + b %% res <? a |_| b;
float add___(int a, float b)
  requires true
  ensures res = a + b %% res <? a |_| b;
float add___(float a, int b)
  requires true
  ensures res = a + b %% res <? a |_| b;
float minus___(float a, float b)
  requires true
  ensures res = a - b %% res <? a |_| b;
float minus___(int a, float b)
  requires true
  ensures res = a - b %% res <? a |_| b;
float minus___(float a, int b)
  requires true
  ensures res = a - b %% res <? a |_| b;
float mult___(float a, float b)
  requires true
  ensures res = a * b %% res <? a |_| b;
float mult___(int a, float b)
  requires true
  ensures res = a * b %% res <? a |_| b;
float mult___(float a, int b)
  requires true
  ensures res = a * b %% res <? a |_| b;
//////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////
// <BASIC> BOOLEAN OPERATIONS
//////////////////////////////////////////////////////////////////
bool eq___(bool a, bool b)
   case {
    a  = b -> ensures  res %% res <? a |_| b;
    a != b -> ensures !res %% res <? a |_| b;
  }
bool eq___(int a, int b)
  case {
    a  = b -> ensures  res %% res <? a |_| b;
    a != b -> ensures !res %% res <? a |_| b;
  }
bool neq___(bool a, bool b)
  case {
    a  = b -> ensures !res %% res <? a |_| b;
    a != b -> ensures  res %% res <? a |_| b;
  }
bool neq___(int a, int b)
  case {
    a  = b -> ensures !res %% res <? a |_| b;
    a != b -> ensures  res %% res <? a |_| b;
  }
bool lt___(int a, int b)
  case {
    a <  b -> ensures  res %% res <? a |_| b;
    a >= b -> ensures !res %% res <? a |_| b;
  }
bool lte___(int a, int b)
  case {
    a <= b -> ensures  res %% res <? a |_| b;
    a >  b -> ensures !res %% res <? a |_| b;
  }
bool gt___(int a, int b)
  case {
    a >  b -> ensures  res %% res <? a |_| b;
    a <= b -> ensures !res %% res <? a |_| b;
  }
bool gte___(int a, int b)
  case {
    a >= b -> ensures  res %% res <? a |_| b;
    a <  b -> ensures !res %% res <? a |_| b;
  }
bool land___(bool a, bool b)
  case {
     a -> case {
       b -> ensures  res %% res <? a |_| b;
      !b -> ensures !res %% res <? a |_| b;
    }
    !a -> ensures !res %% res <? a |_| b;
  }
bool lor___(bool a, bool b)
  case {
     a -> requires true ensures res %% res <? a |_| b;
    !a -> case {
       b -> ensures  res %% res <? a |_| b;
      !b -> ensures !res %% res <? a |_| b;
    }
  }
bool not___(bool a)
  case {
     a -> ensures !res %% res <? a |_| b;
    !a -> ensures  res %% res <? a |_| b;
  }
//////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////
// <NEW> PRIMITIVE RELATIONS
//////////////////////////////////////////////////////////////////
relation induce(int value) == true. // Special Relation: indicate the value to do induction on
relation dom (int [] a, int low, int high).
relation domb(bool[] a, int low, int high).

axiom dom (a,low,high) & low<=l & h<=high ==> dom (a,l,h).
axiom domb(a,low,high) & low<=l & h<=high ==> domb(a,l,h).
axiom domb(a,low,high) & low<=l | h<=high ==> domb(a,l,h).

relation update_array_1d_b(bool[] a, bool[] b, bool val, int i).
relation update_array_1d  (int [] a, int [] r, int  val, int i).
relation update_array_2d  (int[,] a, int[,] r, int  val, int i, int j).

relation amodr(int[] a, int[] b, int i, int j) ==
    forall(k : (i<=k & k<=j | a[k] = b[k])).
//////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////
// <NEW> ARRAY FUNCTIONS
//////////////////////////////////////////////////////////////////
// 1D array access
int array_get_elm_at___1d(int[] a, int i)
  requires true
  ensures res = a[i] %% res <? a |_| i;
bool array_get_elm_at___1d(bool[] a, int i)
	requires [ahalb,ahaub]
				domb(a,ahalb,ahaub)
				& ahalb <= i
				& i <= ahaub
	ensures res = a[i] %% res <? a |_| i;

// 2D array access
int array_get_elm_at___2d(int[,] a, int i, int j)
	requires true
	ensures res = a[i,j] %% res <? a |_| i |_| j;
//////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////
// CONCURRENCY
//////////////////////////////////////////////////////////////////
// Thread Object: thrd, barrier, lock [carrying resource]
data thrd{}
data barrier{
  int phase;
}
data lock{
}

// Concurrency Operations
int fork()
  requires true
  ensures  true;
void join()
  requires true
  ensures  true;
void init()
  requires true
  ensures  true;
void finalize()
  requires true
  ensures  true;
void acquire()
  requires true
  ensures  true;
void release()
  requires true
  ensures  true;
//////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////
// POINTER TRANSLATION
//////////////////////////////////////////////////////////////////
// Pointer Object: integer pointer & integer double pointer
data int_ptr{
  int val;
}
data int_ptr_ptr{
  int_ptr val;
}

// Pointer Operations
void delete_ptr(int_ptr@R x)
  requires x::int_ptr<v>
  ensures  true;
void delete_ptr(int_ptr_ptr@R x)
  requires x::int_ptr_ptr<v>
  ensures  true;
//////////////////////////////////////////////////////////////////

int[] update___1d(int v, ref int[] a, int i)
  requires true
  ensures  update_array_1d(a,res,v,i);
bool[] update___1d(bool v, bool[] a, int i)
	requires [ahalb,ahaub] domb(a,ahalb,ahaub) & ahalb <= i & i <= ahaub
	ensures domb(res,ahalb,ahaub) & update_array_1d_b(a,res,v,i);

int[,] update___2d(int v, int[,] a, int i, int j)
	requires true
	ensures  update_array_2d(a,res,v,i,j);

int[] aalloc___(int dim)
	requires true
	ensures  dom(res,0,dim-1);

pred_prim memLoc<heap:bool,size:int> inv size>0;

//////////////////////////////////////////////////////////////////
// BAG
//////////////////////////////////////////////////////////////////
relation set_comp(bag((Object,Object)) g, bag(Object) S, Object d).
relation concrete(bag(Object) g).
relation cyclic(bag((Object,Object)) g).
relation acyclic(bag((Object,Object)) g).
relation waitS(bag((Object,Object)) g, bag(Object) S, Object d).
//////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////
// RANDOM & NON-DETERMINISM
//////////////////////////////////////////////////////////////////
int rand_int ()
  requires true
  ensures  true;

bool rand_bool ()
  requires true
  ensures  res or !res;
//////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////
// STRING
//////////////////////////////////////////////////////////////////
// String Object
data char_star {
  int val;
  char_star next;
}

// String Predicates
WSS<p> ==
  self::WFSeg<q> * q::char_star<0, p>
  inv true;
WFSeg<p> ==
  self = p
  or self::char_star<v, q> * q::WFSeg<p> & v!=0
  inv true;
WSSN<p, n> ==
  self::WFSegN<q, n-1> * q::char_star<0, p>
  inv self!=null & n>=0;
WFSegN<p, n> ==
  self = p & n = 0
  or self::char_star<v, q> * q::WFSegN<p, n-1> & v!=0
  inv n>=0;
MEM<> ==
  self = null or
  self::char_star<_, p> * p::MEM<>;
pred_extn size[R]<k> ==
   k=0
   or R::size<i> & k=1+i
   inv k>=0;

// String Operations
char_star __plus_plus_char(char_star x)
  requires x::char_star<_,q>@L & Term[]
  ensures  res=q ;
int __get_char(char_star x)
  requires x::char_star<v,_>@L & Term[]
  ensures  res=v;
void __write_char(char_star x, int v)
  requires x::char_star<_,q> & Term[]
  ensures  x::char_star<v,q>;
char_star plus_plus_char(char_star x)
  requires x::char_star<_,q>@L & Term[]
  ensures  res=q ;
int get_char(char_star x)
  requires x::char_star<v,_>@L & Term[]
  ensures  res=v;
void write_char(char_star x, int v)
  requires x::char_star<_,q> & Term[]
  ensures  x::char_star<v,q>;
//////////////////////////////////////////////////////////////////

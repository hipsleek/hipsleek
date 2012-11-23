class __DivByZeroErr  extends __Error {}
class __ArrBoundErr  extends __Error {}

int add___(int a, int b) 
  requires true 
  ensures res = a + b;

int minus___(int a, int b) 
  requires true
  ensures res = a - b;

int mult___(int a, int b) 
  requires true 
  ensures res = a * b;

int div___(int a, int b) 
 case {
  a >= 0 -> case {
    b >= 1 -> ensures (exists r: a = b*res + r & res >= 0 & 0 <= r <= b-1);
    b <= -1 -> ensures (exists r: a = b*res + r & res <= 0 & 0 <= r <= -b-1);
    -1 < b < 1 -> ensures true & flow __DivByZeroErr;
    }
  a < 0 -> case {
    b >= 1 -> ensures (exists r: a = b*res + r & res <= -1 & 0 <= r <= b-1);
    b <= -1 -> ensures (exists r: a = b*res + r & res >= 1 & 0 <= r <= -b-1);
    -1 < b < 1 -> ensures true & flow __DivByZeroErr;
    }
}


int div2(int a, int b)
 requires true 
 case {
  b != 0 -> ensures true;
  b = 0 -> ensures true & flow __DivByZeroErr; 
 }

int div3(int a, int b) 
 case {
  b = 0 -> requires false ensures false;
  b != 0 -> ensures true;
 }

int div4(int a, int b) 
  requires b != 0 
  ensures true;

int mod___(int a, int b) case {
  a >= 0 -> case {
	b >= 1 -> case {
	  a < b -> ensures res = a;
	  a >= b -> case {
		a < 2*b -> ensures res = a - b;
		a >= 2*b -> ensures (exists q: a = b*q + res & q >= 0 & 0 <= res <= b-1);
	  }
	}
    b <= -1 -> ensures (exists q: a = b*q + res & q <= 0 & 0 <= res <= -b-1);
    -1 < b < 1 -> ensures true & flow __DivByZeroErr;
  }
  a < 0 -> case {
    b >= 1 -> ensures (exists q: a = b*q + res & q <= -1 & 0 <= res <= b-1);
    b <= -1 -> ensures (exists q: a = b*q + res & q >= 1 & 0 <= res <= -b-1);
    -1 < b < 1 -> ensures true & flow __DivByZeroErr;
  }
}

bool eq___(int a, int b) 
  case {
    a = b -> ensures res;
    a != b -> ensures !res;}

bool eq___(bool a, bool b) 
  case {
    a = b -> ensures res;
    a != b -> ensures !res;}

bool eq___(float a, float b) 
  case {
    a = b -> ensures res;
    a != b -> ensures !res;}

bool neq___(int a, int b) 
  case {
    a = b -> ensures !res;
    a != b -> ensures res;}

bool neq___(bool a, bool b) case {
    a = b -> ensures !res;
    a != b -> ensures res;}

bool neq___(float a, float b) case {
    a = b -> ensures !res;
    a != b -> ensures res;}

bool lt___(int a, int b) case {
    a <  b -> ensures  res;
    a >= b -> ensures !res;}

bool lt___(float a, float b) case {
    a <  b -> ensures  res;
    a >= b -> ensures !res;}

bool lte___(int a, int b) case {
    a <= b -> ensures  res;
    a >  b -> ensures !res;}

bool lte___(float a, float b) case {
    a <= b -> ensures  res;
    a >  b -> ensures !res;}

bool gt___(int a, int b) case {
    a >  b -> ensures  res;
    a <= b -> ensures !res;}

bool gt___(float a, float b) case {
    a >  b -> ensures  res;
    a <= b -> ensures !res;}

bool gte___(int a, int b) case {
    a >= b -> ensures  res;
    a <  b -> ensures !res;}

bool gte___(float a, float b) case {
    a >= b -> ensures  res;
    a <  b -> ensures !res;}

bool land___(bool a, bool b) case {
  a -> case { b -> ensures res; 
              !b -> ensures !res;}
 !a -> ensures !res;}

bool lor___(bool a, bool b) case {
  a -> requires true ensures res;
  !a -> case { b -> ensures res; 
                !b -> ensures !res;}}

bool not___(bool a) 
   case { a -> ensures !res; 
          !a -> ensures res;}

int pow___(int a, int b) 
   requires true 
   ensures true;



//////////////////////////////////////////////////////////////////
// <NEW> PRIMITIVE RELATIONS
//////////////////////////////////////////////////////////////////

// Special relation to indicate the value to do induction on
relation induce(int value) == true.

relation dom(int[] a, int low, int high).

relation domb(bool[] a, int low, int high).

axiom dom(a,low,high) & low<=l & h<=high ==> dom(a,l,h).

axiom domb(a,low,high) & low<=l & h<=high ==> domb(a,l,h).

relation update_array_1d_b(bool[] a, bool[] b, bool val, int i).

relation update_array_1d(int[] a, int[] r, int val, int i).

relation update_array_2d(int[,] a, int[,] r, int val, int i, int j).

relation amodr(int[] a, int[] b, int i, int j) == 
    forall(k : (i<=k & k<=j | a[k] = b[k])).

relation bnd(int[] a, int i, int j, int low, int high) == 
 	(i > j | i<=j & forall ( k : (k < i | k > j | low <= a[k] <= high))).

//////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////


//////////////////////////////////////////////////////////////////
// <NEW> PRIMITIVE FUNCTIONS
//////////////////////////////////////////////////////////////////

int array_get_elm_at___1d(int[] a, int i) 
	requires [ahalb,ahaub]
				dom(a,ahalb,ahaub) 
				& ahalb <= i 
				& i <= ahaub
	ensures res = a[i];
	
bool array_get_elm_at___1d(bool[] a, int i) 
	requires [ahalb,ahaub]
				domb(a,ahalb,ahaub) 
				& ahalb <= i 
				& i <= ahaub
	ensures res = a[i];

// 2D array access
int array_get_elm_at___2d(int[,] a, int i, int j) 
	requires true
	ensures res = a[i,j];

int[] update___1d(int v, int[] a, int i)
	requires [ahalb,ahaub]
				dom(a,ahalb,ahaub) 
				& ahalb <= i 
				& i <= ahaub
	ensures dom(res,ahalb,ahaub) 
				& update_array_1d(a,res,v,i);
				
				
bool[] update___1d(bool v, bool[] a, int i)
	requires [ahalb,ahaub] domb(a,ahalb,ahaub) & ahalb <= i & i <= ahaub
	ensures domb(res,ahalb,ahaub) & update_array_1d_b(a,res,v,i);

int[,] update___2d(int v, int[,] a, int i, int j)
	requires true
	ensures update_array_2d(a,res,v,i,j);

int[] aalloc___(int dim) 
	requires true 
	ensures dom(res,0,dim-1);

//////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////

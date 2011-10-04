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
    /* -1 < b < 1 -> requires false ensures false; */
    -1 < b < 1 -> ensures true & flow __DivByZeroErr;
    }
  a < 0 -> case {
    b >= 1 -> ensures (exists r: a = b*res + r & res <= -1 & 0 <= r <= b-1);
    b <= -1 -> ensures (exists r: a = b*res + r & res >= 1 & 0 <= r <= -b-1);
    /* -1 < b < 1 -> requires false ensures false; */
    -1 < b < 1 -> ensures true & flow __DivByZeroErr;
    }
}


// why is flow of div2 __Error rather __DivByZeroErr?
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

int mod(int a, int b) case {
  a >= 0 -> case {
    b >= 1 -> ensures (exists q: a = b*q + res & q >= 0 & 0 <= res <= b-1);
    b <= -1 -> ensures (exists q: a = b*q + res & q <= 0 & 0 <= res <= -b-1);
    -1 < b < 1 -> ensures true & flow __DivByZeroErr;
    /* -1 < b < 1 -> requires false ensures false; */
  }
  a < 0 -> case {
    b >= 1 -> ensures (exists q: a = b*q + res & q <= -1 & 0 <= res <= b-1);
    b <= -1 -> ensures (exists q: a = b*q + res & q >= 1 & 0 <= res <= -b-1);
    -1 < b < 1 -> ensures true & flow __DivByZeroErr;
    /* -1 < b < 1 -> requires false ensures false; */
  }
}
/*
float add___(float a, float b) 
  requires true 
  ensures res = a + b;

float minus___(float a, float b) 
  requires true 
  ensures res = a - b;


float mult___(float a, float b) 
  requires true 
  ensures res = a * b;

float div___(float a, float b) 
 case {
  b = 0.0 -> ensures true & flow __DivByZeroErr;
  b != 0.0 -> ensures res = a / b;
 }
// requires b!=0.0
// ensures ensures res = a / b;
*/
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
// <OLD> SPECIFICATIONS
//////////////////////////////////////////////////////////////////
//
//relation update_array(int[] a, int i, int v, int[] r) == true.
//
//int array_get_elm_at___(int[] a, int i) 
//   requires true 
//   ensures res = a[i];
//
//int[] update___(int[] a, int i, int v) 
//   requires true 
//   ensures update_array(a,i,v,res);
//
//////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////


//////////////////////////////////////////////////////////////////
// <NEW> PRIMITIVE RELATIONS
//////////////////////////////////////////////////////////////////

// Special relation to indicate the value to do induction on
relation induce(int value) == true.

relation dom(int[] a, int low, int high) == true.

relation update_array(int[] a, int i, int val, int[] r) == true.

relation amodr(int[] a, int[] b, int i, int j) == 
    forall(k : (i<=k & k<=j | a[k] = b[k])).

relation bnd(int[] a, int i, int j, int low, int high) == 
 	(i > j | i<=j & forall ( k : (k < i | k > j | low <= a[k] <= high))).

//////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////


//////////////////////////////////////////////////////////////////
// <NEW> PRIMITIVE FUNCTIONS
//////////////////////////////////////////////////////////////////

int array_get_elm_at___(int[] a, int i) 
  requires [ahalb,ahaub]
				dom(a,ahalb,ahaub) 
				& ahalb <= i 
				& i <= ahaub
  ensures true;
  requires true
  ensures res = a[i];
  /*
	requires [ahalb,ahaub]
				dom(a,ahalb,ahaub) 
				& ahalb <= i 
				& i <= ahaub
	ensures res = a[i];
  */

int[] update___(int[] a, int i, int v) 
//void update___(ref int[] a, int i, int v) 
	requires [ahalb,ahaub]
				dom(a,ahalb,ahaub) 
				& ahalb <= i 
				& i <= ahaub
     ensures dom(res,ahalb,ahaub);//'
     requires true
	 ensures  update_array(a,i,v,res);//'
     /* requires [s,b,low,high] bnd(a,s,b,low,high) & s<=i<=b & low<=v<=high */
     /* ensures bnd(res,s,b,low,high); */
/*	requires [ahalb,ahaub]
				dom(a,ahalb,ahaub) 
				& ahalb <= i 
				& i <= ahaub
	ensures dom(res,ahalb,ahaub) 
				& update_array(a,i,v,res);
*/


int[] aalloc___(int dim) 
	requires true 
	ensures dom(res,0,dim-1);

//////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////

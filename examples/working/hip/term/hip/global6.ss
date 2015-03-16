data node {
	int val;
	node next;
}

ll<n> == self=null & n=0
	or self::node<_, r> * r::ll<n-1>
	inv n>=0;

// bug triggered by presence of global

global int a,b,c,d,e;
global node x2;



int f1() {
  a = a + 1;
  return f2();
}

int f2() {
  b = b + 1;
  return f3();
}


int f3() {
  c = c + 1;
  return f4();
}

int f4() {
  d = 10;
  return f5();
}

int f5() {
  if (e > 0) {
    e--;
    return f4();
  } else {
    return 15;
  }
}

int foo22(node x)
	requires x::ll<n> & n>3
	ensures true;
{

  node x2=x.next;
  node x3 = x.next;
  int z;
  {
    int z;
    z=z+1;
  bind x3 to (v,n) in { z= v; } 
  return z;
  }
}


// see ../hip/global6.ss

struct node {
  int val;
  struct node *next;
};

/*@
ll<n> == self=null & n=0
  or self::node<_, p> * p::ll<n-1>
  inv n>=0;
*/

int a,b,c,d,e;
struct node x2;

int f1()
/*@
  requires true
  ensures true;
*/
{
  a = a + 1;
  return f2();
}

int f2()
/*@
  requires true
  ensures true;
*/
{
  b = b + 1;
  return f3();
}


int f3()
/*@
  requires true
  ensures true;
*/
{
  c = c + 1;
  return f4();
}

int f4()
/*@
  requires true
  ensures true;
*/
{
  d = 10;
  return f5();
}

int f5()
/*@
  requires true
  ensures true;
*/
{
  if (e > 0) {
    e--;
    return f4();
  } else {
    return 15;
  }
}

int foo22(struct node x)
/*@
	requires x::ll<n> & n>3
	ensures true;
*/
{
  struct node x1 = *(x.next);
  struct node x2 = *(x1.next);
  struct node x3 = *(x2.next);
  int z;
  z=z+1;
  //@bind x3 to (v,n) in { z= v; } 
  return z;
}

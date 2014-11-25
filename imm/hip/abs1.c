struct node{
 int val;
 struct node* next;
};


/*@
ll<> == self=null or
  self::node<_,q>*q::ll<>
  inv true;
*/

void foo(struct node* x) __attribute__ ((noreturn))
/*@  requires x::ll<>
     ensures  x::ll<>;
*/;
  
void test(struct node* x)
/*@  requires x::ll<>
     ensures  x::ll<>;
*/
{
  int a;
}


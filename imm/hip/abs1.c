struct node{
 int val;
 struct node* next;
};

/*@

ll<> == self::node<_,null> or
  self::node<_,q> * q::ll<>
  inv self!=null;

sll<m> == self::node<v,null> & m = v or
  self::node<v,q> * q::sll<min_tail> & m = min(v, min_tail)
  inv self!=null;
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
  foo(x);
}


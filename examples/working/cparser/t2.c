struct node {
  int val;
  struct node* next;
};

/*@
ll<n> == self=null & n=0
  or self::node^<_, q> * q::ll<n-1>
  inv n>=0;
*/

void* malloc(int size) __attribute__ ((noreturn))
/*@
  case {
    size <= 0 -> requires true ensures res = null;
    size >  0 -> requires true ensures res != null;
  }
*/;


struct node* f(int x)
/*@
  requires true
  ensures res::ll<1> & 4<x
      or res::ll<2> & 0<x<=4
      or res::ll<3> & x<=0;
*/
{
  struct node* y = malloc(sizeof(struct node));
  if (x>0) {
    y->val = 1;
    y->next = NULL;
  } else {
    struct node z = {6, NULL};
    y->val = 5;
    y->next = &z;
  }
 
  if (x>4) {
    //y=y;
  } else{
    struct node* z = malloc(sizeof(struct node));
    z->val = 2;
    z->next = y;
    y = z;
  };
  
  return y;
}



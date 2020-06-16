//Ex.4: Memory Leak
struct node
{
  int data;
  struct node *next;
};

/*@
pred ll<n> == self = null & n = 0
           or self::node<_, q> * q::ll<n-1>
   inv n >= 0;

pred lseg<n,q> == self = q & n=0
           or self::node<_, q> * q::lseg<n-1,q>
   inv n >= 0;
*/

struct node *malloc(int size)
/*@
  case {
    size <= 0 -> requires true ensures res = null;
    size >  0 ->
      requires true
      ensures res::node<_, _>;
  }
*/;



// Memory Leak Example
int main()
/*@
  requires true
  ensures res=0;
*/
{
  struct node *head = NULL;
  struct node **p = &head;
  /*@
    dprint;
  */


  /*@
    assert head'=null;
  */

  return 0;
}


/*
ex4c.c

addr_head::node_star<q> * q::node<null> & head'=q
p = addr_head


int main()[]
static EBase: [][](htrue) * ([] & true)( FLOW __norm) {EAssume: 3,:(emp) * ([] & res = 0)( FLOW __norm)}
dynamic EBase: [][](hfalse) * ([] & false)( FLOW __false) 
{
{local: node head,node_star p
node head
node_star p
{member access head~~>value = (107, ):__cast_void_pointer_to_node__(null)
p = head
dprint
 :assert_inexact EBase: [][](emp) * ([] & head' = null)( FLOW __norm) 
 assume: 

(111, ):return 0}}
}

*/

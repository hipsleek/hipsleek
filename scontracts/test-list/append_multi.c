struct node{
 int val;
 struct node* next;
};

/*@
  list<n,B> == self=null & n=0 & B={}
           or self::node<v,q> * q::list<n-1,B1> & B = union(B1,{v})
  inv n>=0;

  lseg<p, n> == self=p & n=0
           or self::node<_, q> * q::lseg<p, n-1>
  inv n>=0;

  lseg_x<p, n, x> == self=p & n=0
           or self::node<x, q> * q::lseg_x<p, n-1, x>
  inv n>=0;

  // ll with all elements 0
  // ll with all elements 1

  // method to update part of one list
*/

void update(struct node* x, int n, int num)
/*@
     case {
       x!=null ->
           requires x::lseg<null,n> & num>=0 & num<=n
           ensures  x::lseg_x<z,num,0> * z::lseg<null,n-num>;
       x=null  ->
          requires true
          ensures  true;
     }
*/
{
    if(x==NULL || num==0) return;
    else {
        x->val = 0;
        update(x->next,n-1,num-1);
    }
}

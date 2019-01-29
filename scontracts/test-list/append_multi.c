struct node{
 int val;
 struct node* next;
};

/*@
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

void update1(struct node* x, int num)
/*@
     case {
       x!=null ->
           requires x::lseg<null,n> & num>=0
           ensures  x::lseg_x<z,num,0> * z::lseg<null,n-num> & num<n
                 or x::lseg_x<z,n,0> & num>=n;
       x=null  ->
          requires true
          ensures  true;
     }
*/
{
    if(x==NULL || num==0) return;
    else {
        x->val = 0;
        update1(x->next,num-1);
    }
}

void update2(struct node* x, int num)
/*@
     case {
       x!=null ->
           case {
             num<n  ->
                requires x::lseg<null,n> & num>=0
                ensures  x::lseg_x<z,num,0> * z::lseg<null,n-num>;
             num>=n ->
                requires x::lseg<null,n> & num>=0
                ensures  x::lseg_x<z,n,0>;
           }
       x=null  ->
          requires true
          ensures  true;
  }
*/
{
    if(x==NULL || num==0) return;
    else {
        x->val = 0;
        update2(x->next,num-1);
    }
}

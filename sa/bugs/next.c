#include "inc.h"

struct node* get_next(struct node* x)
{
  return x->next;
}

struct node* testhar(struct node* x)
/*@
  requires x::node<_,null>
  ensures x::node<_,null> & res=null;
*/
{
  return get_next(x);
}

/*
[ HP_18(x) ::= x::node<key,DP>@M,
 GP_19(x,res) ::= x::node<key,res>@M]

===>
HP_18(x) ::= x::node<key,DP>@M,
 GP_19(x,res) ::= x::node<key,res> & res = DP@M
 */

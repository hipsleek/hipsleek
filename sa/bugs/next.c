#include "inc.h"

struct node* get_next(struct node* x)
{
  return x->next;
}

/*
[ HP_18(x) ::= x::node<key,DP>@M,
 GP_19(x,res) ::= x::node<key,res>@M]

===>
HP_18(x) ::= x::node<key,DP>@M,
 GP_19(x,res) ::= x::node<key,res> & res = DP@M
 */

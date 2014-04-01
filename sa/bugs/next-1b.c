#include "../bugs/inc.h"

struct node* get_next(struct node* x)
{
  struct node* tmp = x;
  tmp->next = NULL;
  return x;
}



/*
[ HP_18(x) ::= x::node<key,DP>@M,
 GP_19(x,res) ::= x::node<key,res>@M]

===>
HP_18(x) ::= x::node<key,DP>@M,
 GP_19(x,res) ::= x::node<key,res> & res = DP@M
 */

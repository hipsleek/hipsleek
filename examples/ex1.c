#include<stdio.h>

struct node {
    int val;
    struct node *next;
};

/*@
  ll<sum> == self=null & sum = 0
          or self::node<v, r> * r::ll<sum2> & sum = v + sum2;
*/

int main() {
    struct node* x;
    return 1;
}

int sum(struct node* x)
/*@
  requires x::ll<n> ensures res = n;
*/
{
    if (x == NULL) return 0;
    else {
        int k;
        k = sum(x->next);
        return x->val + k;
    }
}

#include "stdlib.h"

struct node
{
  int val;
};

struct node* nodenew()
{
  struct node * ans = (struct node *)calloc(1, sizeof(struct node));
  return ans;
}

struct node {
  int key;
  struct node* next;
};

//need control-sensitive analysis

// x: mut
struct node* get_next(struct node* x,struct node* y)
{
  struct node* tmp = x;
  tmp = y;
  return tmp;
}

//x: imm
/* struct node* get_next2(struct node* x,struct node* y) */
/* { */
/*   struct node* tmp = y; */
/*   tmp = x; */
/*   return tmp; */
/* } */

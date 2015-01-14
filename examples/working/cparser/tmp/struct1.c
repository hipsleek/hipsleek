struct node {
  int val;
  struct node *x;
};

int main ()
/*@
  requires true
  ensures true;
*/
{
  struct node m;
  return 0;
  
}

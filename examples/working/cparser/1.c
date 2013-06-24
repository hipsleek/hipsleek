struct node{
  int x;
  int y;
}

struct node foo()
/*@
  requires true
  ensures false;
*/;

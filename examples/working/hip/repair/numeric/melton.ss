data node {
	int val;
  int next;
}

node malloc()
  requires true ensures res::node<_, _>;


// void foo()
// requires true ensures true;
// {
//    node a = malloc();

//    node b = malloc();

//    a.val = 3;
//    // free(a);
//    free(b);

// }

// 

void foo(int x)
requires true ensure true;
{
  x = x + 1;
  node a = malloc();
  a.val = 3;
  if (x < 6){
     
  }

}
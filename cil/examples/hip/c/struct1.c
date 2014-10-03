struct point {
  int x;
  int y;
};


int foo()
{
  struct point px;
  px.x = 0;
  px.y = 1;
  return px.x;
}


/*
  Expected 

*/

//../hip -infer "@shape_prepost"

void test_fun(int* x)
/*
  infer [@term]
  requires true
  ensures true;
*/
{
    *x = *x + 1;
}

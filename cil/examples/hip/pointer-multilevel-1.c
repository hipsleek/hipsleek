int foo1 (int* p)
/*@
  requires p::int^<i>
  ensures p::int^<i-1>;
*/
{
  *p = *p-1;
  return 0;
}


int foo2 (int** p)
/*@
  requires p::int^^<i>
  ensures p::int^^<i-1>;
*/
{
  **p = **p-1;
  return 0;
}

int foo3 (int*** p)
/*@
  requires p::int^^^<i>
  ensures p::int^^^<i-1>;
*/
{
  ***p = ***p-1;
  return 0;
}

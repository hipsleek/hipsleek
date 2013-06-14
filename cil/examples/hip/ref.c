void foo1(int* a)
/*@
  requires a::int^<p>
  ensures a::int^<p-1>;
*/
{
  (*a)--;
}


void foo2(int** a)
/*@
  requires a::int^^<p>
  ensures a::int^^<p-1>;
*/
{
  (**a)--;
}

void foo3(int*** a)
/*@
  requires a::int^^^<p>
  ensures a::int^^^<p-1>;
*/
{
  (***a)--;
}

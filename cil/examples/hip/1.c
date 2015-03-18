int foo1 (int* xxx1)
/*@
  requires xxx1::int^<p>
  ensures xxx1::int^<p-1>;
*/
{
  *xxx1 = *xxx1-1;
  return 0;
}


int foo2 (int** xxx2)
/*@
  requires xxx2::int^^<p>
  ensures xxx2::int^^<p-1>;
*/
{
  **xxx2 = **xxx2-1;
  return 0;
}

int foo3 (int*** xxx3)
/*@
  requires xxx3::int^^^<p>
  ensures xxx3::int^^^<p-1>;
*/
{
  ***xxx3 = ***xxx3-1;
  return 0;
}

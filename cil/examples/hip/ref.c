void foo(int* a)
/*@
  requires a::int*<p>
  ensures a::int*<p-1>;
*/
{
  (*a)--;
}

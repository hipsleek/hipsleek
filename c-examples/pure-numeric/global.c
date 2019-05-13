int k;
int n;

/*@
relation A(int x, int y, int z).
*/

void increase()
/*@
  infer [A]
  requires true
  ensures A(n, k, k');
*/
{
	k = k+n;
  //@ dprint;
}

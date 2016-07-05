/**
 * Test the array allocation using new expression.
 * 
 * @author Vu An Hoa
 */
int main()
	requires true
	ensures res = 5;
{
	int[] a;
	// new expression will add domain constraint: dom(a',0,4) 
	a = new int[5];
	a[0] = 0;
	a[1] = 1;
	a[1 + 1] = 3;
  a[2] = a[2] + 1;
	int x = a[0] + a[2 - 1] + a[2];
  dprint;
	return x;
}

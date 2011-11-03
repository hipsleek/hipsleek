int main()
	requires true
	ensures res = 4;
{
	int[] a;
	// new expression will add domain constraint: dom(a',0,4) 
	a = new int[5];
	a[0] = 0;
	a[1] = 1;
	a[2] = 3;
	int x = a[0] + a[1] + a[2];
	return x;
}
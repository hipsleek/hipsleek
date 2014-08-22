void loop (int x)
/*
requires true
ensures true;
*/
case {
   x<=0 -> requires Term[] ensures true;
   x>0 -> requires Term[x] ensures true;
 }
{
	if (x<=0) return;
	else loop(x-1);
}

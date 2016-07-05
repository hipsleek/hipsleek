void main ()
requires Loop
ensures false;
{
	int bob = 13;
	int samantha = 17;
	loop(bob, samantha);
}

void loop (ref int bob, ref int samantha)
case {
	bob+samantha>=100 -> requires Term ensures true;
	bob+samantha<100 -> requires Loop ensures false;
}
{
	if (bob + samantha < 100) {
		int temp = bob;
		bob = samantha;
		samantha = temp;
		loop(bob, samantha);
	}
}

int f91(int n)
requires true 
ensures n<=100 & res=91 or n>100 & res=n-10;
{
	if (n>100) return (n-10);
       	else {
		return f91(f91(n+11));
	}
}

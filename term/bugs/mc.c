#include<stdio.h>

int gd=300;
void mc (int x, int c)
{
 int d;
           d = 200+21*c-2*x;
//	 if (gd<=d)  
           printf("(%d,%d,%d,%d)-> \n",x,c,d,gd);
	 gd =d;
 if (c>0)
	{
	   if (x>100)
	   {
		  x=x-10;
		  c=c-1;
	   }
	   else
	   {
		x=x+11;
		c=c+1;
	   }
	   mc(x,c);
	}
}

int main()
{
	int x=1,c=1;
	for(x=-10000;x<=10000; x++)
	{//gd = 200+21*c-2*x+1;
	gd = -10000;
	scanf("%d",&x);
	 mc(x,c);
	}
}

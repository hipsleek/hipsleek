class KnapsackDP
{
    static int nbObjects;
    static int [] weight={2,3,5,2,4,6,3,1};
    static int [] utility={5,8,14,6,13,17,10,4};
    static int weightmax=12;
    static int [] [] array;

    // Display the table
    static void consoleDisplay()
    {
	int i,j;
	for(i=0;i<nbObjects;i++) 
	    {
		for(j=0;j<=weightmax;j++)
		    {
			//System.out.print(array[i][j]+"\t");
		    }
		//System.out.println("");
	    }
    }

    // LateX
    static void Display()
    {
	int i,j;
	for(i=0;i<nbObjects;i++) 
	    {
		for(j=0;j<=weightmax;j++)
		    {
			if (j!=weightmax) {} //System.out.print(array[i][j]+" & ");
			else {} //System.out.print(array[i][j]+" ");
		    }
		//System.out.println("\\\\");
	    }
}

    // Extract the solution from the table
    static void InterpretArray()
    {
	int i,u,w;
	u=0;
	w=weightmax;
	
	for(i=nbObjects-1;i>=1;i--)
	    {
		if (array[i][w]!=array[i-1][w])
		    {
			//System.out.print((i+1)+" ");
			w=w-weight[i];
			u=u+utility[i];
		    }
	    }

	if (array[0][w]!=0);	
	{
	    //System.out.println("1");
	    w=w-weight[0];
	    u=u+utility[0];
	}
	
	//System.out.println("Cross check:"+u+" remaining weight "+w);
}

    static int max(int a, int b)
    {
	//if (a>b) return a; else return b;
	return ( (a>b) ? (a) : (b) );
    }

    static void SolveDP()
    {
	int i,j;
	array=new int[nbObjects][weightmax+1];
	
	// initialize the first row	
	for(j=0;j<=weightmax;j++)
	    if (j<weight[0]) array[0][j]=0; 
	    else array[0][j]=utility[0];			
	// for all other rows
	for(i=1;i<nbObjects;i++)
	    {
		for(j=0;j<=weightmax;j++)
		    if (j-weight[i]<0) array[i][j]=array[i-1][j];
		    else
			array[i][j]=max( array[i-1][j],
					 array[i-1][j-weight[i]]+utility[i]);	
	    }
    }

    public static void main(String[] args)
    {
	//System.out.println("Solving knapsack using the dynamic programming paradigm.");
	nbObjects = args.length;
	SolveDP();
	Display();
	//System.out.println("Reading solution:");
	InterpretArray();
    }
}

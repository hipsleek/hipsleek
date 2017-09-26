int fun(int i, int j)
case{
     i>j -> requires i>j ensures res = 0;
     i<=j -> requires i<=j ensures res = 0;
	 
     }
{
 if(i>j){
	 return fun(i,j+1);
		}
   else{
	return 0;
	       }
   }

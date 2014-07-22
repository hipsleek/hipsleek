/**
 Example: array initialization.
 **/
 
pred_prim arr<low:int,high:int,s:bag(int)>
  inv low<=high;

lemma a::arr<i,k,S> & i<=j<k 
  <-> a::arr<i,j,S1> * a::arr<j+1,k,S2>
    & S=union(S1,S2);

void update_arr(int v,arr a,int i)
  requires a::arr<i,i,_>
  ensures a::arr<i,i,{v}>;

int get_arr(int v,arr a,int i)
  requires a::arr<i,i,S>@L
  ensures res in S;

arr new_arr(int size)
  requires size>0
  ensures res::arr<0,size-1,{0}>;

void initleft(arr a, int i, int j) 
  requires a::arr<i,j,_> 
  ensures a::arr<i,j,{0}>;
{
       	if (i <= j)
	{
          update_arr(0,a,j);
	  initleft(a, i, j-1);
	}
}

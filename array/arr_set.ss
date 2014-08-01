/**
 Example: array initialization.
 **/
 
pred_prim arr<low:int,high:int,s:bag(int)>
  inv low<=high;

pred_prim arr_set<index:bag(int),s:bag(int)>;

upred<i,j,S> == emp & i>j & S={}
   or a::arr<i,i,S1> * a::upred<i+2,j,S2> & S=union(S1,S2);

lemma self::arr<i,k,S> & i<=j<k 
  <-> self::arr<i,j,S1> * self::arr<j+1,k,S2>
    & S=union(S1,S2);

void update_arr(int v,arr a,int i)
  requires a::arr<i,i,_>
  ensures a::arr<i,i,{v}>;

int get_arr(arr a,int i)
  requires a::arr<i,i,S>@L
  ensures res in S;

arr new_arr(int size)
  requires size>0
  ensures res::arr<0,size-1,{0}>;

// Initialize an array from left to right with 0, without loop involved 
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

// Initialize an array with some scalar value, with loop
void initLoop(arr a,int i,int j)
  requires a::arr<i,j,S>
  ensures a::arr<i,j,{0}>;
{
  int k=i;
  while(k<j)
    //requires a::arr<i,k,S> ensures ?;
    {
    update_arr(0,a,k);
    k++;
  }
}

// Update array a with another array b.
// Assuming that these two arrays have the same length
void initWithArr(arr a,arr b,int i,int j)
  requires a::arr<i,j,_> * b::arr<i,j,S>
  ensures a::arr<i,j,S>;
{
  if(i<j){
    update_arr(get_arr(b,i),a,i);
  }
}

// Return the greatest element in an array, without loop
int getMax(arr a,int i,int j)
  requires a::arr<i,j,S>@L
  ensures forall(x: x notin S | res >=x);
{
  if(i==j){
    return get_arr(a,i);
  }
  else{
    int tmp = getMax(a,i+1,j);
    int cur = get_arr(a,i);
    if(tmp>cur){
      return tmp;
    }
    else{
      return cur;
    }
  }
}

// Initialize all the even element in an array
void partialInit(arr a,int i, int j)
//requires a::arr<i,j,S>
// ensures ?? How to capture? Here we only use the range to capture the index. What if we capture the indexes with set too?
{
  
  if(i<j&&i%2==0){
    update_arr(0,a,i);
    partialInit(a,i+1,j);
    
  }
}

// Return the first element of array whose value is x
int sentinel(arr a, int x, int i, int j)
  requires a::arr<i,j,S>
  ensures a::arr<i,res-1,S1> * a::arr<res,res,{x}>*
          a::arr<res+1,j,_> &  x notin S1;
{
  if(i<j){
    if(get_arr(a,i)==x){
      return i;
    }
    else{
      return sentinel(a,x,i+1,j);
    }
  }
  else
    {
      return -1;
    }
}

/*
 Examples for verifying while loop
 */

//SUCCESS
void fun(ref int i)
  requires i=0
  ensures i'=10; //'
{
  while(i<10)
    requires true
    ensures i<10 & i'=10
         or i>=10 & i'=i; //'
  {
    i=i+1;
  }
}

//SUCCESS
void loop_fun(ref int i)
    requires true
    ensures i<10 & i'=10
         or i>=10 & i'=i; //'
{
  if(i<10)
  {
    i=i+1;
    loop_fun(i);
  }
}

//SUCCESS
void loop_fun3(ref int i,ref int j)
  requires true
  ensures i<10 & i'=10 & j'=j+i'-i
       or i>=10 & i'=i & j'=j; //'
{
  if(i<10){
    i=i+1;
    j=j+1;
    loop_fun3(i,j);
  }
}

//SUCCESS
void fun3(ref int i,ref int j)
  requires i=0
  ensures i'=10 & j'=j+10; //'
{
  while(i<10)
    requires true
    ensures i<10 & i'=10 & j'=j+i'-i
         or i>=10 & i'=i & j'=j; //'
  {
    i=i+1;
    j=j+1;
  }
}


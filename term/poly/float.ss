void loop(ref float x)
 case {
  x>0.0 -> requires Term[x] ensures false;
  x<=0.0  -> requires Term ensures x'=x; //'
}
{
  if (x>0.0) loop(x/2.0);
} 

// TODO : BUG incorrect
void loop2(ref float x)
 case {
  x>=0.01 -> requires Term[x] ensures true; // why not x'<0.01;//'
  x<0.01  -> requires Term[] ensures x'=x; //'
}
{
  if (x>=0.01) loop2(x/2.0);
} 


// TODO : BUG incorrect
void loop3(ref float x)
 case {
  x<0.0-0.01 -> requires Term[0.0-x] ensures true; // why not x'<0.01;//'
  x>=0.0-0.01  -> requires Term[] ensures x'=x; //'
}
{
  if (x< 0.0-0.01) loop3(x/2.0);
}  

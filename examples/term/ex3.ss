/*
void loop(ref int x)
 case {
	x>11 	->  requires true ensures x'=10; //'
	x<=11 	->  requires true ensures x'=x-1; //'
 }
// variance x
{
 int xinit=x;
 x=x-1;
 if (x>10) {
   assert xinit'-x>0 & xinit'>11;
   loop(x);
 }
}
*/
/*
void loop(ref int x)
 case {
 x>11 ->  requires xx=1 & x>= 0 ensures x'=10; //'
  x<=11 ->  requires xx=0 ensures x'=x-1; //'
 }
// variance x
{
 int xinit=x;
 x=x-1;
 if (x>10) {
   assert x-x'>0 & xx=1;
   loop(x);
 }
}
*/
void loop(ref int x)
 case {
 x>11 ->  requires true ensures x'=10; //'
  x<=11 ->  requires true ensures x'=x-1; //'
 }
// variance x
{
 int xinit=x;
 x=x-1;
 if (x>10) {
   assert x-x'>0 & x>0;
   loop(x);
 }
}


/*
As-If Infinitely Ranged Integer Model,
http://www.sei.cmu.edu/reports/10tn008.pdf
unsigned int ui1, ui2, usum;
Initialize ui1 and ui2 
if (UINT_MAX - ui1 < ui2) {
 handle error condition 
}
else {
usum = ui1 + ui2;
}
*/

int add(int ui1,int ui2)
case{ (\inf - ui1) < ui2 -> ensures true & flow __Error;
      (\inf - ui1) >= ui2 -> ensures res = ui1 + ui2;}
//requires true
//ensures res = ui1 + ui2;
{
int usum;
usum = ui1 + ui2;
return usum;
}


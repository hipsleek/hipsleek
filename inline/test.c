int main(void)
/*@ requires true
    ensures true;
*/
{
char a[100];

a[2000] = 1;
return 0;
}

/*

int main()[]
static EList
dynamic EBase: [][](hfalse) * ([] & false)( FLOW __false) 
{
{local: int[] a
int[] a
{a[2000] = 1
(98, ):return 0}}
}

{
{local: int[] a
int[] a
{a[2000] = 1
(106, ):return 0}}
}


{(int[] a;
{(a = {((int v_int_8_1816;
(v_int_8_1816 = 1;
(int v_int_8_1815;
v_int_8_1815 = 2000)));
update___1d$int~int[]~int(v_int_8_1816,a,v_int_8_1815))};
(int v_int_9_1817;
(v_int_9_1817 = 0;
ret# v_int_9_1817)))})}


 */

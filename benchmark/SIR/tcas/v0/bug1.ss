relation dom(int[] a, int x, int y) == true.
global int Alt_Layer_Value;	

int ALIM (ref int[] Positive_RA_Alt_Thresh)
    requires  dom(Positive_RA_Alt_Thresh, 0, 3) &  Positive_RA_Alt_Thresh[0] = 400 &  Positive_RA_Alt_Thresh[1] = 500 &
                 Positive_RA_Alt_Thresh[2] = 640 &  Positive_RA_Alt_Thresh[3] = 740 &
                 Alt_Layer_Value = 0
    ensures  dom(Positive_RA_Alt_Thresh', 0, 3)  &  Positive_RA_Alt_Thresh'[0] = 400 &  Positive_RA_Alt_Thresh'[1] = 500 &
                 Positive_RA_Alt_Thresh'[2] = 640 &  Positive_RA_Alt_Thresh'[3] = 740 & Alt_Layer_Value' = 0 &
     (res = 400);
//(res = 400 | res = 500 | res = 640 | res = 740)
{
 return Positive_RA_Alt_Thresh[Alt_Layer_Value];
}


/*
global int v1;
global int v2;

int getv1()
  requires true
  ensures res=v1 & v1'=v1;
{
  return v1;
}

bool test(bool bv)
  requires v1 < v2
 case {
  bv -> ensures v1' < v2' & res;
  !bv -> ensures v1' < v2' & !res;
 }
{
  bool temp = v1 > v2;
  if (temp)
    return !(bv);
  else return bv;
}
*/

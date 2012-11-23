relation dom(int[] a, int x, int y) == true.
global int Alt_Layer_Value;



int ALIM (ref int[] Positive_RA_Alt_Thresh,  ref int Alt_Layer_Value)
 requires  dom(Positive_RA_Alt_Thresh, 0, 3) 
    &  Positive_RA_Alt_Thresh[0] = 400 
    &  Positive_RA_Alt_Thresh[1] = 500 
    &  Positive_RA_Alt_Thresh[2] = 640 
    &  Positive_RA_Alt_Thresh[3] = 740 
    &  Alt_Layer_Value = 0
 ensures  dom(Positive_RA_Alt_Thresh', 0, 3)  
     & Positive_RA_Alt_Thresh'[0] = 400 
     & Positive_RA_Alt_Thresh'[1] = 500 
     & Positive_RA_Alt_Thresh'[2] = 640 
     & Positive_RA_Alt_Thresh'[3] = 740 
     & Alt_Layer_Value' = 0 
     & Alt_Layer_Value'=Alt_Layer_Value
     & Positive_RA_Alt_Thresh'=Positive_RA_Alt_Thresh
     & (res = 400);
//(res = 400 | res = 500 | res = 640 | res = 740)
{
 int k =  Positive_RA_Alt_Thresh[Alt_Layer_Value];
 //dprint;
 return k;
}

int ALIM2 (ref int[] arr,  int i)
 requires  [s,b] dom(arr, s, b) & s<=i<=b 
 ensures  arr'=arr & res=arr[i];
{
 int k =  arr[i];
 return k;
}


int ALIM3 (int[] arr,  int i)
 requires  [s,b] dom(arr, s, b) & s<=i<=b 
 ensures   res=arr[i];
{
 int k =  arr[i];
// k = AIM;
 return k;
}


int ALIM4 (ref int[] arr,  int i)
 requires  [s,b] dom(arr, s, b) & s<=i<b 
 ensures   res=arr[i] & arr'[i+1]=1
              & forall (a: a=(i+1) | arr'[a]=arr[a]) ;
{
 arr[i+1] = 1;
 int k =  arr[i];
 return k;
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

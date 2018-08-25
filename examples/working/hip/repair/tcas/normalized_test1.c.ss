data node {
int fst;
int snd;
int third;
int fourth;
}


global node Positive_RA_Alt_Thresh;
global int Alt_Layer_Value;
global int Cur_Vertical_Sep;
global bool High_Confidence;
global bool Two_of_Three_Reports_Valid;
global int Own_Tracked_Alt;
global int Own_Tracked_Alt_Rate;
global int Other_Tracked_Alt;
global int Up_Separation;
global int Down_Separation;
global int Other_RAC;
global int Other_Capability;
global int Climb_Inhibit;
int int_error()
requires true
ensures false;

int ALIM()

requires Positive_RA_Alt_Thresh::node<a,b,c,d> & Alt_Layer_Value = 0
ensures Positive_RA_Alt_Thresh::node<a,b,c,d> & (Alt_Layer_Value = 0) & (res = a);
requires Positive_RA_Alt_Thresh::node<a,b,c,d> & Alt_Layer_Value = 1
ensures Positive_RA_Alt_Thresh::node<a,b,c,d> & (Alt_Layer_Value = 1) & (res = b);
{
int tmp;
if (Alt_Layer_Value == 0) {
  return Positive_RA_Alt_Thresh.fst;
}
if (Alt_Layer_Value == 1) {
  return Positive_RA_Alt_Thresh.snd;
}
if (Alt_Layer_Value == 2) {
  return Positive_RA_Alt_Thresh.third;
}
if (Alt_Layer_Value == 3) {
  return Positive_RA_Alt_Thresh.fourth;
}
tmp = int_error();
return tmp;
}


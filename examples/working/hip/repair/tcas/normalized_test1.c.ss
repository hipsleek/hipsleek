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
bool __bool_of_int___(int param)
requires param = 0 ensures !(res);
requires param != 0 ensures res;


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
int Inhibit_Biased_Climb()

requires Climb_Inhibit = 1
ensures (Climb_Inhibit = 1) & (res = Up_Separation+100);
requires Climb_Inhibit = 0
ensures (Climb_Inhibit = 0) & (res = Up_Separation);
{
if (__bool_of_int___(Climb_Inhibit)) {
  return Up_Separation + 100;
} else {
return Up_Separation;
}
}
bool Own_Above_Threat()
requires true
ensures ((res) & (Other_Tracked_Alt < Own_Tracked_Alt)) | ((!(res)) & (!(Other_Tracked_Alt < Own_Tracked_Alt)));
{
return Other_Tracked_Alt < Own_Tracked_Alt;
}
bool Own_Below_Threat()
requires true
ensures ((res) & (Other_Tracked_Alt > Own_Tracked_Alt)) | ((!(res)) & (!(Other_Tracked_Alt > Own_Tracked_Alt)));
{
return Own_Tracked_Alt < Other_Tracked_Alt;
}
bool Non_Crossing_Biased_Climb()

requires Positive_RA_Alt_Thresh::node<a,b,c,d> & (Alt_Layer_Value = 0) & ((Climb_Inhibit = 1) & ((Up_Separation+100) > Down_Separation))
ensures Positive_RA_Alt_Thresh::node<a,b,c,d> & (Alt_Layer_Value = 0) & ((Climb_Inhibit = 1) & (((Up_Separation+100) > Down_Separation) & (((res) & ((Own_Tracked_Alt >= Other_Tracked_Alt) | (Down_Separation < a))) | ((!(res)) & (!((Own_Tracked_Alt >= Other_Tracked_Alt) | (Down_Separation < a)))))));
requires Positive_RA_Alt_Thresh::node<a,b,c,d> & (Alt_Layer_Value = 0) & ((Climb_Inhibit = 1) & ((Up_Separation+100) <= Down_Separation))
ensures Positive_RA_Alt_Thresh::node<a,b,c,d> & (Alt_Layer_Value = 0) & ((Climb_Inhibit = 1) & (((Up_Separation+100) <= Down_Separation) & (((res) & ((Own_Tracked_Alt > Other_Tracked_Alt) & ((Cur_Vertical_Sep >= 300) & (Up_Separation >= a)))) | ((!(res)) & (!((Own_Tracked_Alt > Other_Tracked_Alt) & ((Cur_Vertical_Sep >= 300) & (Up_Separation >= a))))))));
{
bool result;
bool tmp;
bool tmp___0;
int tmp___1;
bool tmp___2;
int tmp___3;
int tmp___4;
tmp___4 = Inhibit_Biased_Climb();
if ((tmp___4 - Down_Separation) > 0) {
  tmp = Own_Below_Threat();
tmp___0 = Own_Below_Threat();
tmp___1 = ALIM();
result = (!tmp) || (tmp___0 && (!((Down_Separation - tmp___1) > 0)));
} else {
tmp___2 = Own_Above_Threat();
tmp___3 = ALIM();
result = (tmp___2 && ((Cur_Vertical_Sep - 300) >= 0)) && ((Up_Separation - tmp___3) >= 0);
}
return result;
}


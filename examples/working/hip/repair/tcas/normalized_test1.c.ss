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

void initialize()
requires Positive_RA_Alt_Thresh::node<a,b,c,d> & true
ensures Positive_RA_Alt_Thresh::node<a2,b2,c2,d2> & (a2 = 400) & ((b2 = 500) & ((c2 = 640) & (d2 = 740)));
{
Positive_RA_Alt_Thresh.fst = 400;
Positive_RA_Alt_Thresh.snd = 500;
Positive_RA_Alt_Thresh.third = 640;
Positive_RA_Alt_Thresh.fourth = 740;
}
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
tmp = int_error();
return tmp;
}
int Inhibit_Biased_Climb()

requires Climb_Inhibit = 1
ensures (Climb_Inhibit = 1) & (res = Up_Separation+100);
requires Climb_Inhibit = 0
ensures (Climb_Inhibit = 0) & (res = Up_Separation);
{
int tmp;
if (__bool_of_int___(Climb_Inhibit)) {
  tmp = Up_Separation + 100;
} else {
tmp = Up_Separation;
}
return tmp;
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
int tmp___2;
bool tmp___3;
int tmp___4;
int tmp___5;
int tmp___6;
tmp___6 = Inhibit_Biased_Climb();
if (tmp___6 > Down_Separation) {
  tmp = Own_Below_Threat();
if (tmp) {
  tmp___0 = Own_Below_Threat();
if (tmp___0) {
  tmp___1 = ALIM();
if (Down_Separation > tmp___1) {
  tmp___2 = 0;
} else {
tmp___2 = 1;
}
} else {
tmp___2 = 0;
}
} else {
tmp___2 = 1;
}
result = __bool_of_int___(tmp___2);
} else {
tmp___3 = Own_Above_Threat();
if (tmp___3) {
  if (Cur_Vertical_Sep >= 300) {
  tmp___4 = ALIM();
if (Up_Separation >= tmp___4) {
  tmp___5 = 1;
} else {
tmp___5 = 0;
}
} else {
tmp___5 = 0;
}
} else {
tmp___5 = 0;
}
result = __bool_of_int___(tmp___5);
}
return result;
}
bool Non_Crossing_Biased_Descend()

requires Positive_RA_Alt_Thresh::node<a,b,c,d> & (Alt_Layer_Value = 0) & ((Climb_Inhibit = 1) & ((Up_Separation+100) > Down_Separation))
ensures Positive_RA_Alt_Thresh::node<a,b,c,d> & (Alt_Layer_Value = 0) & ((Climb_Inhibit = 1) & (((Up_Separation+100) > Down_Separation) & (((res) & ((Own_Tracked_Alt < Other_Tracked_Alt) & ((Cur_Vertical_Sep >= 300) & (Down_Separation >= a)))) | ((!(res)) & (!((Own_Tracked_Alt < Other_Tracked_Alt) & ((Cur_Vertical_Sep >= 300) & (Down_Separation >= a))))))));
requires Positive_RA_Alt_Thresh::node<a,b,c,d> & (Alt_Layer_Value = 0) & ((Climb_Inhibit = 1) & ((Up_Separation+100) <= Down_Separation))
ensures Positive_RA_Alt_Thresh::node<a,b,c,d> & (Alt_Layer_Value = 0) & ((Climb_Inhibit = 1) & (((Up_Separation+100) <= Down_Separation) & (((res) & ((Own_Tracked_Alt <= Other_Tracked_Alt) | (Up_Separation >= a))) | ((!(res)) & (!((Own_Tracked_Alt <= Other_Tracked_Alt) | (Up_Separation >= a)))))));
{
bool result;
bool tmp;
int tmp___0;
int tmp___1;
bool tmp___2;
bool tmp___3;
int tmp___4;
int tmp___5;
int tmp___6;
tmp___6 = Inhibit_Biased_Climb();
if (tmp___6 > Down_Separation) {
  tmp = Own_Below_Threat();
if (tmp) {
  if (Cur_Vertical_Sep >= 300) {
  tmp___0 = ALIM();
if (Down_Separation >= tmp___0) {
  tmp___1 = 1;
} else {
tmp___1 = 0;
}
} else {
tmp___1 = 0;
}
} else {
tmp___1 = 0;
}
result = __bool_of_int___(tmp___1);
} else {
tmp___2 = Own_Above_Threat();
if (tmp___2) {
  tmp___3 = Own_Above_Threat();
if (tmp___3) {
  tmp___4 = ALIM();
if (Up_Separation >= tmp___4) {
  tmp___5 = 1;
} else {
tmp___5 = 0;
}
} else {
tmp___5 = 0;
}
} else {
tmp___5 = 1;
}
result = __bool_of_int___(tmp___5);
}
return result;
}
int alt_sep_test()

requires Positive_RA_Alt_Thresh::node<a,b,c,d> & (High_Confidence) & ((Own_Tracked_Alt_Rate <= 600) & ((Cur_Vertical_Sep > 600) & ((((Two_of_Three_Reports_Valid) & (Other_RAC = 0)) | (!(Other_Capability = 1))) & ((Climb_Inhibit = 1) & (((Up_Separation+100) <= Down_Separation) & ((Alt_Layer_Value = 0) & ((Own_Tracked_Alt > Other_Tracked_Alt) & (Up_Separation >= a))))))))
ensures Positive_RA_Alt_Thresh::node<a,b,c,d> & (High_Confidence) & ((Own_Tracked_Alt_Rate <= 600) & ((Cur_Vertical_Sep > 600) & ((((Two_of_Three_Reports_Valid) & (Other_RAC = 0)) | (!(Other_Capability = 1))) & ((Climb_Inhibit = 1) & (((Up_Separation+100) <= Down_Separation) & ((Alt_Layer_Value = 0) & ((Own_Tracked_Alt > Other_Tracked_Alt) & ((Up_Separation >= a) & (res = 2)))))))));
requires Positive_RA_Alt_Thresh::node<a,b,c,d> & (High_Confidence) & ((Own_Tracked_Alt_Rate <= 600) & ((Cur_Vertical_Sep > 600) & ((((Two_of_Three_Reports_Valid) & (Other_RAC = 0)) | (!(Other_Capability = 1))) & ((Climb_Inhibit = 1) & (((Up_Separation+100) > Down_Separation) & ((Alt_Layer_Value = 0) & ((Own_Tracked_Alt < Other_Tracked_Alt) & (Down_Separation < a))))))))
ensures Positive_RA_Alt_Thresh::node<a,b,c,d> & (High_Confidence) & ((Own_Tracked_Alt_Rate <= 600) & ((Cur_Vertical_Sep > 600) & ((((Two_of_Three_Reports_Valid) & (Other_RAC = 0)) | (!(Other_Capability = 1))) & ((Climb_Inhibit = 1) & (((Up_Separation+100) > Down_Separation) & ((Alt_Layer_Value = 0) & ((Own_Tracked_Alt < Other_Tracked_Alt) & ((Down_Separation < a) & (res = 1)))))))));
{
bool enabled;
bool tcas_equipped;
bool intent_not_known;
bool need_upward_RA;
bool need_downward_RA;
int alt_sep;
int tmp;
int tmp___0;
bool tmp___1;
bool tmp___2;
int tmp___3;
bool tmp___4;
bool tmp___5;
int tmp___6;
alt_sep = 0;
if (High_Confidence) {
  if (Own_Tracked_Alt_Rate <= 600) {
  if (Cur_Vertical_Sep > 600) {
  tmp = 1;
} else {
tmp = 0;
}
} else {
tmp = 0;
}
} else {
tmp = 0;
}
enabled = __bool_of_int___(tmp);
tcas_equipped = Other_Capability == 1;
if (Two_of_Three_Reports_Valid) {
  if (Other_RAC == 0) {
  tmp___0 = 1;
} else {
tmp___0 = 0;
}
} else {
tmp___0 = 0;
}
intent_not_known = __bool_of_int___(tmp___0);
tmp___1 = Non_Crossing_Biased_Climb();
if (tmp___1) {
  tmp___2 = Own_Below_Threat();
if (tmp___2) {
  tmp___3 = 1;
} else {
tmp___3 = 0;
}
} else {
tmp___3 = 0;
}
need_upward_RA = __bool_of_int___(tmp___3);
tmp___4 = Non_Crossing_Biased_Descend();
if (tmp___4) {
  tmp___5 = Own_Above_Threat();
if (tmp___5) {
  tmp___6 = 1;
} else {
tmp___6 = 0;
}
} else {
tmp___6 = 0;
}
need_downward_RA = __bool_of_int___(tmp___6);
if (enabled) {
  if (tcas_equipped) {
  if (intent_not_known) {
  if (need_upward_RA) {
  if (need_downward_RA) {
  alt_sep = 0;
} else {
if (need_upward_RA) {
  alt_sep = 1;
} else {
if (need_downward_RA) {
  alt_sep = 2;
} else {
alt_sep = 0;
}
}
}
} else {
if (need_upward_RA) {
  alt_sep = 1;
} else {
if (need_downward_RA) {
  alt_sep = 2;
} else {
alt_sep = 0;
}
}
}
} else {
if (!tcas_equipped) {
  if (need_upward_RA) {
  if (need_downward_RA) {
  alt_sep = 0;
} else {
if (need_upward_RA) {
  alt_sep = 1;
} else {
if (need_downward_RA) {
  alt_sep = 2;
} else {
alt_sep = 0;
}
}
}
} else {
if (need_upward_RA) {
  alt_sep = 1;
} else {
if (need_downward_RA) {
  alt_sep = 2;
} else {
alt_sep = 0;
}
}
}
}
}
} else {
if (!tcas_equipped) {
  if (need_upward_RA) {
  if (need_downward_RA) {
  alt_sep = 0;
} else {
if (need_upward_RA) {
  alt_sep = 1;
} else {
if (need_downward_RA) {
  alt_sep = 2;
} else {
alt_sep = 0;
}
}
}
} else {
if (need_upward_RA) {
  alt_sep = 1;
} else {
if (need_downward_RA) {
  alt_sep = 2;
} else {
alt_sep = 0;
}
}
}
}
}
}
return alt_sep;
}


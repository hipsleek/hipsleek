
global int Up_Separation;
global int Other_Tracked_Alt;
global int Own_Tracked_Alt;

bool Non_Crossing_Biased_Descend()
   requires true
    case {
       Other_Tracked_Alt < Own_Tracked_Alt->
       case {
         Up_Separation >= 400 -> ensures res ;
         Up_Separation < 400 ->  ensures !res ;
       }
       Other_Tracked_Alt >= Own_Tracked_Alt ->  ensures res;
   }
{
    bool result;
   	result = 
	(!(Own_Above_Threat())) 
	|| ((Own_Above_Threat()) 
	&& (Up_Separation >= 400)); 

    return result;
}

bool Own_Above_Threat()
case {
   Other_Tracked_Alt < Own_Tracked_Alt -> ensures res & Other_Tracked_Alt'=Other_Tracked_Alt & Own_Tracked_Alt'=Own_Tracked_Alt;
   Other_Tracked_Alt >= Own_Tracked_Alt -> ensures !res & Other_Tracked_Alt'=Other_Tracked_Alt & Own_Tracked_Alt'=Own_Tracked_Alt;
   }
{
    return (Other_Tracked_Alt < Own_Tracked_Alt);
}

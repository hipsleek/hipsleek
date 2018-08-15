global int Own_Tracked_Alt;
global int Other_Tracked_Alt;

bool Own_Below_Threat()
  requires (Own_Tracked_Alt < Other_Tracked_Alt) ensures res = true;
  requires (Own_Tracked_Alt >= Other_Tracked_Alt) ensures res = false;
{
  return (Own_Tracked_Alt - Other_Tracked_Alt <= 0);
}

bool Own_Above_Threat()
     requires (Other_Tracked_Alt < Own_Tracked_Alt) ensures res = true;
     requires (Other_Tracked_Alt >= Own_Tracked_Alt) ensures res = false;

{
    return (Other_Tracked_Alt - Own_Tracked_Alt <= 0);
}

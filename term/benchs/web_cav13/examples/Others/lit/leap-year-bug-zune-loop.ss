/***********************************************************
Example about the non-terminating bug of Zune's clock driver
Source: http://pastie.org/349916
***********************************************************/

void ConvertDays (int days)
requires MayLoop
ensures true;
{
	int year = 1980; /* = 1980 */
	loop (days, year);
}

void loop (ref int days, ref int year)
case {
	days<=365 -> requires Term ensures days'=days & year'=year;
  days=366 -> 
		//If year is a leap year then the program does not terminate.
		case {
			(exists (k1: year=400*k1)) -> requires Loop ensures false;
			!(exists (k2: year=400*k2)) -> case {
				(exists (k3: year=100*k3)) -> requires Term ensures days'<=365 & year'>year;
				!(exists (k4: year=100*k4)) -> case {
					(exists (k5: year=4*k5)) -> requires Loop ensures false;
					!(exists (k6: year=4*k6)) -> requires Term ensures days'<=365 & year'>year;
				}
			}
		}
	days>366 -> requires Term[days] ensures days'<=365 & year'>year;
}

{
	if (days > 365)
	{
		if (IsLeapYear(year))
		{
			if (days > 366)
			{
				days -= 366;
				year += 1;
			}
		}
		else 
		{
			days -= 365;
			year += 1;
		}
		loop(days, year); //(ERR: not decreasing) when 365<days<=366
	}
}

bool IsLeapYear (int Year)
requires Term
case {
	(exists (k1: Year=400*k1)) -> ensures res;
	!(exists (k2: Year=400*k2)) -> case {
		(exists (k3: Year=100*k3)) -> ensures !res;
		!(exists (k4: Year=100*k4)) -> case {
			(exists (k5: Year=4*k5)) -> ensures res;
			!(exists (k6: Year=4*k6)) -> ensures !res;
		}
	}
}
{
	if (Year % 400 == 0) 
		return true;
	else if (Year % 100 == 0)
		return false;
	else if (Year % 4 == 0)
		return true;
	else
		return false;
}


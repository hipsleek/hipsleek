/***********************************************************
Example about the non-terminating bug of Zune's clock driver
Source: http://pastie.org/349916
***********************************************************/

void ConvertDays (int days)
requires Term
ensures true;
{
	int year = 1980; /* = 1980 */
	loop (days, year);
}

relation is_leap_year (int year) == 
	(exists (k1: year=400*k1)) | (!(exists (k2: year=100*k2)) & (exists (k3: year=4*k3))).

void loop (ref int days, ref int year)
case {
	days<=365 -> requires Term ensures days'=days & year'=year;
  days=366 -> 
		requires is_leap_year(year) & Loop ensures false;
		requires !(is_leap_year(year)) & Term ensures days'<=365 & year'>year;
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
			//loop(days, year);
		}
		else 
		{
			days -= 365;
			year += 1;
			//loop(days, year);
		}
		loop(days, year); //(ERR: not decreasing) when 365<days<=366
	}
}

bool IsLeapYear (int Year)
requires Term
ensures is_leap_year(Year);
{
	bool Leap = false; 
	if ((Year % 4) == 0) {
		Leap = true;
		if ((Year % 100) == 0) {
			if ((Year % 400) == 0)
				Leap = true;
			else
				Leap = false;
		}
	}
	return (Leap);
}


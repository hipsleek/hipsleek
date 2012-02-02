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

void loop (ref int days, ref int year)

case {
	days<=365 -> requires Term ensures days'=days & year'=year;
  days>365 -> requires Term[days] ensures days'<=365 & year'>year;
}

/*
case {
	days<=365 -> requires Term ensures days'=days & year'=year;
  days>365 -> requires MayLoop ensures days'<=365 & year'>year;
}
*/
/*
case {
	days<=365 -> requires Term ensures days'=days & year'=year;
  days=366 -> requires Loop ensures false;
	days>366 -> requires Term[days] ensures days'<=365 & year'>year;
}
*/
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
ensures true;
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


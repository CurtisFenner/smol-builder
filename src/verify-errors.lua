local Report = {}

function Report.DOES_NOT_MODEL(p)
	quit("You must show that ", p.reason, " holds as defined ", p.conditionLocation,
		"\nHowever, you have not shown that condition holds ", p.checkLocation)
end

return Report

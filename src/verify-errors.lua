local Report = {}

function Report.DOES_NOT_MODEL(p)
	quit("You must show ", p.reason, " ", p.conditionLocation,
		"\nHowever, you have not shown that condition to hold ", p.checkLocation)
end

return Report

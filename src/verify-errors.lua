local Report = {}

function Report.DOES_NOT_MODEL(p)
	local ruled = "\nHowever, you have not disproved the possibility that"

	-- Show true statements first
	for _, kv in ipairs(p.counter) do
		if kv.truth then
			ruled = ruled .. "\n\ttrue: " .. kv.expression
		end
	end

	assertis(p.counter, listType(recordType {truth = "boolean", expression = "string"}))

	-- Show false statements last
	for _, kv in ipairs(p.counter) do
		if not kv.truth then
			ruled = ruled .. "\n\tfalse: " .. kv.expression
		end
	end

	if p.conditionLocation == p.checkLocation then
		quit("You must show that ", p.reason, " holds as defined ", p.conditionLocation, ruled)
	end
	quit(
		"You must show that ",
		p.reason,
		" holds as defined ",
		p.conditionLocation,
		ruled,
		"\n",
		p.checkLocation
	)
end

return Report
